#!/usr/bin/env python3
"""Snapshot or restore a fully checked set of SGPT import roots."""

import argparse
import fcntl
from functools import cache
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import tarfile
import tempfile

from build_artifacts import FLAGS, OUTPUT_FACETS, digest, graph, import_hashes, stem

FORMAT = "sgpt-build-cache-v1"
CHUNK_BYTES = 45 * 1024 ** 2


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_json(path):
    return json.loads(path.read_text())


def file_info(path):
    return {"sha256": digest(path), "bytes": path.stat().st_size}


def git(source, *arguments):
    return subprocess.check_output(["git", "-C", source, *arguments], text=True).strip()


def project_info(source, lean):
    commit = git(source, "rev-parse", "HEAD")
    pinned = ("SGPT", "SGPT.lean", "lean-toolchain", "lake-manifest.json", "lakefile.toml")
    require(not git(source, "status", "--porcelain", "--untracked-files=all", "--", *pinned),
            "The Lean source and pins must match the checked-out commit")
    packages = read_json(source / "lake-manifest.json")["packages"]
    require(all(p.get("type") == "git" and p.get("rev") for p in packages),
            "Every external Lake dependency must have an exact Git revision")
    return {
        "source_commit": commit,
        "source_tree": git(source, "rev-parse", "HEAD^{tree}"),
        "toolchain": (source / "lean-toolchain").read_text().strip(),
        "lean_version": subprocess.check_output([lean, "--version"], text=True).strip(),
        "lean_sha256": digest(lean),
        "platform": {"system": platform.system(), "machine": platform.machine()},
        "lake_manifest_sha256": digest(source / "lake-manifest.json"),
        "dependencies": {p["name"]: {"url": p["url"], "commit": p["rev"]} for p in packages},
        "flags": list(FLAGS),
    }


class ChunkWriter:
    """Split a deterministic gzip stream into files small enough for GitHub."""

    def __init__(self, directory):
        self.directory = directory
        self.directory.mkdir()
        self.chunks = []
        self.file = None
        self.remaining = 0

    def write(self, data):
        pending = memoryview(data)
        while pending:
            if not self.remaining:
                self.finish_chunk()
                self.path = self.directory / f"{len(self.chunks):04d}.part"
                self.file = self.path.open("xb")
                self.remaining = CHUNK_BYTES
            count = min(self.remaining, len(pending))
            self.file.write(pending[:count])
            self.remaining -= count
            pending = pending[count:]
        return len(data)

    def finish_chunk(self):
        if self.file is not None:
            self.file.close()
            self.chunks.append({"name": self.path.name, **file_info(self.path)})
            self.file = None


class ChunkReader(io.RawIOBase):
    """Check each chunk while streaming the concatenated gzip data."""

    def __init__(self, directory, chunks):
        self.directory = directory
        self.chunks = iter(chunks)
        self.file = None

    def readable(self):
        return True

    def readinto(self, output):
        while True:
            if self.file is None:
                info = next(self.chunks, None)
                if info is None:
                    return 0
                path = self.directory / info["name"]
                require(path.name == info["name"] and path.is_file() and not path.is_symlink(),
                        f"Invalid archive chunk {path}")
                self.info = info
                self.file = path.open("rb")
                self.sha = hashlib.sha256()
                self.size = 0
            count = self.file.readinto(output)
            if count:
                self.sha.update(memoryview(output)[:count])
                self.size += count
                return count
            self.file.close()
            self.file = None
            require(self.sha.hexdigest() == self.info["sha256"] and self.size == self.info["bytes"],
                    f"Corrupt archive chunk {self.info['name']}")

    def close(self):
        if self.file is not None:
            self.file.close()
        super().close()


def snapshot(args, source, lean, info):
    root = args.artifact_root.resolve(strict=True)
    output = args.output.resolve()
    require(not output.exists(), f"Snapshot output already exists: {output}")
    output.parent.mkdir(parents=True, exist_ok=True)
    modules, external = graph(source, args.entry)
    require(all(entry in modules for entry in args.entry), "All snapshot roots must be local")
    external_artifacts = {name: import_hashes(lean, args.dependency_root, name)
                          for name in sorted(external)}
    settings = {"lean_sha256": info["lean_sha256"], "flags": info["flags"]}
    with (root / "build.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)

        @cache
        def checked(name):
            prefix = stem(name)
            try:
                receipt_path = root / "checks" / f"{name}.json"
                receipt = read_json(receipt_path)
                dependencies = modules[name]
                source_hash = digest(source / (prefix + ".lean"))
                require(receipt["module"] == name and receipt["source_sha256"] == source_hash
                        and receipt["settings"] == settings, f"Stale build receipt for {name}")
                imports = {}
                for dep in dependencies:
                    if dep in external_artifacts:
                        imports[dep] = external_artifacts[dep]
                    else:
                        parent = checked(dep)
                        require(parent is not None, f"Unchecked import {dep} used by {name}")
                        imports[dep] = {tag: item["sha256"] for tag, item in parent[1]["artifacts"].items()}
                require(receipt["inputs"] == imports, f"Mismatched imports for {name}")
                facets = receipt["artifacts"]
                require({".olean", ".ilean"} <= facets.keys() <= set(OUTPUT_FACETS),
                        f"Incomplete compiler outputs for {name}")
                artifacts = {}
                for tag, sha in sorted(facets.items()):
                    path = root / "lean" / (prefix + tag)
                    require(path.is_file() and not path.is_symlink(), f"Missing regular artifact: {path}")
                    actual = file_info(path)
                    require(actual["sha256"] == sha, f"Stale artifact {path}")
                    artifacts[tag] = actual
            except (FileNotFoundError, ValueError):
                if args.partial:
                    return None
                raise
            return (receipt.get("completed_ns", receipt_path.stat().st_mtime_ns),
                    {"source_sha256": source_hash, "imports": list(dependencies), "artifacts": artifacts})

        records = [(name, *result) for name in modules if (result := checked(name)) is not None]
        # A later pass appends objects in build order, keeping existing full chunks reusable.
        records.sort(key=lambda item: (item[1], item[0]))
        records = {name: record for name, _, record in records}
        require(bool(records), "No modules with reusable, import-closed build evidence")
        imported = {dep for record in records.values() for dep in record["imports"]}
        roots = sorted(records.keys() - imported) if args.partial else args.entry
        archived_external = {name: hashes for name, hashes in external_artifacts.items() if name in imported}
        with tempfile.TemporaryDirectory(dir=output.parent) as scratch:
            stage = Path(scratch)
            writer = ChunkWriter(stage / "chunks")
            try:
                with gzip.GzipFile(fileobj=writer, mode="wb", compresslevel=6, mtime=0) as compressed:
                    with tarfile.open(fileobj=compressed, mode="w|", format=tarfile.PAX_FORMAT) as archive:
                        for name, record in records.items():
                            prefix = stem(name)
                            for tag, actual in record["artifacts"].items():
                                path = root / "lean" / (prefix + tag)
                                member = tarfile.TarInfo(prefix + tag)
                                member.size = actual["bytes"]
                                member.mode = 0o644
                                with path.open("rb") as stream:
                                    archive.addfile(member, stream)
            finally:
                writer.finish_chunk()
            require(info == project_info(source, lean), "Source changed during snapshot")
            manifest = {"format": FORMAT, **info, "roots": roots, "modules": records,
                        "external_imports": archived_external, "chunks": writer.chunks,
                        "requested_roots": args.entry, "verified_modules": len(records),
                        "expected_modules": len(modules),
                        "status": "partial" if args.partial else "complete"}
            (stage / "MANIFEST.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
            stage.rename(output)
    print(f"Archived {len(records)}/{len(modules)} modules in {len(writer.chunks)} chunks at {output}")


def restore(args, source, lean, info):
    snapshot_root = args.snapshot.resolve(strict=True)
    manifest = read_json(snapshot_root / "MANIFEST.json")
    require(manifest["format"] == FORMAT and all(manifest.get(k) == v for k, v in info.items()),
            "Snapshot requires its original source commit, compiler and dependency pins")
    modules, external = graph(source, manifest["roots"])
    require(modules.keys() == manifest["modules"].keys() and external == manifest["external_imports"].keys(),
            "Snapshot import closure does not match the source")
    for name in sorted(external):
        require(import_hashes(lean, args.dependency_root, name) == manifest["external_imports"][name],
                f"External artifact mismatch for {name}")
    files = {}
    for name, dependencies in modules.items():
        record = manifest["modules"][name]
        prefix = stem(name)
        require(record["source_sha256"] == digest(source / (prefix + ".lean"))
                and record["imports"] == list(dependencies), f"Source differs for {name}")
        require({".olean", ".ilean"} <= record["artifacts"].keys() <= set(OUTPUT_FACETS),
                f"Missing required cache facets for {name}")
        files.update((prefix + tag, (name, entry)) for tag, entry in record["artifacts"].items())
    destination = args.destination.resolve()
    require(not destination.exists(), f"Restore destination already exists: {destination}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=destination.parent) as scratch:
        stage = Path(scratch)
        artifact_directory = stage / "lean" if args.for_build else stage
        order = {}
        with io.BufferedReader(ChunkReader(snapshot_root / "chunks", manifest["chunks"])) as chunks:
            with gzip.GzipFile(fileobj=chunks) as compressed:
                with tarfile.open(fileobj=compressed, mode="r|") as archive:
                    for member in archive:
                        require(member.name in files and member.isfile(), f"Unexpected archive member {member.name}")
                        name, entry = files.pop(member.name)
                        require(member.size == entry["bytes"], f"Unexpected artifact size: {member.name}")
                        order.setdefault(name, len(order))
                        target = artifact_directory / member.name
                        target.parent.mkdir(parents=True, exist_ok=True)
                        with archive.extractfile(member) as stream, target.open("xb") as output:
                            shutil.copyfileobj(stream, output)
                        require(file_info(target) == entry, f"Artifact hash mismatch: {member.name}")
                while compressed.read(1024 * 1024):
                    pass
            require(not chunks.read(1), "Extra bytes in compressed archive")
        require(not files, f"Missing archive artifacts: {len(files)}")
        if args.for_build:
            evidence = stage / "checks"
            evidence.mkdir()
            (stage / "build.lock").touch()
            records = manifest["modules"]
            hashes = {name: {tag: item["sha256"] for tag, item in record["artifacts"].items()}
                      for name, record in records.items()}
            hashes.update(manifest["external_imports"])
            settings = {"lean_sha256": info["lean_sha256"], "flags": info["flags"]}
            for name, record in records.items():
                receipt = {"module": name, "source_sha256": record["source_sha256"], "settings": settings,
                           "inputs": {dep: hashes[dep] for dep in record["imports"]},
                           "artifacts": hashes[name], "completed_ns": order[name]}
                (evidence / (name + ".json")).write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
        stage.rename(destination)
    print(f"Restored {len(modules)} checked modules at {destination}")


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--source", type=Path, default=Path.cwd())
    cli.add_argument("--lean", type=Path, required=True)
    cli.add_argument("--dependency-root", type=Path, action="append", default=[])
    commands = cli.add_subparsers(dest="command", required=True)

    capture = commands.add_parser("snapshot")
    capture.add_argument("--artifact-root", type=Path, required=True)
    capture.add_argument("--output", type=Path, required=True)
    capture.add_argument("--partial", action="store_true",
                         help="Archive the import-closed set with current build receipts.")
    capture.add_argument("entry", nargs="+", metavar="MODULE")

    restore_cli = commands.add_parser("restore")
    restore_cli.add_argument("--for-build", action="store_true",
                             help="Restore an artifact root with receipts for resuming the build.")
    restore_cli.add_argument("snapshot", type=Path)
    restore_cli.add_argument("destination", type=Path)

    args = cli.parse_args()
    source = args.source.resolve(strict=True)
    lean = args.lean.resolve(strict=True)
    args.dependency_root = tuple(path.resolve(strict=True) for path in args.dependency_root)
    try:
        function = snapshot if args.command == "snapshot" else restore
        function(args, source, lean, project_info(source, lean))
    except (ValueError, OSError) as exc:
        cli.exit(1, f"{exc}\n")


if __name__ == "__main__":
    main()
