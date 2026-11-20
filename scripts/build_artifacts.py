#!/usr/bin/env python3
"""Build the checked Lean import graph into an isolated artifact directory."""

import argparse
from collections import defaultdict, deque
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from functools import cache
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

IMPORT = re.compile(r"(?:(?:public|private|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?(.+)")
COMMENT = re.compile(r"/-|-/|--")
ERROR_HEADER = re.compile(r"^.*\.lean:\d+:\d+: error\b")
FACETS = (".olean", ".olean.private", ".olean.server", ".ir.sig", ".ir")
OUTPUT_FACETS = (*FACETS, ".ilean")
FLAGS = ("-j1", "-DElab.async=false", "-DautoImplicit=false", "-Dpp.unicode.fun=true")


class LeanBuildError(RuntimeError):
    """A module failed compilation while independent modules can still build."""


def imports(path):
    depth = 0
    for line in path.read_text().splitlines():
        offset = 0
        visible = ""
        for mark in COMMENT.finditer(line):
            if not depth:
                visible += line[offset:mark.start()]
                if mark[0] == "--":
                    break
            if mark[0] == "/-":
                depth += 1
            elif mark[0] == "-/" and depth:
                depth -= 1
            offset = mark.end()
        else:
            if not depth:
                visible += line[offset:]
        visible = visible.strip()
        if not visible or visible in {"module", "prelude"}:
            continue
        match = IMPORT.fullmatch(visible)
        if not match:
            break
        yield from match[1].split()


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def stem(module):
    return module.replace(".", "/")


def graph(source, entries):
    dependencies = {}
    external = set()

    def visit(module):
        if module in dependencies or module in external:
            return
        path = source / (stem(module) + ".lean")
        if not path.is_file():
            external.add(module)
            return
        dependencies[module] = tuple(imports(path))
        for dependency in dependencies[module]:
            visit(dependency)

    for module in entries:
        visit(module)
    return dependencies, external


def import_hashes(lean, dependency_roots, module):
    name = stem(module)
    for root in (*dependency_roots, lean.parent.parent / "lib/lean"):
        if (root / (name + ".olean")).is_file():
            return {tag: digest(root / (name + tag)) for tag in FACETS
                    if (root / (name + tag)).is_file()}
    raise FileNotFoundError(f"Pinned dependency artifact missing for {module}")


def install_artifacts(staged, output, artifacts):
    for tag in OUTPUT_FACETS:
        if tag in artifacts:
            staged.with_suffix(tag).replace(output.with_suffix(tag))
        else:
            output.with_suffix(tag).unlink(missing_ok=True)


def write_receipt(path, receipt):
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    temporary.replace(path)


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--source", type=Path, default=Path.cwd())
    cli.add_argument("--lean", type=Path, required=True)
    cli.add_argument("--artifact-root", type=Path, required=True)
    cli.add_argument("--dependency-root", type=Path, action="append", default=[])
    cli.add_argument("--seed-root", type=Path, action="append", default=[],
                     help="Reuse matching modules from another checked artifact directory.")
    cli.add_argument("--workers", type=int, default=2)
    cli.add_argument("--limit", type=int)
    cli.add_argument("--minutes", type=float, help="Stop starting new modules at this wall-clock limit.")
    cli.add_argument("--failure-grace-minutes", type=float, default=0,
                     help="Build independent modules for this long after the first Lean error.")
    cli.add_argument("entry", nargs="+", metavar="MODULE")
    args = cli.parse_args()
    source, lean = args.source.resolve(), args.lean.resolve(strict=True)
    artifact = args.artifact_root.resolve()
    seeds = tuple(dict.fromkeys(root.resolve(strict=True) for root in args.seed_root))
    if artifact in seeds:
        cli.error("The build output cannot also be a supplemental seed")
    binaries = artifact / "lean"
    evidence = artifact / "checks"
    binaries.mkdir(parents=True, exist_ok=True)
    evidence.mkdir(exist_ok=True)
    lock = (artifact / "build.lock").open("a")
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        cli.error(f"Another operation is using {artifact}")
    seed_locks = []
    for root in seeds:
        seed_lock = (root / "build.lock").open("r")
        try:
            fcntl.flock(seed_lock, fcntl.LOCK_SH | fcntl.LOCK_NB)
        except BlockingIOError:
            cli.error(f"Another operation is writing the seed {root}")
        seed_locks.append(seed_lock)
    dependency_roots = tuple(root.resolve(strict=True) for root in args.dependency_root)
    settings = {"lean_sha256": digest(lean), "flags": list(FLAGS)}
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, (binaries, *dependency_roots))))
    dependencies, external = graph(source, args.entry)
    if any(module in external for module in args.entry):
        cli.error("Every entry point must have local source")
    @cache
    def external_hashes(module):
        return import_hashes(lean, dependency_roots, module)

    pending = {}
    reverse = defaultdict(list)
    for module, names in dependencies.items():
        parents = set(names) - external
        pending[module] = len(parents)
        for parent in parents:
            reverse[parent].append(module)
    ready = deque(sorted(module for module, count in pending.items() if count == 0))
    results = {}
    started = 0
    reused = 0

    def matching_cache(module, expected):
        for root in (artifact, *seeds):
            candidate = root / "checks" / (module + ".json")
            if not candidate.is_file():
                continue
            receipt = json.loads(candidate.read_text())
            if any(receipt.get(key) != value for key, value in expected.items()):
                continue
            output = root / "lean" / (stem(module) + ".olean")
            archived = receipt.get("artifacts", {})
            if {".olean", ".ilean"} <= archived.keys() <= set(OUTPUT_FACETS) and all(
                output.with_suffix(tag).is_file() and digest(output.with_suffix(tag)) == sha
                for tag, sha in archived.items()
            ):
                return output, receipt
        return None, None

    def checked(module):
        path = source / (stem(module) + ".lean")
        output = binaries / (stem(module) + ".olean")
        receipt_path = evidence / (module + ".json")
        inputs = {dependency: (external_hashes(dependency) if dependency in external else results[dependency])
                  for dependency in dependencies[module]}
        expected = {"module": module, "source_sha256": digest(path), "settings": settings, "inputs": inputs}
        cached_output, receipt = matching_cache(module, expected)
        if cached_output == output:
            return receipt["artifacts"], True
        if shutil.disk_usage(artifact).free < 300 * 1024 ** 2:
            raise OSError("Insufficient workspace space for another artifact")
        output.parent.mkdir(parents=True, exist_ok=True)
        if cached_output is not None:
            artifacts = receipt["artifacts"]
            with tempfile.TemporaryDirectory(dir=artifact) as scratch:
                staged = Path(scratch) / output.name
                for tag in artifacts:
                    shutil.copyfile(cached_output.with_suffix(tag), staged.with_suffix(tag))
                if digest(path) != expected["source_sha256"]:
                    raise RuntimeError(f"Source changed while reusing {module}")
                install_artifacts(staged, output, artifacts)
            receipt["completed_ns"] = time.time_ns()
            write_receipt(receipt_path, receipt)
            return artifacts, True
        print(f"Checking {module}", flush=True)
        begin = time.monotonic()
        log = evidence / (module + ".log")
        with tempfile.TemporaryDirectory(dir=artifact) as scratch:
            staged = Path(scratch) / output.name
            with log.open("wb") as stream:
                status = subprocess.run([str(lean), *FLAGS, f"--root={source}", "-o", str(staged),
                                         "-i", str(staged.with_suffix(".ilean")), str(path)],
                                        env=env, cwd=source, stdout=stream, stderr=subprocess.STDOUT).returncode
            if status:
                headers = []
                tail = deque(maxlen=60)
                with log.open(errors="replace") as stream:
                    for line in stream:
                        if len(headers) < 20 and ERROR_HEADER.match(line):
                            headers.append(line)
                        tail.append(line)
                diagnostics = "".join(headers + list(tail))
                raise LeanBuildError(f"Lean failed for {module}. See {log}\n{diagnostics}")
            if digest(path) != expected["source_sha256"]:
                raise RuntimeError(f"Source changed while compiling {module}")
            artifacts = {tag: digest(staged.with_suffix(tag)) for tag in OUTPUT_FACETS
                         if staged.with_suffix(tag).is_file()}
            if {".olean", ".ilean"} - artifacts.keys():
                raise RuntimeError(f"Missing compiler output for {module}")
            install_artifacts(staged, output, artifacts)
        expected.update(artifacts=artifacts, elapsed_seconds=round(time.monotonic() - begin, 3),
                        completed_ns=time.time_ns())
        write_receipt(receipt_path, expected)
        return artifacts, False

    with ThreadPoolExecutor(max_workers=args.workers) as executor:
        running = {}
        failures = []
        deadline = time.monotonic() + args.minutes * 60 if args.minutes is not None else float("inf")
        while ready or running:
            while (ready and len(running) < args.workers and time.monotonic() < deadline
                   and (args.limit is None or started < args.limit)):
                module = ready.popleft()
                running[executor.submit(checked, module)] = module
                started += 1
            if not running:
                break
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in done:
                module = running.pop(future)
                try:
                    results[module], cached = future.result()
                except LeanBuildError as exc:
                    if args.failure_grace_minutes <= 0:
                        raise
                    if not failures:
                        deadline = min(deadline, time.monotonic() + args.failure_grace_minutes * 60)
                    failures.append(module)
                    print(str(exc), flush=True)
                    continue
                reused += int(cached)
                print(f"Verified {len(results)}/{len(dependencies)} {module}", flush=True)
                for dependent in reverse[module]:
                    pending[dependent] -= 1
                    if pending[dependent] == 0:
                        ready.append(dependent)
    complete = len(results) == len(dependencies)
    print(json.dumps({"checked_modules": len(results), "modules": len(dependencies), "reused": reused,
                      "complete": complete, "failures": failures}))
    if failures:
        raise SystemExit(1)
    if not complete and args.minutes is not None and time.monotonic() >= deadline:
        raise SystemExit(75)
    if not complete and args.limit is None:
        raise RuntimeError("The compile graph did not finish. Check for dependency cycles.")


if __name__ == "__main__":
    main()
