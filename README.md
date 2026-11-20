# SGPT in Lean

A Lean 4 formalization of Mingchen Xia’s SGPT book. Import `SGPT` for the main
development. The [book index](Book/index.json) and
[coverage ledger](Book/coverage.json) map manuscript labels to Lean declarations.

The ledger maps 848 manuscript entries to Lean declarations and records 93
checked equation anchors. Five entries are prose only. The envelope conjecture
remains open and is included as a Lean statement.
[Manuscript revision `4390e77`](https://github.com/MingchenXia/SGPT/tree/4390e77497d699ac3a4f878b97c34fc867513add).

## Build

The project pins Lean 4.33.1 and Mathlib. From a fresh checkout with Elan installed,
run:

```sh
lake exe cache get
lake build
```

For the main book module only, run `lake build +SGPT`.

| Location | Contents |
| --- | --- |
| `SGPT/` | Book definitions, theorems, and proofs |
| `SGPT/Addenda/` | Additional resolution and Okounkov results |
| `SGPT/Foundations/` and `SGPT/Support/` | Analytic and algebraic infrastructure |
| `SGPT/Checks/` | Separate comparison and reference checks |
| `Audit/` | Declaration checks for each target |

`SGPT.Checks.Literature` uses the published version of the external comparison
library. The other `SGPT.Checks` entry points use a separate version. Keep these
versions in separate Lean import environments because they define some of the
same global names. Run each audit file in its own Lean process after building:

```sh
for file in Audit/*.lean; do
  lake env lean "$file" || exit
done
```

## Contributors

- Mingchen Xia
- Jian Wang
- Siqi He

## License

The formalization is available under the [Apache License 2.0](LICENSE).
See [NOTICE](NOTICE) for third-party attributions.

## Build cache

The three complete checkpoints passed their declaration audits and a clean
restore in GitHub Actions. They cover 19,089 distinct Lean modules across the
three profiles, which share some imports.

| Profile | Modules | Complete checkpoint |
| --- | ---: | --- |
| Core | 9,831 | [Cache](https://github.com/MingchenXia/SGPT-lean/tree/build-cache/checkpoints/core) |
| Comparison | 8,312 | [Cache](https://github.com/MingchenXia/SGPT-lean/tree/build-cache/checkpoints/comparison) |
| Literature comparison | 6,327 | [Cache](https://github.com/MingchenXia/SGPT-lean/tree/build-cache/checkpoints/literature) |

GitHub Actions publishes new and partial checkpoints under
`checkpoints/<profile>/<source-commit>` on the shared
[`build-cache` branch](https://github.com/MingchenXia/SGPT-lean/tree/build-cache).
A partial checkpoint contains the checked modules and their import closure.
Every manifest records the module count, expected total, status, source commit,
compiler, dependency commits, and artifact hashes.
Mathlib and its dependencies use the pinned upstream cache. Native executable
and shared-library outputs are outside the Lean import cache.

After installing the pinned dependencies with `lake exe cache get`, use
`scripts/build_profile.sh core /path/to/build --workers 4` to build and audit
the core profile. Set `SGPT_CACHE_OUTPUT` to a new directory to make a cache
snapshot. A completed snapshot requires the profile audits to pass. Run the
other profiles independently.

To restore a checkpoint, check out the source commit named in its manifest
and download that checkpoint's `MANIFEST.json` and `chunks/` directory. The
restore command checks the toolchain and dependency artifact hashes before
installing files under a new local artifact directory:

```sh
dependency_args=()
IFS=: read -r -a dependency_dirs <<< "$(lake env printenv LEAN_PATH)"
for dir in "${dependency_dirs[@]}"; do
  if [ -d "$dir" ]; then dependency_args+=(--dependency-root "$dir"); fi
done
python3 scripts/build_cache.py --lean "$(elan which lean)" "${dependency_args[@]}" \
  restore /path/to/checkpoint /path/to/restored/lean
LEAN_PATH="/path/to/restored/lean:$(lake env printenv LEAN_PATH)" lean Audit/SGPT.lean
```

Use the audit file corresponding to the restored profile. This cache is for
Lean imports and editor metadata. A standard `lake build` can also generate
Lake traces and native outputs.

To continue compilation from a partial checkpoint, pass `--for-build` to
`restore` and use the destination as the build directory for
`scripts/build_profile.sh`. The builder rechecks the restored receipts against
the current sources and rebuilds modules whose inputs changed.
