#!/usr/bin/env bash
set -euo pipefail

if (( $# < 2 )); then
    printf 'Usage: %s PROFILE BUILD_DIRECTORY [build options]\n' "$0" >&2
    exit 2
fi

profile=$1
build=$2
shift 2

case "$profile" in
    core)
        modules=(SGPT SGPT.Addenda.Okounkov SGPT.Addenda.Resolution)
        audits=(SGPT AddendaOkounkov AddendaResolution)
        ;;
    comparison)
        modules=(SGPT.Checks.Comparison SGPT.Checks.RationalHull SGPT.Checks.NonArchimedean
                 SGPT.Checks.Trace SGPT.Checks.Okounkov)
        audits=(ChecksComparison ChecksRationalHull ChecksNonArchimedean ChecksTrace ChecksOkounkov)
        ;;
    literature)
        modules=(SGPT.Checks.Literature)
        audits=(ChecksLiterature)
        ;;
    *)
        printf 'Unknown profile %s\n' "$profile" >&2
        exit 2
        ;;
esac

lean=$(elan which lean)
lean_path=$(lake env printenv LEAN_PATH)
IFS=: read -r -a dirs <<< "$lean_path"
dep_args=()
for dir in "${dirs[@]}"; do
    if [[ -d "$dir" ]]; then
        dep_args+=(--dependency-root "$dir")
    fi
done

status=0
python3 scripts/build_artifacts.py --lean "$lean" --artifact-root "$build" "${dep_args[@]}" \
    --failure-grace-minutes "${SGPT_FAILURE_GRACE_MINUTES:-0}" "$@" "${modules[@]}" || status=$?
if (( status == 0 )); then
    for audit in "${audits[@]}"; do
        if LEAN_PATH="$(realpath "$build")/lean:$lean_path" "$lean" "Audit/$audit.lean" > "$build/$audit.audit"; then
            continue
        else
            status=$?
            tail -80 "$build/$audit.audit"
            break
        fi
    done
fi

if [[ -n "${SGPT_CACHE_OUTPUT:-}" ]]; then
    partial=()
    if (( status != 0 )); then partial=(--partial); fi
    python3 scripts/build_cache.py --lean "$lean" "${dep_args[@]}" snapshot --artifact-root "$build" \
        "${partial[@]}" --output "$SGPT_CACHE_OUTPUT" "${modules[@]}"
fi
exit "$status"
