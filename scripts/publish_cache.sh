#!/usr/bin/env bash
set -euo pipefail

profile=$1
snapshot=$(realpath "$2")
remote=$(git remote get-url origin)
case "$profile" in
    core|comparison|literature) ;;
    *) exit 2 ;;
esac
branch=build-cache
commit=$(git rev-parse HEAD)
workspace=$(mktemp -d)
trap 'rm -rf "$workspace"' EXIT

git -C "$workspace" init --quiet -b "$branch"
git -C "$workspace" remote add origin "$remote"
git -C "$workspace" config remote.origin.promisor true
git -C "$workspace" config remote.origin.partialclonefilter blob:none
git -C "$workspace" config user.name 'SGPT Build Cache'
git -C "$workspace" config user.email '41898282+github-actions[bot]@users.noreply.github.com'
target="checkpoints/$profile/$commit"
read -r manifest_commit status < <(python3 -c '
import json,sys
with open(sys.argv[1]) as stream:
    manifest = json.load(stream)
print(manifest["source_commit"], manifest.get("status", "complete"))
' "$snapshot/MANIFEST.json")
[[ "$manifest_commit" = "$commit" ]]
case "$status" in
    complete) ;;
    partial)
        manifest_hash=$(sha256sum "$snapshot/MANIFEST.json" | cut -d' ' -f1)
        target="$target/partial/${manifest_hash:0:16}"
        ;;
    *) exit 2 ;;
esac
declare -A known_blobs=()
refresh_tip() {
    local remote_ref type hash
    remote_ref=$(git -C "$workspace" ls-remote --heads origin "refs/heads/$branch")
    known_blobs=()
    if [[ -z "$remote_ref" ]]; then
        git -C "$workspace" update-ref -d "refs/heads/$branch"
        git -C "$workspace" read-tree --empty
        return
    fi
    git -C "$workspace" fetch --quiet --no-tags --depth=1 --filter=blob:none origin "$branch"
    git -C "$workspace" update-ref "refs/heads/$branch" "$(git -C "$workspace" rev-parse FETCH_HEAD)"
    git -C "$workspace" read-tree FETCH_HEAD
    while read -r _ type hash _; do
        if [[ "$type" == blob ]]; then known_blobs[$hash]=1; fi
    done < <(git -C "$workspace" ls-tree -r HEAD)
}

stage_file() {
    local input=$1 path=$2 hash existing
    hash=$(git -C "$workspace" hash-object "$input")
    if existing=$(git -C "$workspace" rev-parse --verify ":$path" 2>/dev/null); then
        [[ "$hash" == "$existing" ]]
        return
    fi
    if [[ -z "${known_blobs[$hash]:-}" ]]; then
        git -C "$workspace" hash-object -w "$input" >/dev/null
        known_blobs[$hash]=1
    fi
    git -C "$workspace" update-index --add --cacheinfo "100644,$hash,$path"
}

publish_batch() {
    local message=$1 attempt input tree previous next
    local -a parents
    shift
    for (( attempt=1; attempt<=8; attempt++ )); do
        for input in "$@"; do
            stage_file "$input" "$target/${input#"$snapshot"/}"
        done
        if git -C "$workspace" diff --cached --quiet; then return; fi
        tree=$(GIT_NO_LAZY_FETCH=1 git -C "$workspace" write-tree --missing-ok)
        parents=()
        if previous=$(git -C "$workspace" rev-parse --verify HEAD 2>/dev/null); then
            parents=(-p "$previous")
        fi
        next=$(git -C "$workspace" commit-tree "$tree" "${parents[@]}" -m "$message")
        git -C "$workspace" update-ref "refs/heads/$branch" "$next"
        if git -C "$workspace" -c pack.window=0 -c pack.useBitmaps=false \
            push --no-thin origin "HEAD:refs/heads/$branch"; then
            return
        fi
        if (( attempt == 8 )); then return 1; fi
        # Another profile can publish while this batch is being prepared.
        sleep "$attempt"
        refresh_tip
    done
}

shopt -s nullglob
chunks=("$snapshot"/chunks/*.part)
(( ${#chunks[@]} > 0 ))
refresh_tip
for (( i=0; i<${#chunks[@]}; i+=8 )); do
    publish_batch "Archive $profile cache chunks for ${commit:0:12}" "${chunks[@]:i:8}"
done
publish_batch "Publish $status verified $profile cache for ${commit:0:12}" "$snapshot/MANIFEST.json"
printf 'Verified %s at %s\n' "$branch" "$(git -C "$workspace" rev-parse HEAD)"
printf 'Checkpoint %s\n' "$target"
