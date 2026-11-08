#!/usr/bin/env bash
# The pin move's cache purge (the owner's tool; pin-core.sh runs it before it stages the pin).
#
#   .github/bot/purge-caches.sh <full sha of the new core pin> [--dry-run]
#
# The core's evaluation caches the organiser's environment, the comparator and the service under
# keys that name the core commit (`rf-org-<sha>`, `rf-kernels-…-<sha>`, `rf-svc-<sha>`; the record
# build cache `rf-record-build-<sha>-…`), and later jobs restore them. A key, once saved, cannot be
# overwritten. So an entry that escaped its sandbox in one evaluation could save such a key for a
# core commit that is public but not yet the pin, and every evaluation after the pin move would
# restore it. Before the pin moves no evaluation has run at the new commit, so no legitimate
# cache names it: every cache whose key contains the new SHA is deleted here.
#   1. No evaluation may be running (an `evaluate-next` run not completed): refused, wait or cancel.
#   2. Every Actions cache whose key starts with one of the core's keys for <sha> (rf-org-,
#      rf-kernels-lean-, rf-kernels-nanoda-, rf-svc-<sha>, rf-record-build-<sha>-) is deleted by
#      its key, every version and scope (--dry-run: listed). The listing is the API's key filter,
#      paginated: no window a flood of other caches could push a key out of.
#   3. They are listed again: none may remain.
# Needs `gh` authenticated as the owner (Actions: write).
set -euo pipefail
SHA=${1:?usage: purge-caches.sh <full commit sha> [--dry-run]}
[[ "$SHA" =~ ^[0-9a-f]{40}$ ]] || { echo "purge-caches: not a full lowercase SHA: $SHA" >&2; exit 2; }
DRY=0; [[ "${2:-}" == --dry-run ]] && DRY=1
REPO=${RF_SUBMISSIONS_REPO:-scaraven/recursion.fast-submissions}

runs=$(gh run list --repo "$REPO" --workflow evaluate-next.yml --limit 100 --json databaseId,status)
busy=$(python3 -I -c 'import json,sys; print(" ".join(str(r["databaseId"]) for r in json.loads(sys.stdin.read()) if r["status"] != "completed"))' <<< "$runs")
if [[ -n "$busy" ]]; then
  echo "purge-caches: an evaluation is running (evaluate-next run(s) $busy): wait until it ends (or cancel it), then move the pin" >&2
  exit 1
fi

# The keys the core's evaluate.yml uses that name a core commit (prefixes; the API's `key` filter is
# a prefix match, server-side, so nothing hides behind a listing window). `rf-kernels-nanoda-` is
# never populated in normal runs (evaluate-next never passes `nanoda`), so an escape could pre-save
# it at any pin: it is purged here like the others.
PREFIXES=("rf-org-$SHA" "rf-kernels-lean-$SHA" "rf-kernels-nanoda-$SHA" "rf-svc-$SHA" "rf-record-build-$SHA-")

keys() {  # the distinct keys of every cache matching one of the prefixes, all pages
  local p
  for p in "${PREFIXES[@]}"; do
    gh api --paginate "repos/$REPO/actions/caches?key=$p&per_page=100"
  done | python3 -I -c '
import json, sys
text, dec, i, keys = sys.stdin.read(), json.JSONDecoder(), 0, set()
while i < len(text):                       # --paginate prints one JSON page after another
    while i < len(text) and text[i].isspace():
        i += 1
    if i >= len(text):
        break
    page, i = dec.raw_decode(text, i)
    keys.update(c["key"] for c in page.get("actions_caches", []))
print("\n".join(sorted(keys)))'
}
found=$(keys)
if [[ -z "$found" ]]; then
  echo "purge-caches: no cache names $SHA"
  exit 0
fi
while read -r key; do
  if [[ $DRY == 1 ]]; then echo "purge-caches: would delete every cache with the key $key"
  else gh api -X DELETE "repos/$REPO/actions/caches?key=$key" >/dev/null; echo "purge-caches: deleted every cache with the key $key"; fi
done <<< "$found"
[[ $DRY == 1 ]] && exit 0
left=$(keys)
[[ -z "$left" ]] || { echo "purge-caches: caches naming $SHA remain: $left" >&2; exit 1; }
echo "purge-caches: no cache names $SHA any more"
