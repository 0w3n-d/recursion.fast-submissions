#!/usr/bin/env bash
# Sets the one core pin (the owner's tool): the `.contract` gitlink (in the index) and the
# `uses: …/evaluate.yml@<PIN>` and `core_ref: <PIN>` of .github/workflows/evaluate-next.yml, in one
# change ready to commit on its own; also `core` in records.json (no record stands at a new pin, so
# each track's record moves to that track's history) and the old pin in the demo fixtures, if they carry it.
# Before it changes anything it deletes every Actions cache whose key names the new commit, and
# refuses while an evaluation is running (purge-caches.sh). Refuses a commit that is not on the
# core's remote, whose evaluate.yml lacks an input the bot passes, or that uses an action by tag
# rather than full commit SHA (the repository requires SHA pins, also inside the called workflow);
# warns if its [entry] caps differ from the bot's.
#
#   .github/bot/pin-core.sh <full sha>
set -euo pipefail
SHA=${1:?usage: pin-core.sh <full commit sha of scaraven/recursion.fast>}
[[ "$SHA" =~ ^[0-9a-f]{40}$ ]] || { echo "pin-core: not a full lowercase SHA: $SHA" >&2; exit 2; }
CORE=https://github.com/scaraven/recursion.fast.git
TOP=$(git rev-parse --show-toplevel)
WF="$TOP/.github/workflows/evaluate-next.yml"
# the current pin is refused (re-pinning it would purge the live caches: a full rebuild next run)
cur_link=$(git -C "$TOP" ls-files -s .contract | cut -d' ' -f2)
cur_ref=$(sed -n -E 's#^[[:space:]]*core_ref:[[:space:]]*([0-9a-f]{40}).*#\1#p' "$WF" | head -1)
if [[ "$SHA" == "$cur_link" || "$SHA" == "$cur_ref" ]]; then
  echo "pin-core: $SHA is already the pin; nothing to do (and its caches stay)" >&2; exit 1
fi

T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
git -C "$T" init -q
if ! git -C "$T" -c protocol.version=2 fetch -q --depth=1 --no-tags "$CORE" "$SHA" 2>/dev/null; then
  echo "pin-core: $SHA is not a commit of $CORE" >&2; exit 1
fi
[[ "$(git -C "$T" rev-parse FETCH_HEAD)" == "$SHA" ]] || { echo "pin-core: fetched another commit" >&2; exit 1; }
git -C "$T" show "$SHA:.github/workflows/evaluate.yml" > "$T/core-evaluate.yml"
git -C "$T" show "$SHA:harness/season.toml" > "$T/season.toml" 2>/dev/null || : > "$T/season.toml"
python3 -I - "$TOP/.github/bot" "$WF" "$T/core-evaluate.yml" "$T/season.toml" <<'PY' >&2
import sys
sys.path.insert(0, sys.argv[1])
import pin
ours, core, season = (open(p, encoding="utf-8").read() for p in sys.argv[2:5])
fatal = pin.inputs_problems(ours, core) + pin.tag_problems(core)
for p in fatal:
    print(f"pin-core: {p}")
for p in pin.caps_problems(season):
    print(f"pin-core: warning (update common.ENTRY_CAPS in the same commit): {p}")
sys.exit(1 if fatal else 0)
PY
# no cache may already name the new pin (purge-caches.sh: refuses while an evaluation runs)
"$TOP/.github/bot/purge-caches.sh" "$SHA" || { echo "pin-core: the cache purge failed; the pin is unchanged" >&2; exit 1; }
head=$(git ls-remote "$CORE" refs/heads/main | cut -f1)
[[ "$head" == "$SHA" ]] || echo "pin-core: warning: $SHA is not the core's main head ($head)" >&2

OLD=$(git -C "$TOP" ls-files -s .contract | cut -d' ' -f2)
sed -i -E \
  -e "s#^([[:space:]]*uses:[[:space:]]*scaraven/recursion\.fast/\.github/workflows/evaluate\.yml@)[0-9a-f]{40}#\1$SHA#" \
  -e "s#^([[:space:]]*core_ref:[[:space:]]*)[0-9a-f]{40}#\1$SHA#" \
  -e "s#^([[:space:]]*ref:[[:space:]]*)[0-9a-f]{40}([[:space:]]*\# THE PIN)#\1$SHA\2#" "$WF"
git -C "$TOP" update-index --cacheinfo "160000,$SHA,.contract"
uses=$(grep -cE "evaluate\.yml@$SHA" "$WF"); refs=$(grep -cE "core_ref:[[:space:]]*$SHA" "$WF")
cos=$(grep -cE "ref:[[:space:]]*$SHA[[:space:]]*# THE PIN" "$WF")
link=$(git -C "$TOP" ls-files -s .contract | cut -d' ' -f2)
[[ "$uses" == 1 && "$refs" == 1 && "$cos" == 1 && "$link" == "$SHA" ]] || {
  echo "pin-core: not all four set (uses $uses, core_ref $refs, core checkout $cos, gitlink $link)" >&2; exit 1; }
git -C "$TOP" add "$WF"
if [[ -f "$TOP/records.json" ]]; then
  python3 -I "$TOP/.github/bot/pin.py" --records "$TOP/records.json" "$SHA" > "$T/records.json"
  cp "$T/records.json" "$TOP/records.json" && git -C "$TOP" add records.json
fi
if [[ -n "$OLD" && "$OLD" != "$SHA" && -d "$TOP/site/demo" ]]; then
  while IFS= read -r f; do sed -i "s/$OLD/$SHA/g" "$f"; git -C "$TOP" add "$f"; done \
    < <(grep -rl --include='*.json' "$OLD" "$TOP/site/demo" || true)
fi
echo "pin-core: the pin is $SHA in all three places, and in records.json (staged). Commit it on its own, e.g.:"
echo "  git commit -m 'Pin the core at ${SHA:0:7}'"
echo "and update the submodule's checkout if you use one: git submodule update .contract"
