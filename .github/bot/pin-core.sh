#!/usr/bin/env bash
# Sets the one core pin (the owner's tool): the `.contract` gitlink (in the index) and the
# `uses: …/evaluate.yml@<PIN>` and `core_ref: <PIN>` of .github/workflows/evaluate-next.yml, in one
# change ready to commit on its own. Verifies the commit exists on the core's remote first.
#
#   .github/bot/pin-core.sh <full sha>
set -euo pipefail
SHA=${1:?usage: pin-core.sh <full commit sha of scaraven/recursion.fast>}
[[ "$SHA" =~ ^[0-9a-f]{40}$ ]] || { echo "pin-core: not a full lowercase SHA: $SHA" >&2; exit 2; }
CORE=https://github.com/scaraven/recursion.fast.git
TOP=$(git rev-parse --show-toplevel)
WF="$TOP/.github/workflows/evaluate-next.yml"

T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
git -C "$T" init -q
if ! git -C "$T" -c protocol.version=2 fetch -q --depth=1 --no-tags "$CORE" "$SHA" 2>/dev/null; then
  echo "pin-core: $SHA is not a commit of $CORE" >&2; exit 1
fi
[[ "$(git -C "$T" rev-parse FETCH_HEAD)" == "$SHA" ]] || { echo "pin-core: fetched another commit" >&2; exit 1; }
# warn (not fail) if the core at SHA does not take the inputs the bot passes, or its [entry] caps differ
git -C "$T" show "$SHA:.github/workflows/evaluate.yml" > "$T/core-evaluate.yml"
git -C "$T" show "$SHA:harness/season.toml" > "$T/season.toml" 2>/dev/null || : > "$T/season.toml"
python3 -I - "$TOP/.github/bot" "$WF" "$T/core-evaluate.yml" "$T/season.toml" <<'PY' >&2 || true
import sys
sys.path.insert(0, sys.argv[1])
import pin
ours, core, season = (open(p, encoding="utf-8").read() for p in sys.argv[2:5])
for p in pin.inputs_problems(ours, core) + pin.caps_problems(season):
    print(f"pin-core: warning: {p}")
PY
head=$(git ls-remote "$CORE" refs/heads/main | cut -f1)
[[ "$head" == "$SHA" ]] || echo "pin-core: warning: $SHA is not the core's main head ($head)" >&2

sed -i -E \
  -e "s#^([[:space:]]*uses:[[:space:]]*scaraven/recursion\.fast/\.github/workflows/evaluate\.yml@)[0-9a-f]{40}#\1$SHA#" \
  -e "s#^([[:space:]]*core_ref:[[:space:]]*)[0-9a-f]{40}#\1$SHA#" "$WF"
git -C "$TOP" update-index --cacheinfo "160000,$SHA,.contract"
uses=$(grep -cE "evaluate\.yml@$SHA" "$WF"); refs=$(grep -cE "core_ref:[[:space:]]*$SHA" "$WF")
link=$(git -C "$TOP" ls-files -s .contract | cut -d' ' -f2)
[[ "$uses" == 1 && "$refs" == 1 && "$link" == "$SHA" ]] || {
  echo "pin-core: not all three set (uses $uses, core_ref $refs, gitlink $link)" >&2; exit 1; }
git -C "$TOP" add "$WF"
echo "pin-core: the pin is $SHA in all three places (staged). Commit it on its own, e.g.:"
echo "  git commit -m 'Pin the core at ${SHA:0:7}'"
echo "and update the submodule's checkout if you use one: git submodule update .contract"
