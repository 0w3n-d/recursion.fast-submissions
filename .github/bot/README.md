# The evaluation bot (owner's notes)

Four workflows and a small Python package (standard library only, run as `python3 -I`):

| File | What |
|---|---|
| `workflows/intake.yml` | `pull_request_target` and `workflow_dispatch` (`pr`, the owner's forced re-intake): precheck, retention tag `rf-source/<id>`, commit status (pending "queued": its time is the queue time) or the invalid status and comment; dispatches `sync`. **Writes nothing on `data`.** |
| `workflows/sync.yml` | the only writer of new queue entries (`rf-data`; dispatched and every 30 min): rescans all open PRs, queues, supersedes, withdraws, sets statuses, compacts; dispatches `evaluate-next` |
| `workflows/evaluate-next.yml` | `workflow_dispatch` (`pr`, `retire`) and a 30-minute schedule; one run at a time (`rf-eval`). `select` → the core's `evaluate.yml` at the pin (the duel against the standing record) → `publish` |
| `workflows/pin-check.yml` | push to `main` (the pin, the core's inputs and `[entry]` caps at the pin, the tests) and PRs touching `.github`/`.contract` (the PR's pins read as data, never its code) |
| `bot.py` | the command line (`intake`, `sync`, `select`, `publish`, `sync-main`, `record-build`) |
| `flows.py` | examine/admit, intake, sync, select, publish, the sync of `main` |
| `precheck.py` | the paths rule (files API) and the tree rule (`git ls-tree`/`cat-file`), the core's `[entry]` caps |
| `rfqueue.py` | `submissions.json`: order (a waiting port, then confirmations, then fair by author), supersede, withdraw, reap, duplicates, records per pin, retirement, ports, stale wins, compaction |
| `decide.py` | status and record rule (the duel and its confirmation), record-cache retry |
| `common.py` | constants: `MARGIN` (0.03) and `RECORD_WINS` (2), the record rule's two parameters, and the caps |
| `render.py`, `attest.py`, `gitdata.py`, `gh.py`, `pin.py`, `pin-core.sh` | comments/statuses/notes.md/records.json; provenance; git plumbing; REST; the pin |
| `simulate.py`, `tests/` | a local end-to-end run against a bare repository, and the tests |

Tests: `python3 -I -m unittest discover -s .github/bot/tests -t .github/bot`. Simulation: `python3 -I .github/bot/simulate.py`.

## Operating it

- **Move the pin** (a new core): `.github/bot/pin-core.sh <sha>`. It sets the `.contract` gitlink and both literals of `evaluate-next.yml`, re-pins `records.json` (`core`; the record moves to `history`) and any demo fixture that carries the old pin. It refuses a core whose `evaluate.yml` lacks an input the bot passes or uses an action by tag rather than full SHA, and warns if the core's `[entry]` caps differ from `common.ENTRY_CAPS` (fix those in the same commit). Commit the change on its own. Then nothing is manual:
  1. Records are per pin: after the move no record stands. The push runs `sync`, which rewrites `data` and `records.json` for the new pin (`record: null`) and dispatches `evaluate-next`. Every run (a forced one included) first evaluates the last standing record's retained commit at the new pin as `<id>-<pin8>`, unpaired, before any other entry, also when that port is re-run after an organiser ERROR or a dead run. A comparable, attested ACCEPT keeps the crown (its own prover binary never blocks it); later entries duel it. Confirmations of the old pin are void and re-queued fresh.
  2. If that port fails, no record stands, and the first comparable, attested ACCEPT at the new pin is the record, unpaired. There is one port entry per pin (an ERROR in it is retried like any entry's). Fallback: `evaluate-next` with `pr` = a PR re-evaluates its newest record or ACCEPT of an earlier pin at the current pin.
- **Confirmation duels**: a candidate that wins a duel is `confirming` and is evaluated again, before every other entry, against the same record; it takes the record only with `RECORD_WINS` wins (credited with the smallest gain). A confirming entry ignores pushes, closing and drafts (its tag is retained); `hold` keeps it waiting. Wins and retries are counted per record from the entry's `duels`: when the record is beaten or the pin moves, a pending confirmation is void and the entry is re-queued fresh (`rfqueue.settle`); when the record is retired, it is `accepted` (`rfqueue.void_confirmations`), so a retirement never crowns one win. A confirmation that is not comparable is run once more (`CONFIRM_RETRIES`). Tune `MARGIN` and `RECORD_WINS` in `common.py` after calibrating with self-duels (and say so in the core's `AGENTS.md` §8).
- **Retire a record**: run `evaluate-next` with `retire` = its id. A record whose own run fails in two duels in a row is retired automatically (a duel it completes resets the count). After a retirement there is no standing record, and the next comparable, attested ACCEPT is the record, unpaired: `hold` any PR you would not want crowned before you retire. Retiring is also the remedy for a near-copy of a record that won both duels by noise.
- **Hold a PR**: label it `hold`. Its queued entry is withdrawn; removing the label queues it again.
- **Force an evaluation**: run `evaluate-next` with `pr` = N. This takes its queued entry, its entry left in `error`, or a port of its record from an earlier pin. `hold` and draft are ignored for a forced run.
- **Re-run the intake** of a PR (e.g. after a bot fix): run `intake` with `pr` = N.
- **A root copied from a fork before its PR was opened** makes the original `invalid` (the copy was queued first). Label the copier's PR `hold` (its queued entry is withdrawn and never evaluated; `retire` it if it already took the record), and ask the original's author to push any change to the root: a changed tree is no longer the copy's, so it is queued.
- **Self-healing**:
  - `sync` admits heads whose intake never ran or failed.
  - `select` re-syncs `main` to the record.
  - A run that died leaves its entry `running`; the next run reaps it (an organiser ERROR, queued once more, then `error`).
  - A `data` branch that cannot be read (too large, wrong format, unreachable) stops every step with an error. Nothing is reset and `main` is not touched.
- **Keep-alive**: GitHub disables `schedule` after 60 days without repository activity. If the queue is idle that long, push any commit to `main` or run `sync` by hand.
- **Settings** the defences rely on (commands in [Owner setup](#owner-setup-once)):
  - rulesets: `data` and `rf-source/*` cannot be deleted or force-pushed, and only GitHub Actions (integration 15368) may create or update them; `main` cannot be deleted or force-pushed;
  - Actions limited to GitHub-owned actions and `scaraven/recursion.fast/*`, with SHA pinning required;
  - approval required for fork PR workflows from outside collaborators (`pin-check` on PRs);
  - no `.github/workflows` on any branch other than `main`: an old branch's `pull_request_target` workflow would run for PRs into it.

## Threats and defences

A submitter controls the PR's title, body, branch name and every byte of its root, the timing of pushes, and any number of PRs and accounts.

| Attack | Defence |
|---|---|
| Run code in a privileged job | The PR is never checked out or run. The bot reads the API's JSON and a bare `git fetch` of `refs/pull/N/head`, through `ls-tree`/`cat-file` (no hooks, no filters, no working tree). The bot code is `main` at the event's commit (sparse `.github`, `persist-credentials: false`). `pin-check` on PRs runs `main`'s checker on the PR's files read as data. |
| Script injection (title, branch, file names, NOTES) | No `${{ }}` of event data in any `run:`. Values pass through `env:`. `GITHUB_OUTPUT` values are validated, and a line break aborts the step. |
| Change the pin, the CI or the bot | Workflows run from `main`. The precheck refuses any path outside one `submissions/<root>/` (renames included). The evaluation uses `main`'s pin literal. `pin.py` refuses a disagreement at run time, and `pin-check` checks the core's inputs and caps at the pin. |
| PR into `data` or another branch | The jobs run only for `refs/heads/main`, and the bot ignores a PR whose base is not `main`. (Old branches must carry no workflows: settings above.) |
| Skip the queue | The queue time is the bot's status time; fork tokens cannot write statuses in the base repository. The order is fair by author. Forcing needs write access. Many accounts each get a fair share (residual: use `hold`, blocking, interaction limits). |
| Re-roll the noise (empty commits, resubmissions, near-copies) | A root tree already evaluated, being evaluated, or queued in another PR is `invalid`. A record needs two duel wins against the same record (`S_cand ≤ 0.97 S_inc`, each in one job), the second on another runner draw. A prover binary of an earlier record never takes the record. Residual: a near-copy (one changed byte in each half) is a fresh candidate; it must win both duels by noise, and the owner retires it if it does. Raising `MARGIN` or `RECORD_WINS` after calibration shrinks the residual. |
| Win by the record failing on a slow runner | The record's failure in a duel (`entry_failed`) never crowns the candidate: it is evaluated once more (keeping a first win), then `accepted`. A record failing in two duels is retired, and the next ACCEPT is the record unpaired. |
| Take the record unpaired after a pin move | The port of the standing record runs before any other entry at the new pin, forced runs and its own re-runs after an ERROR included; the prover-binary rule exempts the record's own commit. |
| Steal credit | The earliest entry with a root tree wins; a later copy by another author is `invalid`. The author is the PR's opener. `Builds on:` keeps only PRs the bot knows. Residual: copying a fork's commits before its PR is opened (submitters: open the PR first). |
| Take a name the organiser keeps on `main` | A root named like a directory under `main:submissions/` that is not a record's root is `invalid`. |
| Overwrite another's entry | Entries are keyed `pr<N>-<sha12>`. One writer (`sync`) applies the PRs' live state. |
| Flood `data` (writes, size) | One writer of new entries (`rf-data`), plus `evaluate-next` (`rf-eval`). Transactions retry with jittered exponential backoff (12 tries, 10 min): 20 concurrent writers lose nothing. Entries that never were evaluated collapse to stubs, at most 50 per PR, and their NOTES copies are deleted. Residual: API rate limits under event floods (interaction limits). |
| Reset the history | Reads fail closed. An absent branch is told from an unreadable one by `ls-remote`. A file over the read cap, malformed or of another format aborts the step. Pushes are never forced. |
| Poison `data` or `main` | Only the bot writes them (rulesets). Copies go to fixed paths (`notes/<id>.md`, `readme/<id>.md`). `main` changes only `submissions/<record root>` (the retained, checked tree) and `records.json`. Strings are sanitised. |
| Markdown injection | Comments put untrusted text in code spans of printable ASCII without backticks. `notes.md` fences each NOTES with a longer `~` run under the bot's header. |
| REJECT published as ACCEPT, a fake record, a replayed result | `attest.py`: `gh attestation verify --repo <this> --signer-workflow …/evaluate.yml --deny-self-hosted-runners`, signer digest = `harness_commit` = pin. The attestation and the result's `job` must name this run, at an attempt no earlier than the one that selected the entry. `verify-record.sh` runs for a comparable ACCEPT. The duel's incumbent must be the standing record (sha and root). Any result whose provenance fails is an organiser ERROR, never published as a verdict. |
| Tamper after queueing | The evaluated commit is the creation-only tag. A moved PR is superseded (with a status on the old head). The record on `main` is the tag's tree, checked equal to the tree the intake read. |
| Sabotage the record build cache | A REJECT that restored modules from the cache, and every retried ERROR, is evaluated once more with `record_cache: false`. The bot passes the standing record's attested manifest hash (`record_manifest_sha256`). A build is cached only if its `manifest.json` matches the attested hash, and it is never run here. |
| Crash the bot or block the queue | Caps are checked before parsing. One unreadable PR is skipped and retried. `select` scans every candidate. A dead run is reaped. Side effects (status, comment, dispatch, `main`) are independent; a failed one fails the job loudly after `data` is written. |
| Escape the core's sandbox; mutable action tags inside the core | The core's business (its `evaluate.yml`): entry jobs hold read-only tokens and cannot attest. The run binding refuses a replayed attested result. `pin.py` (in `pin-check` and `pin-core.sh`) refuses a core whose `evaluate.yml` uses an action by tag. |

## Owner setup (once)

Run after the launch PR is merged, in this order. First pin the core's launch head
(`.github/bot/pin-core.sh <sha>`, its own commit): `pin-core.sh` and `pin-check` refuse a core
without the duel inputs or with tag-pinned actions, and no evaluation can run before. The `data` branch must exist before the bot-only
ruleset forbids anyone else to create it: seed it with the bot's empty state (below), or let the
first `sync` run create it (it does, with or without open PRs; run `sync` by hand). The six action
SHAs in this repository's workflows were checked against their tags on GitHub
(`gh api repos/actions/<name>/git/ref/tags/<tag>`).

```sh
R=scaraven/recursion.fast-submissions
# the branch data, seeded with the bot's own empty state (from a clean checkout of main)
PIN=$(python3 -I .github/bot/pin.py .)
T=$(mktemp -d) && git -C "$T" init -q && git -C "$T" checkout -q --orphan data
python3 -I -c 'import sys; sys.path.insert(0, ".github/bot"); import rfqueue; sys.stdout.buffer.write(rfqueue.dump(rfqueue.empty(sys.argv[1], sys.argv[2])))' "$R" "$PIN" > "$T/submissions.json"
git -C "$T" add submissions.json && git -C "$T" commit -q -m "data: empty state" && git -C "$T" push -q "https://github.com/$R.git" data
# Actions: read-only default token, GitHub-owned actions and the core's workflows only, SHA pins required
gh api -X PUT repos/$R/actions/permissions/workflow -f default_workflow_permissions=read -F can_approve_pull_request_reviews=false
gh api -X PUT repos/$R/actions/permissions -F enabled=true -f allowed_actions=selected -F sha_pinning_required=true
gh api -X PUT repos/$R/actions/permissions/selected-actions -F github_owned_allowed=true -F verified_allowed=false -f 'patterns_allowed[]=scaraven/recursion.fast/*'
# approval for fork-PR workflow runs (only pin-check uses pull_request; pull_request_target runs no PR code)
gh api -X PUT repos/$R/actions/permissions/fork-pr-contributor-approval -f approval_policy=first_time_contributors
gh label create hold --repo $R --color B60205 --description "kept out of the evaluation queue by the owner"
# data and rf-source/* are never deleted or rewritten, and only GitHub Actions (integration 15368) writes them
gh api -X POST repos/$R/rulesets --input - <<'J'
{"name":"bot data immutable","target":"branch","enforcement":"active","bypass_actors":[],
 "conditions":{"ref_name":{"include":["refs/heads/data"],"exclude":[]}},
 "rules":[{"type":"deletion"},{"type":"non_fast_forward"}]}
J
gh api -X POST repos/$R/rulesets --input - <<'J'
{"name":"bot-only data writes","target":"branch","enforcement":"active",
 "bypass_actors":[{"actor_id":15368,"actor_type":"Integration","bypass_mode":"always"}],
 "conditions":{"ref_name":{"include":["refs/heads/data"],"exclude":[]}},
 "rules":[{"type":"creation"},{"type":"update"}]}
J
gh api -X POST repos/$R/rulesets --input - <<'J'
{"name":"retention tags","target":"tag","enforcement":"active",
 "bypass_actors":[{"actor_id":15368,"actor_type":"Integration","bypass_mode":"always"}],
 "conditions":{"ref_name":{"include":["refs/tags/rf-source/*"],"exclude":[]}},
 "rules":[{"type":"creation"},{"type":"deletion"},{"type":"non_fast_forward"},{"type":"update"}]}
J
# the website (site/README.md): GitHub Pages from pages.yml, then optionally a custom domain
gh api -X POST repos/$R/pages -f build_type=workflow
gh workflow run pages.yml --repo $R
# gh api -X PUT repos/$R/pages -f cname=internal.recursion.fast   # after a DNS CNAME internal → scaraven.github.io
# under an event flood: gh api -X PUT repos/$R/interaction-limits -f limit=existing_users -f expiry=one_week
```

The bot pushes its record commits and `records.json` to `main` directly, as fast-forwards. The
existing `main bodyguard` ruleset has only the `deletion` and `non_fast_forward` rules, so it admits
those pushes; do not add a pull-request, status-check or signed-commit rule to `main` (or give
GitHub Actions, integration 15368, a bypass), or every record's publish ends in an error after its
comment. Check with `gh api repos/$R/rulesets` and `gh api repos/$R/branches/main/protection`
(a 404 there means no classic protection). Delete every other branch that carries
`.github/workflows` (after the merge: `v4/guidance`), since a `pull_request_target` workflow on a
branch runs for PRs into it.
