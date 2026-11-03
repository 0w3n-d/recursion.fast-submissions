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
| `rfqueue.py` | `submissions.json`: fair order, supersede, withdraw, reap, duplicates, records per pin, retirement, ports, compaction |
| `decide.py` | status and record rule (the duel), record-cache retry |
| `render.py`, `attest.py`, `gitdata.py`, `gh.py`, `pin.py`, `pin-core.sh` | comments/statuses/notes.md/records.json; provenance; git plumbing; REST; the pin |
| `simulate.py`, `tests/` | a local end-to-end run against a bare repository, and the tests |

Tests: `python3 -I -m unittest discover -s .github/bot/tests -t .github/bot`. Simulation: `python3 -I .github/bot/simulate.py`.

## Operating it

- **Move the pin** (a new core): `.github/bot/pin-core.sh <sha>`. It sets the `.contract` gitlink and both literals of `evaluate-next.yml`. It warns if the core at `<sha>` lacks an input the bot passes, or if its `[entry]` caps differ from `common.ENTRY_CAPS`; fix those in the same commit. Commit the change on its own. Then:
  1. Records are per pin: after the move there is no standing record. The first comparable, attested ACCEPT at the new pin becomes the record, unpaired.
  2. Run `evaluate-next` with `pr` = the old record's PR **first**. That re-evaluates its retained commit at the new pin as `<id>-<pin8>`, so the old record can keep the crown. Later entries then duel it.
- **Retire a record**: run `evaluate-next` with `retire` = its id. A record whose own run fails in two duels is retired automatically. After a retirement there is no standing record, and the next comparable, attested ACCEPT is the record.
- **Hold a PR**: label it `hold`. Its queued entry is withdrawn; removing the label queues it again.
- **Force an evaluation**: run `evaluate-next` with `pr` = N. This takes its queued entry, its entry left in `error`, or a port of its record from an earlier pin. `hold` and draft are ignored for a forced run.
- **Re-run the intake** of a PR (e.g. after a bot fix): run `intake` with `pr` = N.
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
| Re-roll the noise (empty commits, resubmissions) | A root tree already evaluated, or queued in another PR, is `invalid`. A record needs the same-job duel (`S_cand ≤ 0.97 S_inc`). A prover binary of an earlier record never takes the record. |
| Win by the record failing on a slow runner | The record's failure in a duel (`entry_failed`) never crowns the candidate: it is `accepted` and re-queued once for another duel. A record failing in two duels is retired, and the next ACCEPT is the record unpaired. |
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
| Escape the core's sandbox; mutable action tags inside the core | The core's business (its `evaluate.yml`): entry jobs hold read-only tokens and cannot attest. The run binding refuses a replayed attested result. The core still uses `actions/*@v4` and `attest-build-provenance@v2` by tag: pin them there. |

## Owner setup (once)

Run after the launch PR is merged, in this order: the `data` branch must exist before the bot-only
ruleset forbids anyone else to create it (`data` is seeded at launch with an empty
`submissions.json`; if it is missing, the first `sync` run creates it).

```sh
R=scaraven/recursion.fast-submissions
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

The existing `main bodyguard` ruleset (no deletion, no force-push) already admits the bot's
fast-forward record commits. Delete every other branch that carries `.github/workflows` (after the
merge: `v4/guidance`), since a `pull_request_target` workflow on a branch runs for PRs into it.
