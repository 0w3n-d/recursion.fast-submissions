# The evaluation bot (owner's notes)

Three workflows and a small Python package (standard library only, run as `python3 -I`):

| File | What |
|---|---|
| `workflows/intake.yml` | `pull_request_target` and `workflow_dispatch` (`pr`): precheck, retention tag `rf-source/<id>`, queue entry on branch `data`, commit status, one comment, dispatch of `evaluate-next.yml` |
| `workflows/evaluate-next.yml` | `workflow_dispatch` (`pr`: force one) and a 30-minute schedule; one run at a time (`rf-eval`). `select` → the core's `evaluate.yml` at the pin → `publish` |
| `workflows/pin-check.yml` | push to `main` and organiser PRs: the pin agrees in its three places; runs the tests |
| `bot.py` | the command line (`intake`, `select`, `publish`, `sync-main`, `record-build`) |
| `flows.py` | the three steps and the sync of `main` to the record |
| `precheck.py` | the paths rule (files API) and the tree rule (`git ls-tree` / `cat-file` of the head) |
| `rfqueue.py` | `submissions.json`: fair order, supersede, withdraw, reap, duplicates |
| `decide.py` | status and record rule (the duel), the record-cache retry |
| `render.py` | comments, commit statuses, `notes.md`, `records.json` |
| `attest.py` | provenance: `gh attestation verify` + the core's `harness/verify-record.sh` |
| `gitdata.py` | git plumbing: fetch as data, creation-only tags, optimistic transactions |
| `gh.py` | REST client (urllib, `GITHUB_TOKEN`) |
| `pin.py`, `pin-core.sh` | read / set the one pin |
| `simulate.py`, `tests/` | a local end-to-end run against a bare repository, and the unit tests |

Run the tests: `python3 -I -m unittest discover -s .github/bot/tests -t .github/bot`.
Run the simulation: `python3 -I .github/bot/simulate.py`.

## Operating it

- **Move the pin**: `.github/bot/pin-core.sh <sha>` sets the `.contract` gitlink and both literals
  of `evaluate-next.yml`; commit that change on its own. `pin-check.yml` fails on a disagreement,
  and the bot refuses to run with one.
- **Hold a PR**: label it `hold` (its queued entry is withdrawn; removing the label queues it again).
- **Force an evaluation**: run `evaluate-next` with `pr` = N (its queued entry, or its entry left in
  `error`; `hold` and draft are ignored for a forced run).
- **Re-run the intake** of a PR: run `intake` with `pr` = N.
- **`main` lost a record** (a publish failed after `data` was written): every `select` heals it;
  or run `bot.py sync-main` in a job with `contents: write`.
- **Stuck `running` entries** do not exist for long: the next run reaps them (an organiser ERROR,
  queued once more, then `error`).
- **The duel and the record cache** (brief §2a, stage S5): `select` outputs the standing record
  (`incumbent_sha|path|ref`) and `record_cache`; `evaluate-next.yml` passes them to the core only
  once its `evaluate.yml` at the pin takes those inputs. Un-comment the lines marked in the
  `evaluate` job when you move the pin to such a commit.

## Threats and defences

A submitter controls the PR's title, body, branch name and every byte of its root, the timing of
pushes, and any number of PRs and accounts.

| Attack | Defence |
|---|---|
| Run code in the bot's privileged jobs (`pull_request_target`) | The PR is never checked out or run: the API's JSON and a bare `git fetch` of `refs/pull/N/head` read with `ls-tree`/`cat-file` (no hooks, no filters, no working tree). The bot code is `main` at the event's commit, sparse (`.github`), `persist-credentials: false`. |
| Script injection via title, branch, file names, NOTES | No `${{ }}` of event data in any `run:`; values pass through `env:`; `GITHUB_OUTPUT` values are validated (hex, id and root regexes) and newline-free. |
| Change the pin, the CI or the bot | Workflows run from `main`; the precheck refuses any path outside one `submissions/<root>/` (renames' old names included); the evaluation uses the pin literal on `main`, never the PR's `.contract`; `pin.py` refuses a disagreement at run time. |
| Open a PR into `data` or another branch | The intake job runs only for `refs/heads/main`, and the bot ignores a PR whose base is not `main`. |
| Skip the queue | `queued` is the bot's clock; the order is fair by author (brief §4); `workflow_dispatch` (force) needs write access. Many accounts each get a fair share (residual: GitHub accounts are cheap; use `hold`, blocking, or interaction limits). |
| Re-roll the measurement noise (empty commits, resubmitting the same root) | An identical root tree already evaluated, or queued in another PR, is `invalid`; a record needs the same-job duel (`S_cand ≤ 0.97 S_inc`); a prover binary of an earlier record never takes the record. Near-copies remain possible (residual; the duel makes them pointless). |
| Steal credit: copy another's root, or open a PR at another's commit | The earliest entry with a root tree wins; a later one by another author is `invalid`. The author is the PR's opener. Residual: copying a fork's commits before its PR is opened, and near-copies (owner moderation; `Builds on:` citations are public). |
| Overwrite another's queue entry | Entries are keyed `pr<N>-<sha12>`; an event touches only its own PR's entries; the API's live state (not the payload) decides. |
| Poison `data` or `main` | Only the bot writes them (rulesets below). Copied files go to fixed paths (`notes/<id>.md`, `readme/<id>.md`); `main` changes only `submissions/<root>` (the tree object of the retained, checked commit) and `records.json`. Every string is sanitised: printable, length-capped. |
| Markdown injection in comments | Untrusted text appears only in code spans, as printable ASCII without backticks (no links, HTML or @-mentions render). In `notes.md`, each NOTES sits in a `~` fence longer than any run of `~` it contains, under a header the bot writes. |
| Get a REJECT published as ACCEPT, or a fake record | The verdict is the attested `result.json` only. `attest.py`: `gh attestation verify --repo <this> --signer-workflow scaraven/recursion.fast/.github/workflows/evaluate.yml --deny-self-hosted-runners`, signer digest = `harness_commit` = pin, the attestation and the result's `job` name **this run** (a genuine result of another run, replayed, fails), and the core's `verify-record.sh` for an ACCEPT. An unverified ACCEPT is an organiser ERROR, never a record. |
| Tamper with the entry after queueing (force-push) | The evaluated commit is the creation-only tag `rf-source/<id>`; a moved PR is superseded; the record copied to `main` is the tag's tree, checked equal to the tree the intake read. |
| Crash the bot or block the queue | Size caps before parsing (files, bytes, 64 KiB texts, 3000 PR files); JSON errors and recursion are caught; one unreadable PR is skipped; a run that dies leaves `running`, which the next select reaps; the schedule restarts a lost dispatch chain. Residual: API rate-limit exhaustion by event floods (interaction limits). |
| Lose a write to a race | No concurrency group on data writes (it would cancel pending runs): fetch, apply to the fresh state, push without force, retry ≤ 5 times. |
| Sabotage the record build cache | A REJECT or ERROR that reused the cache is evaluated once more without it; a build is cached only if its `manifest.json` matches the attested `entry_build.manifest_sha256`, and the publish job never runs it. The kernel replay stays the trust anchor (S5). |
| Escape the core's sandbox | Out of the bot's scope (the core's `evaluate.yml`): its entry jobs hold read-only tokens; such code still cannot attest a result, and the run binding refuses a replayed one. |
