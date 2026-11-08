# The evaluation bot (owner's notes)

Four workflows and a small Python package (standard library only, run as `python3 -I`):

| File | What |
|---|---|
| `workflows/intake.yml` | `pull_request_target` and `workflow_dispatch` (`pr`, the owner's forced re-intake): precheck, retention tag `rf-source/<id>`, commit status (pending "queued": its time is the queue time) or the invalid status and comment; dispatches `sync`. **Writes nothing on `data`.** |
| `workflows/sync.yml` | the only writer of new queue entries (`rf-data`; dispatched and every 30 min): rescans all open PRs, queues, supersedes, withdraws, sets statuses, compacts; dispatches `evaluate-next` |
| `workflows/evaluate-next.yml` | `workflow_dispatch` (`pr`, `retire`, `resume`) and a 30-minute schedule; one run at a time (`rf-eval`). `select` → the core's `evaluate.yml` at the pin → `publish` |
| `workflows/pin-check.yml` | push to `main` (the pin, the core's inputs and `[entry]` caps at the pin, the tests; `rf-light`) and PRs touching `.github`/`.contract` (the PR's pins read as data, never its code; GitHub-hosted) |
| `bot.py` | the command line (`intake`, `sync`, `select`, `publish`, `sync-main`, `record-build`) |
| `flows.py` | examine/admit, intake, sync, select, publish, the sync of `main` |
| `precheck.py` | the paths rule (files API) and the tree rule (`git ls-tree`/`cat-file`), the core's `[entry]` caps |
| `rfqueue.py` | `submissions.json`: order (a waiting port, then fair by author), supersede, withdraw, reap, duplicates, records per pin, retirement, ports, compaction |
| `decide.py` | status and record rule (`S < (1 − MARGIN) · S_record`), record-cache retry |
| `common.py` | constants: `MARGIN` (0.02, the owner's choice; the measured run-to-run spread of one entry's score is about 1.75 %, so it does not keep noise out), and the caps |
| `render.py`, `attest.py`, `gitdata.py`, `gh.py`, `pin.py`, `pin-core.sh`, `purge-caches.sh`, `wfcheck.py` | comments/statuses/notes.md/records.json; provenance; git plumbing; REST; the pin, and the purge of caches naming a new pin; the workflow safety check |
| `simulate.py`, `tests/` | a local end-to-end run against a bare repository, and the tests |

Tests: `python3 -I -m unittest discover -s .github/bot/tests -t .github/bot`. Simulation: `python3 -I .github/bot/simulate.py`.

## Operating it

- **Move the pin** (a new core): `.github/bot/pin-core.sh <sha>`.
  - **It refuses the current pin.** Re-pinning it would purge its live caches and force a full
    rebuild at the next evaluation.
  - **It purges first.** Before it changes anything it runs `purge-caches.sh <sha>`:
    - it refuses while an `evaluate-next` run is not completed (wait for it, or cancel it);
    - it deletes, by key (every version and scope), each Actions cache whose key starts with one
      of the core's keys for that commit: `rf-org-<sha>`, `rf-kernels-lean-<sha>`,
      `rf-kernels-nanoda-<sha>`, `rf-svc-<sha>`, `rf-record-build-<sha>-`;
    - it checks that none remains.

    The listing uses the API's key filter with pagination, so no flood of other caches can push a
    key out of view.

    **Why:** no evaluation has run at the new commit yet, so no legitimate cache can name it. An
    entry that escaped its sandbox could have saved one (a key cannot be overwritten later), and
    every evaluation at the new pin would have restored it. `purge-caches.sh <sha> --dry-run`
    lists without deleting.

    **`rf-kernels-nanoda-<pin>` is never populated in normal runs:** `evaluate-next` never passes
    `nanoda`. So before enabling nanoda at an existing pin, delete that one key first:
    `gh api -X DELETE "repos/scaraven/recursion.fast-submissions/actions/caches?key=rf-kernels-nanoda-<pin>"`.
  - **The residual at the move:** a run already in flight at the old pin when the pin moves. The
    purge refuses while one runs, but a run that starts between the purge and the push still runs
    at the old pin, and an escape in it could still save a key for the new SHA. So push the pin
    commit right after `pin-core.sh`, with the queue idle. If an evaluation ran in between, run
    `purge-caches.sh <sha>` again before the first evaluation at the new pin (it only deletes).
  - **The residual at the current pin: eviction.** GitHub evicts the least recently used caches
    when the repository passes its 10 GB cache limit. An entry that escaped its sandbox holds the
    job's cache token: it could save enough junk to evict the organiser's caches for the current
    pin, then save forged ones under their keys, which later evaluations at that pin would restore.
    The purge cannot reach this, since it runs only at a pin move.
    - **To keep the store far from the limit,** delete stale caches; the stale ones of earlier
      seasons are the bulk.
    - **To recover,** after an evaluation whose result looks forged, move the pin to a new core
      commit (or delete the pin's `rf-org-`, `rf-kernels-`, `rf-svc-` keys). The next evaluation
      then rebuilds them.
    - **A stronger defence,** not in place yet: compare each result's `environment` hashes with the
      first attested result at the pin.
  - **What else it does:** it sets the `.contract` gitlink and both literals of `evaluate-next.yml`, re-pins `records.json` (`core` and `margin`, the bot's; the record moves to `history`) and any demo fixture that carries the old pin. It refuses a core whose `evaluate.yml` lacks an input the bot passes or uses an action by tag rather than full SHA, and warns if the core's `[entry]` caps differ from `common.ENTRY_CAPS` (fix those in the same commit). Commit the change on its own. Then nothing is manual:
  1. Records are per pin: after the move no record stands. The push runs `sync`, which rewrites `data` and `records.json` for the new pin (`record: null`) and dispatches `evaluate-next`. Every run (a forced one included; while the queue is paused, only a forced one) first evaluates the last standing record's retained commit at the new pin as `<id>-<pin8>`, before any other entry, also when that port is re-run after an organiser ERROR or a dead run. A comparable, attested ACCEPT keeps the crown (its own prover binary never blocks it); later entries must beat its new score by `MARGIN`.
  2. If that port fails, no record stands, and the first comparable, attested ACCEPT at the new pin is the record. There is one port entry per pin (an ERROR in it is retried like any entry's). Fallback: `evaluate-next` with `pr` = a PR re-evaluates its newest record or ACCEPT of an earlier pin at the current pin.
- **The fair order** (AGENTS.md §9): there is no cap on an author's evaluations; the order only decides who goes next. An author's place is set by `counted_at`, the start of their entry's first run that counted (a retry does not refresh it). A run that ended in a named organiser error (`UNCOUNTED_ERRORS`: fingerprint, lengths (the stream did not use the season's fixed chain lengths), drift, setup (also a missing elan in the image), cache, named by the core in `organiser_error`; and attestation, a result whose provenance the bot could not verify) never counts against the author, nor does an entry's first unnamed ERROR (a catch-all harness error, a reaped run); a later one does. Superseded and withdrawn entries never count. A retried entry keeps its queue time and goes through the fair order. Ports are the organiser's and never count. `drift` is among the named errors although `c_P` is sampled during the entry's stream: the sandbox leaves no entry process alive, so only heat could carry over (accepted; if drift ever correlates with one entry, treat it as unnamed).
- **A paused queue**: every run that ends on the organiser's side (any ERROR, named or not; a result whose provenance fails; no result at all; a run that died and was reaped) joins the error streak (`error_streak` in `submissions.json`). Only a clean verdict (a verified ACCEPT, PROVISIONAL or REJECT) whose stream ran on the season's machine (the result has a `stream` and `machine.matches`) clears it: a REJECT at the certificate, or inside the stream (before the drift check), never reached the benchmark-side checks and leaves the streak as it is, neither counted nor cleared. When `PAUSE_AFTER` (2) errors of the streak count (`rfqueue.pause_count`; an error noted more than `STREAK_WINDOW_S`, 7 days, before the streak's newest no longer counts, so unrelated errors weeks apart do not add up), `paused` is set and one issue is opened (by `publish`, or by `select` after a reap). Every `fingerprint`, `lengths`, `setup`, `cache` and `attestation` error counts (`ENTRY_PROOF_ERRORS`: decided before any entry code runs, or by jobs that never fetch the entry); the others (`drift`, measured during the entry's stream; `harness`, a certificate job, which builds the entry, that ended without a certificate; `noresult`, no result artifact, after entry code ran; an unnamed ERROR; a reaped run) count once per author in the streak, since an entry might provoke them: no author can pause the queue alone, and an outage still pauses it at the second author's entry. Per entry nothing changes: a fingerprint or lengths ERROR re-queues the entry without using up an attempt; any other ERROR is retried once, then the entry is `error` (commit status pending, "waiting on the organiser"). While paused, `select` starts nothing but a forced run, and an ERROR in a forced run keeps the pause (no second issue). To resume: fix the cause (for a changed image or machine, [the procedure](#when-the-image-or-the-machine-changes)), then run `evaluate-next` with `pr` = a queued PR (a port due at the pin runs first). Its clean verdict resumes the queue only if its stream ran to the end on the season's machine, so pick an entry likely to get that far: the record's port, or a PR whose earlier commit was ACCEPTed or PROVISIONAL (the site and `notes.md` show them), not a new root that may REJECT at its certificate. If none would, or the cause is fixed and you have checked it otherwise, run `evaluate-next` with `resume` = true: `select` clears the pause and the streak, then takes the next entry as usual. Then force each entry the issue lists as left in `error`. `paused` survives a pin move: moving the pin alone never resumes the queue.
- **Retire a record**: run `evaluate-next` with `retire` = its id. After a retirement there is no standing record, and the next comparable, attested ACCEPT is the record: `hold` any PR you would not want crowned before you retire. Retiring is also the remedy for a near-copy of a record that beat it by noise.
- **Change the margin**: [below](#changing-the-margin).
- **Hold a PR**: label it `hold`. Its queued entry is withdrawn; removing the label queues it again.
- **Clear a pause by hand**: run `evaluate-next` with `resume` = true (see "A paused queue").
- **An owner dispatch can be cancelled.** `evaluate-next` runs one at a time and keeps only one pending run: a dispatch (`pr`, `retire` or `resume`) that waits behind a running evaluation is cancelled when the next scheduled run queues. Dispatch while no `evaluate-next` run is in progress, or check afterwards that yours ran, and dispatch again once the running evaluation has finished.
- **Force an evaluation**: run `evaluate-next` with `pr` = N. This takes its queued entry, its entry left in `error`, or a port of its record from an earlier pin. `hold` and draft are ignored for a forced run.
- **Re-run the intake** of a PR (e.g. after a bot fix): run `intake` with `pr` = N.
- **A root copied from a fork before its PR was opened** makes the original `invalid` (the copy was queued first). Label the copier's PR `hold` (its queued entry is withdrawn and never evaluated; `retire` it if it already took the record), and ask the original's author to push any change to the root: a changed tree is no longer the copy's, so it is queued.
- **Self-healing**:
  - `sync` admits heads whose intake never ran or failed.
  - `select` re-syncs `main` to the record.
  - A run that died leaves its entry `running`; the next run reaps it (an organiser ERROR, queued once more, then `error`).
  - A `data` branch that cannot be read (too large, wrong format, unreachable) stops every step with an error. Nothing is reset and `main` is not touched.
- **Keep-alive**: GitHub disables `schedule` after 60 days without repository activity. If the queue is idle that long, push any commit to `main` or run `sync` by hand.
- **Settings** the defences rely on (commands in [Owner setup](#owner-setup)):
  - rulesets: `data` and `rf-source/*` cannot be deleted or force-pushed, and only GitHub Actions (integration 15368) may create or update them; `main` cannot be deleted or force-pushed;
  - Actions limited to GitHub-owned actions and `scaraven/recursion.fast/*`, with SHA pinning required;
  - approval required for fork PR workflow runs from all outside collaborators. **Never approve a fork PR's workflow run that touches `.github/`**: a `pull_request` run executes the PR's own workflow files. The hard guarantee is the server image's job-started hook (the core's `infra/`), which refuses any job that is not one of this repository's workflows on `main` or the core's `evaluate.yml` called from them; `wfcheck.py` is an advisory lint (a workflow it cannot parse fails) that helps the owner spot a dangerous workflow before approving or merging it. It allows `rf-*` runners and reusable workflows only under `pull_request_target`, `workflow_dispatch`, `schedule` and `push` to `main`, or behind an exact `if: github.event_name == '<one of those>'`. Every job that can run for an event other than `pull_request` is held to an expression allowlist (pull-request fields only in `env:`), checks out only the base commit, and runs no fetched code (fetching `refs/pull/N/head` as data stays allowed). It runs in the intake on every head that touches `.github/` (main's code: a submission's head is `invalid`, an organiser's gets a failing status and a comment), in `pin-check`'s PR job, and in the bot's tests on `main`. Threat model: only the owner writes `main`'s workflows and submissions are never merged, so the lint catches the organiser's mistakes and workflow-editing PRs; it is not a sandbox against a malicious organiser, and every workflow change still needs human review. The host supervisor should also refuse runners for jobs of other events;
  - no `.github/workflows` on any branch other than `main`: an old branch's `pull_request_target` workflow would run for PRs into it.

## Threats and defences

A submitter controls the PR's title, body, branch name and every byte of its root, the timing of pushes, and any number of PRs and accounts.

| Attack | Defence |
|---|---|
| Run code in a privileged job | The PR is never checked out or run. The bot reads the API's JSON and a bare `git fetch` of `refs/pull/N/head`, through `ls-tree`/`cat-file` (no hooks, no filters, no working tree). The bot code is `main` at the event's commit (sparse `.github`, `persist-credentials: false`). `pin-check` on PRs runs `main`'s checker on the PR's files read as data. |
| Script injection (title, branch, file names, NOTES) | No `${{ }}` of event data in any `run:`. Values pass through `env:`. `GITHUB_OUTPUT` values are validated, and a line break aborts the step. |
| Change the pin, the CI or the bot | Workflows run from `main`. The precheck refuses any path outside one `submissions/<root>/` (renames included). The evaluation uses `main`'s pin literal. `pin.py` refuses a disagreement at run time, and `pin-check` checks the core's inputs and caps at the pin. |
| PR into `data` or another branch | The jobs run only for `refs/heads/main`, and the bot ignores a PR whose base is not `main`. (Old branches must carry no workflows: settings above.) |
| Skip the queue | The queue time is the bot's status time; fork tokens cannot write statuses in the base repository. The order is fair by author. Forcing needs write access. There is no cap per author, so one account with many PRs is the same case as many accounts: each author gets a round-robin share, so against one other author a flooder takes every second evaluation, and others are delayed by one evaluation per round, never starved. The queue stays bounded per PR (one queued head, at most 50 stubs). Residual: use `hold`, blocking, interaction limits. |
| Re-roll the noise (empty commits, resubmissions, near-copies) | A root tree already evaluated, being evaluated, or queued in another PR is `invalid`. A record needs `S < (1 − MARGIN) · S_record` on the season's machine (fingerprint), `MARGIN` = 2 % (the owner's). A prover binary of an earlier record never takes the record. Residual: one entry's score varies by σ ≈ 1.75 % from run to run (measured at the smoke shape), so two runs differ by about √2·σ ≈ 2.5 %, more than the margin: a near-copy (one changed byte) is a fresh candidate and can beat the record by noise alone (roughly one attempt in five); the owner retires it if it does. With no cap per author, such re-rolls are bounded only by throughput (every second evaluation against one other active author, every evaluation when nobody else waits); against a determined re-roller, `hold` the PRs and retire. A noise-proof margin would be 3·√2·σ ≈ 7.4 %. |
| Take the record after a pin move | The port of the standing record runs before any other entry at the new pin, forced runs and its own re-runs after an ERROR included; the prover-binary rule exempts the record's own commit. |
| Steal credit | The earliest entry with a root tree wins; a later copy by another author is `invalid`. The author is the PR's opener. `Builds on:` keeps only PRs the bot knows. Residual: copying a fork's commits before its PR is opened (submitters: open the PR first). |
| Take a name the organiser keeps on `main` | A root named like a directory under `main:submissions/` that is not a record's root is `invalid`. |
| Overwrite another's entry | Entries are keyed `pr<N>-<sha12>`. One writer (`sync`) applies the PRs' live state. |
| Flood `data` (writes, size) | One writer of new entries (`rf-data`), plus `evaluate-next` (`rf-eval`). Transactions retry with jittered exponential backoff (12 tries, 10 min): 20 concurrent writers lose nothing. Entries that never were evaluated collapse to stubs, at most 50 per PR, and their NOTES copies are deleted. Residual: API rate limits under event floods (interaction limits). |
| Reset the history | Reads fail closed. An absent branch is told from an unreadable one by `ls-remote`. A file over the read cap, malformed or of another format aborts the step. Pushes are never forced. |
| Poison `data` or `main` | Only the bot writes them (rulesets). Copies go to fixed paths (`notes/<id>.md`, `readme/<id>.md`). `main` changes only `submissions/<record root>` (the retained, checked tree) and `records.json`. Strings are sanitised. |
| Markdown injection | Comments put untrusted text in code spans of printable ASCII without backticks. `notes.md` fences each NOTES with a longer `~` run under the bot's header. |
| REJECT published as ACCEPT, a fake record, a replayed result | `attest.py`: `gh attestation verify --repo <this> --signer-workflow …/evaluate.yml`, a self-hosted runner (`runnerEnvironment`), signer digest = `harness_commit` = pin. The attestation and the result's `job` must name this run, at an attempt no earlier than the one that selected the entry. `verify-record.sh` runs for a comparable ACCEPT (it also requires the result's runner to be the organiser's, with the single label `rf-bench`; the server registers each runner with exactly one label, `rf-bench` or `rf-light`). Any result whose provenance fails is an organiser ERROR, never published as a verdict. |
| Tamper after queueing | The evaluated commit is the creation-only tag. A moved PR is superseded (with a status on the old head). The record on `main` is the tag's tree, checked equal to the tree the intake read. |
| Sabotage the record build cache | A REJECT that restored modules from the cache, and every retried ERROR, is evaluated once more with `record_cache: false`. The bot passes the standing record's attested manifest hash (`record_manifest_sha256`). A build is cached only if its `manifest.json` matches the attested hash, and it is never run here. |
| Crash the bot or block the queue | Caps are checked before parsing. One unreadable PR is skipped and retried. `select` scans every candidate. A dead run is reaped. Side effects (status, comment, dispatch, `main`) are independent; a failed one fails the job loudly after `data` is written. |
| Escape the core's sandbox; mutable action tags inside the core | The core's business (its `evaluate.yml`): entry jobs hold read-only tokens and cannot attest. The run binding refuses a replayed attested result. `pin.py` (in `pin-check` and `pin-core.sh`) refuses a core whose `evaluate.yml` uses an action by tag. |

## Owner setup

Once, after the launch PR is merged, in this order. First pin the core's launch head
(`.github/bot/pin-core.sh <sha>`, its own commit): `pin-core.sh` and `pin-check` refuse a core
whose `evaluate.yml` lacks an input the bot passes, requires one it does not, or uses tag-pinned actions, and no evaluation can run before. The `data` branch must exist before the bot-only
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
# approval for every outside collaborator's fork-PR workflow run (only pin-check uses pull_request, on the
# organiser's rf-light runner; pull_request_target runs no PR code)
gh api -X PUT repos/$R/actions/permissions/fork-pr-contributor-approval -f approval_policy=all_external_contributors
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
`.github/workflows`, since a `pull_request_target` workflow on a
branch runs for PRs into it.

### When the image or the machine changes

A rebuilt image, a microcode change, a `slots.json` change, a reboot into another frequency
policy, or a new `RUNNER_VERSION` gives the bench VM a new fingerprint (the core's
`infra/README.md`, "The machine fingerprint"). Until the season records it, every evaluation stops
in its setup job as a `fingerprint` ERROR that costs no entry anything, and two of them pause the
queue. In order:

1. **Drain and change.** Drain the slots, rebuild or reboot, run the release gate
   (`infra/README.md`, "Updating the golden image"). The gate checks the fingerprint file but
   does not print its hash.
2. **Read the new hash** in a bench VM, on the host (the bench slot still drained):

   ```sh
   rf-test bench /opt/rf-runner/tests/fp-guest.sh      # FP-HASH <the new fingerprint> file-sha256 …
   # the harness's own check, from a tarball of the core with its top directory core/:
   echo 'cd ~/core && python3 -I harness/aggregate.py --check-machine --season harness/season.toml' > /tmp/fp-check.sh
   rf-test bench /tmp/fp-check.sh --tar core.tar       # "… mismatched (fingerprint NEW, the season expects OLD)"
   ```

   Run the second command again after step 3 on that commit: it prints nothing once they agree.
3. **A core commit** that sets `[machine] fingerprint` in `harness/season.toml` to the new hash
   (and its comment's image id), pushed to the core's `main`. If the hardware itself changed, not
   only the image, it is a new season's machine: in the same commit re-measure `[calibration]
   ref_ns` (`rf-test bench /opt/rf-runner/tests/noise.sh --tar core.tar`, the median of 30
   `calib` runs) and re-derive `c_P_drift`, `v_ref` and `κ` from runs on it, and review the
   margin ([below](#changing-the-margin)).
4. **Move the pin** to that commit: `.github/bot/pin-core.sh <sha>`, commit on its own, push to
   `main` at once, with no evaluation running. `pin-core.sh` first runs `purge-caches.sh <sha>`:
   it refuses while an evaluation runs, and deletes any Actions cache already naming the new
   commit (see "Move the pin" above). Undrain the slots.
5. **The port runs by itself** if the queue is not paused: the push runs `sync`, which
   dispatches `evaluate-next`, whose first evaluation is the standing record's port to the new pin
   (see "Move the pin" above). Its comparable ACCEPT keeps the crown with its new score.
6. **If the queue paused** (it pauses by itself when evaluations ran on the changed machine
   before the pin moved, as after an unplanned reboot or a retired runner version):
   `paused` and the error streak survive the pin move, so nothing runs until you run
   `evaluate-next` with `pr` = any queued PR. While a port is due, that forced run evaluates the
   **port**, not the PR named. A clean verdict of the port whose stream ran to the end (an ACCEPT,
   or a REJECT after the stream) resumes the queue, and the queue goes on by itself. If the port
   ERRORs, the queue stays paused and it is retried once: the next forced run, with any PR,
   evaluates it again. After its second ERROR the port is `error` and no longer due, so a forced
   run with any other PR evaluates that PR; to re-run the port, run `evaluate-next` with `pr` =
   **the record's pull request**: `select` takes that PR's newest entry left in `error` and gives
   it a fresh attempt count. That entry is the port (unless a later commit of that PR was itself
   left in `error` after the port), and a queued entry of that PR is taken before it. If the
   port's certificate or stream REJECTs, no record stands at the pin
   and the queue stays paused: force an entry that should complete its stream, or use
   `resume` = true. Then force each entry the pause issue lists as left in `error`, and close the
   issue. Check: `submissions.json` on `data` has no `paused` and an empty
   `error_streak`.

### Changing the rules mid-season

A rules change is a core commit and a pin move: `pin-core.sh <sha>` (above), committed on its own.
Records are per pin: after the move none stands until the record's port is evaluated at the new
pin (first, before any other entry), so a change that moves scores re-baselines the record. If
the `[entry]` caps change, `pin-core.sh` warns: update `common.ENTRY_CAPS` in the same commit. A
paused queue stays paused across the move (resume it as in step 6 above).

### Changing the margin

The owner's choice (now 2 %), between seasons; the measured run-to-run noise of one entry's
score (σ ≈ 1.75 % at the smoke shape) is the reference for it. Every place that states it: here `MARGIN` and its comment in `common.py`, `margin` in `records.json`, this
README (the `common.py` row and the "Re-roll the noise" defence), `AGENTS.md` §10, `README.md`,
`site/rules.html`, `site/llms.txt`, the two demo datasets (`site/demo/submissions.json` and
`site/demo/empty/submissions.json`, with the demo reasons that quote it), and the fallback `0.02` in `site/common.js` (used when
`submissions.json` cannot be read; twice); in the core, `README.md`, `AGENTS.md` §8 (the rule
and "The margin") and §12 (the near-copy limitation and the end-of-stream gain),
changed by a core commit and a pin move. The next `sync` or `select` treats a stored state with
another margin as stale and rewrites `data` and `records.json` with the new one; no entry changes
status, and records already taken stand.
