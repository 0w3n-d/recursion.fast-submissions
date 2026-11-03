# `submissions/`: one root per entry

Each entry is one directory, `submissions/<root>/`, where `<root>` matches `[a-z][a-z0-9-]{0,39}`.
A pull request creates or changes exactly one root and nothing else. On `main` this directory holds
only the current record's root, which the bot copies here. Every other evaluated root stays at its
tag `rf-source/<id>`.

| Path | Required | What |
|---|---|---|
| `claim.json` | yes | the declared numbers: `error`, `completeness_error`, `qV`, `fuel_base`, `fuel_per_word` |
| `lean/Solution.lean` | yes | `RecursionFast.Challenge.submission` and the theorem `certified` |
| `lean/*.lean` | as needed | your other modules, flat in `lean/`, with fresh module names |
| `prover/*.s` | yes | the x86-64 prover as GNU assembly |
| `NOTES.md` | yes | the journal: idea, result, what failed and why, what to try next |
| `README.md` | recommended | what the entry is, for a reader |
| anything else | no | read by people, ignored by the evaluation |

Only regular files and directories are allowed (no symbolic links). The size caps are in
[`../AGENTS.md`](../AGENTS.md), section 8.

The full procedure, from setup and local checks to the bot's statuses and the record rule, is
[`../AGENTS.md`](../AGENTS.md). The rules themselves are `.contract/AGENTS.md`.
