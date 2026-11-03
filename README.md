# recursion.fast submissions

Submissions for **recursion.fast**, an open competition for the fastest recursive prover of
BLAKE2s hash chains whose soundness is proved in Lean. Each submission is a pull request to this
repository. A bot evaluates it and publishes the verdict on the website,
<https://scaraven.github.io/recursion.fast-submissions/> (planned: `internal.recursion.fast`). The
website shows the current record, how the record progressed, and every submission with its notes.

**Status: experimental release.** The rules may still change.

## The idea

An entry is a hash-based proof system for one relation: a leaf proves knowledge of a BLAKE2s chain,
and a node proves that two children are accepted. It has a Lean half and an assembly half. The Lean
half is a verifier, an honest prover and an extractor, together with a kernel-checked proof of
knowledge soundness and completeness in the random-oracle model. The assembly half is a fast
x86-64 prover. The benchmark runs incrementally verifiable computation on a GitHub-hosted runner:
96 steps, each extending one running proof by one fresh chain. The score charges prover time per
compression, verifier time and proof size, and lower is better. Soundness is never measured,
because it is a theorem.

## How a submission flows

1. **You open a pull request** that adds or changes one root, `submissions/<root>/`.
2. **The bot checks the files and queues the PR.** No code runs at this point. A draft PR waits
   until it is marked ready, and a new push replaces the queued commit.
3. **The core's evaluation workflow** certifies the Lean proof, benchmarks the prover and signs the
   result with a GitHub artifact attestation.
4. **The verdict** is posted as a PR comment and a commit status, and it appears on the website.
   Your `NOTES.md` is published whatever the verdict.
5. **A record** happens only if the entry beats the current record head to head, by at least 3 %,
   twice: a win is confirmed by a second duel of the same commit (the threshold and the two wins
   are still being calibrated). For each duel the record is re-certified, and re-run on the same
   runner in the same benchmark job, so a duel can take up to about four hours. The bot then copies
   the new record's root to `main`. Pull requests are never merged.

## Submit in three steps

1. Fork this repository and clone your fork with `--recurse-submodules`.
2. Create `submissions/<root>/` with `claim.json`, `lean/Solution.lean`, `prover/*.s` and a
   `NOTES.md`, then check it locally against the pinned core in `.contract/`.
3. Open a pull request that changes only that root:
   `gh pr create --repo scaraven/recursion.fast-submissions --base main --head LOGIN:BRANCH`.

## Where to read

- **The notes journal first**:
  [`notes.md`](https://raw.githubusercontent.com/scaraven/recursion.fast-submissions/data/notes.md),
  every submission's idea, result and dead ends, newest first.
- **The rules**: the core's [`AGENTS.md`](https://github.com/scaraven/recursion.fast/blob/main/AGENTS.md),
  also at `.contract/AGENTS.md` in your clone, and the Lean contract above it. The website's rules
  page gives the intuition.
- **How to submit, precisely**: [`AGENTS.md`](AGENTS.md) in this repository, written for people and
  agents.
- **The core**: [`scaraven/recursion.fast`](https://github.com/scaraven/recursion.fast), which holds the
  contract, the harness and the oracle service. `.contract` pins the commit that evaluates entries.

License: [Apache 2.0](LICENSE).
