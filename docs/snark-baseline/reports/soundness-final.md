# Report: the `final` direction (`SpartanChainSoundnessFinal`)

This module covers blueprint §9.3 `final` and L-K3, built on `SpartanChainSoundnessDefs` (namespace
`SpartanChain.KS`); it does not edit that file.

- **Status.** There is no `sorry`, and `lake build +SpartanChainSoundnessFinal` is green.
- **Axioms.** Every theorem uses only `propext`, `Classical.choice` and `Quot.sound`
  (`logs/spartan-chain/rs-proximity/axioms-final.log`).
- **Source rule.** It reports `47 files, 0 finding(s)`.
- **Size.** 197 code lines and 19 theorems; the module checks in 9.5 s.

The evaluators `ev` are abstract throughout.

## What is proved (namespace `SpartanChain.SoundnessFinal`)

| item | statement |
|---|---|
| `leafProg_accept` | `(leafProg LV c π).runLog L = some true →` `n ≤ chainCap`, `π.size = leafSize n`, `c = leafStmt h n`, `n = 0 → h = s`, and `n ≠ 0 →` the SNARK verifier accepts on `L` |
| `pathOf_cases`, `entriesOf_snoc`, `stmtOf_snoc`, `kapOf_snoc`, `FS_snoc`, `cut_snoc`, `posClass_zero`, `posClass_last`, `len_eq` (`len κ = pV κ + 1 + nJ κ`) | path and position facts |
| `doom_seed` | a one-entry chain of a false statement is doomed, for every prefix log (`Alg` at position 0 is `FS`) |
| **`doom_of_not_esc`** | `¬ Esc ev L → IsChain L j → FS es_j → Doom ev (L₀ L j) es_j`, by strong induction along `predIdx`. Each prefix of a chain is a chain (`matches_of_append`), and prefixes after `absorb(root)` share the cut, hence `L₀` (`cut_snoc`) |
| **L-K3 `accept_not_doomed`** | `¬ Bad L`, a complete chain (`(pathOf L j).length = len κ`), `¬ Rej`, and `ColumnsAccepted L es` imply `¬ Doom ev (L₀ L j) es` |
| `chainEnd_of_runChain` | `¬ Bad`, `¬ Esc` and `RunChain ev L s n h` give `chainEnd s n = h` |
| `leaf_final`, **`mu_final_leaf`** | `μ ev L < 1` and `leafProg` accepting on `L`, given `RunChain` for `n ≥ 1`, give `n ≤ chainCap ∧ c = leafStmt h n ∧ chainEnd s n = h`. `not_bad_esc_of_mu` gives `μ < 1 → ¬Bad ∧ ¬Esc` |

How L-K3 is proved:

1. `split_at_cut` splits `L` as `L₀ ++ e :: L₁` at `absorb(root)`, and `rootOf_eq` identifies the
   chain's root.
2. `SoundnessPCS.verify2_miss` (new, `SpartanChainSoundnessPCS`) shows that the accepted column
   phase gives `Miss` for both difference sets of `filled L₀ root = Uof (L₀ L j) es`. It uses
   `verify2_runLog` and `opened_not_mem`, which goes through `open_binding_prefix`.
3. The last `Alg` row needs `¬ Miss (Dof …)`, which contradicts step 2.

No algebra, and no `chain_sound` or `zDec`, is needed for `final`: the doom at the seed is `FS`
itself, and `¬ Esc` carries it to the end. `chain_sound` is used only by the `τ_0` escape bound
in `step`.

## What `runLog_chain` (L-K4) must deliver

`mu_final_leaf` takes L-K4 as a hypothesis, `hchain`, in exactly this form (defined in this
module):

```lean
def ColumnsAccepted (L es : Log) : Prop :=
  ∃ st opens,
    (Ligero.verify2 (kapOf es) st (rootOf es) (rVec (kapOf es) es).toArray (aOf (kapOf es) es)
        (ubarOf (kapOf es) es) (msgOf (entAt es (pV (kapOf es))).1) opens).runLog L = some true ∧
      idxTuple L (kapOf es) st (msgOf (entAt es (pV (kapOf es))).1) = bOf (kapOf es) es

def RunChain (ev) (L : Log) (s : Digest) (n : ℕ) (h : Digest) : Prop :=
  ∃ j, IsChain L j ∧ (pathOf L j).length = len (kapOf (entriesOf L (pathOf L j))) ∧
    stmtOf (entriesOf L (pathOf L j)) = (s, n, h) ∧ ¬ Rej ev (entriesOf L (pathOf L j)) ∧
    ColumnsAccepted L (entriesOf L (pathOf L j))
```

The lemma needed from the log and Spartan agents:

```lean
theorem runLog_chain (ev) {L s n h π} (hb : ¬ Bad L) (hn : 1 ≤ n)
    (hacc : (snarkProg ev s n h π).runLog L = some true) : RunChain ev L s n h
```

`leafProg`'s header check gives `n ≤ chainCap`. The lemma has to establish the following
identities:

- **`κ`.** `Verifier.kap n` is the same as `kapOf es` (`Nat.clog 2 n`).
- **Root.** `tail`'s `readLabel π 0` is `rootOf es`, which is `parseAbsorbRoot` of the
  `absorb(root)` query.
- **`r`.** `verify1`'s `r` is `rVec κ es` as a list.
- **Row weights.** `eqTable (pc.point.drop (lk κ))` is `aOf κ es`.
- **`ū`.** `readEFs (π.extract 31 (off₁ κ)) 0 (msgLen κ)` is `ubarOf κ es`.
- **`vB`.** It is the message of the `absorb(v)` entry, and `st` is the state before it.
- **Index answers.** `idxTuple` is the chain's last `J` answers (`bOf`).
- **No rejection.** `¬ Rej`, i.e. checks (a)–(f) pass on the chain's data.

`SpartanChainSubmission` remains for the KState assembly: the extraction
`E c π L = some (.leaf s n)` and `R c w`, from `mu_final_leaf` and `checkNode_sound`.
