# Focused re-review of BLUEPRINT-R1 §9 (the security argument in the potential form)

Reviewed: `docs/snark-baseline/BLUEPRINT-R1.md` §9 (lines 661–966) and §14, as revised after
`docs/reviews/BLUEPRINT-R1-review.md`. Target: the amended contract
`rf-core-ks/RecursionFast/Contract/Security.lean` (`KState`: `empty`; `step`: for fresh `q`,
`|L| < logCap = 2^96`, `μ L < 1`, `Σ_a μ(L ++ [(q,a)]) ≤ (μ L + ε)·2^256`; `final`:
`|L| ≤ logCap`, `μ L < 1`, `runLog L = some true` ⇒ `∃ w, E c π L = some w ∧ R c w`),
`Library/PaperTheorem.lean` (`paper`), and `Contract/Relation.lean`
(`Rel _ c (.leaf s n) ↔ n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n`). Read-only; no Lean was
run (the blueprint has no Lean yet). Every failure below is a concrete log.

**Verdict: not ready to formalise.** The structure is right and most of it checks: per-column
trees with zero fill, `Bad` (i)–(iv), the chain forest, the far/close modes, every algebraic
round, the `final` chain, the ε arithmetic. But as defined, `step` is **false** for two logs a
formaliser would hit at once (S9-M1, S9-M2), and two lemmas in the inventory are false as
written (S9-M3). All three fixes are changes to definitions and hypotheses. None of them changes
the protocol, a byte, a parameter or `ε = 2^-129`. After the fixes, §9 is ready.

---

## Major findings

### S9-M1. `Doom_T` ignores failed verifier checks, so a sumcheck round escapes with probability 1

**Where.** §9.2 (line 760: `Esc_T(ρ) := Doom_T(ρ−1) ∧ ¬Doom_T(ρ)`). The R2, R4 and R6 rows
(line 767 ff.). The R7 `p_T` (line 795). §9.3 step, bullet "a single-answer squeeze".

**Argument.** The R2 row's Doom column after round `l` is `FarDoom ∨ cl_{l+1} ≠
g*_{l+1}(0)+g*_{l+1}(1)`. Its escape bound says "the check `g_l(0)+g_l(1) = cl_l` passed", but
the event `Esc_T` does not include that condition. No row tracks the absorb of `g_l`, so
`Doom_T(ρ−1)` is the doom after `r_{x,l−1}`.

Take a log `L` with:
- the seed of a false statement;
- `absorb(root)` of an honestly built tree for any Boolean non-satisfying witness (close mode);
- the `m` R0 answers, `absorb(ū)`;
- `ℓ_x` answers `τ` with `P_{ℓ_x} ≠ 0` (no R1 escape);
- then `absorb(g_0)` with **`g_0 := g*_0`**, the true round polynomial. Its check fails because
  `g*_0(0)+g*_0(1) = Σ G ≠ 0 = cl_0`, but the log does not care.

`L` has `¬Bad`, `¬Esc` and no partial multi-answer round, so `μ L = 0`. Let the fresh query be
the next squeeze. For **every** answer, `cl_1 = g*_0(r) = g*_1(0)+g*_1(1)`, so `Esc_T(R2, 0)`
holds and `μ(L_a) = 1` for all non-`Bad` `a`. Then `Σ_a μ(L_a) ≈ 2^256 > ε·2^256`, and `step`
fails.

The same happens at R4 and R6. It also happens after any absorb row whose check failed: doom can
drop to false there (the table makes the implication conditional on the check passing) and later
re-enter at a sumcheck round. The R7 `p_T` is a related problem: it is defined as a miss count,
not as the escape event. Once failed checks are made dooming (the fix), a chain that is doomed
only because a check failed can have `D_T = ∅` and `p_T = 1`, and `step` fails at the first R7
answer.

**Fix.**
1. Add a rejection disjunct:
   `Doom_T(ρ) := Rej_T(ρ) ∨ FarDoom ∨ alg_T(ρ)`.
   `Rej_T(ρ)` means some check of `leafProg` that is a function of `T`'s data through position
   `ρ` fails: a sumcheck consistency check, a final check after R2, R4 or R6, the slice-weighted
   inner check, or the check at `v`. It is monotone.
2. Index rounds by **chain positions** (every absorb and every squeeze), so that `ρ−1` is
   unambiguous. Add the lemma `doom_absorb`: an absorb never turns `Doom` from true to false.
   This is the table's "implied by the previous row" argument, which with `Rej` needs no
   hypothesis.
3. Define `p_T` uniformly as the **conditional count of `Esc_T(round)`**, not of "miss `D`" or
   "far ∧ close". It then vanishes automatically under `Rej`. The R0 and R7 bounds are
   unchanged: the bound is used only when `¬Rej`.

`final` is unaffected: an accepted run has no `Rej`. L-K3 gains a trivial `Rej` case.

### S9-M2. `μ` sums `p_T` over every prefix of a partial round (double counting)

**Where.** §9.1 line 721 ("a list that stops anywhere in this pattern is a chain"). Line 727
("an entry lies on at most one chain"; with prefix-closed chains, each entry *ends* one chain and
lies on many). §9.3 line 802/805 (the sum is over "the entries of `L` that end a partial
multi-answer round"). The step bullets at lines 829 ff.

**Argument.** Inside R7, the entries `e_j` and `e_{j+1}` (`j+1 < J`) both end a partial round,
so `μ` counts both `p` values. The step bullets treat `p_T` as *replaced* when the round
advances, but the definition *adds* it.

Concrete log, at `ℓ_N = 12` (`cnt = 21`, `J = 13`), far mode with `|D| = e+1`:
- a doomed chain whose 12 index answers all missed `D`, so its last prefix has
  `p_12 = (17/24)^8 ≈ 0.063`;
- the shorter prefixes add `p_11 ≈ 4.5·10^-5` and less, so `X ≈ 0.063` and `μ L ≈ 0.063`.

Let the fresh query be the 13th squeeze. Then
`Σ_a μ(L_a)/2^256 ≥ Pr[Esc] + Pr[¬Esc]·X ≈ 0.063 + 0.937·0.063 ≈ 0.122`. That is more than
`μ L + ε`, so `step` fails. R0 has the same defect.

**Fix.** Sum only over **frontier** entries. An entry `e` that is the `j`-th answer of a partial
multi-answer round of a chain is on the frontier when the next squeeze query `0x30 ‖ a_e` is not
in `L.map Prod.fst`. Under `¬Bad`, that query is the only chain extension of `e`: an absorb from
`a_e` mid-round matches no pattern. The fresh query `0x30 ‖ a_e` removes `e` from the frontier
and adds the new entry, so the middle-answer case is
`X' = X − p_T(L) + p_{T'}(L_a)` with `Σ_a p_{T'}(L_a) = 2^256·p_T(L)`, as the bullets intend.
Reword line 727 ("each entry ends exactly one chain").

### S9-M3. Two lemma statements are false as written: L-M4 and L-K7 (and §9.1 line 694)

**L-M4** (line 917): its hypothesis is "some entry of `L` **at or after** the cut has
`root ∈ labelsIn(q)`". Counterexample: `L₀ = []` and `L = [(node query, answer with [a]_31 =
root), absorb(root)]`. The `absorb(root)` entry lies after the cut, `¬Bad` holds, but
`tree_{[]}(root) ≠ tree_L(root)`. The use in §9.1 (`L₀(T)` ends just before `T`'s
`absorb(root)`) is fine.

**Fix:** write the log as `L₀ ++ e :: L₁` where **`e` is the `absorb(root)` entry**
(`parseAbsorbRoot q_e = some root`). Write L-M3's "at the cut" the same way. An arbitrary carrier
with `root ∈ labelsIn(q_e)` is not enough. A node query whose own truncated answer is `root` is
not a label hit under the strict `i < j`, and `col_L` would read it while `col_{L₀}` gives `none`.
For an absorb carrier, a self-hit is read as a non-node and gives `none` on both sides. With this
hypothesis the lemma is true, and the implementer's `Merkle.tree_prefix` proves exactly this
form.

**L-K7** (line 949) and the claim at line 694 ("**earlier** in `L`"): `Bad` (iii) uses `i < j`,
so a **self-hit** (`q = 0x30 ‖ st` with answer `st`) is not `Bad`. Counterexample:
`L = [(0x30 ‖ a, a)]` has `¬Bad`, but its predecessor is the entry itself, which does not precede
it. Such an entry lies on no chain, because a chain starts at a seed and `(i)` excludes a second
entry with answer `st`. But the lemma as stated is false, and L-K8 ("a unique predecessor")
inherits it. **Fix (simplest):** make (iii) `i ≤ j`. This costs one more answer per step
(`2^-256`), and L-K1 becomes `≤ L.length·(3·2^8+1) + 1`. Alternatively, state L-K7 non-strictly
and prove separately that self-hits are on no chain.

### The implementer's corrections (`reports/oracle-merkle-transcript.md`), checked

The Merkle/Transcript implementer found three blueprint statements false and corrected them in
`SpartanChainMerkle.lean` and `SpartanChainTranscript.lean`. All three corrections are right.

1. **L-M2 needs `¬Collision L`.** This is correct. The blueprint's L-M2 assumes only that the
   build queries are in `L` and consistent with `H`. An *earlier* entry with a different query
   but the same 31-byte truncated answer is then the first entry that `col_L` reads, and the
   descent fails. The lemma is a positive control, so the extra hypothesis is harmless: it holds
   on honest logs except with probability about `|L|²·2^-248`. Add it to §9.4.
2. **`StateHit` with `i ≤ j`.** This is the same as S9-M3 above, and correct.
3. **L-M4 with the cut at the `absorb(root)` entry.** This is the same as S9-M3 above, with the
   carrier restricted to the absorb, and correct. The split form `open_binding_prefix`
   (`¬Collision ∧ ¬Hit`, log `L₀ ++ e :: L₁`) is the right L-M3. The one-log `open_binding`
   needs only `¬Collision`.

**How the corrections propagate.**

- **L-K1.** The bound becomes `#{a : Bad(L ++ [(q,a)])} ≤ L.length·(3·2^8+1) + 1`. The `+1` is
  the answer equal to `q`'s own state. Self label-hits stay uncharged, which is fine by 3. The
  fraction is unchanged to the precision quoted, and `ε = 2^-129` stands. The implementer's
  `Collision` is unordered, so it charges the same `|L|·2^8`.
- **L-K4.** It must also return the **index** of the run chain's `absorb(root)` entry, so that
  `final` can split `L = L₀(T) ++ e :: L₁` and apply `open_binding_prefix` to each opened
  column. The run's Fiat–Shamir entries are pairwise distinct and strictly ordered by
  `pred_unique_lt`, which with `i ≤ j` is now true.
- **L-K5.** In `step`, the stability of `U_T` needs only that `L₀(T)` is a fixed prefix (no
  L-M4). In `final`, L-K3 uses `open_binding_prefix` at the split from L-K4. Both `Collision`
  and `Hit` are disjuncts of `Bad`.
- **L-K8.** With `i ≤ j`, a fresh non-`Bad` entry is never its own predecessor. "Extends a chain
  of `L` or is a seed or extends nothing" is then exact, with no self-loop case. Under `i < j`
  it was not.

---

## Minor findings

- **S9-m1 (L-S1's hypothesis is inverted).** Line 867 assumes
  `g(0)+g(1) = g*(0)+g*(1)`. In every application the check passed while doomed, so
  `g(0)+g(1) = cl ≠ g*(0)+g*(1)`. The lemma is true but cannot be applied. **Fix:** drop the
  hypothesis (`g ≠ g*`, both of degree `≤ d`, suffices), or replace it by `≠`, from which
  `g ≠ g*` follows.
- **S9-m2 (L-K2a/b/c are stated on `L ++ [(q,a)]`).** Under `Bad(L_a)` the chains of `L_a` are
  not the intended ones (`pred` becomes ambiguous). The step argument already sums an "intended
  value" over all `a`. State `p` as a function of the round data, `pRound(U_T, msgs, answers so
  far)`, and state L-K2 on the formal extension `T ++ [(q,a)]`. Then the step's
  `Σ_{¬Bad} actual = Σ_{¬Bad} intended ≤ Σ_all intended` is literal.
- **S9-m3 (L-K4 wording).** "The entries `find?`-answering the run's queries … form a chain"
  includes the Merkle queries, which are never chain entries. Restrict it to the Fiat–Shamir
  queries, and add as a separate clause that the run's Merkle sub-programs are `verifyPath`
  instances (needed by L-M3 via `runLog_bind`).
- **S9-m4 (`min(1, ·)` is unnecessary).** `μ := if Bad ∨ Esc then 1 else Σ_frontier p` has the
  same `step` and `final` proofs, because `μ L < 1` still gives `¬Bad ∧ ¬Esc`. Removing the
  `min` removes `min_le` bookkeeping.

## Simpler `μ` (answer to question 3)

These changes cut proof effort without weakening (1)–(2):

1. **One generic round lemma.** Treat every squeeze as an answer of a *round*: the R0 block of
   `m`, the R7 block of `J`, or a singleton for R1–R6. Define `p` as the conditional count of
   that round's `Esc` event (S9-M1, step 3) on frontier entries (S9-M2). L-K2a/b/c and the
   single-answer bullet then become one lemma, `roundPot_split : Σ_a p(prefix ++ [a]) =
   2^256·p(prefix)`, with `p([]) = Pr[Esc]`. That is a `Fintype.sum` split over
   `Digest × Digest^{r−j−1}`. The step has three cases: Bad, no-op, round answer.
2. **Optional closed form for R7.** In both modes `|D| ≥ e+1 > 7N/24` (close mode:
   `d − e ≥ e + 1`). So
   `p_T := [¬Rej ∧ doomed entering ∧ all indices so far miss D_T]·(17/24)^{t − drawn}` is a
   valid supermartingale (`≤` instead of `=` in the split). L-RS3 then becomes a per-answer count
   (`#{a : all its chunks miss D} = (N−|D|)^{c}·2^{256−cℓ_N}`), and the `5/12` close-mode figure
   is not needed. R0 cannot be closed-form (its event is not a product). A per-answer R0 via the
   interleaved affine-line lemma would need ArkLib's
   `exists_codewords_agree_of_many_close_scalars` generalised to an `F^m` alphabet, which is no
   cheaper than the planned double count over `E^m`. Keep R0 on the generic count.
3. Drop `min` (S9-m4).

---

## Checked and found correct (after the fixes above)

- **`step` skeleton.** The bound `μ(L_a) ≤ [Bad] + [¬Bad]([Esc] + X')` holds pointwise, and
  replacing actual values by intended values on non-`Bad` answers is sound (no Jensen needed).
  Under `¬Bad(L_a)`, a fresh entry is a leaf of the forest:
  - (iii) means no old entry's predecessor changes;
  - (i) and (iv) make answers unique;
  - `U_T` reads the fixed prefix `L₀(T)`.

  So old chains, their escapes and their `p` are unchanged.
- **L-K1 count.**
  - Collisions: `|L|·2^8`.
  - Label hits: `2|L|·2^8`. The new query's own labels pointing at old answers are the honest
    direction and are rightly not charged.
  - State hits: `|L|`.
  - Repeats: none, since `q` is fresh.

  The resulting fraction is `< 3·2^-152 + 2^-160`. `ε`:
  `2^-129.3499 + 3·2^-152 + 2^-160 + 2^-256 < 2^-129`.
- **Adversarial logs.**
  - Repeats are `Bad` (iv).
  - A state answered after its use is `Bad` (iii).
  - A subtree completed after `absorb(root)` is `Bad` (ii), and anyway invisible to `U_T`.
  - Forks are possible only at absorbs, and each fork costs a fresh query.
  - Many statements and many roots give independent chains.
  - Self-referential Merkle nodes (a label in its own query) are harmless: `col` and the path
    read the same unique entries.
  - Wrong-shape leaves or nodes give `none`, and no path can verify through them.
- **Per-round bounds.**
  - R0: L-RS2, `≤ d/|E| ≤ 2^-169.2`. The `2^{64m}` preimage count is exact.
  - R1: multilinear restriction, `≤ 1`.
  - R2/R4/R6: `≤ 3, 2, 2` once the check is in the event (S9-M1).
  - R3: `≤ 2`.
  - R5: `π^{(p+1)}_k = π^{(p)}_k + f_p^{2^k}π^{(p)}_{k+M_p}`. Re-derived: Frobenius is bijective,
    so `≤ 1` per stage. `π^{(6)}_0 = T + T*` by additivity of `Φ` and L-R3.
  - R7: far `|D| > e`; close `|D| ≥ d − e`; `(17/24)^260 = 2^-129.35`.
- **The absorb-row implications** (triple, slices, `v`) hold with no division, including when
  `eq(τ, r_x)`, `M̃_ρ` or `W̃(r'')` vanish.
- **`final` chain.**
  - `μ L < 1` gives `¬Bad ∧ ¬Esc`.
  - A node proof is `checkNode_sound`. For `n = 0`, `h = s = chainEnd s 0`.
  - For a true statement, `decode π = some (.leaf s n)` and `Rel` holds (`n ≤ chainCap` and
    `c = leafStmt h n` are checked by `V`; `decodeWit_cons` reads word 5 as `n`, and `V` reads
    the same bytes).
  - For a false statement, the run's Fiat–Shamir entries form a complete chain (L-K4/L-K7: under
    `¬Bad` the run's answers are pairwise distinct, so no FS query repeats). It is doomed at
    every position. At the end, `c* ∈ D` is opened, a verifying path forces the opened column
    to be `tree_{L₀}(root) c*`, which is `U_T`'s column (L-M3; a missing column has no verifying
    path, so the zero fill is never opened), and the mode's equation fails at `c*`.
- **Links in the chain.**
  - The decoded `q_dec` is in `K` (`close_in_K`), so `w_dec` is Boolean.
  - `F ≢ 0` follows from L-C2. `pub(s, h)` comes from the chain's seed, which equals the proof's
    `(s, n, h)`.
  - Slices: `δ = 0` gives `Σ_i eq(r_lo,i)s_i = w̃_dec(r_u)` (L-E3).
  - Ring switching: `T* = Σ_{u'} W q_dec`.
  - Ligero: `v = Σ_i a_i q_dec[i]` gives `Σ_j b_j v_j = q̃_dec(r'')`.

  No gap.
- **Lemmas true as written:** L-M3 (with "at the cut" read as `L₀ ++ e :: L₁`, where `e` is the
  `absorb(root)` entry), L-M2 (with `¬Collision`, as corrected by the implementer), L-S2, L-S3,
  L-R1 (re-derived through the `K`-basis `{1, y^{2^k}, y^{2^{k+1}}}` and the 64 distinct
  conjugates), L-R2, L-R3, L-R4, L-E4, L-RS1, L-RS2 (ArkLib `prob_of_bad_pts`: `3e < d`, bound
  `d/|F|`), L-RS3, L-RS4, L-K1, L-K3 (plus the `Rej` case), L-K8 (with the M3 fix).
