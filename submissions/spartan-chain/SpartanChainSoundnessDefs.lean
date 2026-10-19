import SpartanChainSoundnessLog
import SpartanChainSoundnessPCS
import SpartanChainSpartanProtocol
import RecursionFast.Library.Security

/-!
# The definitions of the knowledge state (BLUEPRINT-R1 §9.2–§9.3)

The objects of §9.2 and §9.3 — rejection `Rej`, algebraic doom `Alg`, `Doom`, `EscAt`, `Esc`, the
formal extensions `ext`/`ext1`, the conditional counts `condCount`, the round charges `pRound` and
the potential `μ` — for a fixed evaluator family `ev` (the `Spartan.Evals` of the verifier, one per
`(κ, n, s, h)`). The proofs are in `SpartanChainSoundnessKS` (`step`) and
`SpartanChainSoundnessFinal` (`final`).

**Part A (generic).** For any doom predicate `D L₀ es` and charge `φ L₀ es` on a chain's prefix log
`L₀` and entries `es`: `EscAtG`, `EscG`, `termG`, `sumG`, `muG` (§9.3's `μ`).

**Part B (positions and rounds).** `pre8` (the shape before the column-index squeezes),
`rnd κ p` (the multi-answer round `(s0, r)` of an answer position: R0 is `(1, rows κ)`, R7 is
`(len κ − J − 1, J)`), `lastAns`, `ext1`, `ext`, `condCount`, `pRoundG`.

**Part C (the leaf transcript read off a chain).** Positions (`pU`, `pTau`, `pG`, `pTri`, `pGi`,
`pS`, `pF`, `pGr`, `pV`), the messages and challenges of §6.2 at those positions, the claims, the
checks (a)–(f) (`Rej`, literally the verifier's: `verifyRounds`' round test, `eqPts`, `zV`,
`target`, `weightEval`), the modes and the decoded witness (`far`, `FarDoom`, `zDec`), the table of
`Alg` by position class (`posClass`), `Doom`, and `μ`.

Index conventions: a chain `es` has position `ρ = es.length − 1`; `κ = kapOf es`; `m = rows κ`,
`ℓ = 15 + κ` rounds outer and inner, `8 + κ` ring-switching rounds, `J = nJ κ` index answers. The
R1CS has `2 ^ (14 + κ + 1)` rows and columns (`Ix κ`), so the tables are bound over `14 + κ + 1`
variables (which is `15 + κ`).
-/

namespace SpartanChain
open RecursionFast Merkle Transcript SoundnessLog
open scoped NNReal

namespace KS

/-! ## Part A: the potential over chains (generic) -/

section Potential

variable (D : Log → Log → Prop) (φ : Log → Log → ℝ≥0)

/-- **`EscAt`**: the chain `es` (of at least two entries) was doomed before its last entry and is
not after it, both for the matrix of the prefix `L₀`. -/
def EscAtG (L₀ es : Log) : Prop := 2 ≤ es.length ∧ D L₀ es.dropLast ∧ ¬ D L₀ es

/-- **`Esc`**: some chain of `L` escapes at its last entry. -/
def EscG (L : Log) : Prop := ∃ j ∈ chains L, EscAtG D (L₀ L j) (entriesOf L (pathOf L j))

open Classical in
/-- The charge of chain `j` in `L`: its `φ` if its last entry is on the frontier, else `0`. -/
noncomputable def termG (L : Log) (j : ℕ) : ℝ≥0 :=
  if OnFrontier L L[j]! then φ (L₀ L j) (entriesOf L (pathOf L j)) else 0

/-- The sum of the frontier charges over the chains of `L`. -/
noncomputable def sumG (L : Log) : ℝ≥0 := ((chains L).map (termG φ L)).sum

open Classical in
/-- **The potential** (§9.3): `1` on a bad or escaped log, else the frontier charges. -/
noncomputable def muG (L : Log) : ℝ≥0 := if Bad L ∨ EscG D L then 1 else sumG φ L

end Potential

/-! ## Part B: positions, rounds, formal extensions -/

section Positions
open PCS

/-- The number of column-index answers `J = ⌈t / cnt⌉`. -/
abbrev nJ (κ : ℕ) : ℕ := nAns (lN κ) tQ

/-- The steps of the leaf transcript through `absorb(v)` (before the `J` index squeezes). -/
def pre8 (κ : ℕ) : List Step :=
  [.seed, .absorb 0x01 31] ++ List.replicate (rows κ) .squeeze ++
    [.absorb 0x02 (24 * msgLen κ)] ++ List.replicate (15 + κ) .squeeze ++
    (List.replicate (15 + κ) [.absorb 0x03 96, .squeeze]).flatten ++ [.absorb 0x04 72, .squeeze] ++
    (List.replicate (15 + κ) [.absorb 0x05 72, .squeeze]).flatten ++ [.absorb 0x06 1536] ++
    List.replicate 6 .squeeze ++ (List.replicate (8 + κ) [.absorb 0x07 72, .squeeze]).flatten ++
    [.absorb 0x08 (24 * msgLen κ)]

theorem shape_eq_pre8 (κ : ℕ) : shape κ = pre8 κ ++ List.replicate (nJ κ) .squeeze := rfl

/-- **The multi-answer round of an answer position** `p`: `some (s0, r)` when `p` is one of the
`r` answers `s0 + 1, …, s0 + r` of a round entered at the absorb position `s0` — R0 (`(1, rows κ)`)
or R7 (`(len κ − J − 1, J)`); `none` at every other position. -/
def rnd (κ p : ℕ) : Option (ℕ × ℕ) :=
  if 2 ≤ p ∧ p ≤ 1 + rows κ then some (1, rows κ)
  else if (pre8 κ).length ≤ p ∧ p < len κ then some ((pre8 κ).length - 1, nJ κ)
  else none

end Positions

section Ext

/-- The answer of the last entry (`default` for the empty list). -/
def lastAns (es : Log) : Digest := (es.getLast?.map Prod.snd).getD default

/-- **`ext1`**: the chain extended by the squeeze of its last answer, answered `a`. -/
def ext1 (es : Log) (a : Digest) : Log := es ++ [(squeezeQ (lastAns es), a)]

/-- **`ext`**: the formal extension of `es` by the answers `as`, each a squeeze of the previous
answer. -/
def ext (es : Log) (as : List Digest) : Log := as.foldl ext1 es



/-- The entry at position `p` (`default` past the end). -/
def entAt (es : Log) (p : ℕ) : ByteArray × Digest := es.getD p default

/-- The statement `(s, n, h)` of a chain's seed (entry `0`). -/
def stmtOf (es : Log) : Digest × ℕ × Digest := (seedOf (entAt es 0).1).getD default

/-- The shape parameter `κ = ⌈log₂ n⌉` of a chain. -/
def kapOf (es : Log) : ℕ := Nat.clog 2 (stmtOf es).2.1

variable (D : Log → Log → Prop)

open Classical in
/-- **`condCount`** (§9.2): the conditional count of the escape event `EscAt (ext es₀ ·)` of a round
of `r` answers entered at `es₀`, given the first answers `pre`, as a fraction of `2^256` per missing
answer. -/
noncomputable def condCount (L₀ es₀ : Log) (r : ℕ) (pre : List Digest) : ℝ≥0 :=
  (extCount (fun as => EscAtG D L₀ (ext es₀ as)) pre (r - pre.length) : ℝ≥0) /
    2 ^ (256 * (r - pre.length))

/-- **`pRound`** (§9.3): inside a multi-answer round, after `1 ≤ i < r` answers, the conditional
count of the round's escape given those answers; `0` everywhere else. -/
noncomputable def pRoundG (L₀ es : Log) : ℝ≥0 :=
  match rnd (kapOf es) (es.length - 1) with
  | some (s0, r) =>
    if es.length - 1 - s0 < r then
      condCount D L₀ (es.take (s0 + 1)) r ((es.drop (s0 + 1)).map Prod.snd)
    else 0
  | none => 0

end Ext

/-! ## Part C: the leaf transcript read off a chain -/

section Leaf
open PCS Spartan SoundnessPCS RS

/-! ### Positions of §6.2 (indices into `shape κ`) -/

/-- `absorb(ū)`. -/
def pU (κ : ℕ) : ℕ := 2 + rows κ
/-- `τ_l`. -/
def pTau (κ l : ℕ) : ℕ := 3 + rows κ + l
/-- `absorb(g_l)` (outer); `r_{x,l}` is the next position. -/
def pG (κ l : ℕ) : ℕ := 3 + rows κ + (15 + κ) + 2 * l
/-- `absorb(v_A ‖ v_B ‖ v_C)`; `ρ` is the next position. -/
def pTri (κ : ℕ) : ℕ := 3 + rows κ + 3 * (15 + κ)
/-- `absorb(g'_l)` (inner); `r_{y,l}` is the next position. -/
def pGi (κ l : ℕ) : ℕ := pTri κ + 2 + 2 * l
/-- `absorb(s_0 ‖ … ‖ s_63)`. -/
def pS (κ : ℕ) : ℕ := pTri κ + 2 + 2 * (15 + κ)
/-- `f_p`. -/
def pF (κ p : ℕ) : ℕ := pS κ + 1 + p
/-- `absorb(g''_l)` (ring switching); `r''_l` is the next position. -/
def pGr (κ l : ℕ) : ℕ := pS κ + 7 + 2 * l
/-- `absorb(v)`; the index answers follow. -/
def pV (κ : ℕ) : ℕ := pS κ + 7 + 2 * (8 + κ)

/-! ### Messages and challenges -/

/-- The message of an absorb query `0x20 ‖ st ‖ kind ‖ msg`: its bytes from `34` on. -/
def msgOf (q : ByteArray) : ByteArray := q.extract 34 q.size


/-- The `c` field elements of the message at position `p`. -/
def efsAt (es : Log) (p c : ℕ) : Array EF := Ligero.readEFs (msgOf (entAt es p).1) 0 c

/-- The field challenge of the answer at position `p`. -/
def chAt (es : Log) (p : ℕ) : EF := chE (entAt es p).2

/-- The root of a chain: the label of its `absorb(root)` entry. -/
def rootOf (es : Log) : Label := (parseAbsorbRoot (entAt es 1).1).getD default

/-- `r_0, …, r_{m−1}` (R0). -/
def rVec (κ : ℕ) (es : Log) : List EF := (List.range (rows κ)).map fun i => chAt es (2 + i)
/-- `ū`. -/
def ubarOf (κ : ℕ) (es : Log) : Array EF := efsAt es (pU κ) (msgLen κ)
/-- `τ`. -/
def tauOf (κ : ℕ) (es : Log) : List EF := (List.range (15 + κ)).map fun l => chAt es (pTau κ l)
/-- `g_l` (outer, 4 coefficients). -/
def gOut (κ : ℕ) (es : Log) (l : ℕ) : Array EF := efsAt es (pG κ l) 4
/-- `r_x`. -/
def rxOf (κ : ℕ) (es : Log) : List EF := (List.range (15 + κ)).map fun l => chAt es (pG κ l + 1)
/-- `(v_A, v_B, v_C)`. -/
def triOf (κ : ℕ) (es : Log) : EF × EF × EF :=
  let t := efsAt es (pTri κ) 3
  (t.getD 0 0, t.getD 1 0, t.getD 2 0)
/-- `ρ` (the batching challenge). -/
def rhoOf (κ : ℕ) (es : Log) : EF := chAt es (pTri κ + 1)
/-- `g'_l` (inner, 3 coefficients). -/
def gIn (κ : ℕ) (es : Log) (l : ℕ) : Array EF := efsAt es (pGi κ l) 3
/-- `r_y`. -/
def ryOf (κ : ℕ) (es : Log) : List EF := (List.range (15 + κ)).map fun l => chAt es (pGi κ l + 1)
/-- The 64 slices. -/
def slicesOf (κ : ℕ) (es : Log) : Array EF := efsAt es (pS κ) 64
/-- `f_0, …, f_5`. -/
def fsOf (κ : ℕ) (es : Log) : List EF := (List.range 6).map fun p => chAt es (pF κ p)
/-- `g''_l` (ring switching, 3 coefficients). -/
def gRs (κ : ℕ) (es : Log) (l : ℕ) : Array EF := efsAt es (pGr κ l) 3
/-- `r''`. -/
def rrOf (κ : ℕ) (es : Log) : List EF := (List.range (8 + κ)).map fun l => chAt es (pGr κ l + 1)
/-- `v` (the evaluation row combination). -/
def vOf (κ : ℕ) (es : Log) : Array EF := efsAt es (pV κ) (msgLen κ)
/-- The `J` index answers. -/
def bOf (κ : ℕ) (es : Log) : Fin (nJ κ) → Digest := fun j => (entAt es (pV κ + 1 + j)).2
/-- `r_hi`: coordinates `6 … 13 + κ` of `r_y` (the packed-witness point of ring switching). -/
def rhiOf (κ : ℕ) (es : Log) : List EF := ((ryOf κ es).take (lu κ)).drop 6
/-- The row weights `a_i = eq(r''_hi, i)` of the evaluation test. -/
def aOf (κ : ℕ) (es : Log) : Array EF := eqTable ((rrOf κ es).drop (lk κ))

/-! ### The claims and the checks (a)–(f) -/

/-- The outer claims: `cl_0 = 0`, `cl_{l+1} = g_l(r_{x,l})`. -/
def clOut (κ : ℕ) (es : Log) : ℕ → EF
  | 0 => 0
  | l + 1 => peval (gOut κ es l) ((rxOf κ es).getD l 0)

/-- The inner claims: `cl'_0 = v_A + ρ v_B + ρ² v_C`, `cl'_{l+1} = g'_l(r_{y,l})`. -/
def clIn (κ : ℕ) (es : Log) : ℕ → EF
  | 0 => (triOf κ es).1 + rhoOf κ es * (triOf κ es).2.1 + rhoOf κ es ^ 2 * (triOf κ es).2.2
  | l + 1 => peval (gIn κ es l) ((ryOf κ es).getD l 0)

/-- The ring-switching claims: `cl''_0 = T = Σ_i x^i Φ(s_i)`, `cl''_{l+1} = g''_l(r''_l)`. -/
def clRs (κ : ℕ) (es : Log) : ℕ → EF
  | 0 => target xE (fsOf κ es) (slicesOf κ es)
  | l + 1 => peval (gRs κ es l) ((rrOf κ es).getD l 0)

/-- The verifier's round test (`verifyRounds`): `d + 1` coefficients and `g(0) + g(1) = claim`. -/
def RoundOK (d : ℕ) (g : Array EF) (claim : EF) : Prop :=
  g.size = d + 1 ∧ peval g 0 + peval g 1 = claim

/-- **Rejection** (§9.2): some check (a)–(f) of `leafProg` whose inputs are complete at the chain's
position `ρ = es.length − 1` fails. The evaluators are `ev κ n s h` of the chain's seed. -/
def Rej (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals) (es : Log) : Prop :=
  let κ := kapOf es
  let ρ := es.length - 1
  let E := ev κ (stmtOf es).2.1 (stmtOf es).1 (stmtOf es).2.2
  let t := triOf κ es
  let M := E.mats (rxOf κ es) (ryOf κ es)
  let r := rhoOf κ es
  -- (a) the outer rounds
  (∃ l < 15 + κ, pG κ l ≤ ρ ∧ ¬ RoundOK 3 (gOut κ es l) (clOut κ es l)) ∨
  -- (b) the outer final check
  (pTri κ ≤ ρ ∧ clOut κ es (15 + κ) ≠ eqPts (tauOf κ es) (rxOf κ es) * (t.1 * t.2.1 + t.2.2)) ∨
  -- (c) the inner rounds
  (∃ l < 15 + κ, pGi κ l ≤ ρ ∧ ¬ RoundOK 2 (gIn κ es l) (clIn κ es l)) ∨
  -- (d) the inner final check
  (pS κ ≤ ρ ∧ clIn κ es (15 + κ) ≠
    (M.1 + r * M.2.1 + r ^ 2 * M.2.2) * zV κ E (slicesOf κ es) (ryOf κ es)) ∨
  -- (e) the ring-switching rounds
  (∃ l < 8 + κ, pGr κ l ≤ ρ ∧ ¬ RoundOK 2 (gRs κ es l) (clRs κ es l)) ∨
  -- (f) the weighted final check against `v' = Σ_j b_j v_j`
  (pV κ ≤ ρ ∧ clRs κ es (8 + κ) ≠
    weightEval (fsOf κ es) (rhiOf κ es) (rrOf κ es) *
      dot (eqTable ((rrOf κ es).take (lk κ))) (vOf κ es))

/-! ### Modes, decoding, the true values -/

/-- The statement is false: `chainEnd s n ≠ h`. -/
def FS (es : Log) : Prop := chainEnd (stmtOf es).1 (stmtOf es).2.1 ≠ (stmtOf es).2.2

/-- **Far mode**: the committed matrix is not `e`-close to the code. -/
def Far (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) : Prop :=
  ¬ eClose (code κ) (UE κ U) (radius κ)

/-- The R0 combination is far too (after the `m` answers). -/
def FarDoom (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (es : Log) : Prop :=
  Far κ U ∧ ¬ Close (code κ) (radius κ) (∑ i : Fin (rows κ), (rVec κ es).getD i 0 • UE κ U i)

theorem qRow_lt (κ : ℕ) (u : Fin (2 ^ (8 + κ))) : u.val / 2 ^ lk κ < rows κ := by
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← msgLen, mul_comm, msgLen, ← msgLen, mul_comm, rows_mul]
  exact u.isLt

/-- The decoded packed witness `q_dec(u') = Q[u' / k][u' mod k]` (§5.2's layout). -/
noncomputable def qPack (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (u : Fin (2 ^ (8 + κ))) : F :=
  qDec κ U ⟨u.val / 2 ^ lk κ, qRow_lt κ u⟩ ⟨u.val % 2 ^ lk κ, Nat.mod_lt _ (by positivity)⟩

theorem pack_eq (κ : ℕ) : 2 ^ (6 + (8 + κ)) = 2 ^ (14 + κ) := by ring_nf

/-- Bit-plane `i` of the decoded witness: `Q_i(u') = w_dec(i + 64 u')` (§4.1). -/
noncomputable def qPlane (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (i : Fin (2 ^ 6))
    (u : Fin (2 ^ (8 + κ))) : EF :=
  EF.ofF (wDec κ U (Fin.cast (pack_eq κ) (join i u)))

/-- The slices' errors `δ_i = s_i + Q̃_i(r_hi)` (characteristic two). -/
noncomputable def deltaOf (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (es : Log) :
    Fin (2 ^ 6) → EF :=
  fun i => (slicesOf κ es).getD i 0 + mle (qPlane κ U i) (ptOf (8 + κ) (rhiOf κ es))

/-- The ring-switching weights `x^i`. -/
def wX (i : Fin (2 ^ 6)) : EF := algebraMap F EF (F.x ^ (i : ℕ))

/-- The decoded extended witness `z_dec = (w_dec ‖ pub(s, h))`. -/
noncomputable def zOfU (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (es : Log) : Ix κ → EF :=
  zDec κ U (stmtOf es).1 (stmtOf es).2.2

/-- The chain matrices of `(κ, n)`. -/
noncomputable def matA (κ : ℕ) (es : Log) : Ix κ → Ix κ → EF := chainA (stmtOf es).2.1 κ
noncomputable def matB (κ : ℕ) : Ix κ → Ix κ → EF := chainB κ
def matC (κ : ℕ) : Ix κ → Ix κ → EF := chainC κ

/-- The residual table `F = Az ∘ Bz + Cz` (zerocheck). -/
noncomputable def fTbl (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (es : Log) : Array EF :=
  Array.ofFn (residual (matA κ es) (matB κ) (matC κ) (zOfU κ U es))

/-- The outer tables `eq(τ, ·), Az, Bz, Cz`. -/
noncomputable def oTbls (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (es : Log) :
    Array (Array EF) :=
  outerTables (tauOf κ es) (matA κ es) (matB κ) (matC κ) (zOfU κ U es)

/-- The inner tables `M̃_ρ(r_x, ·), z`. -/
noncomputable def iTbls (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (es : Log) :
    Array (Array EF) :=
  innerTables (ptOf (14 + κ + 1) (rxOf κ es)) (rhoOf κ es) (matA κ es) (matB κ) (matC κ)
    (zOfU κ U es)

/-- The ring-switching tables `W = Φ(eq(r_hi, ·))`, `q_dec`. -/
noncomputable def wTbls (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (es : Log) :
    Array (Array EF) :=
  #[Array.ofFn (n := 2 ^ (8 + κ)) fun u => Phi (fsOf κ es) (eq (ptOf (8 + κ) (rhiOf κ es)) (cube u)),
    Array.ofFn (n := 2 ^ (8 + κ)) fun u => EF.ofF (qPack κ U u)]

/-- A sumcheck claim is false after `i` rounds: `cl_i ≠` the true sum of the tables bound at the
first `i` challenges, over the remaining `nv − i` variables. -/
def SumWrong (e : Expr) (ts : Array (Array EF)) (cl : ℕ → EF) (chs : List EF) (nv i : ℕ) : Prop :=
  cl i ≠ trueSum e (bindAll ts (chs.take i)) (nv - i)

/-- The difference set of the column phase: far mode against `(r, ū)`, close mode against `(a, v)`. -/
noncomputable def Dof (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (es : Log) :
    Finset (Fin (cols κ)) := by
  classical
  exact if Far κ U then Dset κ U (fun i => (rVec κ es).getD i 0) (fun j => (ubarOf κ es).getD j 0)
    else Dset κ U (fun i => (aOf κ es).getD i 0) (fun j => (vOf κ es).getD j 0)

/-- `v` is not the decoded row combination `Σ_i a_i q_dec[i]`. -/
def VWrong (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (es : Log) : Prop :=
  (fun j : Fin (2 ^ lk κ) => (vOf κ es).getD j 0) ≠
    fun j => ∑ i : Fin (rows κ), (aOf κ es).getD i 0 * EF.ofF (qDec κ U i j)

/-! ### The table of `Alg` (§9.2) -/

/-- The position classes of §9.2's table (one per step of §6.2). -/
inductive PosClass where
  /-- the seed -/
  | seed
  /-- `absorb(root)` -/
  | root
  /-- R0 answer `j` (`1 ≤ j ≤ m` answers given) -/
  | r0 (j : ℕ)
  /-- `absorb(ū)` -/
  | ubar
  /-- `τ_l` -/
  | tau (l : ℕ)
  /-- `absorb(g_l)` -/
  | gOut (l : ℕ)
  /-- `r_{x,l}` -/
  | rx (l : ℕ)
  /-- `absorb(v_A ‖ v_B ‖ v_C)` -/
  | tri
  /-- `ρ` -/
  | rho
  /-- `absorb(g'_l)` -/
  | gIn (l : ℕ)
  /-- `r_{y,l}` -/
  | ry (l : ℕ)
  /-- `absorb(slices)` -/
  | sl
  /-- `f_p` -/
  | f (p : ℕ)
  /-- `absorb(g''_l)` -/
  | gRs (l : ℕ)
  /-- `r''_l` -/
  | rr (l : ℕ)
  /-- `absorb(v)` -/
  | vabs
  /-- R7 answer `j` (`1 ≤ j ≤ J` answers given) -/
  | r7 (j : ℕ)

/-- The position class of position `ρ` of shape `κ`. -/
def posClass (κ ρ : ℕ) : PosClass :=
  if ρ = 0 then .seed
  else if ρ = 1 then .root
  else if ρ ≤ 1 + rows κ then .r0 (ρ - 1)
  else if ρ = pU κ then .ubar
  else if ρ < pG κ 0 then .tau (ρ - pTau κ 0)
  else if ρ < pTri κ then
    (if (ρ - pG κ 0) % 2 = 0 then .gOut ((ρ - pG κ 0) / 2) else .rx ((ρ - pG κ 0) / 2))
  else if ρ = pTri κ then .tri
  else if ρ = pTri κ + 1 then .rho
  else if ρ < pS κ then
    (if (ρ - pGi κ 0) % 2 = 0 then .gIn ((ρ - pGi κ 0) / 2) else .ry ((ρ - pGi κ 0) / 2))
  else if ρ = pS κ then .sl
  else if ρ < pGr κ 0 then .f (ρ - pF κ 0)
  else if ρ < pV κ then
    (if (ρ - pGr κ 0) % 2 = 0 then .gRs ((ρ - pGr κ 0) / 2) else .rr ((ρ - pGr κ 0) / 2))
  else if ρ = pV κ then .vabs
  else .r7 (ρ - pV κ)

/-- The step of §6.2 of each position class. -/
def stepOf (κ : ℕ) : PosClass → Step
  | .seed => .seed
  | .root => .absorb 0x01 31
  | .r0 _ => .squeeze
  | .ubar => .absorb 0x02 (24 * msgLen κ)
  | .tau _ => .squeeze
  | .gOut _ => .absorb 0x03 96
  | .rx _ => .squeeze
  | .tri => .absorb 0x04 72
  | .rho => .squeeze
  | .gIn _ => .absorb 0x05 72
  | .ry _ => .squeeze
  | .sl => .absorb 0x06 1536
  | .f _ => .squeeze
  | .gRs _ => .absorb 0x07 72
  | .rr _ => .squeeze
  | .vabs => .absorb 0x08 (24 * msgLen κ)
  | .r7 _ => .squeeze

/-- The row of §9.2's table for the position class `c`, read off `es` with the matrix `U`. -/
def AlgRow (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (es : Log) (c : PosClass) : Prop :=
  let nv := 14 + κ + 1
  let close (P : Prop) : Prop := FarDoom κ U es ∨ (¬ Far κ U ∧ P)
  match c with
  | .seed => FS es
  | .root => FS es
  | .r0 j => if j < rows κ then FS es else FS es ∧ (FarDoom κ U es ∨ ¬ Far κ U)
  | .ubar => FS es ∧ (FarDoom κ U es ∨ ¬ Far κ U)
  | .tau l => close (tbl (nv - l - 1) (SpartanChain.bindT (fTbl κ U es) ((tauOf κ es).take (l + 1))) ≠ 0)
  | .gOut l => close (SumWrong outerExpr (oTbls κ U es) (clOut κ es) (rxOf κ es) nv l)
  | .rx l => close (SumWrong outerExpr (oTbls κ U es) (clOut κ es) (rxOf κ es) nv (l + 1))
  | .tri => close (triOf κ es ≠
      (mle (matVec (matA κ es) (zOfU κ U es)) (ptOf nv (rxOf κ es)),
        mle (matVec (matB κ) (zOfU κ U es)) (ptOf nv (rxOf κ es)),
        mle (matVec (matC κ) (zOfU κ U es)) (ptOf nv (rxOf κ es))))
  | .rho => close (SumWrong innerExpr (iTbls κ U es) (clIn κ es) (ryOf κ es) nv 0)
  | .gIn l => close (SumWrong innerExpr (iTbls κ U es) (clIn κ es) (ryOf κ es) nv l)
  | .ry l => close (SumWrong innerExpr (iTbls κ U es) (clIn κ es) (ryOf κ es) nv (l + 1))
  | .sl => close (deltaOf κ U es ≠ 0)
  | .f p => close (rsDoom wX (deltaOf κ U es) 5 ((fsOf κ es).take (p + 1)))
  | .gRs l => close (SumWrong innerExpr (wTbls κ U es) (clRs κ es) (rrOf κ es) (8 + κ) l)
  | .rr l => close (SumWrong innerExpr (wTbls κ U es) (clRs κ es) (rrOf κ es) (8 + κ) (l + 1))
  | .vabs => close (VWrong κ U es)
  | .r7 j => if j < nJ κ then close (VWrong κ U es)
      else close (VWrong κ U es) ∧ ¬ Miss (lN κ) tQ (nJ κ) (Dof κ U es) (bOf κ es)

/-- **Algebraic doom** `Alg U es` (§9.2's table), by the position class of `ρ = es.length − 1`. -/
def Alg (κ : ℕ) (U : Fin (rows κ) → Fin (cols κ) → F) (es : Log) : Prop :=
  AlgRow κ U es (posClass κ (es.length - 1))

/-- The committed matrix of a chain with prefix log `L₀`: `U_{L₀}(root)` (§9.1, `filled`). -/
noncomputable def Uof (L₀ es : Log) : Fin (rows (kapOf es)) → Fin (cols (kapOf es)) → F :=
  filled (kapOf es) L₀ (rootOf es)

/-- **Doom** (§9.2): a failed check or algebraic doom, for the matrix of the prefix `L₀`. -/
def Doom (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals) (L₀ es : Log) : Prop :=
  Rej ev es ∨ Alg (kapOf es) (Uof L₀ es) es

/-- **`EscAt`** for `Doom`. -/
def EscAt (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals) (L₀ es : Log) : Prop :=
  EscAtG (Doom ev) L₀ es

/-- **`Esc`** for `Doom`. -/
def Esc (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals) (L : Log) : Prop := EscG (Doom ev) L

/-- **`pRound`** for `Doom`. -/
noncomputable def pRound (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals) (L₀ es : Log) : ℝ≥0 :=
  pRoundG (Doom ev) L₀ es

/-- **The potential `μ`** of §9.3. -/
noncomputable def μ (ev : ℕ → ℕ → Digest → Digest → Spartan.Evals) (L : Log) : ℝ≥0 :=
  muG (Doom ev) (pRound ev) L

end Leaf

end KS

end SpartanChain
