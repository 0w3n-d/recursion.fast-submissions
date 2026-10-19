import SpartanChainOracle

/-!
# The Merkle tree over the oracle (BLUEPRINT-R1 §5.3, §9.1)

Leaves are columns (`8m` bytes each), `N = 2^ℓ` of them. Labels are 31 bytes (`[D-8]`):

* leaf `λ(c) = [H(0x00 ‖ column c)]₃₁`;
* node `λ(v) = [H(0x01 ‖ λ(left) ‖ λ(right))]₃₁`;
* the label at level `l`, index `j` covers columns `j·2^l … (j+1)·2^l − 1` (`lab`); the root is
  `lab ℓ 0`.

A path for column `c` is the `ℓ` sibling labels, bottom-up; at level `l` the bit `l` of `c` says
whether the running label is the right child (`climb`).

* The prover: `build` (all levels, as a query program, for any oracle), `root`, `path`.
* The verifier: `verify root c col path : OProg Bool`.
* The log side (§9.1, per column as review BP-M1 asks): `pre L λ` (the first entry of `L` whose
  answer has label `λ`), the log-read column `colL L w λ l c` (the `w`-byte column `c` under `λ`,
  read top-down off `L`; `none` if a query on the way is missing or of the wrong shape) and the
  filled matrix column `colOr`; the bad events `Collision` and `Hit` (the full `Bad`, with state
  hits and repeated queries, is in `SpartanChainTranscript`).

Proved: **L-M1** `path_complete`, **L-M2** `tree_of_log`, **L-M3** `open_binding` (per column),
and the prefix fact that replaces L-M4: under no hit, a column read off a log under a label
carried in an input of a prefix (e.g. the root of `absorb(root)`) is read off that prefix
(`colL_prefix`); columns read off a log are read off every extension (`colL_append`).
-/

namespace SpartanChain
open RecursionFast

namespace Merkle

/-! ## Parsing queries -/

/-- The column of a leaf query of a `w`-byte column. -/
def parseLeaf (w : ℕ) (q : ByteArray) : Option ByteArray :=
  match q.data.toList with
  | b :: col => if b = 0x00 ∧ col.length = w then some ⟨col.toArray⟩ else none
  | [] => none

/-- The two child labels of a node query. -/
def parseNode (q : ByteArray) : Option (Label × Label) :=
  match q.data.toList with
  | b :: rest =>
    if h : b = 0x01 ∧ rest.length = 62 then
      some (⟨(rest.take 31).toArray, by simp [h.2]⟩, ⟨(rest.drop 31).toArray, by simp [h.2]⟩)
    else none
  | [] => none

/-- The root of an `absorb(root)` query `0x20 ‖ st ‖ 0x01 ‖ root` (65 bytes). -/
def parseAbsorbRoot (q : ByteArray) : Option Label :=
  match q.data.toList with
  | b :: rest =>
    if h : b = 0x20 ∧ rest.length = 64 ∧ rest[32]? = some 0x01 then
      some ⟨(rest.drop 33).toArray, by simp [h.2.1]⟩
    else none
  | [] => none

theorem parseLeaf_leafQ {w : ℕ} {col : ByteArray} (h : col.size = w) :
    parseLeaf w (leafQ col) = some col := by
  simp only [parseLeaf, leafQ_data]
  subst h
  have hl : col.data.toList.length = col.size := by rw [Array.length_toList]; rfl
  simp only [hl, and_self, ite_true]

theorem parseLeaf_eq_some {w : ℕ} {q col : ByteArray} (h : parseLeaf w q = some col) :
    q = leafQ col ∧ col.size = w := by
  unfold parseLeaf at h
  split at h
  · rename_i b rest hq
    split_ifs at h with hb
    cases h
    refine ⟨ByteArray.ext_toList ?_, ?_⟩
    · simp [hq, hb.1]
    · simp [ByteArray.size, hb.2]
  · cases h

theorem leafQ_inj {a b : ByteArray} (h : leafQ a = leafQ b) : a = b :=
  ByteArray.ext_toList (by simpa using congrArg (fun q => q.data.toList) h)

theorem parseNode_nodeQ (l r : Label) : parseNode (nodeQ l r) = some (l, r) := by
  simp [parseNode, nodeQ_data, Vector.toList]

theorem parseNode_eq_some {q : ByteArray} {l r : Label} (h : parseNode q = some (l, r)) :
    q = nodeQ l r := by
  unfold parseNode at h
  split at h
  · rename_i b rest hq
    split_ifs at h with hb
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    apply ByteArray.ext_toList
    simp [hq, hb.1, Vector.toList]
  · cases h

theorem nodeQ_inj {a b c d : Label} (h : nodeQ a b = nodeQ c d) : a = c ∧ b = d := by
  have := congrArg parseNode h
  simpa [parseNode_nodeQ] using this

theorem parseAbsorbRoot_absorbQ (st : Digest) (root : Label) :
    parseAbsorbRoot (absorbQ st 0x01 (bytesOf root)) = some root := by
  simp [parseAbsorbRoot, absorbQ_data, bytesOf, List.drop_append, Vector.toList,
    List.drop_eq_nil_of_le (as := st.toArray.toList) (i := 33) (by simp)]

/-- The labels a query carries in its input: the children of a node query, the root of an
`absorb(root)` query (§9.1, the hit event). -/
def labelsIn (q : ByteArray) : List Label :=
  (match parseNode q with
    | some (a, b) => [a, b]
    | none => []) ++ (parseAbsorbRoot q).toList

theorem mem_labelsIn_nodeQ (l r : Label) : l ∈ labelsIn (nodeQ l r) ∧ r ∈ labelsIn (nodeQ l r) := by
  simp [labelsIn, parseNode_nodeQ]

/-! ## The prover's tree -/

/-- Ask `q`, keep the label of the answer. -/
def hashL (q : ByteArray) : OProg Label := trunc <$> OProg.ask q

/-- The label at level `l`, index `j`, of the tree of the columns `cols` under the oracle `H`
(the specification of `build`). -/
def lab (H : ByteArray → Digest) (cols : ℕ → ByteArray) : ℕ → ℕ → Label
  | 0, j => trunc (H (leafQ (cols j)))
  | l + 1, j => trunc (H (nodeQ (lab H cols l (2 * j)) (lab H cols l (2 * j + 1))))

/-- One level up: pair the labels `2j, 2j + 1`. -/
def nextLevel (prev : Array Label) : OProg (Array Label) :=
  (Array.range (prev.size / 2)).mapM fun j => hashL (nodeQ prev[2 * j]! prev[2 * j + 1]!)

/-- The levels from `cur` up, `r` more levels. -/
def buildUp : ℕ → Array Label → OProg (List (Array Label))
  | 0, cur => pure [cur]
  | r + 1, cur => do
    let nxt ← nextLevel cur
    let rest ← buildUp r nxt
    pure (cur :: rest)

/-- **The prover's tree**: all `ℓ + 1` levels of the tree of `2^ℓ` columns, leaves first. -/
def build (cols : Array ByteArray) (ℓ : ℕ) : OProg (Array (Array Label)) := do
  let leaves ← cols.mapM fun c => hashL (leafQ c)
  let lv ← buildUp ℓ leaves
  pure lv.toArray

/-- The root of a built tree of height `ℓ`. -/
def root (lv : Array (Array Label)) (ℓ : ℕ) : Label := lv[ℓ]![0]!

/-- The sibling of index `j`. -/
def sib (j : ℕ) : ℕ := if j % 2 = 0 then j + 1 else j - 1

/-- The path of column `c` in a built tree of height `ℓ`: the siblings, bottom-up. -/
def path (lv : Array (Array Label)) (ℓ c : ℕ) : List Label :=
  (List.range ℓ).map fun l => lv[l]![sib (c / 2 ^ l)]!

/-! ## The verifier -/

/-- Climb from the label `cur` of index `c` along the siblings `ss`, bottom-up. -/
def climb : Label → ℕ → List Label → OProg Label
  | cur, _, [] => pure cur
  | cur, c, s :: ss => do
    let nxt ← hashL (if c % 2 = 0 then nodeQ cur s else nodeQ s cur)
    climb nxt (c / 2) ss

/-- **The path check**: the column `col` opened at index `c` with the path `ss` against `root`. -/
def verify (root : Label) (c : ℕ) (col : ByteArray) (ss : List Label) : OProg Bool := do
  let lf ← hashL (leafQ col)
  let top ← climb lf c ss
  pure (decide (top = root))

theorem climb_append (cur : Label) (c : ℕ) (ss ts : List Label) :
    climb cur c (ss ++ ts) = climb cur c ss >>= fun x => climb x (c / 2 ^ ss.length) ts := by
  induction ss generalizing cur c with
  | nil => simp [climb]
  | cons s ss ih =>
    simp only [List.cons_append, climb, ih, bind_assoc, List.length_cons]
    congr; funext x; congr 2
    rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]

/-! ## L-M1: completeness of paths -/

section complete
variable (H : ByteArray → Digest) (cols : ℕ → ByteArray)

theorem run_hashL (q : ByteArray) : (hashL q).run H = trunc (H q) := by simp [hashL]

theorem run_nextLevel (r l : ℕ) :
    (nextLevel ((Array.range (2 ^ (r + 1))).map (lab H cols l))).run H =
      (Array.range (2 ^ r)).map (lab H cols (l + 1)) := by
  simp only [nextLevel, OProg.run_arrayMapM, run_hashL]
  apply Array.ext
  · simp [pow_succ]
  · intro j h1 h2
    simp only [Array.size_map, Array.size_range, pow_succ] at h1 h2
    simp only [Array.getElem_map, Array.getElem_range]
    rw [getElem!_pos _ _ (by simp [pow_succ]; omega),
      getElem!_pos _ _ (by simp [pow_succ]; omega)]
    simp [lab]

theorem run_buildUp (r l : ℕ) :
    (buildUp r ((Array.range (2 ^ r)).map (lab H cols l))).run H =
      (List.range (r + 1)).map fun i => (Array.range (2 ^ (r - i))).map (lab H cols (l + i)) := by
  induction r generalizing l with
  | zero => simp [buildUp]
  | succ r ih =>
    have hn := run_nextLevel H cols r l
    simp only [buildUp, OProg.run_bind, hn, ih, OProg.run_pure]
    rw [List.range_succ_eq_map (n := r + 1), List.map_cons, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    simp only [Function.comp, Nat.succ_eq_add_one]
    rw [show l + 1 + i = l + (i + 1) by omega, show r - i = r + 1 - (i + 1) by omega]

/-- The levels of `build`, as a specification. -/
theorem run_build {cols : Array ByteArray} {ℓ : ℕ} (hs : cols.size = 2 ^ ℓ) :
    (build cols ℓ).run H = ((List.range (ℓ + 1)).map fun i =>
      (Array.range (2 ^ (ℓ - i))).map (lab H (fun j => cols[j]!) i)).toArray := by
  have hl : (cols.map fun c => (hashL (leafQ c)).run H) =
      (Array.range (2 ^ ℓ)).map (lab H (fun j => cols[j]!) 0) := by
    apply Array.ext
    · simp [hs]
    · intro j h1 h2
      simp only [Array.getElem_map, Array.getElem_range, run_hashL, lab]
      rw [getElem!_pos _ _ (by simpa using h1)]
  simp only [build, OProg.run_bind, OProg.run_arrayMapM, hl, run_buildUp, OProg.run_pure]
  simp

/-- An entry of the specified levels. -/
theorem spec_get (A : ℕ → ℕ → Label) {ℓ i j : ℕ} (hi : i ≤ ℓ) (hj : j < 2 ^ (ℓ - i)) :
    (((List.range (ℓ + 1)).map fun i => (Array.range (2 ^ (ℓ - i))).map (A i)).toArray[i]!)[j]!
      = A i j := by
  simp [Nat.lt_succ_of_le hi, hj]

theorem lt_of_sib {j k : ℕ} (hk : 0 < k) (hj : j < 2 ^ k) : sib j < 2 ^ k := by
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ k = 2 * M := ⟨2 ^ (k - 1), by rw [← pow_succ']; congr; omega⟩
  unfold sib; split_ifs <;> omega

theorem climb_spec (r l j : ℕ) :
    (climb (lab H cols l j) j
      ((List.range r).map fun i => lab H cols (l + i) (sib (j / 2 ^ i)))).run H =
      lab H cols (l + r) (j / 2 ^ r) := by
  induction r generalizing l j with
  | zero => simp [climb]
  | succ r ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have hs : ((fun i => lab H cols (l + i) (sib (j / 2 ^ i))) ∘ Nat.succ) =
        fun i => lab H cols (l + 1 + i) (sib (j / 2 / 2 ^ i)) := by
      funext i
      simp only [Function.comp, Nat.div_div_eq_div_mul, ← pow_succ']
      congr 1; omega
    rw [hs]
    simp only [climb, OProg.run_bind, run_hashL, Nat.add_zero, pow_zero, Nat.div_one]
    have hlab : trunc (H (if j % 2 = 0 then nodeQ (lab H cols l j) (lab H cols l (sib j))
        else nodeQ (lab H cols l (sib j)) (lab H cols l j))) = lab H cols (l + 1) (j / 2) := by
      simp only [lab, sib]
      split_ifs with h
      · congr 4 <;> omega
      · congr 4 <;> omega
    rw [hlab, ih]
    rw [Nat.div_div_eq_div_mul, ← pow_succ']
    congr 1; omega

/-- **L-M1 `path_complete`**: for every oracle, the prover's path of every column verifies
against the root of the prover's tree. -/
theorem path_complete {cols : Array ByteArray} {ℓ c : ℕ} (hs : cols.size = 2 ^ ℓ)
    (hc : c < 2 ^ ℓ) :
    (verify (root ((build cols ℓ).run H) ℓ) c cols[c] (path ((build cols ℓ).run H) ℓ c)).run H
      = true := by
  rw [run_build H hs]
  set f : ℕ → ByteArray := fun j => cols[j]!
  have hpath : path (((List.range (ℓ + 1)).map fun i =>
      (Array.range (2 ^ (ℓ - i))).map (lab H f i)).toArray) ℓ c =
      (List.range ℓ).map fun i => lab H f (0 + i) (sib (c / 2 ^ i)) := by
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    have hb : c / 2 ^ i < 2 ^ (ℓ - i) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]; rwa [Nat.sub_add_cancel hi.le]
    rw [spec_get _ (by omega) (lt_of_sib (by omega) hb), Nat.zero_add]
  have hroot : root (((List.range (ℓ + 1)).map fun i =>
      (Array.range (2 ^ (ℓ - i))).map (lab H f i)).toArray) ℓ = lab H f (0 + ℓ) (c / 2 ^ ℓ) := by
    rw [Nat.div_eq_of_lt hc, root, spec_get _ le_rfl (by simp), Nat.zero_add]
  have hleaf : (hashL (leafQ cols[c])).run H = lab H f 0 c := by
    simp [run_hashL, lab, f, getElem!_pos cols c (by omega)]
  rw [hpath, hroot]
  simp only [verify, OProg.run_bind, hleaf, climb_spec, OProg.run_pure, decide_true]

end complete

/-! ## The log side (§9.1, revised by BP-M1) -/

/-- `pre_L(λ)`: the first entry of `L` whose answer has label `λ`. -/
def pre (L : Log) (lb : Label) : Option (ByteArray × Digest) :=
  L.find? fun e => decide (trunc e.2 = lb)

/-- **The column under a label, read off the log** (per column, BP-M1): the `w`-byte column `c`
of the tree of height `l` under `lb`, read top-down from `pre L lb` (at height `i + 1` the bit `i`
of `c` chooses the child) down to a leaf query; `none` if a query on the way is missing or of the
wrong shape. Only the bits below `l` of `c` are read. -/
def colL (L : Log) (w : ℕ) : Label → ℕ → ℕ → Option ByteArray
  | lb, 0, _ => (pre L lb).bind fun e => parseLeaf w e.1
  | lb, l + 1, c => (pre L lb).bind fun e => (parseNode e.1).bind fun ab =>
      colL L w (if c / 2 ^ l % 2 = 0 then ab.1 else ab.2) l c

/-- `U_L(root)`'s column `c`: the column read off the log, or `fill` if it is missing (BP-M1). -/
def colOr (L : Log) (w : ℕ) (root : Label) (ℓ : ℕ) (fill : ByteArray) (c : ℕ) : ByteArray :=
  (colL L w root ℓ c).getD fill

/-- *Collision*: two entries with different queries and the same label. -/
def Collision (L : Log) : Prop :=
  ∃ e₁ ∈ L, ∃ e₂ ∈ L, e₁.1 ≠ e₂.1 ∧ trunc e₁.2 = trunc e₂.2

/-- *Label hit*: an entry whose label occurs in the input of an earlier entry (a child of a node
query or the root of an `absorb(root)` query). -/
def Hit (L : Log) : Prop :=
  ∃ i j : ℕ, ∃ (hij : i < j) (hj : j < L.length),
    trunc L[j].2 ∈ labelsIn (L[i]'(hij.trans hj)).1

/-- Under no collision, the first entry with the label of an entry of the log has its query. -/
theorem pre_of_mem {L : Log} (hc : ¬ Collision L) {e : ByteArray × Digest} (he : e ∈ L) :
    ∃ e', pre L (trunc e.2) = some e' ∧ e' ∈ L ∧ e'.1 = e.1 := by
  obtain ⟨e', he'⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr ⟨e, he, by simp⟩ : (pre L (trunc e.2)).isSome)
  have hm := List.mem_of_find?_eq_some he'
  have ht : trunc e'.2 = trunc e.2 := by simpa using List.find?_some he'
  refine ⟨e', he', hm, ?_⟩
  by_contra hne
  exact hc ⟨e', hm, e, he, hne, ht⟩

theorem pre_eq_of_trunc {L : Log} (hc : ¬ Collision L) {e : ByteArray × Digest} (he : e ∈ L)
    {lb : Label} (hlb : trunc e.2 = lb) {e' : ByteArray × Digest} (h : pre L lb = some e') :
    e'.1 = e.1 := by
  subst hlb
  obtain ⟨e'', h1, -, h2⟩ := pre_of_mem hc he
  rw [h] at h1; cases h1; exact h2

/-! ## L-M2: the honest tree is read off a log that contains its queries -/

section ofLog
variable (H : ByteArray → Digest)

theorem mem_queries_buildUp (cols : ℕ → ByteArray) (r l : ℕ) (i j : ℕ) (hi : i < r) (hj : j < 2 ^ (r - i - 1)) :
    nodeQ (lab H cols (l + i) (2 * j)) (lab H cols (l + i) (2 * j + 1)) ∈
      (buildUp r ((Array.range (2 ^ r)).map (lab H cols l))).queries H := by
  induction r generalizing l i with
  | zero => omega
  | succ r ih =>
    have hn := run_nextLevel H cols r l
    simp only [buildUp, OProg.queries_bind, hn, OProg.queries_pure,
      List.append_nil, List.mem_append]
    rcases i with _ | i
    · have hj' : j < 2 ^ r := by simpa using hj
      left
      simp only [nextLevel, OProg.queries_arrayMapM, hashL, OProg.queries_map,
        OProg.queries_ask, List.mem_flatMap, List.mem_singleton]
      refine ⟨j, by simp [pow_succ]; omega, ?_⟩
      rw [getElem!_pos _ _ (by simp [pow_succ]; omega),
        getElem!_pos _ _ (by simp [pow_succ]; omega)]
      simp
    · right
      have := ih (l + 1) i (by omega) (by simpa [Nat.sub_sub, Nat.add_comm] using hj)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

/-- The columns under `lab l j` read off a log holding the honest queries. -/
theorem colL_lab {L : Log} {cols : Array ByteArray} {ℓ w : ℕ} (hs : cols.size = 2 ^ ℓ)
    (hw : ∀ c ∈ cols, c.size = w) (hcons : ∀ e ∈ L, e.2 = H e.1)
    (hq : ∀ q ∈ (build cols ℓ).queries H, q ∈ L.map Prod.fst) (hcol : ¬ Collision L) :
    ∀ l j c, l ≤ ℓ → j < 2 ^ (ℓ - l) →
      colL L w (lab H (fun j => cols[j]!) l j) l c = some cols[j * 2 ^ l + c % 2 ^ l]! := by
  set f : ℕ → ByteArray := fun j => cols[j]!
  have hmem : ∀ q ∈ (build cols ℓ).queries H, (q, H q) ∈ L := by
    intro q h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (hq q h)
    rwa [← hcons e he]
  have hleaves : (cols.map fun c => (hashL (leafQ c)).run H) =
      (Array.range (2 ^ ℓ)).map (lab H f 0) := by
    apply Array.ext
    · simp [hs]
    · intro j h1 h2
      simp only [Array.getElem_map, Array.getElem_range, run_hashL, lab, f]
      rw [getElem!_pos _ _ (by simpa using h1)]
  have hbq : (build cols ℓ).queries H = (cols.toList.flatMap fun c => [leafQ c]) ++
      (buildUp ℓ ((Array.range (2 ^ ℓ)).map (lab H f 0))).queries H := by
    rw [build, OProg.queries_bind, OProg.run_arrayMapM, hleaves, OProg.queries_bind]
    simp [hashL]
  intro l
  induction l with
  | zero =>
    intro j c _ hj
    have hjc : j < cols.size := by simpa [hs] using hj
    have hin : (leafQ (f j), H (leafQ (f j))) ∈ L := by
      apply hmem; rw [hbq]; apply List.mem_append_left
      simp only [List.mem_flatMap, List.mem_singleton]
      exact ⟨cols[j], by simp, by simp [f, getElem!_pos cols j hjc]⟩
    simp only [colL, pow_zero, Nat.mod_one, mul_one, add_zero]
    cases hp : pre L (lab H f 0 j) with
    | none =>
      obtain ⟨e', h1, -⟩ := pre_of_mem hcol hin
      simp [lab] at h1 hp; rw [hp] at h1; cases h1
    | some e' =>
      have h1 := pre_eq_of_trunc hcol hin rfl hp
      simp only [Option.bind_some, h1]
      exact parseLeaf_leafQ (hw _ (by simp [f, getElem!_pos cols j hjc]))
  | succ l ih =>
    intro j c hl hj
    have hq' : nodeQ (lab H f l (2 * j)) (lab H f l (2 * j + 1)) ∈
        (build cols ℓ).queries H := by
      rw [hbq]; apply List.mem_append_right
      have := mem_queries_buildUp H f ℓ 0 l j (by omega) (by
        have : ℓ - l - 1 = ℓ - (l + 1) := by omega
        rwa [this])
      simpa using this
    have hin := hmem _ hq'
    have hlt : ∀ j', j' < 2 * j + 2 → j' < 2 ^ (ℓ - l) := by
      intro j' h'
      have : 2 ^ (ℓ - l) = 2 * 2 ^ (ℓ - (l + 1)) := by rw [← pow_succ']; congr 1; omega
      omega
    simp only [colL]
    cases hp : pre L (lab H f (l + 1) j) with
    | none =>
      obtain ⟨e', h1, -⟩ := pre_of_mem hcol hin
      simp [lab] at h1 hp; rw [hp] at h1; cases h1
    | some e' =>
      have h1 := pre_eq_of_trunc hcol hin rfl hp
      simp only [Option.bind_some, h1, parseNode_nodeQ]
      rw [Nat.mod_pow_succ]
      have hm := Nat.mod_lt c (show 0 < 2 ^ l by positivity)
      split_ifs with hb
      · rw [ih (2 * j) c (by omega) (hlt _ (by omega)), hb]
        congr 2; rw [pow_succ]; ring
      · have hb1 : c / 2 ^ l % 2 = 1 := by omega
        rw [ih (2 * j + 1) c (by omega) (hlt _ (by omega)), hb1]
        congr 2; rw [pow_succ]; ring

/-- **L-M2 `tree_of_log`**: on a log that is consistent with `H`, holds every query the honest
build asks under `H` and has no collision, every column read under the honest root is the
prover's column. (The no-collision hypothesis is needed: an earlier entry with the root's label
and another query would be `pre_L(root)`.) -/
theorem tree_of_log {L : Log} {cols : Array ByteArray} {ℓ w : ℕ} (hs : cols.size = 2 ^ ℓ)
    (hw : ∀ c ∈ cols, c.size = w) (hcons : ∀ e ∈ L, e.2 = H e.1)
    (hq : ∀ q ∈ (build cols ℓ).queries H, q ∈ L.map Prod.fst) (hcol : ¬ Collision L)
    {c : ℕ} (hc : c < 2 ^ ℓ) :
    colL L w (root ((build cols ℓ).run H) ℓ) ℓ c = some cols[c]! := by
  have hr : root ((build cols ℓ).run H) ℓ = lab H (fun j => cols[j]!) ℓ 0 := by
    rw [run_build H hs]
    simp [root]
  rw [hr, colL_lab H hs hw hcons hq hcol ℓ 0 c le_rfl (by simp), Nat.mod_eq_of_lt hc]
  simp

end ofLog

/-! ## L-M3: binding -/

theorem open_binding_aux {L : Log} (hcol : ¬ Collision L) {w : ℕ} {col : ByteArray}
    (hw : col.size = w) (hleaf : leafQ col ∈ L.map Prod.fst) :
    ∀ (ss : List Label) (lb : Label) (c : ℕ),
      (∀ q ∈ (climb (trunc (OProg.logOracle L (leafQ col))) c ss).queries
        (OProg.logOracle L), q ∈ L.map Prod.fst) →
      (climb (trunc (OProg.logOracle L (leafQ col))) c ss).run (OProg.logOracle L) = lb →
      colL L w lb ss.length c = some col := by
  set O := OProg.logOracle L
  intro ss
  induction ss using List.reverseRecOn with
  | nil =>
    intro lb c _ hrun
    simp only [climb, OProg.run_pure] at hrun
    simp only [List.length_nil, colL]
    obtain ⟨e, hp, -, he⟩ := pre_of_mem hcol (OProg.mem_logOracle hleaf)
    simp only at hp he
    rw [hrun] at hp
    rw [hp, Option.bind_some, he]
    exact parseLeaf_leafQ hw
  | append_singleton ss s ih =>
    intro lb c hq hrun
    set x := (climb (trunc (O (leafQ col))) c ss).run O
    set b := c / 2 ^ ss.length % 2
    set qn := if b = 0 then nodeQ x s else nodeQ s x
    have hcl : climb (trunc (O (leafQ col))) c (ss ++ [s]) =
        climb (trunc (O (leafQ col))) c ss >>= fun y =>
          hashL (if c / 2 ^ ss.length % 2 = 0 then nodeQ y s else nodeQ s y) >>= fun z =>
            pure z := by
      rw [climb_append]; rfl
    rw [hcl] at hq hrun
    simp only [OProg.run_bind, run_hashL, OProg.run_pure] at hrun
    simp only [OProg.queries_bind, hashL, OProg.queries_map, OProg.queries_ask,
      OProg.queries_pure, List.append_nil, List.mem_append, List.mem_singleton] at hq
    have hqn : qn ∈ L.map Prod.fst := hq qn (Or.inr rfl)
    have hsub : ∀ q ∈ (climb (trunc (O (leafQ col))) c ss).queries O, q ∈ L.map Prod.fst :=
      fun q h => hq q (Or.inl h)
    obtain ⟨e, hp, -, he⟩ := pre_of_mem hcol (OProg.mem_logOracle hqn)
    simp only at hp he
    have hpq : parseNode qn = some (if b = 0 then x else s, if b = 0 then s else x) := by
      simp only [qn]; split_ifs <;> exact parseNode_nodeQ _ _
    change trunc (O qn) = lb at hrun
    rw [hrun] at hp
    simp only [List.length_append, List.length_singleton, colL, hp, Option.bind_some, he, hpq]
    change colL L w (if b = 0 then (if b = 0 then x else s) else (if b = 0 then s else x))
      ss.length c = some col
    have hx : (if b = 0 then (if b = 0 then x else s) else (if b = 0 then s else x)) = x := by
      split_ifs <;> rfl
    rw [hx]
    exact ih x c hsub rfl

/-- **L-M3 `open_binding`** (per column, BP-M1): on a log without collisions, a `w`-byte column
whose path of length `ℓ` verifies against `root`, reading the answers from the log, is the column
`c` read off the log under `root`. -/
theorem open_binding {L : Log} (hcol : ¬ Collision L) {w ℓ c : ℕ} {root : Label}
    {col : ByteArray} {ss : List Label} (hw : col.size = w) (hlen : ss.length = ℓ)
    (hv : (verify root c col ss).runLog L = some true) : colL L w root ℓ c = some col := by
  obtain ⟨hq, hrun⟩ := (OProg.runLog_eq_some_iff _ _).mp hv
  simp only [verify, OProg.queries_bind, hashL, OProg.queries_map, OProg.queries_ask,
    OProg.run_bind, OProg.run_map, OProg.run_ask, List.singleton_append, List.mem_cons,
    OProg.queries_pure, List.append_nil, forall_eq_or_imp, OProg.run_pure,
    decide_eq_true_eq] at hq hrun
  subst hlen
  exact open_binding_aux hcol hw hq.1 ss root c hq.2 hrun

/-! ## Reading on a prefix (§9.1: the tree is read on the log before `absorb(root)`) -/

theorem pre_append {L : Log} {lb : Label} {e : ByteArray × Digest} (L' : Log)
    (h : pre L lb = some e) : pre (L ++ L') lb = some e := by
  simp only [pre, List.find?_append] at h ⊢; rw [h]; rfl

/-- A column read off a log is read off every extension of it. -/
theorem colL_append {L : Log} {w : ℕ} (L' : Log) :
    ∀ {lb : Label} {l c : ℕ} {col : ByteArray},
      colL L w lb l c = some col → colL (L ++ L') w lb l c = some col := by
  intro lb l
  induction l generalizing lb with
  | zero =>
    intro c col h
    simp only [colL, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨e, he, h⟩ := h
    exact ⟨e, pre_append L' he, h⟩
  | succ l ih =>
    intro c col h
    simp only [colL, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨e, he, ab, hab, h⟩ := h
    exact ⟨e, pre_append L' he, ab, hab, ih h⟩

/-- A label carried in an input of `L` with no entry of `L` has none in an extension without a
hit. -/
theorem pre_none_append {L L' : Log} (hb : ¬ Hit (L ++ L')) {lb : Label}
    (hin : ∃ e ∈ L, lb ∈ labelsIn e.1) (h : pre L lb = none) : pre (L ++ L') lb = none := by
  simp only [pre, List.find?_append] at h ⊢
  rw [h, Option.none_or, List.find?_eq_none]
  intro e he hlb
  obtain ⟨e₀, he₀, hl⟩ := hin
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he₀
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
  apply hb
  refine ⟨i, L.length + j, by omega, by rw [List.length_append]; omega, ?_⟩
  rw [List.getElem_append_right (Nat.le_add_right _ _), List.getElem_append_left hi]
  simp only [Nat.add_sub_cancel_left]
  rw [of_decide_eq_true hlb]
  exact hl

/-- **The column is on the prefix**: under no hit, a column read off `L ++ L'` under a label
carried in an input of `L` is already read off `L`. -/
theorem colL_prefix {L L' : Log} (hb : ¬ Hit (L ++ L')) {w : ℕ} :
    ∀ {l : ℕ} {lb : Label} {c : ℕ} {col : ByteArray}, (∃ e ∈ L, lb ∈ labelsIn e.1) →
      colL (L ++ L') w lb l c = some col → colL L w lb l c = some col := by
  intro l
  induction l with
  | zero =>
    intro lb c col hin h
    simp only [colL] at h ⊢
    cases hp : pre L lb with
    | none => rw [pre_none_append hb hin hp] at h; cases h
    | some e => rw [pre_append L' hp] at h; exact h
  | succ l ih =>
    intro lb c col hin h
    simp only [colL] at h ⊢
    cases hp : pre L lb with
    | none => rw [pre_none_append hb hin hp] at h; cases h
    | some e =>
      rw [pre_append L' hp, Option.bind_some] at h
      rw [Option.bind_some]
      have heL : e ∈ L := List.mem_of_find?_eq_some hp
      cases hn : parseNode e.1 with
      | none => rw [hn] at h; cases h
      | some ab =>
        rw [hn, Option.bind_some] at h
        rw [Option.bind_some]
        have hl : ab.1 ∈ labelsIn e.1 ∧ ab.2 ∈ labelsIn e.1 := by
          rw [parseNode_eq_some (q := e.1) (l := ab.1) (r := ab.2) (by rw [hn])]
          exact mem_labelsIn_nodeQ _ _
        refine ih ⟨e, heL, ?_⟩ h
        split_ifs
        · exact hl.1
        · exact hl.2

/-- A query whose first byte is `0x20` (an absorb) is neither a node nor a leaf query. -/
theorem parse_of_tag20 {q : ByteArray} (h : q.data.toList.head? = some 0x20) :
    parseNode q = none ∧ ∀ w, parseLeaf w q = none := by
  unfold parseNode parseLeaf
  split
  · rename_i b rest hq
    rw [hq] at h
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    exact ⟨by simp, fun w => by simp⟩
  · exact ⟨rfl, fun _ => rfl⟩

theorem head_of_parseAbsorbRoot {q : ByteArray} {root : Label}
    (h : parseAbsorbRoot q = some root) : q.data.toList.head? = some 0x20 := by
  unfold parseAbsorbRoot at h
  split at h
  · rename_i b rest hq
    split_ifs at h with hb
    simp [hq, hb.1]
  · cases h

/-- Appending one entry that is neither a node nor a leaf query adds no column. -/
theorem colL_of_append_one {L : Log} {e : ByteArray × Digest} (hn : parseNode e.1 = none)
    (hl : ∀ w, parseLeaf w e.1 = none) {w : ℕ} :
    ∀ {l : ℕ} {lb : Label} {c : ℕ} {col : ByteArray},
      colL (L ++ [e]) w lb l c = some col → colL L w lb l c = some col := by
  intro l
  induction l with
  | zero =>
    intro lb c col h
    simp only [colL, pre, List.find?_append] at h ⊢
    cases hp : L.find? (fun x => decide (trunc x.2 = lb)) with
    | none =>
      rw [hp, Option.none_or] at h
      cases h1 : [e].find? (fun x => decide (trunc x.2 = lb)) with
      | none => rw [h1] at h; cases h
      | some e' =>
        have : e' = e := by simpa using List.mem_of_find?_eq_some h1
        subst this; rw [h1, Option.bind_some, hl] at h; cases h
    | some e' => rw [hp, Option.some_or] at h; exact h
  | succ l ih =>
    intro lb c col h
    simp only [colL, pre, List.find?_append] at h ⊢
    cases hp : L.find? (fun x => decide (trunc x.2 = lb)) with
    | none =>
      rw [hp, Option.none_or] at h
      cases h1 : [e].find? (fun x => decide (trunc x.2 = lb)) with
      | none => rw [h1] at h; cases h
      | some e' =>
        have : e' = e := by simpa using List.mem_of_find?_eq_some h1
        subst this; rw [h1, Option.bind_some, hn] at h; cases h
    | some e' =>
      rw [hp, Option.some_or, Option.bind_some] at h
      rw [Option.bind_some]
      cases hn' : parseNode e'.1 with
      | none => rw [hn'] at h; cases h
      | some ab =>
        rw [hn', Option.bind_some] at h
        rw [Option.bind_some]
        exact ih h

/-- **L-M4 `tree_prefix`** (restated, §9.1): split the log at the entry `e` that absorbs `root`
(`L₀` is the prefix strictly before it). Under no label hit, every column under `root` read off
the whole log is read off `L₀`, and conversely (`colL_append`): the committed matrix is fixed when
the root is absorbed. (The cut must be at the absorb entry: an entry of the tree between `L₀` and
the absorb would be read off the whole log and not off `L₀`.) -/
theorem tree_prefix {L₀ L₁ : Log} {e : ByteArray × Digest} {root : Label}
    (hb : ¬ Hit (L₀ ++ e :: L₁)) (he : parseAbsorbRoot e.1 = some root) {w ℓ c : ℕ} :
    colL (L₀ ++ e :: L₁) w root ℓ c = colL L₀ w root ℓ c := by
  have hsplit : L₀ ++ e :: L₁ = (L₀ ++ [e]) ++ L₁ := by simp
  cases h : colL L₀ w root ℓ c with
  | some col =>
    rw [hsplit]
    exact colL_append L₁ (colL_append [e] h)
  | none =>
    cases h' : colL (L₀ ++ e :: L₁) w root ℓ c with
    | none => rfl
    | some col =>
      exfalso
      rw [hsplit] at h' hb
      have hin : ∃ e' ∈ L₀ ++ [e], root ∈ labelsIn e'.1 :=
        ⟨e, by simp, by simp [labelsIn, he]⟩
      have h1 := colL_prefix hb hin h'
      obtain ⟨hn, hl⟩ := parse_of_tag20 (head_of_parseAbsorbRoot he)
      rw [colL_of_append_one hn hl h1] at h
      cases h

/-- **L-M3 `open_binding`, restated** (§9.1, review BP-M1): on a log without collision and label
hit, split at the entry `e` that absorbs `root`; a `w`-byte column whose path of length `ℓ`
verifies against `root` on the whole log is column `c` of the tree read off the prefix `L₀`.
So a column missing from `tree_{L₀}(root)` has no verifying path. -/
theorem open_binding_prefix {L₀ L₁ : Log} {e : ByteArray × Digest} {root : Label}
    (hc : ¬ Collision (L₀ ++ e :: L₁)) (hb : ¬ Hit (L₀ ++ e :: L₁))
    (he : parseAbsorbRoot e.1 = some root) {w ℓ c : ℕ} {col : ByteArray} {ss : List Label}
    (hw : col.size = w) (hlen : ss.length = ℓ)
    (hv : (verify root c col ss).runLog (L₀ ++ e :: L₁) = some true) :
    colL L₀ w root ℓ c = some col := by
  rw [← tree_prefix hb he]
  exact open_binding hc hw hlen hv

/-- Collisions are kept by appending. -/
theorem collision_append {L : Log} (L' : Log) (h : Collision L) : Collision (L ++ L') := by
  obtain ⟨e₁, h₁, e₂, h₂, hne, ht⟩ := h
  exact ⟨e₁, by simp [h₁], e₂, by simp [h₂], hne, ht⟩

/-- Label hits are kept by appending. -/
theorem hit_append {L : Log} (L' : Log) (h : Hit L) : Hit (L ++ L') := by
  obtain ⟨i, j, hij, hj, hm⟩ := h
  refine ⟨i, j, hij, by simp; omega, ?_⟩
  rwa [List.getElem_append_left hj, List.getElem_append_left (hij.trans hj)]

end Merkle

end SpartanChain
