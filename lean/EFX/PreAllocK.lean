import EFX.PreAlloc
import EFX.K4Ties

/-!
# Pre-allocations with bases and needs of any size (`k4/lb4.md` §1; ledger K4.LB4.S)

The k = 4 construction LB₄ builds *pre-allocations* in which an agent's base can have any number of
goods and its needs are any set between the goods worth more than the base and all goods outside it.
This file proves `k4/lb4.md` §1 (Theorem 1′₄, the counting, Lemma 2₄) and §2 (Lemma 3₄, and the Shape
paragraph's deduction), for any number of relevant goods per agent where the text allows it, with values in
`Nat` (rationals by scaling; real values are not formalized at k = 4): only additivity is used. It generalizes `EFX/PreAlloc.lean` (Theorem 1′ of
`proofs/lb_last_step.md`, k = 3), whose pre-allocations are ranking-based (picks and upgraded pairs), and
reuses the model (`EFX/Model.lean`) and the list layer (`EFX/Lists.lean`).

Setting (over lists): agents `agents`, goods `goods`, values `v : A → G → Nat`.
- A pre-allocation is a map `base : G → Option A` (`base g = some i` iff `g ∈ B_i`, so bases are
  disjoint) and needs `N : A → G → Prop` (`N i g` iff `g ∈ N_i`). `baseOf goods base i` is `B_i`,
  `junk goods base` is `J`, `junkOf goods base X j` is `C_j` (the junk in `j`'s bundle), `NA agents N`
  is `NA = ⋃ N_i`.
- `Needs`: the Definition's bounds `{g ∈ R_i ∖ B_i : v_i(g) > v_i(B_i)} ⊆ N_i ⊆ R_i ∖ B_i`. The pick
  needs (`g ≻_i Y`, for a strict order consistent with the values, `RankOK`), the needs of an empty base
  (`R_i`) and the value-based needs are instances (`Needs.pick`, `Needs.empty`, `Needs.valueBased`).
- `Frozen`: the base is one good, and it is in `NA`. `Valid`: (V1) and (V2).
- `Completion`: owner `o` (a listed free agent) or none; every good goes to a listed agent, every base
  good to its base's agent, a frozen agent other than `o` gets no junk, a free agent `j ≠ o` gets
  junk `C_j` with `|C_j| ≤ cap(j) = 2 − |B_j|` (with its sign: `|C_j| + |B_j| ≤ 2`).
- `OC`: the owner constraint (OC₄), `v_j(X_o ∖ {h}) ≤ v_j(X_j)` for every `j ≠ o` and `h ∈ X_o`.
- `ownerNeeds`: the needs with the owner's replaced by `N_o^X = {g ∈ R_o ∖ X_o : v_o(g) > v_o(X_o)}`.
- `SoundCompletion`: a completion satisfying (OC₄) of a valid pre-allocation, the owner's needs taken from
  its bundle (the base-needs version is a special case, `SoundCompletion.of_baseNeeds`).

Results, in the order of `k4/lb4.md`:
- **Theorem 1′₄** (§1): `Valid.sound` (owner's needs from its base) and `Valid.sound_ownerNeeds` (owner's
  needs `N_o^X`): every completion satisfying (OC₄) is EFX₀. `efx0_of_needs`: the proof, from only what it
  uses. The text's hypotheses "only `X_o` may have more than 2 goods" and "frozen agents hold exactly their
  base" hold in every completion (`Completion.length_le_two`, `Completion.frozen_base`), so they are not
  assumed.
- **Counting** (§1): `numFrozen_eq` (`|F| = |NA|`), `omega_eq` (`ω = |J| − S = |NA| − σ`, `σ = 2n − m`, the
  cap counted with its sign), `complete_none_exists` (if `ω ≤ 0` and every base has at most two goods, a
  completion without owner exists; all its bundles have at most two goods), `Completion.owner_length`
  (when the other slots are filled, the owner holds `|B_o| + cap(o) + ω = ω + 2` goods).
- **Lemma 2₄** (§1, self-protection, `|R_x| ≤ 4`): `selfProtect` (an agent `x ≠ o` with a pick base whose
  slot takes its `≻`-best junk good not yet placed does not envy the owner's bundle, whose base has at most
  one good, so it is not threatened by it); `selfProtect_seq` (the same when the agents fill their slots one
  at a time, `seqFill`, whatever else is placed); `selfProtect_core` (the value argument alone);
  `selfProtect_five` (the value argument fails with five relevant goods) and `Ex5.counterexample` (an instance
  of every hypothesis of `selfProtect` but `|R_x| ≤ 4` in which `x` is threatened), both by `decide`.
- **Lemma 3₄** (§2, the owner search is exact): `ownerSearch_exact_base` in the text's terms (`s₀` with the
  owner's needs from its base; `|B_o| ≥ 3`, or `o` free with `ω ≥ 1` and the other bases of at most two
  goods; strict balance and `|R_o| ≤ 4`): if a sound completion with owner `o` exists, one exists with at
  least `min(|J|, s₀)` junk goods in the other agents' slots and the same `N_o^X`. `ownerSearch_exact`: the
  general form; `move_step`: one move of its proof.
- **Shape** (§2): `SoundCompletion.efx0_d2` (over lists) and `sound_model`, `d2_shape` (model): a sound
  completion is EFX₀ with at most one bundle of more than two goods. `k4D_of_completion`: a sound completion
  of an instance gives the conclusion of conjecture K4.D for it; `target4_of_completions`: with K4.CORE and
  K4.TIE, sound completions of every connected strict k = 4 core with a 4-good agent give TARGET₄. So "LB₄
  never fails ⟹ K4.D ⟹ TARGET₄" holds once every allocation LB₄ returns is a sound completion, which is §2's
  Shape paragraph read against LB₄'s definition (LB₄ itself is not defined in Lean).
- **Non-vacuity** (by `decide`): `Ex.sound`, a two-agent instance whose sound completion gives the owner three
  goods, valid only with the owner's needs taken from its bundle (`Ex.baseNeeds_invalid`); `ExB.sound`, a
  four-agent instance satisfying `Valid.sound`'s hypotheses (owner's needs from its base) with a frozen agent, a
  two-good base, a filled slot and an owner's bundle of three goods (`ExB.shape`).
-/

set_option autoImplicit false

namespace EFX
namespace LB4

open LB (mem_bundle nodup_bundle length_le_one length_le_of_subset)

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Definitions -/

/-- `B_i`, agent `i`'s base: the goods of `goods` that `base` assigns to `i`. -/
def baseOf (goods : List G) (base : G → Option A) (i : A) : List G :=
  goods.filter (fun g => base g = some i)

/-- The junk `J`: the goods of `goods` in nobody's base. -/
def junk (goods : List G) (base : G → Option A) : List G :=
  goods.filter (fun g => base g = none)

/-- `C_j`: the junk goods in `j`'s bundle. -/
def junkOf (goods : List G) (base : G → Option A) (X : G → A) (j : A) : List G :=
  (bundle goods X j).filter (fun g => base g = none)

/-- `NA`, the needed-alone set: the goods that some listed agent needs. -/
def NA (agents : List A) (N : A → G → Prop) (g : G) : Prop := ∃ i ∈ agents, N i g

/-- `N i` is a set of needs of `i` (`k4/lb4.md` §1, Definition): it contains every good outside `B_i`
worth more to `i` than `B_i` (such a good is in `R_i`), and it is contained in `R_i ∖ B_i`. -/
structure Needs (v : A → G → Nat) (goods : List G) (base : G → Option A) (N : A → G → Prop) (i : A) :
    Prop where
  lower : ∀ g ∈ goods, base g ≠ some i → value v i (baseOf goods base i) < v i g → N i g
  upper : ∀ g, N i g → g ∈ goods ∧ 0 < v i g ∧ base g ≠ some i

/-- `j` is frozen: its base is a single good, and that good is in `NA`. -/
def Frozen (agents : List A) (goods : List G) (base : G → Option A) (N : A → G → Prop) (j : A) :
    Prop :=
  ∃ y, baseOf goods base j = [y] ∧ NA agents N y

/-- A valid pre-allocation: (V1) no junk good is in `NA`; (V2) no good of a base of two or more goods is
in `NA`. -/
structure Valid (agents : List A) (goods : List G) (base : G → Option A) (N : A → G → Prop) :
    Prop where
  v1 : ∀ g ∈ junk goods base, ¬ NA agents N g
  v2 : ∀ i, 2 ≤ (baseOf goods base i).length → ∀ g ∈ baseOf goods base i, ¬ NA agents N g

/-- A completion `X` with owner `o` (or none) of the pre-allocation `(base, N)`:
- `alloc`: every good goes to a listed agent;
- `onBase`: every base good goes to its base's agent (so `X_i = B_i ∪ C_i` with `C_i ⊆ J`);
- `owner`: the owner is a listed agent that is not frozen;
- `frozen`: a frozen agent other than the owner gets no junk (cap 0);
- `free`: a free agent `j` other than the owner gets at most `cap(j) = 2 − |B_j|` junk goods, the cap
  counted with its sign (`|C_j| + |B_j| ≤ 2`).
The owner gets the rest of the junk. -/
structure Completion (agents : List A) (goods : List G) (base : G → Option A) (N : A → G → Prop)
    (o : Option A) (X : G → A) : Prop where
  alloc : ∀ g ∈ goods, X g ∈ agents
  onBase : ∀ g ∈ goods, ∀ i, base g = some i → X g = i
  owner : ∀ w, o = some w → w ∈ agents ∧ ¬ Frozen agents goods base N w
  frozen : ∀ j ∈ agents, o ≠ some j → Frozen agents goods base N j → junkOf goods base X j = []
  free : ∀ j ∈ agents, o ≠ some j → ¬ Frozen agents goods base N j →
    (junkOf goods base X j).length + (baseOf goods base j).length ≤ 2

/-- The owner constraint (OC₄): no listed agent other than the owner strongly envies the owner's bundle. -/
def OC (v : A → G → Nat) (agents : List A) (goods : List G) (X : G → A) (o : Option A) : Prop :=
  ∀ w, o = some w → ∀ j ∈ agents, j ≠ w → ∀ h ∈ bundle goods X w,
    value v j ((bundle goods X w).erase h) ≤ value v j (bundle goods X j)

/-- The needs with the owner's replaced by its needs from its bundle,
`N_o^X = {g ∈ R_o ∖ X_o : v_o(g) > v_o(X_o)}`. -/
def ownerNeeds (v : A → G → Nat) (goods : List G) (X : G → A) (N : A → G → Prop) (o : Option A) :
    A → G → Prop :=
  fun i g => if o = some i then g ∈ goods ∧ X g ≠ i ∧ value v i (bundle goods X i) < v i g else N i g

variable {v : A → G → Nat} {agents : List A} {goods : List G} {base : G → Option A}
  {N : A → G → Prop} {o : Option A} {X : G → A}

/-! ## Small lemmas -/

omit [DecidableEq G] in
theorem mem_baseOf {i : A} {g : G} : g ∈ baseOf goods base i ↔ g ∈ goods ∧ base g = some i := by
  simp [baseOf]

omit [DecidableEq A] [DecidableEq G] in
theorem mem_junk {g : G} : g ∈ junk goods base ↔ g ∈ goods ∧ base g = none := by
  simp [junk]

omit [DecidableEq G] in
theorem mem_junkOf {j : A} {g : G} :
    g ∈ junkOf goods base X j ↔ g ∈ goods ∧ X g = j ∧ base g = none := by
  simp only [junkOf, bundle, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

omit [DecidableEq A] in
/-- A value over a list containing `g` is `v g` plus the value of the rest. -/
theorem value_erase {i : A} {g : G} {S : List G} (h : g ∈ S) :
    value v i S = v i g + value v i (S.erase g) := by
  unfold value
  rw [(List.perm_cons_erase h).map (v i) |>.sum_nat]
  simp

omit [DecidableEq G] in
/-- The base goods of `i` are in `i`'s bundle, so the base is worth at most the bundle. -/
theorem value_baseOf_le (hbase : ∀ g ∈ goods, ∀ i, base g = some i → X g = i) (i : A) :
    value v i (baseOf goods base i) ≤ value v i (bundle goods X i) := by
  apply value_sublist
  unfold baseOf bundle
  have : goods.filter (fun g => base g = some i) =
      (goods.filter (fun g => X g = i)).filter (fun g => base g = some i) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro g hg
    by_cases hb : base g = some i
    · simp [hb, hbase g hg i hb]
    · simp [hb]
  rw [this]
  exact List.filter_sublist

/-! ## Theorem 1′₄ -/

/-- **The proof of Theorem 1′₄, from what it uses.** Suppose every listed agent's needs contain the goods
outside its bundle worth more to it than its bundle (`hN`), (V1) and (V2) hold, every base good is with its
base's agent, a frozen agent holds only its base, every bundle but the owner's has at most two goods, and
(OC₄) holds. Then `X` is EFX₀. -/
theorem efx0_of_needs (hg : goods.Nodup)
    (hN : ∀ i ∈ agents, ∀ g ∈ goods, X g ≠ i → value v i (bundle goods X i) < v i g → N i g)
    (hV : Valid agents goods base N) (hbase : ∀ g ∈ goods, ∀ i, base g = some i → X g = i)
    (hfz : ∀ j ∈ agents, Frozen agents goods base N j → ∀ g ∈ goods, X g = j → base g = some j)
    (hsmall : ∀ j ∈ agents, o ≠ some j → (bundle goods X j).length ≤ 2) (hoc : OC v agents goods X o) :
    EFX0L v agents goods X := by
  intro i hi j hj hij g hgj
  -- singletons are never strongly envied
  by_cases hone : (bundle goods X j).length ≤ 1
  · have hlen : ((bundle goods X j).erase g).length = 0 := by
      rw [List.length_erase_of_mem hgj]; omega
    rw [List.length_eq_zero_iff.mp hlen]; simp
  -- the owner's bundle: (OC₄)
  by_cases hjo : o = some j
  · exact hoc j hjo i hi hij g hgj
  -- otherwise `X_j` has exactly two goods, and `X_j ∖ {g}` is one good `x`
  have h2 := hsmall j hj hjo
  have hl1 : ((bundle goods X j).erase g).length = 1 := by
    rw [List.length_erase_of_mem hgj]; omega
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl1
  have hxj : x ∈ bundle goods X j := List.mem_of_mem_erase (by rw [hx]; simp)
  obtain ⟨hxg, hXx⟩ := mem_bundle.mp hxj
  -- `x` is not in `NA`: it is junk (V1), or in `j`'s base, which has two goods (V2) or is `{x}` with `j`
  -- not frozen (a frozen agent holds only its base)
  have hnotNA : ¬ NA agents N x := by
    intro hna
    cases hbx : base x with
    | none => exact hV.v1 x (mem_junk.mpr ⟨hxg, hbx⟩) hna
    | some k =>
      have hkj : k = j := (hbase x hxg k hbx).symm.trans hXx
      subst hkj
      have hxb : x ∈ baseOf goods base k := mem_baseOf.mpr ⟨hxg, hbx⟩
      by_cases hb2 : 2 ≤ (baseOf goods base k).length
      · exact hV.v2 k hb2 x hxb hna
      · have hb1 : baseOf goods base k = [x] := by
          have hnd : (baseOf goods base k).Nodup := hg.sublist List.filter_sublist
          match hB : baseOf goods base k, hnd with
          | [], _ => rw [hB] at hxb; simp at hxb
          | [y], _ => rw [hB] at hxb; simp at hxb; rw [hxb]
          | _ :: _ :: _, _ => rw [hB] at hb2; simp at hb2
        have hF : Frozen agents goods base N k := ⟨x, hb1, hna⟩
        -- a frozen agent holds only its base `{x}`
        have := length_le_one (nodup_bundle hg X k) (y := x) (fun h hh => by
          obtain ⟨hhg, hXh⟩ := mem_bundle.mp hh
          have := mem_baseOf.mpr ⟨hhg, hfz k hj hF h hhg hXh⟩
          rw [hb1] at this; simpa using this)
        omega
  -- so `i` does not need `x`, and `x` is outside `i`'s bundle: it is worth at most `X_i`
  have hxi : X x ≠ i := fun e => hij (e.symm.trans hXx)
  have hle : v i x ≤ value v i (bundle goods X i) :=
    Nat.le_of_not_lt fun hlt => hnotNA ⟨i, hi, hN i hi x hxg hxi hlt⟩
  rw [hx]; simpa using hle

omit [DecidableEq G] in
/-- Needs in the Definition's sense contain the goods outside the bundle worth more than the bundle, when
every base good is with its base's agent. -/
theorem Needs.of_bundle {i : A} (hNi : Needs v goods base N i)
    (hbase : ∀ g ∈ goods, ∀ i, base g = some i → X g = i) :
    ∀ g ∈ goods, X g ≠ i → value v i (bundle goods X i) < v i g → N i g := fun g hg hXg hlt =>
  hNi.lower g hg (fun hb => hXg (hbase g hg i hb))
    (Nat.lt_of_le_of_lt (value_baseOf_le hbase i) hlt)

/-- In a completion, every bundle but the owner's has at most two goods: `X_j = B_j ∪ C_j`, with
`|C_j| + |B_j| ≤ 2` for a free agent and `C_j = ∅`, `|B_j| = 1` for a frozen one. -/
theorem Completion.length_le_two (hC : Completion agents goods base N o X) (hg : goods.Nodup) :
    ∀ j ∈ agents, o ≠ some j → (bundle goods X j).length ≤ 2 := by
  intro j hj hjo
  -- the goods of `X_j` outside the junk are exactly `j`'s base goods
  have hsplit : (bundle goods X j).length ≤
      (junkOf goods base X j).length + (baseOf goods base j).length := by
    rw [List.length_eq_countP_add_countP (fun g => base g = none) (l := bundle goods X j),
      List.countP_eq_length_filter, List.countP_eq_length_filter]
    have : ((bundle goods X j).filter (fun g => ¬ (decide (base g = none)) = true)).length ≤
        (baseOf goods base j).length := by
      apply length_le_of_subset ((nodup_bundle hg X j).sublist List.filter_sublist)
      intro g hgf
      obtain ⟨hgb, hgn⟩ := List.mem_filter.mp hgf
      obtain ⟨hgg, hXg⟩ := mem_bundle.mp hgb
      cases hb : base g with
      | none => simp [hb] at hgn
      | some k =>
        have := hC.onBase g hgg k hb
        rw [hXg] at this; subst this
        exact mem_baseOf.mpr ⟨hgg, hb⟩
    unfold junkOf
    omega
  by_cases hF : Frozen agents goods base N j
  · obtain ⟨y, hy, -⟩ := id hF
    have := hC.frozen j hj hjo hF
    rw [this, hy] at hsplit
    simp at hsplit
    omega
  · exact Nat.le_trans hsplit (hC.free j hj hjo hF)

omit [DecidableEq G] in
/-- In a completion, a frozen agent other than the owner holds only its base. -/
theorem Completion.frozen_base (hC : Completion agents goods base N o X) :
    ∀ j ∈ agents, o ≠ some j → Frozen agents goods base N j → ∀ g ∈ goods, X g = j →
      base g = some j := by
  intro j hj hjo hF g hg hXg
  cases hb : base g with
  | none =>
    have : g ∈ junkOf goods base X j := mem_junkOf.mpr ⟨hg, hXg, hb⟩
    rw [hC.frozen j hj hjo hF] at this; simp at this
  | some k => rw [← hXg, hC.onBase g hg k hb]

/-- **Theorem 1′₄ (soundness, any k), owner's needs from its base.** Let `(base, N)` be a valid
pre-allocation in which every listed agent's needs are needs in the Definition's sense, and `X` a
completion with owner `o` (or none) satisfying (OC₄). Then `X` is EFX₀, and every bundle but the
owner's has at most two goods. Only additivity is used: no bound on `|R_i|`, no balance. -/
theorem Valid.sound (hg : goods.Nodup) (hNd : ∀ i ∈ agents, Needs v goods base N i)
    (hV : Valid agents goods base N) (hC : Completion agents goods base N o X)
    (hoc : OC v agents goods X o) :
    EFX0L v agents goods X ∧ ∀ j ∈ agents, o ≠ some j → (bundle goods X j).length ≤ 2 := by
  refine ⟨efx0_of_needs hg (fun i hi => (hNd i hi).of_bundle hC.onBase) hV hC.onBase ?_
    (hC.length_le_two hg) hoc, hC.length_le_two hg⟩
  intro j hj hF g hg' hXg
  by_cases hjo : o = some j
  · exact absurd hF ((hC.owner j hjo).2)
  · exact hC.frozen_base j hj hjo hF g hg' hXg

/-- **Theorem 1′₄ (soundness, any k), owner's needs from its bundle.** The same with the owner's needs
replaced by `N_o^X` (`ownerNeeds`), and validity, the frozen agents and the caps computed with them. The
owner's own needs from its base are not used. -/
theorem Valid.sound_ownerNeeds (hg : goods.Nodup)
    (hNd : ∀ i ∈ agents, o ≠ some i → Needs v goods base N i)
    (hV : Valid agents goods base (ownerNeeds v goods X N o))
    (hC : Completion agents goods base (ownerNeeds v goods X N o) o X)
    (hoc : OC v agents goods X o) :
    EFX0L v agents goods X ∧ ∀ j ∈ agents, o ≠ some j → (bundle goods X j).length ≤ 2 := by
  refine ⟨efx0_of_needs hg (N := ownerNeeds v goods X N o) (fun i hi g hg' hXg hlt => ?_) hV hC.onBase
    ?_ (hC.length_le_two hg) hoc, hC.length_le_two hg⟩
  · by_cases hio : o = some i
    · simp only [ownerNeeds, hio, ↓reduceIte]
      exact ⟨hg', hXg, hlt⟩
    · simp only [ownerNeeds, hio, ↓reduceIte]
      exact (hNd i hi hio).of_bundle hC.onBase g hg' hXg hlt
  · intro j hj hF g hg' hXg
    by_cases hjo : o = some j
    · exact absurd hF ((hC.owner j hjo).2)
    · exact hC.frozen_base j hj hjo hF g hg' hXg

omit [DecidableEq G] in
/-- Taking the owner's needs from its bundle only shrinks them: `N_o^X ⊆ N_o` for needs in the
Definition's sense, so `NA` computed with `N_o^X` is contained in `NA`. -/
theorem ownerNeeds_le (hC : ∀ g ∈ goods, ∀ i, base g = some i → X g = i)
    (hNd : ∀ i ∈ agents, Needs v goods base N i) :
    ∀ i ∈ agents, ∀ g, ownerNeeds v goods X N o i g → N i g := by
  intro i hi g hN
  by_cases hio : o = some i
  · simp only [ownerNeeds, hio, ↓reduceIte] at hN
    exact (hNd i hi).of_bundle hC g hN.1 hN.2.1 hN.2.2
  · simpa [ownerNeeds, hio] using hN

omit [DecidableEq G] in
/-- Hence (V1) and (V2) with the owner's needs from its base imply them with its needs from its bundle. -/
theorem Valid.toOwnerNeeds (hV : Valid agents goods base N)
    (hC : ∀ g ∈ goods, ∀ i, base g = some i → X g = i) (hNd : ∀ i ∈ agents, Needs v goods base N i) :
    Valid agents goods base (ownerNeeds v goods X N o) := by
  have hNA : ∀ g, NA agents (ownerNeeds v goods X N o) g → NA agents N g := fun g ⟨i, hi, h⟩ =>
    ⟨i, hi, ownerNeeds_le hC hNd i hi g h⟩
  exact ⟨fun g hg h => hV.v1 g hg (hNA g h), fun i h2 g hg h => hV.v2 i h2 g hg (hNA g h)⟩


omit [DecidableEq G] in
/-- A completion with the owner's needs from its base is one with its needs from its bundle: `NA` only
shrinks, so fewer agents are frozen, and an agent that stops being frozen had base `{y}` and no junk. -/
theorem Completion.toOwnerNeeds (hC : Completion agents goods base N o X)
    (hNd : ∀ i ∈ agents, Needs v goods base N i) :
    Completion agents goods base (ownerNeeds v goods X N o) o X := by
  have hNA : ∀ g, NA agents (ownerNeeds v goods X N o) g → NA agents N g := fun g ⟨i, hi, h⟩ =>
    ⟨i, hi, ownerNeeds_le hC.onBase hNd i hi g h⟩
  have hF : ∀ j, Frozen agents goods base (ownerNeeds v goods X N o) j → Frozen agents goods base N j :=
    fun j ⟨y, hy, hna⟩ => ⟨y, hy, hNA y hna⟩
  refine ⟨hC.alloc, hC.onBase, fun w hw => ⟨(hC.owner w hw).1, fun h => (hC.owner w hw).2 (hF w h)⟩,
    fun j hj hjo h => hC.frozen j hj hjo (hF j h), fun j hj hjo _ => ?_⟩
  by_cases hFj : Frozen agents goods base N j
  · obtain ⟨y, hy, -⟩ := id hFj
    rw [hC.frozen j hj hjo hFj, hy]; simp
  · exact hC.free j hj hjo hFj

/-! ## The needs LB₄ uses -/

omit [DecidableEq G] in
/-- The value-based needs `{g ∉ B_i : v_i(g) > v_i(B_i)}` are needs. -/
theorem Needs.valueBased (i : A) :
    Needs v goods base (fun _ g => g ∈ goods ∧ base g ≠ some i ∧ value v i (baseOf goods base i) < v i g) i :=
  ⟨fun g hg hb hlt => ⟨hg, hb, hlt⟩, fun g ⟨hg, hb, hlt⟩ => ⟨hg, by omega, hb⟩⟩

omit [DecidableEq G] in
/-- The needs of an empty base: all of `R_i`. -/
theorem Needs.empty {i : A} (h0 : baseOf goods base i = []) :
    Needs v goods base (fun _ g => g ∈ goods ∧ 0 < v i g) i := by
  refine ⟨fun g hg _ hlt => ⟨hg, by omega⟩, fun g ⟨hg, hpos⟩ => ⟨hg, hpos, fun hb => ?_⟩⟩
  have := mem_baseOf.mpr ⟨hg, hb⟩
  rw [h0] at this; simp at this

/-- `pref i` is a strict order `≻_i` consistent with `i`'s values (`k4/lb4.md` §0): it is asymmetric, and
`v_i(g) > v_i(h) > 0` implies `g ≻_i h`. (Transitivity and totality are not needed.) -/
structure RankOK (v : A → G → Nat) (pref : A → G → G → Prop) (i : A) : Prop where
  asymm : ∀ g h, pref i g h → ¬ pref i h g
  consistent : ∀ g h, 0 < v i h → v i h < v i g → pref i g h

/-- The needs of a pick `y`: the goods of `R_i` ranked above `y`. -/
def pickNeeds (v : A → G → Nat) (goods : List G) (pref : A → G → G → Prop) (y : G) (i : A) (g : G) :
    Prop :=
  g ∈ goods ∧ 0 < v i g ∧ pref i g y

omit [DecidableEq G] in
/-- The needs of a pick are needs, for a relevant pick and a ranking consistent with the values. -/
theorem Needs.pick {pref : A → G → G → Prop} {i : A} {y : G} (hB : baseOf goods base i = [y])
    (hy : 0 < v i y) (hR : RankOK v pref i) :
    Needs v goods base (fun _ => pickNeeds v goods pref y i) i := by
  refine ⟨fun g hg _ hlt => ?_, fun g ⟨hg, hpos, hpref⟩ => ⟨hg, hpos, fun hb => ?_⟩⟩
  · rw [hB] at hlt
    simp only [value_cons, value_nil, Nat.add_zero] at hlt
    exact ⟨hg, by omega, hR.consistent g y hy hlt⟩
  · have := mem_baseOf.mpr ⟨hg, hb⟩
    rw [hB, List.mem_singleton] at this
    subst this
    exact hR.asymm g g hpref hpref

/-! ## The D2 shape and the chain to K4.D -/

/-- What every allocation LB₄ returns is (`k4/lb4.md` §2): a completion `X` with owner `o` (or none) of a
pre-allocation `(base, N)` whose non-owner agents have needs in the Definition's sense, valid and
completed with the owner's needs from its bundle, satisfying (OC₄). (With the owner's needs from its base
instead, `SoundCompletion.of_baseNeeds`.) -/
structure SoundCompletion (v : A → G → Nat) (agents : List A) (goods : List G) (base : G → Option A)
    (N : A → G → Prop) (o : Option A) (X : G → A) : Prop where
  needs : ∀ i ∈ agents, o ≠ some i → Needs v goods base N i
  valid : Valid agents goods base (ownerNeeds v goods X N o)
  completion : Completion agents goods base (ownerNeeds v goods X N o) o X
  oc : OC v agents goods X o

/-- The version with the owner's needs from its base is a special case. -/
theorem SoundCompletion.of_baseNeeds (hNd : ∀ i ∈ agents, Needs v goods base N i)
    (hV : Valid agents goods base N) (hC : Completion agents goods base N o X)
    (hoc : OC v agents goods X o) : SoundCompletion v agents goods base N o X :=
  ⟨fun i hi _ => hNd i hi, hV.toOwnerNeeds hC.onBase hNd, hC.toOwnerNeeds hNd, hoc⟩

/-- **The D2 shape, over lists.** A sound completion is a complete EFX₀ allocation of `goods` to
`agents` with at most one bundle of more than two goods (the owner's, or any agent's if there is no
owner). -/
theorem SoundCompletion.efx0_d2 (hS : SoundCompletion v agents goods base N o X) (hg : goods.Nodup)
    (hne : agents ≠ []) :
    IsAllocation agents goods X ∧ EFX0L v agents goods X ∧
      ∃ w ∈ agents, ∀ j ∈ agents, j ≠ w → (bundle goods X j).length ≤ 2 := by
  obtain ⟨hE, hlen⟩ := Valid.sound_ownerNeeds hg hS.needs hS.valid hS.completion hS.oc
  refine ⟨hS.completion.alloc, hE, ?_⟩
  cases ho : o with
  | some w =>
    exact ⟨w, (hS.completion.owner w ho).1, fun j hj hjw => hlen j hj (by rw [ho]; simpa using Ne.symm hjw)⟩
  | none =>
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil agents hne
    exact ⟨w, hw, fun j hj _ => hlen j hj (by rw [ho]; simp)⟩

/-- **Theorem 1′₄ in the model's terms.** A sound completion of an instance (agents `Fin n`, goods
`Fin m`) is EFX₀, and every bundle but the owner's has at most two goods. -/
theorem sound_model (I : Inst) {base : Fin I.m → Option (Fin I.n)} {N : Fin I.n → Fin I.m → Prop}
    {o : Option (Fin I.n)} {X : I.Alloc}
    (hS : SoundCompletion I.v (List.finRange I.n) (List.finRange I.m) base N o X) :
    I.EFX0 X ∧ ∀ j, o ≠ some j → finSum I.m (fun g => if X g = j then 1 else 0) ≤ 2 := by
  obtain ⟨hE, hlen⟩ := Valid.sound_ownerNeeds (List.nodup_finRange I.m) hS.needs hS.valid hS.completion hS.oc
  refine ⟨(Inst.efx0_iff I X).mpr hE, fun j hj => ?_⟩
  rw [LB.finSum_bundle_eq]
  exact hlen j (List.mem_finRange j) hj

/-- **The D2 shape, in the model's terms.** If every bundle except the owner's (if any) has at most two
goods, then at most one bundle has more than two goods. -/
theorem d2_shape (I : Inst) (hn : 0 < I.n) {X : I.Alloc} {o : Option (Fin I.n)}
    (h : ∀ j, o ≠ some j → finSum I.m (fun g => if X g = j then 1 else 0) ≤ 2) :
    ∃ w, ∀ j, j ≠ w → finSum I.m (fun g => if X g = j then 1 else 0) ≤ 2 := by
  cases o with
  | some w => exact ⟨w, fun j hj => h j (by simpa using Ne.symm hj)⟩
  | none => exact ⟨⟨0, hn⟩, fun j _ => h j (by simp)⟩

/-- **LB₄ never fails ⟹ K4.D, for one instance.** If an instance with at least one agent has a sound
completion (every allocation LB₄ returns is one), it has an EFX₀ allocation with at most one bundle of
more than two goods: the conclusion of conjecture K4.D (and of `EFX.LB.corollaryD` at k = 3). -/
theorem k4D_of_completion (I : Inst) (hn : 0 < I.n)
    (h : ∃ (base : Fin I.m → Option (Fin I.n)) (N : Fin I.n → Fin I.m → Prop) (o : Option (Fin I.n))
      (X : I.Alloc), SoundCompletion I.v (List.finRange I.n) (List.finRange I.m) base N o X) :
    ∃ X : I.Alloc, I.EFX0 X ∧ ∃ w, ∀ j, j ≠ w → finSum I.m (fun g => if X g = j then 1 else 0) ≤ 2 := by
  obtain ⟨base, N, o, X, hS⟩ := h
  obtain ⟨hE, hlen⟩ := sound_model I hS
  exact ⟨X, hE, d2_shape I hn hlen⟩

/-- **LB₄ never fails ⟹ TARGET₄ (up to `Nn` agents).** With K4.CORE and K4.TIE
(`EFX.target4_of_strict_cores`): if every connected strict k = 4 core with at most `Nn` agents and a 4-good
agent has a sound completion (which LB₄ never failing on it would give), every instance with at most `Nn`
agents and at most four relevant goods per agent has an EFX₀ allocation. -/
theorem target4_of_completions (I : Inst) (hn : 0 < I.n) (Nn : Nat) (hN : I.n ≤ Nn)
    (hcore : ∀ (w : Fin I.n → Fin I.m → Nat) (agents : List (Fin I.n)) (goods : List (Fin I.m)),
      agents.Nodup → goods.Nodup → agents.length ≤ Nn → IsCore4 w agents goods →
      Connected w agents goods → Strict w agents goods → (∃ i ∈ agents, (relevant w i goods).length = 4) →
      ∃ (base : Fin I.m → Option (Fin I.n)) (N : Fin I.n → Fin I.m → Prop) (o : Option (Fin I.n))
        (X : Fin I.m → Fin I.n), SoundCompletion w agents goods base N o X)
    (h : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X :=
  target4_of_strict_cores I hn Nn hN (fun w agents goods hag hgd hl hc hconn hs h4 => by
    obtain ⟨base, N, o, X, hS⟩ := hcore w agents goods hag hgd hl hc hconn hs h4
    exact ⟨X, hS.completion.alloc,
      (Valid.sound_ownerNeeds hgd hS.needs hS.valid hS.completion hS.oc).1⟩) h


/-! ## Counting (`k4/lb4.md` §1, "Counting (any k)") -/

section counting

/-- Double counting: summing, over the agents, the number of goods related to each agent is summing,
over the goods, the number of agents related to each good. -/
theorem sum_countP_comm {α β : Type} (p : α → β → Bool) (as : List α) :
    ∀ gs : List β, (as.map (fun i => gs.countP (p i))).sum = (gs.map (fun g => as.countP (fun i => p i g))).sum
  | [] => by induction as <;> simp_all
  | g :: gs => by
    have ih := sum_countP_comm p as gs
    have e : ∀ bs : List α, (bs.map (fun i => (g :: gs).countP (p i))).sum =
        (bs.map (fun i => gs.countP (p i))).sum + bs.countP (fun i => p i g) := by
      intro bs
      induction bs with
      | nil => simp
      | cons b bs ihb =>
        have h1 : (g :: gs).countP (p b) = gs.countP (p b) + (if p b g then 1 else 0) := List.countP_cons
        have h2 : (b :: bs).countP (fun i => p i g) = bs.countP (fun i => p i g) + (if p b g then 1 else 0) :=
          List.countP_cons
        simp only [List.map_cons, List.sum_cons]
        rw [ihb, h1, h2]
        omega
    rw [e, ih]
    simp only [List.map_cons, List.sum_cons]
    omega

omit [DecidableEq G] in
/-- In a list of distinct agents that contains every base's agent, exactly one agent (none) has `g` in its
base if `g` is (not) in a base. -/
theorem countP_base (as : List A) (has : as.Nodup) {b : Option A} (hb : ∀ k, b = some k → k ∈ as) :
    as.countP (fun i => decide (b = some i)) = if b = none then 0 else 1 := by
  cases b with
  | none => simp
  | some k =>
    have hk := hb k rfl
    simp only [reduceCtorEq, ↓reduceIte, Option.some.injEq]
    induction as with
    | nil => simp at hk
    | cons a as ih =>
      rw [List.countP_cons]
      obtain ⟨ha, has'⟩ := List.nodup_cons.mp has
      by_cases hka : k = a
      · subst hka
        have : as.countP (fun i => decide (k = i)) = 0 :=
          List.countP_eq_zero.mpr fun i hi hki => ha (by simp at hki; exact hki ▸ hi)
        simp [this]
      · have := ih has' (fun k' hk' => by cases hk'; exact (List.mem_cons.mp hk).resolve_left hka)
          ((List.mem_cons.mp hk).resolve_left hka)
        simp [hka, this]

/-- A sum over distinct agents in which every term but `w`'s vanishes is `w`'s term. -/
theorem sum_single (f : A → Int) {w : A} :
    ∀ {as : List A}, as.Nodup → w ∈ as → (∀ j ∈ as, j ≠ w → f j = 0) → (as.map f).sum = f w
  | [], _, hw, _ => by simp at hw
  | a :: as, has, hw, h0 => by
    obtain ⟨ha, has'⟩ := List.nodup_cons.mp has
    simp only [List.map_cons, List.sum_cons]
    by_cases haw : a = w
    · subst haw
      have : (as.map f).sum = 0 := by
        have : ∀ bs : List A, (∀ j ∈ bs, f j = 0) → (bs.map f).sum = 0 := by
          intro bs hbs
          induction bs with
          | nil => simp
          | cons b bs ih =>
            simp only [List.map_cons, List.sum_cons, hbs b (by simp),
              ih (fun j hj => hbs j (by simp [hj]))]
            simp
        exact this as (fun j hj => h0 j (by simp [hj]) (fun e => ha (e ▸ hj)))
      rw [this]; simp
    · rw [h0 a (by simp) haw, sum_single f has' ((List.mem_cons.mp hw).resolve_left (Ne.symm haw))
        (fun j hj hjw => h0 j (by simp [hj]) hjw)]
      simp

open Classical in
/-- `cap(i)`, counted with its sign: `0` for a frozen agent, `2 − |B_i|` for a free one (negative for a base
of three or more goods). -/
noncomputable def cap (agents : List A) (goods : List G) (base : G → Option A) (N : A → G → Prop) (i : A) :
    Int :=
  if Frozen agents goods base N i then 0 else 2 - ((baseOf goods base i).length : Int)

/-- `S = Σ_i cap(i)`. -/
noncomputable def capSum (agents : List A) (goods : List G) (base : G → Option A) (N : A → G → Prop) :
    Int :=
  (agents.map (cap agents goods base N)).sum

open Classical in
/-- `|NA|`: the number of goods (of `goods`) that some listed agent needs. -/
noncomputable def numNA (agents : List A) (goods : List G) (N : A → G → Prop) : Nat :=
  goods.countP (fun g => decide (NA agents N g))

open Classical in
/-- `|F|`: the number of frozen listed agents. -/
noncomputable def numFrozen (agents : List A) (goods : List G) (base : G → Option A) (N : A → G → Prop) :
    Nat :=
  agents.countP (fun j => decide (Frozen agents goods base N j))

omit [DecidableEq G] in
open Classical in
/-- In a valid pre-allocation, an agent is frozen iff exactly one of its base goods is in `NA` (and
otherwise none is). -/
theorem frozen_count (hV : Valid agents goods base N) (hg : goods.Nodup) (j : A) :
    (if Frozen agents goods base N j then 1 else 0) =
      goods.countP (fun g => decide (base g = some j) && decide (NA agents N g)) := by
  have e : goods.countP (fun g => decide (base g = some j) && decide (NA agents N g)) =
      (baseOf goods base j).countP (fun g => decide (NA agents N g)) := by
    rw [baseOf, List.countP_filter]
    apply List.countP_congr
    intro g _
    simp [Bool.and_comm]
  rw [e]
  have hnd : (baseOf goods base j).Nodup := hg.sublist List.filter_sublist
  by_cases hF : Frozen agents goods base N j
  · obtain ⟨y, hy, hna⟩ := id hF
    simp only [hF, ↓reduceIte]
    rw [hy]; simp [hna]
  · simp only [hF, ↓reduceIte]
    symm
    apply List.countP_eq_zero.mpr
    intro g hg' hna
    simp only [decide_eq_true_eq] at hna
    by_cases h2 : 2 ≤ (baseOf goods base j).length
    · exact hV.v2 j h2 g hg' hna
    · apply hF
      refine ⟨g, ?_, hna⟩
      match hB : baseOf goods base j, hnd with
      | [], _ => rw [hB] at hg'; simp at hg'
      | [y], _ => rw [hB] at hg'; simp at hg'; rw [hg']
      | _ :: _ :: _, _ => rw [hB] at h2; simp at h2

/-- A count is a sum of indicators. -/
theorem countP_eq_sum {α : Type} (p : α → Bool) :
    ∀ l : List α, l.countP p = (l.map (fun a => if p a then 1 else 0)).sum
  | [] => by simp
  | a :: l => by rw [List.countP_cons, countP_eq_sum p l]; simp; omega

omit [DecidableEq G] in
/-- **`|F| = |NA|`.** In a valid pre-allocation every good of `NA` is the whole base of exactly one agent,
which is frozen, and every frozen agent's base is one good of `NA`. -/
theorem numFrozen_eq (hV : Valid agents goods base N) (hag : agents.Nodup) (hg : goods.Nodup)
    (hmem : ∀ g ∈ goods, ∀ i, base g = some i → i ∈ agents) :
    numFrozen agents goods base N = numNA agents goods N := by
  classical
  unfold numFrozen numNA
  rw [countP_eq_sum, countP_eq_sum]
  have e1 : (agents.map (fun j => if decide (Frozen agents goods base N j) = true then 1 else 0)) =
      agents.map (fun j => goods.countP (fun g => decide (base g = some j) && decide (NA agents N g))) := by
    apply List.map_congr_left
    intro j _
    rw [← frozen_count hV hg j]
    simp
  rw [e1, sum_countP_comm (fun j g => decide (base g = some j) && decide (NA agents N g)) agents goods]
  congr 1
  apply List.map_congr_left
  intro g hgg
  by_cases hna : NA agents N g
  · have hb : base g ≠ none := fun hb => hV.v1 g (mem_junk.mpr ⟨hgg, hb⟩) hna
    have := countP_base agents hag (b := base g) (hmem g hgg)
    simp only [hb, ↓reduceIte] at this
    simp only [hna, decide_true, Bool.and_true, ↓reduceIte]
    exact this
  · simp [hna]

/-- Sums of integer differences. -/
theorem sum_map_sub_int {α : Type} (f h : α → Int) :
    ∀ l : List α, (l.map (fun a => f a - h a)).sum = (l.map f).sum - (l.map h).sum
  | [] => by simp
  | a :: l => by simp only [List.map_cons, List.sum_cons, sum_map_sub_int f h l]; omega

theorem sum_map_two {α : Type} : ∀ l : List α, (l.map (fun _ => (2 : Int))).sum = 2 * (l.length : Int)
  | [] => by simp
  | a :: l => by simp only [List.map_cons, List.sum_cons, List.length_cons, sum_map_two l]; omega

theorem sum_map_cast {α : Type} (f : α → Nat) :
    ∀ l : List α, (l.map (fun a => (f a : Int))).sum = ((l.map f).sum : Nat)
  | [] => by simp
  | a :: l => by simp only [List.map_cons, List.sum_cons, sum_map_cast f l]; omega

omit [DecidableEq G] in
/-- The goods are the junk and the bases: `m = |J| + Σ_i |B_i|`. -/
theorem length_goods (hag : agents.Nodup) (hmem : ∀ g ∈ goods, ∀ i, base g = some i → i ∈ agents) :
    goods.length = (junk goods base).length + (agents.map (fun i => (baseOf goods base i).length)).sum := by
  have e : (agents.map (fun i => (baseOf goods base i).length)) =
      agents.map (fun i => goods.countP (fun g => decide (base g = some i))) := by
    apply List.map_congr_left
    intro i _
    rw [baseOf, List.countP_eq_length_filter]
  rw [e, sum_countP_comm (fun i g => decide (base g = some i)) agents goods]
  have e2 : (goods.map (fun g => agents.countP (fun i => decide (base g = some i)))) =
      goods.map (fun g => if decide (base g = none) = true then 0 else 1) := by
    apply List.map_congr_left
    intro g hg
    rw [countP_base agents hag (hmem g hg)]
    simp
  rw [e2, List.length_eq_countP_add_countP (fun g => decide (base g = none)), junk,
    List.countP_eq_length_filter, countP_eq_sum]
  have e3 : ∀ l : List G, (l.map (fun g => if decide (base g = none) = true then 0 else 1)).sum =
      (l.map (fun g => if (decide ¬ (decide (base g = none)) = true) = true then 1 else 0)).sum := by
    intro l
    congr 1
    apply List.map_congr_left
    intro g _
    by_cases hb : base g = none <;> simp [hb]
  rw [e3]

omit [DecidableEq G] in
open Classical in
/-- `cap(i) = 2 − |B_i| − [i frozen]`: a frozen agent has a base of one good. -/
theorem cap_eq (i : A) :
    cap agents goods base N i =
      2 - ((baseOf goods base i).length : Int) - ((if Frozen agents goods base N i then 1 else 0 : Nat) : Int) := by
  unfold cap
  by_cases hF : Frozen agents goods base N i
  · obtain ⟨y, hy, -⟩ := id hF
    simp only [hF, ↓reduceIte, hy]
    simp
  · simp [hF]

omit [DecidableEq G] in
/-- **Counting (any k).** With `cap(i) = 2 − |B_i|` counted with its sign (0 for frozen agents),
`S = Σ cap(i)` and `ω = |J| − S`: `ω = |NA| − σ`, where `σ = 2n − m` (`n` agents, `m` goods). -/
theorem omega_eq (hV : Valid agents goods base N) (hag : agents.Nodup) (hg : goods.Nodup)
    (hmem : ∀ g ∈ goods, ∀ i, base g = some i → i ∈ agents) :
    ((junk goods base).length : Int) - capSum agents goods base N =
      (numNA agents goods N : Int) - (2 * (agents.length : Int) - (goods.length : Int)) := by
  classical
  have hm := length_goods (base := base) hag hmem
  have hF := numFrozen_eq hV hag hg hmem
  have hS : capSum agents goods base N = 2 * (agents.length : Int) -
      (((agents.map (fun i => (baseOf goods base i).length)).sum : Nat) : Int) -
      ((numFrozen agents goods base N : Nat) : Int) := by
    unfold capSum
    rw [List.map_congr_left (fun i _ => cap_eq (agents := agents) (goods := goods) (base := base) (N := N) i)]
    rw [sum_map_sub_int, sum_map_sub_int, sum_map_cast, sum_map_cast]
    unfold numFrozen
    rw [countP_eq_sum]
    rw [sum_map_two]
    have e : (agents.map (fun j => if Frozen agents goods base N j then 1 else 0)) =
        agents.map (fun j => if decide (Frozen agents goods base N j) = true then 1 else 0) := by
      apply List.map_congr_left; intro j _; simp
    rw [e]
  rw [hS, hF, hm]
  push_cast
  omega

omit [DecidableEq G] in
/-- In a completion, `|X_j| = |C_j| + |B_j|`. -/
theorem Completion.length_eq (hC : Completion agents goods base N o X) (j : A) :
    (bundle goods X j).length = (junkOf goods base X j).length + (baseOf goods base j).length := by
  rw [List.length_eq_countP_add_countP (fun g => base g = none) (l := bundle goods X j), junkOf,
    ← List.countP_eq_length_filter]
  congr 1
  rw [bundle, List.countP_filter, baseOf, ← List.countP_eq_length_filter]
  apply List.countP_congr
  intro g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro ⟨hb, hX⟩
    cases hbg : base g with
    | none => exact absurd hbg hb
    | some k => rw [← hX, hC.onBase g hg k hbg]
  · intro hb
    exact ⟨by rw [hb]; simp, hC.onBase g hg j hb⟩

omit [DecidableEq G] in
/-- The junk is split among the listed agents: `|J| = Σ_j |C_j|`. -/
theorem Completion.junk_length (hC : Completion agents goods base N o X) (hag : agents.Nodup) :
    (junk goods base).length = (agents.map (fun j => (junkOf goods base X j).length)).sum := by
  have e : agents.map (fun j => (junkOf goods base X j).length) =
      agents.map (fun j => goods.countP (fun g => decide (X g = j) && decide (base g = none))) := by
    apply List.map_congr_left
    intro j _
    rw [junkOf, bundle, List.filter_filter, ← List.countP_eq_length_filter]
    apply List.countP_congr
    intro g _
    simp [And.comm]
  rw [e, sum_countP_comm (fun j g => decide (X g = j) && decide (base g = none)) agents goods, junk,
    ← List.countP_eq_length_filter, countP_eq_sum]
  congr 1
  apply List.map_congr_left
  intro g hg
  have hX := countP_base agents hag (b := some (X g)) (fun k hk => by cases hk; exact hC.alloc g hg)
  by_cases hb : base g = none
  · simp only [hb, decide_true, Bool.and_true, ↓reduceIte]
    simp only [reduceCtorEq, ↓reduceIte, Option.some.injEq] at hX
    exact hX.symm
  · simp [hb]

omit [DecidableEq G] in
open Classical in
/-- **The owner's bundle.** In a completion with a free owner `w` in which every other agent's slots are
filled (every free `j ≠ w` gets exactly `cap(j) = 2 − |B_j|` junk goods), the owner gets
`|X_w| = |B_w| + cap(w) + ω = ω + 2` goods, `ω = |J| − S`. -/
theorem Completion.owner_length {w : A} (hC : Completion agents goods base N (some w) X)
    (hag : agents.Nodup)
    (hfill : ∀ j ∈ agents, j ≠ w → ¬ Frozen agents goods base N j →
      (junkOf goods base X j).length + (baseOf goods base j).length = 2) :
    ((bundle goods X w).length : Int) = ((junk goods base).length : Int) - capSum agents goods base N + 2 := by
  have hw := hC.owner w rfl
  have hJ := hC.junk_length hag
  have hsum : (agents.map (fun j => ((junkOf goods base X j).length : Int) - cap agents goods base N j)).sum =
      ((junkOf goods base X w).length : Int) - cap agents goods base N w := by
    apply sum_single (fun j => ((junkOf goods base X j).length : Int) - cap agents goods base N j) hag hw.1
    intro j hj hjw
    have hjo : some w ≠ some j := fun e => hjw (Option.some.inj e).symm
    by_cases hF : Frozen agents goods base N j
    · rw [hC.frozen j hj hjo hF]; unfold cap; simp [hF]
    · have := hfill j hj hjw hF
      unfold cap; simp only [hF, ↓reduceIte]; omega
  rw [sum_map_sub_int, sum_map_cast] at hsum
  have hcw : cap agents goods base N w = 2 - ((baseOf goods base w).length : Int) := by
    unfold cap; simp [hw.2]
  rw [hC.length_eq w, hJ]
  unfold capSum
  omega

open Classical in
/-- The slots `max(cap(j), 0)`: none for a frozen agent, `2 − |B_j|` (truncated at 0) for a free one. -/
noncomputable def slots (agents : List A) (goods : List G) (base : G → Option A) (N : A → G → Prop) (j : A) :
    Nat :=
  if Frozen agents goods base N j then 0 else 2 - (baseOf goods base j).length

open Classical in
/-- The completion without owner: base goods to their base's agent, the junk into the slots in the order of
`agents` (`EFX.LB.fill`); `d` receives what nothing places (nothing, under `complete_none_exists`). -/
noncomputable def completeNone (agents : List A) (goods : List G) (base : G → Option A) (N : A → G → Prop)
    (d : A) (g : G) : A :=
  match base g with
  | some i => i
  | none => (LB.fill (slots agents goods base N) agents (junk goods base) g).getD d

/-- **If `ω ≤ 0`, there is a completion without owner** (and by `Completion.length_le_two` all its bundles
have at most two goods; by Theorem 1′₄ it is EFX₀, (OC₄) being empty): when every base has at most two goods
and `|J| ≤ S`, the junk fits the slots. -/
theorem complete_none_exists (hag : agents.Nodup) (hg : goods.Nodup)
    (hmem : ∀ g ∈ goods, ∀ i, base g = some i → i ∈ agents)
    (hB2 : ∀ j ∈ agents, (baseOf goods base j).length ≤ 2)
    (hω : ((junk goods base).length : Int) - capSum agents goods base N ≤ 0) (d : A) :
    Completion agents goods base N none (completeNone agents goods base N d) := by
  classical
  -- `S` is the number of slots
  have hS : capSum agents goods base N = ((agents.map (slots agents goods base N)).sum : Nat) := by
    unfold capSum
    rw [← sum_map_cast]
    congr 1
    apply List.map_congr_left
    intro j hj
    have := hB2 j hj
    by_cases hF : Frozen agents goods base N j
    · simp [cap, slots, hF]
    · simp only [cap, slots, hF, ↓reduceIte]; omega
  have hfit : (junk goods base).length ≤ (agents.map (slots agents goods base N)).sum := by omega
  have hplace : ∀ g ∈ goods, base g = none → ∃ j, LB.fill (slots agents goods base N) agents (junk goods base) g = some j :=
    fun g hgg hb => LB.fill_cover (mem_junk.mpr ⟨hgg, hb⟩) hfit
  -- a junk good of `j`'s bundle was placed with `j` by `fill`
  have hjunk : ∀ j, ∀ g ∈ junkOf goods base (completeNone agents goods base N d) j,
      LB.fill (slots agents goods base N) agents (junk goods base) g = some j := by
    intro j g hgC
    obtain ⟨hgg, hXg, hb⟩ := mem_junkOf.mp hgC
    obtain ⟨k, hk⟩ := hplace g hgg hb
    simp only [completeNone, hb, hk, Option.getD_some] at hXg
    rw [hk, hXg]
  refine ⟨fun g hgg => ?_, fun g _ i hb => (by simp [completeNone, hb]), fun w hw => (by cases hw),
    fun j _ _ hF => ?_, fun j _ _ hF => ?_⟩
  · cases hb : base g with
    | some i => simp only [completeNone, hb]; exact hmem g hgg i hb
    | none =>
      obtain ⟨k, hk⟩ := hplace g hgg hb
      simp only [completeNone, hb, hk, Option.getD_some]
      exact (LB.fill_some hk).1
  · -- a frozen agent has no slot, so `fill` gives it nothing
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro g hgC
    have := LB.fill_pos (hjunk j g hgC)
    simp [slots, hF] at this
  · have hc := LB.fill_count hag ((nodup_bundle hg _ j).sublist List.filter_sublist) (hjunk j)
    have := hB2 j (by assumption)
    simp only [slots, hF, ↓reduceIte] at hc
    unfold junkOf
    omega

end counting

/-! ## Lemma 2₄ (self-protection) -/

section selfProtect

omit [DecidableEq A] [DecidableEq G] in
/-- Irrelevant goods add nothing: a value is the value of the relevant part. -/
theorem value_filter_pos (i : A) : ∀ S : List G, value v i S = value v i (S.filter (fun g => 0 < v i g))
  | [] => by simp
  | g :: S => by
    rw [value_cons, value_filter_pos i S]
    by_cases hg : 0 < v i g
    · simp [hg]
    · simp [hg]; omega

omit [DecidableEq A] in
/-- Two distinct goods of a bundle are worth together at most the bundle. -/
theorem two_le_value {i : A} {y t : G} {S : List G} (hy : y ∈ S) (ht : t ∈ S) (hyt : y ≠ t) :
    v i y + v i t ≤ value v i S := by
  rw [value_erase (v := v) (i := i) hy]
  have := le_value_of_mem v i ((List.mem_erase_of_ne (Ne.symm hyt)).mpr ht)
  omega

omit [DecidableEq A] in
/-- **Lemma 2₄, its core (values only).** Let `x` value at most four goods of `goods`, hold `y` with
`v_x(y) > 0`, and let `Xo` be a bundle disjoint from `x`'s in which every good is worth at most `v_x(y)` to
`x`. Suppose every good of `Xo` that `x` values lies in `Bo` (at most one good) or in `U`, and either `x`
values no good of `U`, or `x` also holds a good `t ≠ y` it values, worth at least every good of `U`.
Then `x` does not envy `Xo`. -/
theorem selfProtect_core {x : A} {Xx Xo Bo U : List G} {y : G}
    (hR : (relevant v x goods).length ≤ 4)
    (hXo : Xo.Nodup) (hXog : ∀ g ∈ Xo, g ∈ goods) (hdisj : ∀ g ∈ Xo, g ∉ Xx)
    (hy : y ∈ Xx) (hyg : y ∈ goods) (hypos : 0 < v x y) (hbelow : ∀ g ∈ Xo, v x g ≤ v x y)
    (hBo : Bo.length ≤ 1) (hcov : ∀ g ∈ Xo, 0 < v x g → g ∈ Bo ∨ g ∈ U)
    (hslot : (∀ g ∈ U, v x g = 0) ∨
      ∃ t ∈ Xx, t ≠ y ∧ t ∈ goods ∧ 0 < v x t ∧ ∀ g ∈ U, v x g ≤ v x t) :
    value v x Xo ≤ value v x Xx := by
  have hyX : v x y ≤ value v x Xx := le_value_of_mem v x hy
  -- `L`: the goods of `Xo` that `x` values
  rw [value_filter_pos (v := v) x Xo]
  have hL : (Xo.filter (fun g => 0 < v x g)).Nodup := hXo.sublist List.filter_sublist
  have hLmem : ∀ g ∈ Xo.filter (fun g => 0 < v x g), g ∈ Xo ∧ 0 < v x g := fun g hg' => by
    simpa using List.mem_filter.mp hg'
  -- a list of at most one such good is worth at most `v_x(y)`
  have hone : (Xo.filter (fun g => 0 < v x g)).length ≤ 1 →
      value v x (Xo.filter (fun g => 0 < v x g)) ≤ value v x Xx := by
    intro h1
    match hLe : Xo.filter (fun g => 0 < v x g), h1 with
    | [], _ => simp
    | [p], _ =>
      have hp := (hLmem p (by rw [hLe]; simp)).1
      simp only [value_cons, value_nil, Nat.add_zero]
      exact Nat.le_trans (hbelow p hp) hyX
  rcases hslot with hU0 | ⟨t, ht, hty, htg, htpos, htmax⟩
  · -- `x` values nothing in `U`: its valued goods of `Xo` are in `Bo`
    apply hone
    refine Nat.le_trans (length_le_of_subset hL fun g hg' => ?_) hBo
    obtain ⟨hgXo, hgpos⟩ := hLmem g hg'
    rcases hcov g hgXo hgpos with h | h
    · exact h
    · have := hU0 g h; omega
  · -- `x` holds `y` and `t`; at most two of its (at most four) valued goods remain for `Xo`
    have hlen : (Xo.filter (fun g => 0 < v x g)).length + 2 ≤ 4 := by
      have hnd : (y :: t :: Xo.filter (fun g => 0 < v x g)).Nodup := by
        refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, hL⟩⟩
        · intro hm
          rcases List.mem_cons.mp hm with e | hm
          · exact hty e.symm
          · exact hdisj y (hLmem y hm).1 hy
        · intro hm; exact hdisj t (hLmem t hm).1 ht
      have := length_le_of_subset hnd (T := relevant v x goods) (fun g hg' => by
        unfold relevant
        rcases List.mem_cons.mp hg' with rfl | hg'
        · simpa using ⟨hyg, hypos⟩
        rcases List.mem_cons.mp hg' with rfl | hg'
        · simpa using ⟨htg, htpos⟩
        · obtain ⟨hgXo, hgpos⟩ := hLmem g hg'
          simpa using ⟨hXog g hgXo, hgpos⟩)
      simp only [List.length_cons] at this
      omega
    by_cases h1 : (Xo.filter (fun g => 0 < v x g)).length ≤ 1
    · exact hone h1
    -- two goods `p`, `q`: not both in `Bo`, so one is in `U` and worth at most `t`
    have hyt := two_le_value (v := v) (i := x) hy ht (Ne.symm hty)
    match hLe : Xo.filter (fun g => 0 < v x g), hlen, h1, hL with
    | [], _, h1, _ => simp at h1
    | [_], _, h1, _ => simp at h1
    | _ :: _ :: _ :: _, hlen, _, _ => simp at hlen
    | [p, q], _, _, hpq =>
      have hp := hLmem p (by rw [hLe]; simp)
      have hq := hLmem q (by rw [hLe]; simp)
      have hpq' : p ≠ q := by simp at hpq; exact hpq
      simp only [value_cons, value_nil, Nat.add_zero]
      have hbp := hbelow p hp.1
      have hbq := hbelow q hq.1
      rcases hcov p hp.1 hp.2 with hpB | hpU
      · rcases hcov q hq.1 hq.2 with hqB | hqU
        · have := length_le_of_subset (S := [p, q]) (by simp [hpq']) (fun g hg' => by
            rcases List.mem_cons.mp hg' with rfl | hg'
            · exact hpB
            · simp at hg'; rw [hg']; exact hqB)
          simp at this; omega
        · have := htmax q hqU; omega
      · have := htmax p hpU; omega

/-- **Lemma 2₄ (self-protection, `|R_x| ≤ 4`).** Let `(base, N)` be a valid pre-allocation (`N` the needs
used, so the owner's may be `N_o^X`) and `X` a completion with owner `w` whose base has at most one good.
Let `x ≠ w` be a listed agent with at most four relevant goods whose base is a pick `{y}` it values, and
whose needs contain the goods it ranks above `y` (its needs are those of a pick, for a strict order `≻_x`
consistent with its values). Let `U` be the junk not yet placed when `x` fills its slot: it contains every
junk good that ends in the owner's bundle (goods placed earlier went into other agents' slots, goods placed
later only leave the owner's bundle). Suppose `x` takes its `≻_x`-best good of `U` it values, if there is
one. Then `x` does not envy the owner's bundle; in particular it is not threatened by it. -/
theorem selfProtect {w : A} (hV : Valid agents goods base N)
    (hC : Completion agents goods base N (some w) X) (hBo : (baseOf goods base w).length ≤ 1)
    {x : A} (hx : x ∈ agents) (hxw : x ≠ w) (hR : (relevant v x goods).length ≤ 4)
    {y : G} (hBx : baseOf goods base x = [y]) (hy : 0 < v x y)
    {pref : A → G → G → Prop} (hrank : RankOK v pref x)
    (hNx : ∀ g, pickNeeds v goods pref y x g → N x g)
    {U : List G} (hUJ : ∀ g ∈ U, g ∈ junk goods base)
    (hU : ∀ g ∈ junk goods base, X g = w → g ∈ U)
    (hslot : (∃ g ∈ U, 0 < v x g) →
      ∃ t ∈ U, X t = x ∧ 0 < v x t ∧ ∀ g ∈ U, 0 < v x g → g ≠ t → pref x t g) (hg : goods.Nodup) :
    value v x (bundle goods X w) ≤ value v x (bundle goods X x) ∧
      ∀ h ∈ bundle goods X w, value v x ((bundle goods X w).erase h) ≤ value v x (bundle goods X x) := by
  have hyb : y ∈ baseOf goods base x := by rw [hBx]; simp
  obtain ⟨hyg, hby⟩ := mem_baseOf.mp hyb
  have hyX : y ∈ bundle goods X x := mem_bundle.mpr ⟨hyg, hC.onBase y hyg x hby⟩
  -- a good of the owner's bundle is junk or the owner's base good
  have hsrc : ∀ g ∈ bundle goods X w, g ∈ junk goods base ∨ g ∈ baseOf goods base w := by
    intro g hgb
    obtain ⟨hgg, hXg⟩ := mem_bundle.mp hgb
    cases hb : base g with
    | none => exact Or.inl (mem_junk.mpr ⟨hgg, hb⟩)
    | some k =>
      have := hC.onBase g hgg k hb
      rw [hXg] at this; subst this
      exact Or.inr (mem_baseOf.mpr ⟨hgg, hb⟩)
  -- no good of the owner's bundle is in `NA`: not junk (V1), and the owner's base good would freeze it
  have hnotNA : ∀ g ∈ bundle goods X w, ¬ NA agents N g := by
    intro g hgb hna
    rcases hsrc g hgb with hJ | hB
    · exact hV.v1 g hJ hna
    · have hB1 : baseOf goods base w = [g] := by
        match hB' : baseOf goods base w, hBo with
        | [], _ => rw [hB'] at hB; simp at hB
        | [z], _ => rw [hB'] at hB; simp at hB; rw [hB]
      exact (hC.owner w rfl).2 ⟨g, hB1, hna⟩
  have hmain : value v x (bundle goods X w) ≤ value v x (bundle goods X x) := by
    refine selfProtect_core (Bo := baseOf goods base w) (U := U) hR (nodup_bundle hg X w)
      (fun g hgb => (mem_bundle.mp hgb).1) (fun g hgw hgx => hxw ((mem_bundle.mp hgx).2.symm.trans
        (mem_bundle.mp hgw).2)) hyX hyg hy (fun g hgb => ?_) hBo (fun g hgb hpos => ?_) ?_
    · -- the goods `x` ranks above `y` are in `NA`, so not in the owner's bundle
      refine Nat.le_of_not_lt fun hlt => hnotNA g hgb ⟨x, hx, hNx g ⟨(mem_bundle.mp hgb).1, ?_, ?_⟩⟩
      · omega
      · exact hrank.consistent g y hy hlt
    · rcases hsrc g hgb with hJ | hB
      · exact Or.inr (hU g hJ (mem_bundle.mp hgb).2)
      · exact Or.inl hB
    · by_cases hex : ∃ g ∈ U, 0 < v x g
      · obtain ⟨t, htU, hXt, htpos, hbest⟩ := hslot hex
        obtain ⟨htg, hbt⟩ := mem_junk.mp (hUJ t htU)
        refine Or.inr ⟨t, mem_bundle.mpr ⟨htg, hXt⟩, fun e => ?_, htg, htpos, fun g hgU => ?_⟩
        · rw [e, hby] at hbt; cases hbt
        · by_cases hgpos : 0 < v x g
          · by_cases hgt : g = t
            · rw [hgt]; exact Nat.le_refl _
            · exact Nat.le_of_not_lt fun hlt =>
                hrank.asymm t g (hbest g hgU hgpos hgt) (hrank.consistent g t htpos hlt)
          · omega
      · exact Or.inl fun g hgU => Nat.eq_zero_of_not_pos fun hpos => hex ⟨g, hgU, hpos⟩
  exact ⟨hmain, fun h _ => Nat.le_trans (value_sublist v x List.erase_sublist) hmain⟩

/-- Sequential slot filling (`k4/lb4.md` Lemma 2₄): the agents of `xs` in turn each take the good
`choose x pool` (if any) from `pool`, the junk not yet placed. The result lists the placements `(x, t)`. -/
def seqFill (choose : A → List G → Option G) : List A → List G → List (A × G)
  | [], _ => []
  | x :: xs, pool =>
    match choose x pool with
    | none => seqFill choose xs pool
    | some t => (x, t) :: seqFill choose xs (pool.erase t)

omit [DecidableEq A] in
theorem seqFill_agent {choose : A → List G → Option G} :
    ∀ {xs : List A} {pool : List G} {p : A × G}, p ∈ seqFill choose xs pool → p.1 ∈ xs
  | [], _, _, h => by simp [seqFill] at h
  | x :: xs, pool, p, h => by
    unfold seqFill at h
    split at h
    · exact List.mem_cons_of_mem x (seqFill_agent h)
    · rcases List.mem_cons.mp h with rfl | h
      · simp
      · exact List.mem_cons_of_mem x (seqFill_agent h)

omit [DecidableEq A] in
/-- At the turn of each agent `x` of `xs` the pool `P` contains every good of the initial pool that the
fill never places, `P` is part of the initial pool, and `x` places the good `choose x P` (if any). -/
theorem seqFill_pool {choose : A → List G → Option G} :
    ∀ {xs : List A} {pool : List G} {x : A}, x ∈ xs → ∃ P : List G,
      (∀ g ∈ pool, (∀ y, (y, g) ∉ seqFill choose xs pool) → g ∈ P) ∧ (∀ g ∈ P, g ∈ pool) ∧
      ∀ t, choose x P = some t → (x, t) ∈ seqFill choose xs pool
  | [], _, _, hx => by simp at hx
  | x₀ :: xs, pool, x, hx => by
    by_cases hx₀ : x = x₀
    · subst hx₀
      refine ⟨pool, fun g hg _ => hg, fun g hg => hg, fun t ht => ?_⟩
      unfold seqFill; rw [ht]; simp
    have hxs : x ∈ xs := (List.mem_cons.mp hx).resolve_left hx₀
    cases hc : choose x₀ pool with
    | none =>
      obtain ⟨P, h1, h2, h3⟩ := seqFill_pool (choose := choose) (pool := pool) hxs
      refine ⟨P, fun g hg hno => h1 g hg (fun y hy => hno y ?_), h2, fun t ht => ?_⟩
      · unfold seqFill; rw [hc]; exact hy
      · unfold seqFill; rw [hc]; exact h3 t ht
    | some t₀ =>
      obtain ⟨P, h1, h2, h3⟩ := seqFill_pool (choose := choose) (pool := pool.erase t₀) hxs
      have hunf : seqFill choose (x₀ :: xs) pool = (x₀, t₀) :: seqFill choose xs (pool.erase t₀) := by
        simp only [seqFill, hc]
      refine ⟨P, fun g hg hno => h1 g ?_ (fun y hy => hno y ?_), fun g hg => List.mem_of_mem_erase (h2 g hg),
        fun t ht => ?_⟩
      · have : g ≠ t₀ := fun e => hno x₀ (by rw [hunf, e]; simp)
        exact (List.mem_erase_of_ne this).mpr hg
      · rw [hunf]; exact List.mem_cons_of_mem _ hy
      · rw [hunf]; exact List.mem_cons_of_mem _ (h3 t ht)

/-- **Lemma 2₄ for the sequential fill.** Let the agents of `xs` (not the owner `w`) fill their slots one at a
time from the pool `pool` of junk goods, each taking its `≻`-best valued good of the pool if it has one
(`hchoose`), and let `X` give each placed good to its placer and every other junk good of the owner's bundle
come from `pool` (goods placed before the fill went into other agents' slots; whatever is placed after only
leaves the owner's bundle). Then no agent `x` of `xs` with at most four relevant goods, a pick base `{y}` it
values and the needs of a pick envies the owner's bundle. -/
theorem selfProtect_seq {w : A} (hV : Valid agents goods base N)
    (hC : Completion agents goods base N (some w) X) (hBo : (baseOf goods base w).length ≤ 1)
    {pref : A → G → G → Prop} {choose : A → List G → Option G}
    (hchoose : ∀ x P, (∃ g ∈ P, 0 < v x g) →
      ∃ t, choose x P = some t ∧ t ∈ P ∧ 0 < v x t ∧ ∀ g ∈ P, 0 < v x g → g ≠ t → pref x t g)
    {xs : List A} (hwxs : w ∉ xs) {pool : List G} (hpool : ∀ g ∈ pool, g ∈ junk goods base)
    (hplace : ∀ p ∈ seqFill choose xs pool, X p.2 = p.1)
    (hrest : ∀ g ∈ junk goods base, X g = w → g ∈ pool)
    {x : A} (hxs : x ∈ xs) (hx : x ∈ agents) (hR : (relevant v x goods).length ≤ 4)
    {y : G} (hBx : baseOf goods base x = [y]) (hy : 0 < v x y) (hrank : RankOK v pref x)
    (hNx : ∀ g, pickNeeds v goods pref y x g → N x g) (hg : goods.Nodup) :
    value v x (bundle goods X w) ≤ value v x (bundle goods X x) ∧
      ∀ h ∈ bundle goods X w, value v x ((bundle goods X w).erase h) ≤ value v x (bundle goods X x) := by
  obtain ⟨P, h1, h2, h3⟩ := seqFill_pool (choose := choose) (pool := pool) hxs
  refine selfProtect hV hC hBo hx (fun e => hwxs (e ▸ hxs)) hR hBx hy hrank hNx
    (U := P) (fun g hg => hpool g (h2 g hg)) (fun g hgJ hXg => ?_) (fun hex => ?_) hg
  · -- a junk good of the owner's bundle was never placed by the fill, so it is still in `x`'s pool
    refine h1 g (hrest g hgJ hXg) (fun z hz => ?_)
    have hXz := hplace _ hz
    have hzxs := seqFill_agent hz
    simp only at hXz hzxs
    rw [hXg] at hXz
    exact hwxs (hXz ▸ hzxs)
  · obtain ⟨t, hct, htP, htpos, hbest⟩ := hchoose x P hex
    exact ⟨t, htP, hplace _ (h3 t hct), htpos, hbest⟩

/-- The value argument of Lemma 2₄ fails with five relevant goods (`k4/lb4.md` §1): `x` values goods `0, …, 4`
at `10, 9, 8, 7, 6` and good `5` at `0`, holds `{0, 1}` (its pick `0` and its best junk good `1`), and the
owner holds `{2, 3, 4, 5}`. Every good of the owner's bundle is worth at most `x`'s pick and at most `t = 1`,
`x` values five goods, and `x` is threatened: without good `5` the owner's bundle is worth `21 > 19`. (This
is the values only; `Ex5.counterexample` is a full instance of `selfProtect`'s other hypotheses.) -/
theorem selfProtect_five :
    let v : Unit → Fin 6 → Nat := fun _ g => if g.val < 5 then 10 - g.val else 0
    (relevant v () (List.finRange 6)).length = 5 ∧
      (∀ g ∈ ([2, 3, 4, 5] : List (Fin 6)), v () g ≤ v () 0 ∧ v () g ≤ v () 1) ∧
      value v () [0, 1] < value v () (([2, 3, 4, 5] : List (Fin 6)).erase 5) := by
  decide

end selfProtect

/-! ## Lemma 3₄ (the owner search is exact) -/

section ownerSearch

omit [DecidableEq G] in
theorem filter_sublist_of_imp {p q : G → Bool} :
    ∀ {l : List G}, (∀ g ∈ l, p g = true → q g = true) → (l.filter p).Sublist (l.filter q)
  | [], _ => by simp
  | g :: l, h => by
    have ih := filter_sublist_of_imp (l := l) (fun g' hg' => h g' (by simp [hg']))
    by_cases hp : p g = true
    · have hq := h g (by simp) hp
      simp only [List.filter_cons, hp, hq, ↓reduceIte]
      exact ih.cons_cons g
    · by_cases hq : q g = true
      · simp only [List.filter_cons, hp, hq, ↓reduceIte, Bool.false_eq_true]
        exact ih.cons g
      · simp only [List.filter_cons, hp, hq, ↓reduceIte, Bool.false_eq_true]
        exact ih

theorem sum_le_sum_of_le {α : Type} (f g : α → Nat) :
    ∀ l : List α, (∀ a ∈ l, f a ≤ g a) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    have := sum_le_sum_of_le f g l (fun b hb => h b (by simp [hb]))
    have := h a (by simp)
    omega

theorem exists_lt_of_sum_lt {α : Type} (f g : α → Nat) (l : List α)
    (h : (l.map f).sum < (l.map g).sum) : ∃ a ∈ l, f a < g a :=
  Classical.byContradiction fun hno =>
    Nat.not_le_of_lt h (sum_le_sum_of_le g f l fun a ha =>
      Nat.le_of_not_lt fun hlt => hno ⟨a, ha, hlt⟩)

/-- Splitting a sum over distinct agents into `w`'s term and the others'. -/
theorem sum_split (f : A → Nat) {w : A} :
    ∀ {l : List A}, l.Nodup → w ∈ l → (l.map f).sum = f w + (l.map (fun j => if j = w then 0 else f j)).sum
  | [], _, hw => by simp at hw
  | a :: l, hl, hw => by
    obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
    simp only [List.map_cons, List.sum_cons]
    by_cases haw : a = w
    · subst haw
      have : (l.map (fun j => if j = a then 0 else f j)) = l.map f :=
        List.map_congr_left fun j hj => by simp [show j ≠ a from fun e => ha (e ▸ hj)]
      rw [this]; simp
    · rw [sum_split f hl' ((List.mem_cons.mp hw).resolve_left (Ne.symm haw))]
      simp [haw]; omega

open Classical in
/-- `s`: the slots of the listed agents other than `w`, frozen agents computed with the needs `M` (the text's
`s₀` takes the owner's needs from its base). -/
noncomputable def otherSlots (agents : List A) (goods : List G) (base : G → Option A) (M : A → G → Prop)
    (w : A) : Nat :=
  (agents.map (fun j => if j = w ∨ Frozen agents goods base M j then 0 else 2 - (baseOf goods base j).length)).sum

/-- Move the good `ℓ` to agent `x`. -/
def moveTo (X : G → A) (ℓ : G) (x : A) : G → A := fun g => if g = ℓ then x else X g

section move
variable {w x : A} {ℓ : G}

theorem bundle_moveTo_other (hℓ : X ℓ = w) {j : A} (hjw : j ≠ w) (hjx : j ≠ x) :
    bundle goods (moveTo X ℓ x) j = bundle goods X j := by
  unfold bundle moveTo
  apply List.filter_congr
  intro g _
  by_cases hg : g = ℓ
  · subst hg; simp [hℓ, Ne.symm hjx, Ne.symm hjw]
  · simp [hg]

theorem bundle_moveTo_owner (hℓ : X ℓ = w) (hxw : x ≠ w) :
    (bundle goods (moveTo X ℓ x) w).Sublist (bundle goods X w) := by
  unfold bundle
  apply filter_sublist_of_imp
  intro g _ h
  unfold moveTo at h
  by_cases hg : g = ℓ
  · subst hg; simp [hxw] at h
  · simpa [hg] using h

theorem bundle_moveTo_x :
    (bundle goods X x).Sublist (bundle goods (moveTo X ℓ x) x) := by
  unfold bundle
  apply filter_sublist_of_imp
  intro g _ h
  unfold moveTo
  by_cases hg : g = ℓ
  · subst hg; simp
  · simpa [hg] using h

/-- The owner's bundle after the move is its bundle without `ℓ`. -/
theorem value_moveTo_owner (hg : goods.Nodup) (hℓg : ℓ ∈ goods) (hℓ : X ℓ = w) (hxw : x ≠ w) (i : A) :
    value v i (bundle goods (moveTo X ℓ x) w) + v i ℓ = value v i (bundle goods X w) := by
  have e : bundle goods (moveTo X ℓ x) w = (bundle goods X w).erase ℓ := by
    rw [List.Nodup.erase_eq_filter (nodup_bundle hg X w)]
    unfold bundle moveTo
    rw [List.filter_filter]
    apply List.filter_congr
    intro g _
    by_cases hgl : g = ℓ
    · subst hgl; simp [hxw]
    · simp [hgl]
  rw [e, value_erase (v := v) (i := i) (mem_bundle.mpr ⟨hℓg, hℓ⟩)]
  omega

omit [DecidableEq G] in
/-- Counting the junk goods of a bundle as a `countP` over the goods. -/
theorem junkOf_length (j : A) (Y : G → A) :
    (junkOf goods base Y j).length = goods.countP (fun g => decide (Y g = j) && decide (base g = none)) := by
  rw [junkOf, bundle, List.filter_filter, List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro g _
  simp [Bool.and_comm]

/-- A `countP` over distinct goods, when the predicate changes at one good `ℓ` only. -/
theorem countP_change {p q : G → Bool} (hg : goods.Nodup) (hℓ : ℓ ∈ goods)
    (hpq : ∀ g ∈ goods, g ≠ ℓ → p g = q g) :
    goods.countP p + (if q ℓ then 1 else 0) = goods.countP q + (if p ℓ then 1 else 0) := by
  have hperm := List.perm_cons_erase hℓ
  rw [hperm.countP_eq p, hperm.countP_eq q, List.countP_cons, List.countP_cons]
  have : (goods.erase ℓ).countP p = (goods.erase ℓ).countP q := by
    apply List.countP_congr
    intro g hg'
    have hne : g ≠ ℓ := fun e => by
      subst e; exact (List.Nodup.mem_erase_iff hg).mp hg' |>.1 rfl
    rw [hpq g (List.mem_of_mem_erase hg') hne]
  rw [this]
  omega

theorem junkOf_moveTo_x (hg : goods.Nodup) (hℓg : ℓ ∈ goods) (hℓ : X ℓ = w) (hxw : x ≠ w)
    (hbℓ : base ℓ = none) :
    (junkOf goods base (moveTo X ℓ x) x).length = (junkOf goods base X x).length + 1 := by
  rw [junkOf_length, junkOf_length]
  have := countP_change (goods := goods) (ℓ := ℓ)
    (p := fun g => decide (X g = x) && decide (base g = none))
    (q := fun g => decide (moveTo X ℓ x g = x) && decide (base g = none)) hg hℓg
    (fun g _ hgl => by simp [moveTo, hgl])
  have hq : (decide (moveTo X ℓ x ℓ = x) && decide (base ℓ = none)) = true := by simp [moveTo, hbℓ]
  have hp : (decide (X ℓ = x) && decide (base ℓ = none)) = false := by simp [hℓ, Ne.symm hxw]
  simp only [hq, hp, ↓reduceIte, Bool.false_eq_true] at this
  omega

theorem junkOf_moveTo_owner (hg : goods.Nodup) (hℓg : ℓ ∈ goods) (hℓ : X ℓ = w) (hxw : x ≠ w)
    (hbℓ : base ℓ = none) :
    (junkOf goods base (moveTo X ℓ x) w).length + 1 = (junkOf goods base X w).length := by
  rw [junkOf_length, junkOf_length]
  have := countP_change (goods := goods) (ℓ := ℓ)
    (p := fun g => decide (X g = w) && decide (base g = none))
    (q := fun g => decide (moveTo X ℓ x g = w) && decide (base g = none)) hg hℓg
    (fun g _ hgl => by simp [moveTo, hgl])
  have hq : (decide (moveTo X ℓ x ℓ = w) && decide (base ℓ = none)) = false := by simp [moveTo, hxw]
  have hp : (decide (X ℓ = w) && decide (base ℓ = none)) = true := by simp [hℓ, hbℓ]
  simp only [hq, hp, ↓reduceIte, Bool.false_eq_true] at this
  omega

end move

omit [DecidableEq G] in
theorem junkOf_length_le (j : A) : (junkOf goods base X j).length ≤ (junk goods base).length := by
  rw [junkOf_length, junk, ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro g _ h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  simpa using h.2

omit [DecidableEq G] in
theorem ownerNeeds_ext {X' : G → A} {w : A} (h : ∀ g, ownerNeeds v goods X' N (some w) w g ↔ ownerNeeds v goods X N (some w) w g) :
    ownerNeeds v goods X' N (some w) = ownerNeeds v goods X N (some w) := by
  funext i g
  apply propext
  by_cases hiw : i = w
  · subst hiw; exact h g
  · have : (some w = some i) = False := by simp [Ne.symm hiw]
    simp [ownerNeeds, this]

/-- **One step of Lemma 3₄.** If the other agents' junk goods fill fewer than `s` slots (`s` at most the other
agents' slots, frozen agents computed with needs `M` whose frozen agents include those of `N_o^X`) and the
owner has a junk good, one junk good of the owner's bundle can be moved into a free slot so that the result is again a
sound completion with the same owner's needs `N_o^X` (hence the same frozen agents and slots). -/
theorem move_step {w : A} {M : A → G → Prop} {s : Nat} (hag : agents.Nodup) (hg : goods.Nodup)
    (hS : SoundCompletion v agents goods base N (some w) X)
    (hM : ∀ j, Frozen agents goods base (ownerNeeds v goods X N (some w)) j → Frozen agents goods base M j)
    (hs : s ≤ otherSlots agents goods base M w)
    (hbal : ∀ g ∈ goods, 0 < v w g → 2 * v w g < value v w goods)
    (hR4 : (relevant v w goods).length ≤ 4)
    (hBR : ∀ g ∈ baseOf goods base w, 0 < v w g)
    (hbig : 3 ≤ (baseOf goods base w).length ∨
      3 + s ≤ (baseOf goods base w).length + (junk goods base).length)
    (hlt : (junk goods base).length - (junkOf goods base X w).length < s)
    (hpos : 0 < (junkOf goods base X w).length) :
    ∃ X' : G → A, SoundCompletion v agents goods base N (some w) X' ∧
      ownerNeeds v goods X' N (some w) = ownerNeeds v goods X N (some w) ∧
      (junkOf goods base X' w).length + 1 = (junkOf goods base X w).length := by
  classical
  have hC := hS.completion
  have hw := hC.owner w rfl
  have hJC := junkOf_length_le (goods := goods) (base := base) (X := X) w
  -- 1. a free agent `x ≠ w` with an unused slot
  have hsumC : (agents.map (fun j => if j = w then 0 else (junkOf goods base X j).length)).sum +
      (junkOf goods base X w).length = (junk goods base).length := by
    rw [hC.junk_length hag, sum_split (fun j => (junkOf goods base X j).length) hag hw.1]; omega
  have hsl : otherSlots agents goods base M w ≤ (agents.map (fun j =>
      if j = w ∨ Frozen agents goods base (ownerNeeds v goods X N (some w)) j then 0
      else 2 - (baseOf goods base j).length)).sum := by
    apply sum_le_sum_of_le
    intro j _
    by_cases h1 : j = w ∨ Frozen agents goods base M j
    · simp [h1]
    · have h2 : ¬ (j = w ∨ Frozen agents goods base (ownerNeeds v goods X N (some w)) j) :=
        fun h => h1 (h.imp id (hM j))
      simp [h1, h2]
  obtain ⟨x, hx, hxlt⟩ := exists_lt_of_sum_lt
    (fun j => if j = w then 0 else (junkOf goods base X j).length) _ agents
    (Nat.lt_of_lt_of_le (by omega) hsl)
  have hxw : x ≠ w := fun e => by simp [e] at hxlt
  have hxF : ¬ Frozen agents goods base (ownerNeeds v goods X N (some w)) x := fun h => by simp [h] at hxlt
  have hxslot : (junkOf goods base X x).length + (baseOf goods base x).length + 1 ≤ 2 := by
    simp only [hxw, hxF, or_self, ↓reduceIte] at hxlt; omega
  -- 2. a good `ℓ` to move: worthless to the owner, or else the owner holds all its relevant goods
  have hlen := hC.length_eq w
  obtain ⟨ℓ, hℓC, hℓcase⟩ : ∃ ℓ ∈ junkOf goods base X w,
      v w ℓ = 0 ∨ (0 < v w ℓ ∧ ∀ g ∈ goods, 0 < v w g → X g = w) := by
    by_cases h0 : ∃ ℓ ∈ junkOf goods base X w, v w ℓ = 0
    · obtain ⟨ℓ, hℓ, h⟩ := h0; exact ⟨ℓ, hℓ, Or.inl h⟩
    · obtain ⟨ℓ, hℓ⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos hpos)
      refine ⟨ℓ, hℓ, Or.inr ⟨Nat.pos_of_ne_zero fun e => h0 ⟨ℓ, hℓ, e⟩, fun g hgg hgpos => ?_⟩⟩
      refine Classical.byContradiction fun hXg => ?_
      -- otherwise the owner's bundle lies in `R_w ∖ {g}`, which has at most three goods
      have hsub := length_le_of_subset (S := g :: bundle goods X w) (T := relevant v w goods)
        (List.nodup_cons.mpr ⟨fun hm => hXg (mem_bundle.mp hm).2, nodup_bundle hg X w⟩) (fun h hh => by
          unfold relevant
          rcases List.mem_cons.mp hh with rfl | hh
          · simpa using ⟨hgg, hgpos⟩
          obtain ⟨hhg, hXh⟩ := mem_bundle.mp hh
          cases hbh : base h with
          | none =>
            have hJ : h ∈ junkOf goods base X w := mem_junkOf.mpr ⟨hhg, hXh, hbh⟩
            simpa using ⟨hhg, Nat.pos_of_ne_zero fun e => h0 ⟨h, hJ, e⟩⟩
          | some k =>
            have := hC.onBase h hhg k hbh
            rw [hXh] at this; subst this
            simpa using ⟨hhg, hBR h (mem_baseOf.mpr ⟨hhg, hbh⟩)⟩)
      simp only [List.length_cons] at hsub
      rcases hbig with hb | hb <;> omega
  obtain ⟨hℓg, hXℓ, hbℓ⟩ := mem_junkOf.mp hℓC
  -- 3. the owner's needs `N_o^X` do not change
  have hval := value_moveTo_owner (v := v) (x := x) hg hℓg hXℓ hxw w
  have hON : ownerNeeds v goods (moveTo X ℓ x) N (some w) = ownerNeeds v goods X N (some w) := by
    apply ownerNeeds_ext
    intro g
    simp only [ownerNeeds, ↓reduceIte]
    rcases hℓcase with h0 | ⟨hℓpos, hall⟩
    · by_cases hgl : g = ℓ
      · subst hgl; simp [h0, hXℓ]
      · simp only [moveTo, hgl, ↓reduceIte]; rw [h0] at hval; rw [Nat.add_zero] at hval; rw [hval]
    · -- both are empty: the owner holds every good it values, and keeps more than `ℓ` without it
      have hgoods : value v w goods ≤ value v w (bundle goods X w) := by
        rw [value_filter_pos (v := v) w goods]
        apply value_sublist
        unfold bundle
        apply filter_sublist_of_imp
        intro g hg' h
        simp only [decide_eq_true_eq] at h ⊢
        exact hall g hg' h
      have := hbal ℓ hℓg hℓpos
      constructor
      · rintro ⟨hgg, hXg, hlt⟩
        by_cases hgl : g = ℓ
        · subst hgl; omega
        · simp only [moveTo, hgl, ↓reduceIte] at hXg
          exact absurd (hall g hgg (by omega)) hXg
      · rintro ⟨hgg, hXg, hlt⟩
        exact absurd (hall g hgg (by omega)) hXg
  -- 4. the moved allocation is a sound completion
  refine ⟨moveTo X ℓ x, ⟨hS.needs, hON ▸ hS.valid, ?_, ?_⟩, hON,
    junkOf_moveTo_owner hg hℓg hXℓ hxw hbℓ⟩
  · rw [hON]
    refine ⟨fun g hg' => ?_, fun g hg' i hb => ?_, hC.owner, fun j hj hjo hF => ?_,
      fun j hj hjo hF => ?_⟩
    · unfold moveTo; split
      · exact hx
      · exact hC.alloc g hg'
    · have : g ≠ ℓ := fun e => by rw [e, hbℓ] at hb; cases hb
      simp only [moveTo, this, ↓reduceIte]; exact hC.onBase g hg' i hb
    · have hjw : j ≠ w := fun e => hjo (by rw [e])
      have hjx : j ≠ x := fun e => hxF (e ▸ hF)
      unfold junkOf; rw [bundle_moveTo_other hXℓ hjw hjx]
      exact hC.frozen j hj hjo hF
    · have hjw : j ≠ w := fun e => hjo (by rw [e])
      by_cases hjx : j = x
      · subst hjx
        rw [junkOf_moveTo_x hg hℓg hXℓ hxw hbℓ]; omega
      · unfold junkOf; rw [bundle_moveTo_other hXℓ hjw hjx]
        exact hC.free j hj hjo hF
  · intro w' hw' j hj hjw h hh
    cases hw'
    have hsubw := bundle_moveTo_owner (goods := goods) hXℓ hxw
    have hle1 : value v j ((bundle goods (moveTo X ℓ x) w).erase h) ≤ value v j ((bundle goods X w).erase h) :=
      value_sublist v j (hsubw.erase h)
    have hle2 := hS.oc w rfl j hj hjw h (hsubw.subset hh)
    have hle3 : value v j (bundle goods X j) ≤ value v j (bundle goods (moveTo X ℓ x) j) := by
      by_cases hjx : j = x
      · subst hjx; exact value_sublist v j bundle_moveTo_x
      · rw [bundle_moveTo_other hXℓ hjw hjx]; exact Nat.le_refl _
    omega

/-- **Lemma 3₄ (the owner search is exact), general form.** Let `X` be a sound completion with owner `w`,
where `w` is strictly balanced (`2 v_w(g) < v_w(M)` for every good it values), values at most four goods
and every good of its base. Let `s` be at most the slots of the other agents, the frozen agents computed
with needs `M` whose frozen agents include those of `N_o^X` (`M = N`, the owner's needs from its base,
and `s` all those slots give the text's `s₀`, `ownerSearch_exact_base`; a smaller `s` covers `k4/lb4.c`'s
`s₀`, which gives a rotated agent no slot). Suppose `|B_w| ≥ 3`, or `|B_w| + |J| ≥ s + 3` (with
`|J| = s + cap(w) + ω` this is `ω ≥ 1` when `|B_w| + cap(w) = 2`). Then some sound completion `X'` with the
same owner's needs `N_o^X` puts at least `min(|J|, s)` junk goods into the other agents' slots
(`|C| = |J| − |C_w|`). -/
theorem ownerSearch_exact {w : A} {M : A → G → Prop} {s : Nat} (hag : agents.Nodup) (hg : goods.Nodup)
    (hS : SoundCompletion v agents goods base N (some w) X)
    (hM : ∀ j, Frozen agents goods base (ownerNeeds v goods X N (some w)) j → Frozen agents goods base M j)
    (hs : s ≤ otherSlots agents goods base M w)
    (hbal : ∀ g ∈ goods, 0 < v w g → 2 * v w g < value v w goods)
    (hR4 : (relevant v w goods).length ≤ 4)
    (hBR : ∀ g ∈ baseOf goods base w, 0 < v w g)
    (hbig : 3 ≤ (baseOf goods base w).length ∨
      3 + s ≤ (baseOf goods base w).length + (junk goods base).length) :
    ∃ X' : G → A, SoundCompletion v agents goods base N (some w) X' ∧
      ownerNeeds v goods X' N (some w) = ownerNeeds v goods X N (some w) ∧
      min (junk goods base).length s ≤ (junk goods base).length - (junkOf goods base X' w).length := by
  suffices h : ∀ n (X : G → A), (junkOf goods base X w).length = n →
      SoundCompletion v agents goods base N (some w) X →
      (∀ j, Frozen agents goods base (ownerNeeds v goods X N (some w)) j → Frozen agents goods base M j) →
      ∃ X' : G → A, SoundCompletion v agents goods base N (some w) X' ∧
        ownerNeeds v goods X' N (some w) = ownerNeeds v goods X N (some w) ∧
        min (junk goods base).length s ≤ (junk goods base).length - (junkOf goods base X' w).length
    from h _ X rfl hS hM
  intro n
  induction n with
  | zero => intro X hn hS _; exact ⟨X, hS, rfl, by rw [hn]; omega⟩
  | succ n ih =>
    intro X hn hS hM
    by_cases hdone : min (junk goods base).length s ≤ (junk goods base).length - (n + 1)
    · exact ⟨X, hS, rfl, by rw [hn]; exact hdone⟩
    · obtain ⟨X₁, hS₁, hON₁, hlen₁⟩ :=
        move_step hag hg hS hM hs hbal hR4 hBR hbig (by omega) (by omega)
      obtain ⟨X', hS', hON', hmin⟩ := ih X₁ (by omega) hS₁ (by rw [hON₁]; exact hM)
      exact ⟨X', hS', hON'.trans hON₁, hmin⟩

/-- Sums over distinct agents split into `w`'s term and the others' (integer version). -/
theorem sum_split_int (f : A → Int) {w : A} :
    ∀ {l : List A}, l.Nodup → w ∈ l → (l.map f).sum = f w + (l.map (fun j => if j = w then 0 else f j)).sum
  | [], _, hw => by simp at hw
  | a :: l, hl, hw => by
    obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
    simp only [List.map_cons, List.sum_cons]
    by_cases haw : a = w
    · subst haw
      have : (l.map (fun j => if j = a then 0 else f j)) = l.map f :=
        List.map_congr_left fun j hj => by simp [show j ≠ a from fun e => ha (e ▸ hj)]
      rw [this]; simp
    · rw [sum_split_int f hl' ((List.mem_cons.mp hw).resolve_left (Ne.symm haw))]
      simp [haw]; omega

omit [DecidableEq G] in
open Classical in
/-- When every other agent's base has at most two goods, `S = s + cap(w)`: the slots of the others are
their caps. -/
theorem otherSlots_add_cap {w : A} {M : A → G → Prop} (hag : agents.Nodup) (hw : w ∈ agents)
    (hB2 : ∀ j ∈ agents, j ≠ w → (baseOf goods base j).length ≤ 2) :
    (otherSlots agents goods base M w : Int) + cap agents goods base M w = capSum agents goods base M := by
  unfold capSum otherSlots
  rw [sum_split_int (cap agents goods base M) hag hw, ← sum_map_cast]
  have : agents.map (fun j => (((if j = w ∨ Frozen agents goods base M j then 0
      else 2 - (baseOf goods base j).length : Nat)) : Int)) =
      agents.map (fun j => if j = w then 0 else cap agents goods base M j) := by
    apply List.map_congr_left
    intro j hj
    by_cases hjw : j = w
    · simp [hjw]
    · have := hB2 j hj hjw
      by_cases hF : Frozen agents goods base M j
      · simp [hjw, hF, cap]
      · simp only [hjw, hF, or_self, ↓reduceIte, cap]; omega
  rw [this]; omega

open Classical in
/-- **Lemma 3₄, in the text's terms.** Let `X` be a sound completion with owner `w`, whose needs from its base
`N w` are needs in the Definition's sense; `w` strictly balanced, with at most four relevant goods and its
base among them. Let `s₀` be the slots of the other agents with the owner's needs from its base
(`otherSlots … N w`). Suppose either `|B_w| ≥ 3` (a rotated agent with `|O| ≥ 3`), or `w` is free with its
needs from its base, every other agent's base has at most two goods, and `ω ≥ 1` (`ω = |J| − S`, `S` with the
owner's needs from its base). Then some sound completion with the same `N_o^X` has at least `min(|J|, s₀)`
slot goods. -/
theorem ownerSearch_exact_base {w : A} (hag : agents.Nodup) (hg : goods.Nodup)
    (hS : SoundCompletion v agents goods base N (some w) X) (hNw : Needs v goods base N w)
    (hbal : ∀ g ∈ goods, 0 < v w g → 2 * v w g < value v w goods)
    (hR4 : (relevant v w goods).length ≤ 4)
    (hBR : ∀ g ∈ baseOf goods base w, 0 < v w g)
    (hcase : 3 ≤ (baseOf goods base w).length ∨
      (¬ Frozen agents goods base N w ∧ (∀ j ∈ agents, j ≠ w → (baseOf goods base j).length ≤ 2) ∧
        1 ≤ ((junk goods base).length : Int) - capSum agents goods base N)) :
    ∃ X' : G → A, SoundCompletion v agents goods base N (some w) X' ∧
      ownerNeeds v goods X' N (some w) = ownerNeeds v goods X N (some w) ∧
      min (junk goods base).length (otherSlots agents goods base N w) ≤
        (junk goods base).length - (junkOf goods base X' w).length := by
  have hw := (hS.completion.owner w rfl).1
  have hNd : ∀ i ∈ agents, Needs v goods base N i := fun i hi => by
    by_cases hiw : i = w
    · subst hiw; exact hNw
    · exact hS.needs i hi (fun e => hiw (Option.some.inj e).symm)
  refine ownerSearch_exact hag hg hS (fun j ⟨y, hy, i, hi, hN⟩ =>
    ⟨y, hy, i, hi, ownerNeeds_le hS.completion.onBase hNd i hi y hN⟩) (Nat.le_refl _) hbal hR4 hBR ?_
  rcases hcase with h3 | ⟨hwF, hB2, hω⟩
  · exact Or.inl h3
  · right
    have e := otherSlots_add_cap (M := N) (base := base) (goods := goods) hag hw hB2
    have hc : cap agents goods base N w = 2 - ((baseOf goods base w).length : Int) := by
      unfold cap; simp [hwF]
    omega

end ownerSearch


end LB4

/-! ## A non-vacuity example -/

namespace LB4.Ex

/-- Two agents, five goods: agent 0 values them `4, 3, 2, 2, 0`, agent 1 values them `3, 1, 1, 1, 1`. -/
def v : Fin 2 → Fin 5 → Nat := fun i g => if i.val = 0 then [4, 3, 2, 2, 0][g.val]! else [3, 1, 1, 1, 1][g.val]!

/-- Good 0 is agent 0's pick; goods 1–4 are junk; agent 1 has an empty base. -/
def base : Fin 5 → Option (Fin 2) := fun g => if g.val = 0 then some 0 else none

/-- Agent 0 takes good 1 into its slot; the owner, agent 1, takes goods 2, 3, 4. -/
def X : Fin 5 → Fin 2 := fun g => if g.val ≤ 1 then 0 else 1

/-- Agent 0's needs are those of its pick, its top good: none. -/
abbrev N : Fin 2 → Fin 5 → Prop := fun _ _ => False

theorem noNeeds : ∀ i g, ¬ ownerNeeds v (List.finRange 5) X N (some 1) i g := by
  intro i g
  have h : ∀ i ∈ List.finRange 2, ∀ g ∈ List.finRange 5, ¬ ownerNeeds v (List.finRange 5) X N (some 1) i g := by
    unfold ownerNeeds; decide
  exact h i (List.mem_finRange i) g (List.mem_finRange g)

theorem noNA : ∀ g, ¬ NA (List.finRange 2) (ownerNeeds v (List.finRange 5) X N (some 1)) g :=
  fun g ⟨i, _, h⟩ => noNeeds i g h

theorem noFrozen :
    ∀ j, ¬ Frozen (List.finRange 2) (List.finRange 5) base (ownerNeeds v (List.finRange 5) X N (some 1)) j :=
  fun _ ⟨y, _, h⟩ => noNA y h

/-- **Non-vacuity.** The example is a sound completion, with an owner's bundle of three goods; so
`SoundCompletion` (Theorem 1′₄'s hypotheses, the owner's needs from its bundle) can hold with a large bundle. -/
theorem sound : SoundCompletion v (List.finRange 2) (List.finRange 5) base N (some 1) X ∧
    (bundle (List.finRange 5) X 1).length = 3 := by
  refine ⟨⟨?_, ⟨fun g _ h => noNA g h, fun _ _ g _ h => noNA g h⟩, ?_, by unfold OC; decide⟩, by decide⟩
  · intro i _ hio
    have hi0 : i = 0 := by revert i; decide
    subst hi0
    refine ⟨?_, fun g h => h.elim⟩
    have : ∀ g ∈ List.finRange 5, base g ≠ some 0 →
        value v 0 (baseOf (List.finRange 5) base 0) < v 0 g → False := by decide
    exact fun g hg hb hlt => this g hg hb hlt
  · refine ⟨fun g _ => List.mem_finRange _, ?_, fun w hw => ?_, fun j _ _ hF => absurd hF (noFrozen j), ?_⟩
    · have : ∀ g ∈ List.finRange 5, ∀ i ∈ List.finRange 2, base g = some i → X g = i := by decide
      exact fun g hg i hb => this g hg i (List.mem_finRange i) hb
    · cases hw; exact ⟨List.mem_finRange _, noFrozen 1⟩
    · have : ∀ j ∈ List.finRange 2, some 1 ≠ some j →
          (junkOf (List.finRange 5) base X j).length + (baseOf (List.finRange 5) base j).length ≤ 2 := by decide
      exact fun j hj hjo _ => this j hj hjo

/-- With the owner's needs from its (empty) base, `N_1 = R_1`, the same pre-allocation is not valid: junk
good 1 is needed. Taking the owner's needs from its bundle is what makes it valid (`k4/lb4.md` §3, item 4). -/
theorem baseNeeds_invalid :
    ¬ Valid (List.finRange 2) (List.finRange 5) base (fun i g => i = 1 ∧ 0 < v 1 g) :=
  fun h => h.v1 1 (by decide) ⟨1, by decide, by decide⟩

/-- Hence, by Theorem 1′₄, the example is EFX₀. -/
theorem efx0 : (Inst.mk 2 5 v).EFX0 X := (sound_model (Inst.mk 2 5 v) sound.1).1

end LB4.Ex

/-! ## Non-vacuity with the owner's needs from its base -/

namespace LB4.ExB

/-- Agent 0 values good 0; agent 1 goods 3, 4, 5; agent 2 goods 0, 1, 2; agent 3 goods 0, 5, 6, 7. -/
def v : Fin 4 → Fin 8 → Nat := fun i g =>
  [[5, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 3, 3, 1, 0, 0], [10, 6, 5, 0, 0, 0, 0, 0],
    [5, 0, 0, 0, 0, 1, 1, 4]][i.val]![g.val]!
/-- Bases: `{0}` (agent 0), `{3, 4}` (agent 1), `{1}` (agent 2), `{7}` (agent 3); junk 2, 5, 6. -/
def base : Fin 8 → Option (Fin 4) := fun g =>
  [some 0, some 2, none, some 1, some 1, none, none, some 3][g.val]!
/-- Agent 2's slot takes junk good 2; the owner, agent 3, takes junk goods 5, 6 with its base good 7. -/
def X : Fin 8 → Fin 4 := fun g => [0, 2, 2, 1, 1, 3, 3, 3][g.val]!
/-- The value-based needs of every agent (from its base). -/
abbrev N : Fin 4 → Fin 8 → Prop := fun i g =>
  g ∈ List.finRange 8 ∧ base g ≠ some i ∧ value v i (baseOf (List.finRange 8) base i) < v i g

theorem na_iff : ∀ g, NA (List.finRange 4) N g ↔ g = 0 := by
  have h : ∀ g : Fin 8, (∃ i ∈ List.finRange 4, N i g) ↔ g = 0 := by decide
  exact h

theorem frozen_iff : ∀ j, Frozen (List.finRange 4) (List.finRange 8) base N j ↔ j = 0 := by
  intro j
  constructor
  · rintro ⟨y, hy, hna⟩
    rw [na_iff] at hna; subst hna
    have : ∀ j : Fin 4, baseOf (List.finRange 8) base j = [0] → j = 0 := by decide
    exact this j hy
  · rintro rfl; exact ⟨0, by decide, (na_iff 0).mpr rfl⟩

/-- **Non-vacuity of `Valid.sound`.** The example satisfies its hypotheses (every agent's needs, the owner's
included, from its base). -/
theorem sound :
    (∀ i ∈ List.finRange 4, Needs v (List.finRange 8) base N i) ∧
    Valid (List.finRange 4) (List.finRange 8) base N ∧
    Completion (List.finRange 4) (List.finRange 8) base N (some 3) X ∧
    OC v (List.finRange 4) (List.finRange 8) X (some 3) := by
  refine ⟨fun i _ => ⟨fun g hg hb hlt => ⟨hg, hb, hlt⟩, fun g ⟨hg, hb, hlt⟩ => ⟨hg, by omega, hb⟩⟩,
    ⟨fun g hg h => ?_, fun i h2 g hg h => ?_⟩,
    ⟨fun g _ => List.mem_finRange _, ?_, fun w hw => ?_, fun j _ _ hF => ?_, fun j _ hjo _ => ?_⟩, ?_⟩
  · rw [na_iff] at h; subst h; revert hg; decide
  · rw [na_iff] at h; subst h
    have : ∀ i : Fin 4, 2 ≤ (baseOf (List.finRange 8) base i).length → 0 ∉ baseOf (List.finRange 8) base i := by
      decide
    exact this i h2 hg
  · have : ∀ g : Fin 8, ∀ i : Fin 4, base g = some i → X g = i := by decide
    exact fun g _ i h => this g i h
  · cases hw; exact ⟨List.mem_finRange _, fun h => by have := (frozen_iff 3).mp h; revert this; decide⟩
  · rw [frozen_iff] at hF; subst hF; decide
  · have : ∀ j : Fin 4, some 3 ≠ some j →
        (junkOf (List.finRange 8) base X j).length + (baseOf (List.finRange 8) base j).length ≤ 2 := by
      decide
    exact this j hjo
  · unfold OC; decide

/-- The example has a frozen agent (0), a two-good base (agent 1), a filled slot (agent 2) and an owner's
bundle of three goods. -/
theorem shape : Frozen (List.finRange 4) (List.finRange 8) base N 0 ∧
    (baseOf (List.finRange 8) base 1).length = 2 ∧
    (junkOf (List.finRange 8) base X 2).length + (baseOf (List.finRange 8) base 2).length = 2 ∧
    (bundle (List.finRange 8) X 3).length = 3 :=
  ⟨(frozen_iff 0).mpr rfl, by decide, by decide, by decide⟩

/-- Hence, by Theorem 1′₄, it is EFX₀. -/
theorem efx0 : EFX0L v (List.finRange 4) (List.finRange 8) X :=
  (Valid.sound (List.nodup_finRange 8) sound.1 sound.2.1 sound.2.2.1 sound.2.2.2).1

end LB4.ExB

/-! ## `|R_x| ≤ 4` is needed in Lemma 2₄: a full instance (from the independent audit of PR #31) -/

namespace LB4.Ex5

def v5 : Fin 2 → Fin 6 → Nat := fun i g => if i.val = 0 then [10, 9, 8, 7, 6, 0][g.val]! else 1
def base5 : Fin 6 → Option (Fin 2) := fun g => if g.val = 0 then some 0 else none
def X5 : Fin 6 → Fin 2 := fun g => if g.val ≤ 1 then 0 else 1
abbrev N5 : Fin 2 → Fin 6 → Prop := fun _ _ => False
abbrev pref5 : Fin 2 → Fin 6 → Fin 6 → Prop := fun i g h => v5 i h < v5 i g
abbrev N5X := ownerNeeds v5 (List.finRange 6) X5 N5 (some 1)
theorem n5x_empty : ∀ i g, ¬ N5X i g := by
  intro i g
  have : ∀ i : Fin 2, ∀ g : Fin 6, ¬ N5X i g := by unfold N5X ownerNeeds; decide
  exact this i g
theorem na5 : ∀ g, ¬ NA (List.finRange 2) N5X g := fun g ⟨i, _, h⟩ => n5x_empty i g h
theorem hyps5 :
    Valid (List.finRange 2) (List.finRange 6) base5 N5X ∧
    Completion (List.finRange 2) (List.finRange 6) base5 N5X (some 1) X5 ∧
    (baseOf (List.finRange 6) base5 1).length ≤ 1 ∧
    (relevant v5 0 (List.finRange 6)).length = 5 ∧
    baseOf (List.finRange 6) base5 0 = [0] ∧ 0 < v5 0 0 ∧ RankOK v5 pref5 0 ∧
    (∀ g, pickNeeds v5 (List.finRange 6) pref5 0 0 g → N5X 0 g) := by
  have hF : ∀ j, ¬ Frozen (List.finRange 2) (List.finRange 6) base5 N5X j := fun _ ⟨y, _, h⟩ => na5 y h
  refine ⟨⟨fun g _ h => na5 g h, fun _ _ g _ h => na5 g h⟩,
    ⟨fun g _ => List.mem_finRange _, ?_, fun w hw => ?_, fun j _ _ h => absurd h (hF j), ?_⟩,
    by decide, by decide, by decide, by decide, ⟨fun g h h1 h2 => by omega, fun g h h1 h2 => h2⟩, ?_⟩
  · have : ∀ g : Fin 6, ∀ i : Fin 2, base5 g = some i → X5 g = i := by decide
    exact fun g _ i h => this g i h
  · cases hw; exact ⟨List.mem_finRange _, hF 1⟩
  · have : ∀ j : Fin 2, some 1 ≠ some j →
        (junkOf (List.finRange 6) base5 X5 j).length + (baseOf (List.finRange 6) base5 j).length ≤ 2 := by
      decide
    exact fun j _ hjo _ => this j hjo
  · intro g ⟨_, _, hp⟩
    have : ∀ g : Fin 6, ¬ pref5 0 g 0 := by decide
    exact absurd hp (this g)
abbrev U5 : List (Fin 6) := [1, 2, 3, 4, 5]
theorem slot5a : ∀ g ∈ U5, g ∈ junk (List.finRange 6) base5 := by decide
theorem slot5b : ∀ g ∈ junk (List.finRange 6) base5, X5 g = 1 → g ∈ U5 := by decide
theorem slot5c : ∃ t ∈ U5, X5 t = 0 ∧ 0 < v5 0 t ∧ ∀ g ∈ U5, 0 < v5 0 g → g ≠ t → v5 0 g < v5 0 t := by decide
theorem threatened5 : ¬ ∀ h ∈ bundle (List.finRange 6) X5 1,
    value v5 0 ((bundle (List.finRange 6) X5 1).erase h) ≤ value v5 0 (bundle (List.finRange 6) X5 0) := by
  decide

/-- **`|R_x| ≤ 4` is needed in Lemma 2₄.** In this instance every hypothesis of `selfProtect` holds except
`|R_x| ≤ 4` (agent `0` values five goods): a valid pre-allocation and a completion with owner `1`, whose base
has at most one good; `x = 0 ≠ 1` with pick base `{0}`, a ranking consistent with its values and the needs of a
pick; `U = [1, 2, 3, 4, 5]`, junk, containing every junk good of the owner's bundle, from which `x` took its
best valued good `1`. And `x` is threatened by the owner's bundle. -/
theorem counterexample :
    (Valid (List.finRange 2) (List.finRange 6) base5 N5X ∧
      Completion (List.finRange 2) (List.finRange 6) base5 N5X (some 1) X5 ∧
      (baseOf (List.finRange 6) base5 1).length ≤ 1 ∧
      (relevant v5 0 (List.finRange 6)).length = 5 ∧
      baseOf (List.finRange 6) base5 0 = [0] ∧ 0 < v5 0 0 ∧ RankOK v5 pref5 0 ∧
      (∀ g, pickNeeds v5 (List.finRange 6) pref5 0 0 g → N5X 0 g)) ∧
    (∀ g ∈ U5, g ∈ junk (List.finRange 6) base5) ∧
    (∀ g ∈ junk (List.finRange 6) base5, X5 g = 1 → g ∈ U5) ∧
    ((∃ g ∈ U5, 0 < v5 0 g) →
      ∃ t ∈ U5, X5 t = 0 ∧ 0 < v5 0 t ∧ ∀ g ∈ U5, 0 < v5 0 g → g ≠ t → pref5 0 t g) ∧
    ¬ ∀ h ∈ bundle (List.finRange 6) X5 1,
      value v5 0 ((bundle (List.finRange 6) X5 1).erase h) ≤ value v5 0 (bundle (List.finRange 6) X5 0) :=
  ⟨hyps5, slot5a, slot5b, fun _ => slot5c, threatened5⟩

end LB4.Ex5

end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB4.efx0_of_needs
#print axioms EFX.LB4.Valid.sound
#print axioms EFX.LB4.Valid.sound_ownerNeeds
#print axioms EFX.LB4.Completion.length_le_two
#print axioms EFX.LB4.Needs.pick
#print axioms EFX.LB4.SoundCompletion.of_baseNeeds
#print axioms EFX.LB4.SoundCompletion.efx0_d2
#print axioms EFX.LB4.sound_model
#print axioms EFX.LB4.d2_shape
#print axioms EFX.LB4.k4D_of_completion
#print axioms EFX.LB4.target4_of_completions
#print axioms EFX.LB4.numFrozen_eq
#print axioms EFX.LB4.omega_eq
#print axioms EFX.LB4.selfProtect_core
#print axioms EFX.LB4.selfProtect
#print axioms EFX.LB4.Completion.owner_length
#print axioms EFX.LB4.selfProtect_five
#print axioms EFX.LB4.selfProtect_seq
#print axioms EFX.LB4.move_step
#print axioms EFX.LB4.ownerSearch_exact
#print axioms EFX.LB4.ownerSearch_exact_base
#print axioms EFX.LB4.complete_none_exists
#print axioms EFX.LB4.Ex.sound
#print axioms EFX.LB4.Ex.baseNeeds_invalid
#print axioms EFX.LB4.Ex.efx0
#print axioms EFX.LB4.Completion.frozen_base
#print axioms EFX.LB4.ExB.sound
#print axioms EFX.LB4.ExB.shape
#print axioms EFX.LB4.ExB.efx0
#print axioms EFX.LB4.Ex5.counterexample
