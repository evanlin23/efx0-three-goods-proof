import EFX.LBRun

/-!
# Valid pre-allocations and their completions (`proofs/lb_last_step.md` §2)

Theorem 1′ of `proofs/lb_last_step.md` generalizes Theorem 1 of `proofs/construction.md` (`EFX.LB.Hyp`,
`EFX.LB.sound`) from LB's output to the completions of any *valid pre-allocation*.

A pre-allocation consists of picks `Y` (each agent's pick is one of its three goods, or none; picks are
distinct) and a list `up` of upgraded agents: each `u ∈ up` picked its `b u` and also holds its `c u`; the
goods `c u` are distinct and nobody's pick. The junk is every other good. `NA` is the set of goods that some
agent outside `up` ranks above its pick (all its goods if it has none). The pre-allocation is *valid*
(`Valid`) if (V1) no junk is in `NA` and (V2) `b u`, `c u ∉ NA` for every `u ∈ up`.

An agent outside `up` is *frozen* if its pick is in `NA`, and a *terminal* otherwise; a terminal has one
slot if it has a pick and two if not. A *completion* with an optional owner `o` (`Completion`) gives every
pick to its picker and `c u` to `u`; a frozen agent holds only its pick, an upgraded agent other than `o`
only `b u` and `c u`, and a terminal other than `o` at most its slots beyond its pick. It satisfies the
owner constraint (OC) if no agent `x ∉ up`, `x ≠ o`, with pick `a x`, finds both `b x` and `c x` in `o`'s
bundle.

- `HypNA`: the hypotheses of `EFX.LB.Hyp` with invariant (I1) replaced by what the proof of Theorem 1 uses
  of it (every good of `NA` is somebody's pick) and an optional owner; `Hyp.toHypNA`: every `Hyp` is one.
  `HypNA.efx0`, `HypNA.length_le_two`: Theorem 1 for `HypNA`.
- `Valid`, `Completion`, `Valid.sound`: **Theorem 1′**. Every completion of a valid pre-allocation that
  satisfies (OC) is EFX₀ for every additive valuation consistent with the rankings (ties allowed), and every
  bundle but the owner's has at most two goods.
- `complete`: a concrete completion. The terminals other than the owner fill their slots, in the order of
  `agents`, first from a list `H` of junk goods and then from the rest of the junk; the owner takes what is
  left. `complete_none` (no owner: all junk fits the slots) and `complete_some` (**Lemma 1**, the owner
  criterion: `H` meets every exposed pair and fits the other terminals' slots) show it is a completion
  satisfying (OC).

As in the written proof, only the envier's own values are used; L5 is not used.
-/

set_option autoImplicit false

namespace EFX
namespace LB

variable {A G : Type} [DecidableEq A] [DecidableEq G]

open Profile

/-! ## Theorem 1 with (I1) weakened -/

/-- The hypotheses of Theorem 1 (`EFX.LB.Hyp`) with (I1) replaced by `na`: every good of `NA` is somebody's
pick. The owner `o` is optional; with `o = none` the slot bounds apply to every agent. -/
structure HypNA (P : Profile A G) (agents : List A) (goods : List G) (X : G → A) (Y : A → Option G)
    (U : A → Prop) (o : Option A) : Prop where
  pick : ∀ k y, Y k = some y → y ∈ goods ∧ X y = k ∧ P.rank k y < 3
  na : ∀ g ∈ goods, P.NA agents U Y g → ∃ k, Y k = some g
  upgraded : ∀ k ∈ agents, U k → Y k = some (P.b k) ∧ P.c k ∈ goods ∧ X (P.c k) = k ∧
    ¬ P.NA agents U Y (P.b k) ∧ (o ≠ some k → ∀ g ∈ goods, X g = k → g = P.b k ∨ g = P.c k)
  frozen : ∀ j ∈ agents, ¬ U j → ∀ y, Y j = some y → P.NA agents U Y y →
    ∀ g ∈ goods, X g = j → g = y
  slots : ∀ j ∈ agents, o ≠ some j → ¬ U j → (∀ y, Y j = some y → ¬ P.NA agents U Y y) →
    ((bundle goods X j).filter (fun g => Y j ≠ some g)).length ≤ (if Y j = none then 2 else 1)
  owner : ∀ w, o = some w → 2 < (bundle goods X w).length → ∀ k ∈ agents, k ≠ w → ¬ U k →
    Y k = some (P.a k) → ¬ (P.b k ∈ bundle goods X w ∧ P.c k ∈ bundle goods X w)

variable {P : Profile A G} {agents : List A} {goods : List G} {X : G → A} {Y : A → Option G}
  {U : A → Prop}

/-- Theorem 1's hypotheses are an instance. -/
theorem Hyp.toHypNA {o : A} (h : Hyp P agents goods X Y U o) : HypNA P agents goods X Y U (some o) where
  pick := h.pick
  na := fun g hg hna => by
    obtain ⟨i, hi, -, hp⟩ := hna
    exact h.i1 i hi g hg hp
  upgraded := fun k hk hU => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := h.upgraded k hk hU
    exact ⟨h1, h2, h3, h4, fun hne => h5 (fun e => hne (by rw [e]))⟩
  frozen := h.frozen
  slots := fun j hj hne => h.slots j hj (fun e => hne (by rw [e]))
  owner := fun w hw => by cases hw; exact h.owner

variable {o : Option A}

/-- Every bundle except the owner's has at most two goods. -/
theorem HypNA.length_le_two (h : HypNA P agents goods X Y U o) (hg : goods.Nodup) :
    ∀ j ∈ agents, o ≠ some j → (bundle goods X j).length ≤ 2 := fun j hj hjo =>
  bundle_length_le_two hg (fun hU => ((h.upgraded j hj hU).2.2.2.2 hjo)) (h.frozen j hj)
    (h.slots j hj hjo)

/-- A good in a bundle of at least two goods is not in `NA`. -/
theorem HypNA.not_NA (h : HypNA P agents goods X Y U o) (hg : goods.Nodup) {j : A} (hj : j ∈ agents)
    (hlen : 2 ≤ (bundle goods X j).length) {x : G} (hx : x ∈ bundle goods X j) :
    ¬ P.NA agents U Y x := by
  intro hna
  obtain ⟨hxg, hXx⟩ := mem_bundle.mp hx
  obtain ⟨k, hk⟩ := h.na x hxg hna
  have hXk := (h.pick k x hk).2.1
  rw [hXx] at hXk
  subst hXk
  by_cases hU : U j
  · obtain ⟨hYb, -, -, hnb, -⟩ := h.upgraded j hj hU
    rw [hYb] at hk
    cases hk
    exact hnb hna
  · have := length_le_one (nodup_bundle hg X j) (y := x)
      (fun g hg' => h.frozen j hj hU x hk hna g (mem_bundle.mp hg').1 (mem_bundle.mp hg').2)
    omega

/-- **Theorem 1, weakened hypotheses.** An allocation satisfying `HypNA` is EFX₀ for every additive
valuation consistent with the rankings. -/
theorem HypNA.efx0 (h : HypNA P agents goods X Y U o) (hg : goods.Nodup) {v : A → G → Nat}
    (hv : P.Consistent agents v) : EFX0L v agents goods X := by
  intro i hi j hj hij g hgj
  have hndj := nodup_bundle hg X j
  have hndi := nodup_bundle hg X i
  -- singletons are never strongly envied
  by_cases hsmall : (bundle goods X j).length ≤ 1
  · have hlen : ((bundle goods X j).erase g).length = 0 := by
      rw [List.length_erase_of_mem hgj]; omega
    rw [List.length_eq_zero_iff.mp hlen]; simp
  have hnotNA : ∀ x ∈ bundle goods X j, ¬ P.NA agents U Y x :=
    fun x hx => h.not_NA hg hj (by omega) hx
  have hle : value v i ((bundle goods X j).erase g) ≤ value v i (bundle goods X j) :=
    value_sublist v i List.erase_sublist
  have hdisj : ∀ x, x ∈ bundle goods X j → x ∉ bundle goods X i := fun x hx hx' =>
    hij ((mem_bundle.mp hx').2.symm.trans (mem_bundle.mp hx).2)
  have e1 := value_eq hv hi hndj
  have e2 := value_eq hv hi hndi
  have ra : P.rank i (P.a i) = 0 := rank_a i
  have rb := rank_b hv hi
  have rc := rank_c hv hi
  obtain ⟨h1, h2, h3, h4, -⟩ := hv i hi
  by_cases hUi : U i
  · -- `i` is upgraded: it holds `b i` and `c i`, worth at least `a i`
    obtain ⟨hYb, hcg, hXc, -, -⟩ := h.upgraded i hi hUi
    have hbi : P.b i ∈ bundle goods X i :=
      mem_bundle.mpr ⟨(h.pick i _ hYb).1, (h.pick i _ hYb).2.1⟩
    have hci : P.c i ∈ bundle goods X i := mem_bundle.mpr ⟨hcg, hXc⟩
    have hbj := fun hb => hdisj _ hb hbi
    have hcj := fun hc => hdisj _ hc hci
    rw [e1] at hle
    rw [e2]
    grind
  -- `i` is not upgraded: the goods it ranks above its pick are in `NA`, so not in `X_j`
  have hnp : ∀ x ∈ bundle goods X j, ¬ P.Prefers Y i x :=
    fun x hx hp => hnotNA x hx ⟨i, hi, hUi, hp⟩
  cases hY : Y i with
  | none =>
    have hn : ∀ x, P.rank i x < 3 → x ∉ bundle goods X j := fun x hx hxj =>
      hnp x hxj (by unfold Prefers pickRank; rw [hY]; exact hx)
    have := hn _ (by omega : P.rank i (P.a i) < 3)
    have := hn _ (by omega : P.rank i (P.b i) < 3)
    have := hn _ (by omega : P.rank i (P.c i) < 3)
    rw [e1] at hle
    grind
  | some y =>
    obtain ⟨hyg, hXy, hry⟩ := h.pick i y hY
    have hyi : y ∈ bundle goods X i := mem_bundle.mpr ⟨hyg, hXy⟩
    have hvy := le_value_of_mem v i hyi
    have hn : ∀ x, P.rank i x < P.rank i y → x ∉ bundle goods X j := fun x hx hxj =>
      hnp x hxj (by unfold Prefers pickRank; rw [hY]; exact hx)
    have hyj := fun hy => hdisj _ hy hyi
    have hy3 : y = P.a i ∨ y = P.b i ∨ y = P.c i := by
      unfold rank at hry; grind
    rcases hy3 with rfl | rfl | rfl
    · -- `i` picked its top `a i`
      by_cases hboth : P.b i ∈ bundle goods X j ∧ P.c i ∈ bundle goods X j
      · by_cases hbig : 2 < (bundle goods X j).length
        · -- then `X_j` is the owner's bundle, and the owner constraint excludes this
          have hjo : o = some j := by
            refine Classical.byContradiction fun hjo => ?_
            have := h.length_le_two hg j hj hjo
            omega
          exact absurd hboth (h.owner j hjo hbig i hi hij hUi hY)
        · -- `X_j = {b i, c i}`: without `g` it is one good, worth at most `a i`
          have hl1 : ((bundle goods X j).erase g).length = 1 := by
            rw [List.length_erase_of_mem hgj]; omega
          obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl1
          rw [hx, value_cons, value_nil]
          have := rank_le hv hi (g := P.a i) (h := x) (by omega)
          omega
      · rw [e1] at hle
        grind
    · have := hn (P.a i) (by omega)
      rw [e1] at hle
      grind
    · have := hn (P.a i) (by omega)
      have := hn (P.b i) (by omega)
      rw [e1] at hle
      grind

/-! ## Valid pre-allocations and completions -/

/-- A valid pre-allocation (`proofs/lb_last_step.md` §2): picks `Y` and upgraded agents `up` with
- `pick`, `pick_inj`: each pick is a good of `goods` that its picker, a listed agent, values; picks are
  distinct;
- `up_mem`, `up_b`, `up_c`, `up_c_inj`: each upgraded agent is listed and picked its `b`; its `c` is a good
  that is nobody's pick; the `c`s of distinct upgraded agents are distinct;
- (V1) `v1`: a junk good (nobody's pick and not the `c` of an upgraded agent) is not in `NA`;
- (V2) `v2`: `b u` and `c u` are not in `NA`, for every upgraded `u`. -/
structure Valid (P : Profile A G) (agents : List A) (goods : List G) (Y : A → Option G) (up : List A) :
    Prop where
  pick : ∀ k y, Y k = some y → k ∈ agents ∧ y ∈ goods ∧ P.rank k y < 3
  pick_inj : ∀ k k' y, Y k = some y → Y k' = some y → k = k'
  up_mem : ∀ u ∈ up, u ∈ agents
  up_b : ∀ u ∈ up, Y u = some (P.b u)
  up_c : ∀ u ∈ up, P.c u ∈ goods ∧ ∀ k, Y k ≠ some (P.c u)
  up_c_inj : ∀ u ∈ up, ∀ u' ∈ up, P.c u = P.c u' → u = u'
  v1 : ∀ g ∈ goods, (∀ k, Y k ≠ some g) → (∀ u ∈ up, P.c u ≠ g) → ¬ P.NA agents (· ∈ up) Y g
  v2 : ∀ u ∈ up, ¬ P.NA agents (· ∈ up) Y (P.b u) ∧ ¬ P.NA agents (· ∈ up) Y (P.c u)

/-- A completion of the pre-allocation `(Y, up)` with optional owner `o`, satisfying the owner constraint:
- `alloc`, `pick`, `upc`: every good goes to a listed agent, every pick to its picker, `c u` to `u`;
- `frozen`: an agent outside `up` whose pick is in `NA` holds only its pick;
- `upOnly`: an upgraded agent other than the owner holds only its `b` and `c`;
- `slots`: a terminal (outside `up`, pick not in `NA`) other than the owner holds at most one good beyond
  its pick, or two if it has none;
- `oc`: the owner constraint (OC). -/
structure Completion (P : Profile A G) (agents : List A) (goods : List G) (Y : A → Option G)
    (up : List A) (o : Option A) (X : G → A) : Prop where
  alloc : ∀ g ∈ goods, X g ∈ agents
  pick : ∀ k y, Y k = some y → X y = k
  upc : ∀ u ∈ up, X (P.c u) = u
  frozen : ∀ j ∈ agents, j ∉ up → ∀ y, Y j = some y → P.NA agents (· ∈ up) Y y →
    ∀ g ∈ goods, X g = j → g = y
  upOnly : ∀ u ∈ up, o ≠ some u → ∀ g ∈ goods, X g = u → g = P.b u ∨ g = P.c u
  slots : ∀ j ∈ agents, o ≠ some j → j ∉ up → (∀ y, Y j = some y → ¬ P.NA agents (· ∈ up) Y y) →
    ((bundle goods X j).filter (fun g => Y j ≠ some g)).length ≤ (if Y j = none then 2 else 1)
  oc : ∀ w, o = some w → ∀ x ∈ agents, x ≠ w → x ∉ up → Y x = some (P.a x) →
    ¬ (P.b x ∈ bundle goods X w ∧ P.c x ∈ bundle goods X w)

variable {up : List A}

omit [DecidableEq A] in
/-- Every good of `NA` is somebody's pick: it is not junk (V1) and not the `c` of an upgraded agent (V2). -/
theorem Valid.na_picked (hV : Valid P agents goods Y up) {g : G} (hg : g ∈ goods)
    (hna : P.NA agents (· ∈ up) Y g) : ∃ k, Y k = some g := by
  refine Classical.byContradiction fun hno => ?_
  have hnp : ∀ k, Y k ≠ some g := fun k hk => hno ⟨k, hk⟩
  by_cases hc : ∃ u ∈ up, P.c u = g
  · obtain ⟨u, hu, rfl⟩ := hc
    exact (hV.v2 u hu).2 hna
  · exact hV.v1 g hg hnp (fun u hu e => hc ⟨u, hu, e⟩) hna

/-- A completion of a valid pre-allocation satisfies `HypNA`. -/
theorem Completion.hypNA (hV : Valid P agents goods Y up) (hC : Completion P agents goods Y up o X) :
    HypNA P agents goods X Y (· ∈ up) o where
  pick := fun k y hk => ⟨(hV.pick k y hk).2.1, hC.pick k y hk, (hV.pick k y hk).2.2⟩
  na := fun _ hg hna => hV.na_picked hg hna
  upgraded := fun k _ hk => ⟨hV.up_b k hk, (hV.up_c k hk).1, hC.upc k hk, (hV.v2 k hk).1,
    hC.upOnly k hk⟩
  frozen := hC.frozen
  slots := hC.slots
  owner := fun w hw _ => hC.oc w hw

/-- **Theorem 1′ (soundness of pre-allocations).** Every completion `X` of a valid pre-allocation that
satisfies the owner constraint is EFX₀ for every additive valuation consistent with the rankings (ties
allowed), and every bundle except the owner's has at most two goods. -/
theorem Valid.sound (hV : Valid P agents goods Y up) (hC : Completion P agents goods Y up o X)
    (hg : goods.Nodup) :
    (∀ v : A → G → Nat, P.Consistent agents v → EFX0L v agents goods X) ∧
    ∀ j ∈ agents, o ≠ some j → (bundle goods X j).length ≤ 2 :=
  ⟨fun _ hv => (hC.hypNA hV).efx0 hg hv, (hC.hypNA hV).length_le_two hg⟩

/-! ## A concrete completion (Lemma 1) -/

/-- The junk of the pre-allocation `(Y, up)`: the goods that are no listed agent's pick and not the `c` of
an upgraded agent. -/
def junkList (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) : List G :=
  goods.filter (fun g => (picker agents Y g).isNone && (upOf P up g).isNone)

/-- `S`, the number of slots. -/
def slotSum (P : Profile A G) (agents up : List A) (Y : A → Option G) : Nat :=
  (agents.map (cap P agents up Y)).sum

/-- `g` is in the base of `w`: `w`'s pick, or `w`'s `c` if `w` is upgraded. -/
def InBase (P : Profile A G) (up : List A) (Y : A → Option G) (w : A) (g : G) : Prop :=
  Y w = some g ∨ (w ∈ up ∧ P.c w = g)

/-- The completion with owner `o` (or none) built from the junk goods `H`: picks go to their pickers, `c u`
to each upgraded `u`, and the junk fills the slots of the terminals other than the owner, in the order of
`agents`, first the goods of `H` and then the rest of the junk; whatever is left goes to the owner. The
agent `d` receives goods that nothing else places (none, under the hypotheses of `complete_none` and
`complete_some`). -/
def complete (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (o : Option A)
    (H : List G) (d : A) (g : G) : A :=
  match picker agents Y g with
  | some k => k
  | none =>
    match upOf P up g with
    | some u => u
    | none =>
      (fill (slotsExcept (cap P agents up Y) o) agents
        (H ++ (junkList P agents up Y goods).filter (fun g => g ∉ H)) g).getD (o.getD d)

omit [DecidableEq A] in
theorem mem_junkList {g : G} :
    g ∈ junkList P agents up Y goods ↔ g ∈ goods ∧ picker agents Y g = none ∧ upOf P up g = none := by
  simp [junkList, Option.isNone_iff_eq_none]

omit [DecidableEq A] in
/-- A good among the first `Σ s` goods of `rest` is placed by `fill`. -/
theorem fill_of_mem_take {s : A → Nat} : ∀ {ks : List A} {rest : List G} {g : G},
    g ∈ rest.take (ks.map s).sum → ∃ j, fill s ks rest g = some j
  | [], rest, g, hg => by simp at hg
  | k :: ks, rest, g, hg => by
    unfold fill
    split
    · exact ⟨k, rfl⟩
    · rename_i hgt
      simp only [List.map_cons, List.sum_cons, List.take_add, List.mem_append] at hg
      exact fill_of_mem_take (hg.resolve_left hgt)

omit [DecidableEq A] in
/-- `fill` never places a good with an agent that has no slot. -/
theorem fill_pos {s : A → Nat} {ks : List A} {rest : List G} {g : G} {j : A}
    (h : fill s ks rest g = some j) : 0 < s j :=
  (fill_some h).2.2

omit [DecidableEq G] in
theorem mem_take_append {H R : List G} {g : G} (hg : g ∈ H) :
    ∀ {n : Nat}, H.length ≤ n → g ∈ (H ++ R).take n := by
  induction H with
  | nil => simp at hg
  | cons h H ih =>
    intro n hn
    cases n with
    | zero => simp at hn
    | succ n =>
      rcases List.mem_cons.mp hg with rfl | hg
      · simp
      · simp only [List.cons_append, List.take_succ_cons, List.mem_cons]
        exact Or.inr (ih hg (by simp at hn; omega))

section complete
variable {H : List G} {d : A}

theorem complete_cases (g : G) :
    (∃ k, picker agents Y g = some k ∧ complete P agents up Y goods o H d g = k) ∨
    (picker agents Y g = none ∧ ∃ u, upOf P up g = some u ∧ complete P agents up Y goods o H d g = u) ∨
    (picker agents Y g = none ∧ upOf P up g = none ∧ ∃ j, fill (slotsExcept (cap P agents up Y) o) agents
      (H ++ (junkList P agents up Y goods).filter (fun g => g ∉ H)) g = some j ∧
      complete P agents up Y goods o H d g = j) ∨
    (picker agents Y g = none ∧ upOf P up g = none ∧ fill (slotsExcept (cap P agents up Y) o) agents
      (H ++ (junkList P agents up Y goods).filter (fun g => g ∉ H)) g = none ∧
      complete P agents up Y goods o H d g = o.getD d) := by
  unfold complete
  cases hp : picker agents Y g with
  | some k => exact Or.inl ⟨k, rfl, rfl⟩
  | none =>
    cases hu : upOf P up g with
    | some u => exact Or.inr (Or.inl ⟨rfl, u, rfl, rfl⟩)
    | none =>
      cases hf : fill (slotsExcept (cap P agents up Y) o) agents
          (H ++ (junkList P agents up Y goods).filter (fun g => g ∉ H)) g with
      | some j => exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, j, rfl, by simp⟩))
      | none => exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, by simp⟩))

/-- The completion's properties, for an owner that is a listed terminal or upgraded agent, when every junk
good is placed if there is no owner, and `H` (junk, fitting the other terminals' slots) meets every exposed
pair. -/
theorem complete_completion (hV : Valid P agents goods Y up) (hag : agents.Nodup)
    (hgd : goods.Nodup)
    (ho : ∀ w, o = some w → w ∈ agents ∧ (w ∈ up ∨ ∀ y, Y w = some y → ¬ P.NA agents (· ∈ up) Y y))
    (hnone : o = none → ∀ g ∈ junkList P agents up Y goods, ∃ j, fill (slotsExcept (cap P agents up Y) o)
      agents (H ++ (junkList P agents up Y goods).filter (fun g => g ∉ H)) g = some j)
    (hH : ∀ h ∈ H, h ∈ junkList P agents up Y goods)
    (hHfit : H.length ≤ (agents.map (slotsExcept (cap P agents up Y) o)).sum)
    (hhit : ∀ w, o = some w → ∀ x ∈ agents, x ≠ w → x ∉ up → Y x = some (P.a x) →
      (P.b x ∈ junkList P agents up Y goods ∨ InBase P up Y w (P.b x)) →
      (P.c x ∈ junkList P agents up Y goods ∨ InBase P up Y w (P.c x)) → P.b x ∈ H ∨ P.c x ∈ H) :
    Completion P agents goods Y up o (complete P agents up Y goods o H d) := by
  -- the fallback `o.getD d` is used only for junk, and only when there is an owner
  have hfall : ∀ {g}, g ∈ goods → picker agents Y g = none → upOf P up g = none →
      fill (slotsExcept (cap P agents up Y) o) agents
        (H ++ (junkList P agents up Y goods).filter (fun g => g ∉ H)) g = none →
      ∃ w, o = some w := by
    intro g hg hp hu hf
    cases ho' : o with
    | some w => exact ⟨w, rfl⟩
    | none =>
      obtain ⟨j, hj⟩ := hnone ho' g (mem_junkList.mpr ⟨hg, hp, hu⟩)
      rw [hf] at hj; cases hj
  -- the slots: `fill` places goods only with terminals other than the owner
  have hfillj : ∀ {g j}, fill (slotsExcept (cap P agents up Y) o) agents
      (H ++ (junkList P agents up Y goods).filter (fun g => g ∉ H)) g = some j →
      o ≠ some j ∧ frozenB P agents up Y j = false ∧ j ∉ up := by
    intro g j hf
    have h3 := fill_pos hf
    unfold slotsExcept cap at h3
    by_cases hoj : o = some j
    · simp [hoj] at h3
    · by_cases hfz : frozenB P agents up Y j = true
      · simp [hoj, hfz] at h3
      · by_cases hu : j ∈ up
        · simp [hoj, hu] at h3
        · exact ⟨hoj, by simpa using hfz, hu⟩
  have hpicker : ∀ k y, Y k = some y → picker agents Y y = some k := by
    intro k y hk
    cases hp : picker agents Y y with
    | none => exact absurd hk (picker_none hp k (hV.pick k y hk).1)
    | some k' => rw [hV.pick_inj k' k y (picker_some hp).2 hk]
  refine ⟨fun g hg => ?_, fun k y hk => ?_, fun u hu => ?_, fun j _ hj y hy hna g hg hX => ?_,
    fun u hu hou g hg hX => ?_, fun j _ hoj hj hnf => ?_, fun w hw x hx hxw hxu hxa hboth => ?_⟩
  · -- `alloc`
    rcases complete_cases (P := P) (agents := agents) (up := up) (Y := Y) (goods := goods) (o := o)
      (H := H) (d := d) g with ⟨k, hp, hX⟩ | ⟨-, u, hu, hX⟩ | ⟨-, -, j, hf, hX⟩ | ⟨hp, hu, hf, hX⟩
    · rw [hX]; exact (picker_some hp).1
    · rw [hX]; exact hV.up_mem u (upOf_some hu).1
    · rw [hX]; exact (fill_some hf).1
    · obtain ⟨w, hw⟩ := hfall hg hp hu hf
      rw [hX, hw]; exact (ho w hw).1
  · -- `pick`
    unfold complete; rw [hpicker k y hk]
  · -- `upc`
    have hp : picker agents Y (P.c u) = none := by
      cases hp : picker agents Y (P.c u) with
      | none => rfl
      | some k => exact absurd (picker_some hp).2 ((hV.up_c u hu).2 k)
    unfold complete; rw [hp]
    cases hu' : upOf P up (P.c u) with
    | none => exact absurd rfl (upOf_none hu' u hu)
    | some u' => exact hV.up_c_inj u' (upOf_some hu').1 u hu (upOf_some hu').2
  · -- `frozen`
    have hfz : frozenB P agents up Y j = true := by
      unfold frozenB; rw [hy]; exact naB_iff.mpr hna
    rcases complete_cases (P := P) (agents := agents) (up := up) (Y := Y) (goods := goods) (o := o)
      (H := H) (d := d) g with ⟨k, hp, hX'⟩ | ⟨-, u, hu, hX'⟩ | ⟨-, -, j', hf, hX'⟩ | ⟨hp, hu, hf, hX'⟩
    · rw [hX'] at hX; subst hX
      have := (picker_some hp).2
      rw [hy] at this; cases this; rfl
    · rw [hX'] at hX; subst hX; exact absurd (upOf_some hu).1 hj
    · rw [hX'] at hX; subst hX
      rw [(hfillj hf).2.1] at hfz; cases hfz
    · obtain ⟨w, hw⟩ := hfall hg hp hu hf
      rw [hX', hw] at hX
      simp only [Option.getD_some] at hX
      subst hX
      rcases (ho w hw).2 with hwu | hwt
      · exact absurd hwu hj
      · exact absurd hna (hwt y hy)
  · -- `upOnly`
    rcases complete_cases (P := P) (agents := agents) (up := up) (Y := Y) (goods := goods) (o := o)
      (H := H) (d := d) g with ⟨k, hp, hX'⟩ | ⟨-, u', hu', hX'⟩ | ⟨-, -, j', hf, hX'⟩ | ⟨hp, hu', hf, hX'⟩
    · rw [hX'] at hX; subst hX
      have := (picker_some hp).2
      rw [hV.up_b k hu] at this; cases this; exact Or.inl rfl
    · rw [hX'] at hX; subst hX; exact Or.inr (upOf_some hu').2.symm
    · rw [hX'] at hX; subst hX; exact absurd hu (hfillj hf).2.2
    · obtain ⟨w, hw⟩ := hfall hg hp hu' hf
      rw [hX', hw] at hX
      simp only [Option.getD_some] at hX
      subst hX; exact absurd hw hou
  · -- `slots`
    have hS : ∀ g ∈ (bundle goods (complete P agents up Y goods o H d) j).filter (fun g => Y j ≠ some g),
        fill (slotsExcept (cap P agents up Y) o) agents
          (H ++ (junkList P agents up Y goods).filter (fun g => g ∉ H)) g = some j := by
      intro g hgS
      obtain ⟨hgb, hne⟩ := List.mem_filter.mp hgS
      obtain ⟨hg, hX⟩ := mem_bundle.mp hgb
      rcases complete_cases (P := P) (agents := agents) (up := up) (Y := Y) (goods := goods) (o := o)
        (H := H) (d := d) g with ⟨k, hp, hX'⟩ | ⟨-, u, hu, hX'⟩ | ⟨-, -, j', hf, hX'⟩ | ⟨hp, hu, hf, hX'⟩
      · rw [hX'] at hX; subst hX; simp [(picker_some hp).2] at hne
      · rw [hX'] at hX; subst hX; exact absurd (upOf_some hu).1 hj
      · rw [hX'] at hX; subst hX; exact hf
      · obtain ⟨w, hw⟩ := hfall hg hp hu hf
        rw [hX', hw] at hX
        simp only [Option.getD_some] at hX
        subst hX; exact absurd hw hoj
    have hc := fill_count hag ((nodup_bundle hgd _ j).sublist List.filter_sublist) hS
    have hfz : frozenB P agents up Y j = false := by
      unfold frozenB
      cases hy : Y j with
      | none => rfl
      | some y =>
        show naB P agents up Y y = false
        cases hb : naB P agents up Y y with
        | false => rfl
        | true => exact absurd (naB_iff.mp hb) (hnf y hy)
    have : slotsExcept (cap P agents up Y) o j = if Y j = none then 2 else 1 := by
      simp [slotsExcept, cap, hoj, hfz, hj]
    omega
  · -- `oc`: each of `b x`, `c x` in the owner's bundle is in its base, or junk that `fill` left over
    have hsrc : ∀ g, g ∈ bundle goods (complete P agents up Y goods o H d) w →
        (g ∈ junkList P agents up Y goods ∨ InBase P up Y w g) := by
      intro g hgb
      obtain ⟨hg, hX⟩ := mem_bundle.mp hgb
      rcases complete_cases (P := P) (agents := agents) (up := up) (Y := Y) (goods := goods) (o := o)
        (H := H) (d := d) g with ⟨k, hp, hX'⟩ | ⟨hp, u, hu, hX'⟩ | ⟨-, -, j', hf, hX'⟩ | ⟨hp, hu, hf, hX'⟩
      · rw [hX'] at hX; subst hX; exact Or.inr (Or.inl (picker_some hp).2)
      · rw [hX'] at hX; subst hX; exact Or.inr (Or.inr (upOf_some hu))
      · rw [hX'] at hX; subst hX; exact absurd hw (hfillj hf).1
      · exact Or.inl (mem_junkList.mpr ⟨hg, hp, hu⟩)
    -- a good of `H` is placed by `fill`, so not with the owner
    have hHout : ∀ h ∈ H, h ∉ bundle goods (complete P agents up Y goods o H d) w := by
      intro h hh hhb
      obtain ⟨-, hp, hu⟩ := mem_junkList.mp (hH h hh)
      obtain ⟨j, hj⟩ := fill_of_mem_take (s := slotsExcept (cap P agents up Y) o) (ks := agents)
        (mem_take_append (R := (junkList P agents up Y goods).filter (fun g => g ∉ H)) hh hHfit)
      have hX := (mem_bundle.mp hhb).2
      unfold complete at hX
      rw [hp, hu] at hX
      simp only [hj, Option.getD_some] at hX
      exact (hfillj hj).1 (by rw [hw, hX])
    rcases hhit w hw x hx hxw hxu hxa (hsrc _ hboth.1) (hsrc _ hboth.2) with hb | hc
    · exact hHout _ hb hboth.1
    · exact hHout _ hc hboth.2

/-- **Completion without owner.** If the junk fits the slots (`|J| ≤ S`), `complete` with no owner is a
completion; every bundle has at most two goods. -/
theorem complete_none (hV : Valid P agents goods Y up) (hag : agents.Nodup) (hgd : goods.Nodup)
    (hfit : (junkList P agents up Y goods).length ≤ slotSum P agents up Y) :
    Completion P agents goods Y up none (complete P agents up Y goods none [] d) := by
  refine complete_completion hV hag hgd (fun w hw => by cases hw) (fun _ g hg => ?_)
    (fun h hh => by simp at hh) (by simp) (fun w hw => by cases hw)
  have e1 : ([] : List G) ++ (junkList P agents up Y goods).filter (fun g => g ∉ ([] : List G)) =
      junkList P agents up Y goods := by simp
  have e2 : slotsExcept (cap P agents up Y) none = cap P agents up Y := by
    funext k; simp [slotsExcept]
  rw [e1, e2]
  exact fill_cover hg hfit

/-- **Lemma 1 (owner criterion).** Let `w` be a listed agent that is upgraded or a terminal, and `H` a list
of junk goods, no longer than the number of slots of the agents other than `w`, that meets `{b x, c x}` for
every exposed agent `x` (not upgraded, `x ≠ w`, pick `a x`, `b x` and `c x` each junk or in `w`'s base).
Then `complete` with owner `w` is a completion satisfying the owner constraint. -/
theorem complete_some (hV : Valid P agents goods Y up) (hag : agents.Nodup) (hgd : goods.Nodup)
    {w : A} (hw : w ∈ agents) (hwT : w ∈ up ∨ ∀ y, Y w = some y → ¬ P.NA agents (· ∈ up) Y y)
    (hH : ∀ h ∈ H, h ∈ junkList P agents up Y goods)
    (hHfit : H.length ≤ (agents.map (slotsExcept (cap P agents up Y) (some w))).sum)
    (hhit : ∀ x ∈ agents, x ≠ w → x ∉ up → Y x = some (P.a x) →
      (P.b x ∈ junkList P agents up Y goods ∨ InBase P up Y w (P.b x)) →
      (P.c x ∈ junkList P agents up Y goods ∨ InBase P up Y w (P.c x)) → P.b x ∈ H ∨ P.c x ∈ H) :
    Completion P agents goods Y up (some w) (complete P agents up Y goods (some w) H d) :=
  complete_completion hV hag hgd (fun w' hw' => by cases hw'; exact ⟨hw, hwT⟩)
    (fun h => by cases h) hH hHfit (fun w' hw' => by cases hw'; exact hhit)

end complete

end LB
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB.HypNA.efx0
#print axioms EFX.LB.Valid.sound
#print axioms EFX.LB.complete_none
#print axioms EFX.LB.complete_some
