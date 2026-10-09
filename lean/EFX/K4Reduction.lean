import EFX.Target

/-!
# The k = 4 core reduction (`k4/SCOUT.md` §2, K4.CORE)

- `sharedGoods`: the goods of `goods` relevant to `i` and to some other agent.
- `IsCore4`: a *k = 4 core* (`k4/SCOUT.md` §2, K4.CORE): at least two agents; (C1) every agent has 3 or 4
  relevant goods; (C2) every agent is strictly balanced, each good worth less than its other goods together;
  (C3) an agent with `d` relevant goods has at most `d − 2` private goods (relevant to no other agent): at
  most 1 with 3 goods, at most 2 with 4; (C4) an agent with two private goods `p, q` values them less than
  its shared goods `s, t`, `v(p) + v(q) < v(s) + v(t)`; (C5) every good is relevant to some agent.
- `Connected`: the agents are connected through the goods (no split of the agents into two nonempty sides
  such that no good is relevant to agents on both sides).
- `efx0_split`: **L6 (components)**. EFX₀ allocations of the two sides of such a split combine into one.
- `core_reduction4_conn`: **K4.CORE**. If every *connected* k = 4 core with at most `N` agents has an EFX₀
  allocation, so does every instance with at most `N` agents in which every agent has at most four relevant
  goods. The induction of `EFX.core_reduction` (`proofs/lemmas.md`, CORE), which never uses k: junk goods by
  L3 (`EFX.junk`), then peeling by R1 (`EFX.peel`), then by R2 (`EFX.peelR2`, applied whenever its balance
  condition `v_i(R_i ∖ P) ≤ v_i(P)` holds), then L6 (`efx0_split`); what remains is a connected k = 4 core.
- `core_reduction4`: the same for all k = 4 cores, connected or not.
- `isCore_of_isCore4`, `isCore4_of_isCore`: the k = 4 cores whose agents all have three goods are exactly the
  cores of `EFX.IsCore`.
- `core_reduction4_mixed`: only the connected k = 4 cores that have an agent with four relevant goods are
  needed: a k = 4 core whose agents all have three goods is a core in the sense of `EFX.IsCore`, which
  Corollary D (`EFX.LB.corollaryD_lists`) covers.
- `target4_of_cores`: `core_reduction4_mixed` in the model's terms (`EFX.Inst`, `numRelevant I i ≤ 4`).
-/

set_option autoImplicit false

namespace EFX

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- The goods of `goods` shared by `i` among `agents`: relevant to `i` and to some other agent. -/
def sharedGoods (v : A → G → Nat) (agents : List A) (i : A) (goods : List G) : List G :=
  goods.filter (fun g => decide (0 < v i g ∧ ∃ j ∈ agents, j ≠ i ∧ 0 < v j g))

/-- A k = 4 core (`k4/SCOUT.md` §2, K4.CORE): (C1)–(C5), with at least two agents. -/
def IsCore4 (v : A → G → Nat) (agents : List A) (goods : List G) : Prop :=
  2 ≤ agents.length ∧
  (∀ i ∈ agents, 3 ≤ (relevant v i goods).length ∧ (relevant v i goods).length ≤ 4) ∧
  (∀ i ∈ agents, ∀ g ∈ goods, 2 * v i g < value v i goods) ∧
  (∀ i ∈ agents, (privateGoods v agents i goods).length + 2 ≤ (relevant v i goods).length) ∧
  (∀ i ∈ agents, (privateGoods v agents i goods).length = 2 →
    value v i (privateGoods v agents i goods) < value v i (sharedGoods v agents i goods)) ∧
  (∀ g ∈ goods, ∃ i ∈ agents, 0 < v i g)

/-- The agents are connected through the goods (`proofs/lemmas.md`, L6): a split of the agents into two
sides, `S` and not `S`, such that no good is relevant to agents on both sides, puts all agents on one side. -/
def Connected (v : A → G → Nat) (agents : List A) (goods : List G) : Prop :=
  ∀ S : A → Bool, (∀ g ∈ goods, ∀ i ∈ agents, ∀ j ∈ agents, 0 < v i g → 0 < v j g → S i = S j) →
    ∀ i ∈ agents, ∀ j ∈ agents, S i = S j

section lemmas
variable (v : A → G → Nat)

omit [DecidableEq A] [DecidableEq G] in
/-- Splitting `i`'s relevant goods by a test `q` that only relevant goods pass. -/
theorem length_relevant_split (i : A) (q : G → Bool) (goods : List G)
    (hq : ∀ g, q g = true → 0 < v i g) :
    (relevant v i goods).length =
      (goods.filter q).length + (relevant v i (goods.filter (fun g => !q g))).length := by
  have hpriv : (relevant v i (goods.filter q)).length = (goods.filter q).length := by
    unfold relevant
    congr 1
    rw [List.filter_eq_self]
    intro g hg
    simpa using hq g (List.mem_filter.mp hg).2
  rw [← hpriv]
  unfold relevant
  rw [List.filter_filter, List.filter_filter]
  rw [LB.length_filter_add (goods.filter (fun g => decide (0 < v i g))) q, List.filter_filter,
    List.filter_filter]
  congr 2 <;> apply List.filter_congr <;> intro g _ <;> simp [Bool.and_comm]

omit [DecidableEq A] [DecidableEq G] in
/-- R2's balance condition for a strictly balanced agent with at most one relevant good outside `P`
(the goods passing `q`): `v_i(R_i ∖ P) ≤ v_i(P)`. -/
theorem R2_balance_of_le_one {i : A} {goods : List G} (q : G → Bool)
    (hlt : ∀ g ∈ goods, 2 * v i g < value v i goods)
    (h1 : (relevant v i (goods.filter (fun g => !q g))).length ≤ 1) :
    value v i (relevant v i (goods.filter (fun g => !q g))) ≤ value v i (goods.filter q) := by
  rw [value_relevant]
  have hsplit := value_filter_add v i q goods
  have hQ1 : (goods.filter (fun g => !q g)).countP (fun g => decide (0 < v i g)) ≤ 1 := by
    rw [List.countP_eq_length_filter]
    exact h1
  cases hfav : favorite (v i) (goods.filter (fun g => !q g)) with
  | none =>
    rw [(favorite_eq_none_iff _).mp hfav, value_nil]
    exact Nat.zero_le _
  | some z =>
    obtain ⟨hz, hmax⟩ := favorite_spec _ hfav
    have hQ := value_le_of_countP_le_one v i (v i z) hmax hQ1
    have := hlt z (List.mem_filter.mp hz).1
    omega

omit [DecidableEq G] in
/-- The shared goods are the relevant goods that are not private. -/
theorem sharedGoods_eq {agents : List A} (hag : agents.Nodup) (i : A) (goods : List G) :
    sharedGoods v agents i goods =
      relevant v i (goods.filter (fun g => !isPrivate v i (agents.erase i) g)) := by
  unfold sharedGoods relevant
  rw [List.filter_filter]
  apply List.filter_congr
  intro g _
  have hp := isPrivate_iff v hag (i := i) (g := g)
  cases h : isPrivate v i (agents.erase i) g
  · have hn : ¬ (0 < v i g ∧ ∀ j ∈ agents, j ≠ i → v j g = 0) := fun h' => by
      have := hp.mpr h'; simp_all
    by_cases hi : 0 < v i g
    · have : ∃ j ∈ agents, j ≠ i ∧ 0 < v j g :=
        Classical.byContradiction fun hno =>
          hn ⟨hi, fun j hj hji => Nat.eq_zero_of_not_pos fun hpos => hno ⟨j, hj, hji, hpos⟩⟩
      simp [hi, this]
    · simp [hi]
  · obtain ⟨hi, hall⟩ := hp.mp h
    have : ¬ ∃ j ∈ agents, j ≠ i ∧ 0 < v j g := fun ⟨j, hj, hji, hpos⟩ => by
      have := hall j hj hji; omega
    simp [this]

omit [DecidableEq G] in
/-- The private goods of `i`, as R2's test selects them. -/
theorem privateGoods_eq {agents : List A} (hag : agents.Nodup) (i : A) (goods : List G) :
    privateGoods v agents i goods = goods.filter (isPrivate v i (agents.erase i)) := by
  unfold privateGoods
  apply List.filter_congr
  intro g _
  rw [Bool.eq_iff_iff, decide_eq_true_eq, isPrivate_iff v hag]

omit [DecidableEq G] in
theorem bundle_ite_left {goods : List G} (T : G → Bool) {X1 X2 : G → A} {j : A}
    (h2 : ∀ g ∈ goods, T g = false → X2 g ≠ j) :
    bundle goods (fun g => if T g then X1 g else X2 g) j = bundle (goods.filter T) X1 j := by
  unfold bundle
  rw [List.filter_filter]
  apply List.filter_congr
  intro g hg
  cases hT : T g
  · simp [hT, h2 g hg hT]
  · simp [hT]

omit [DecidableEq G] in
theorem bundle_ite_right {goods : List G} (T : G → Bool) {X1 X2 : G → A} {j : A}
    (h1 : ∀ g ∈ goods, T g = true → X1 g ≠ j) :
    bundle goods (fun g => if T g then X1 g else X2 g) j = bundle (goods.filter (fun g => !T g)) X2 j := by
  unfold bundle
  rw [List.filter_filter]
  apply List.filter_congr
  intro g hg
  cases hT : T g
  · simp [hT]
  · simp [hT, h1 g hg hT]

/-- **L6 (components).** Split the agents by a test `S` and the goods by a test `T` so that every good
relevant to an agent lies on that agent's side. EFX₀ allocations of the two sides combine into an EFX₀
allocation of everything: across the split, every good of the other side's bundles is worthless. -/
theorem efx0_split {agents : List A} {goods : List G} (S : A → Bool) (T : G → Bool)
    (hST : ∀ i ∈ agents, ∀ g ∈ goods, 0 < v i g → S i = T g) {X1 X2 : G → A}
    (hX1 : IsAllocation (agents.filter S) (goods.filter T) X1)
    (hE1 : EFX0L v (agents.filter S) (goods.filter T) X1)
    (hX2 : IsAllocation (agents.filter (fun i => !S i)) (goods.filter (fun g => !T g)) X2)
    (hE2 : EFX0L v (agents.filter (fun i => !S i)) (goods.filter (fun g => !T g)) X2) :
    IsAllocation agents goods (fun g => if T g then X1 g else X2 g) ∧
      EFX0L v agents goods (fun g => if T g then X1 g else X2 g) := by
  -- the owner of a good is on the good's side
  have hS1 : ∀ g ∈ goods, T g = true → X1 g ∈ agents ∧ S (X1 g) = true := fun g hg hT =>
    List.mem_filter.mp (hX1 g (List.mem_filter.mpr ⟨hg, hT⟩))
  have hS2 : ∀ g ∈ goods, T g = false → X2 g ∈ agents ∧ S (X2 g) = false := fun g hg hT => by
    have := List.mem_filter.mp (hX2 g (List.mem_filter.mpr ⟨hg, by simp [hT]⟩))
    simpa using this
  -- each agent's bundle is its bundle on its side
  have hb1 : ∀ j, S j = true →
      bundle goods (fun g => if T g then X1 g else X2 g) j = bundle (goods.filter T) X1 j :=
    fun j hj => bundle_ite_left T fun g hg hT h => by have := (hS2 g hg hT).2; rw [h, hj] at this; simp at this
  have hb2 : ∀ j, S j = false →
      bundle goods (fun g => if T g then X1 g else X2 g) j = bundle (goods.filter (fun g => !T g)) X2 j :=
    fun j hj => bundle_ite_right T fun g hg hT h => by have := (hS1 g hg hT).2; rw [h, hj] at this; simp at this
  -- a good on the other side is worthless
  have hzero : ∀ i ∈ agents, ∀ (Y : List G), (∀ g ∈ Y, g ∈ goods ∧ T g ≠ S i) → ∀ x, value v i (Y.erase x) = 0 :=
    fun i hi Y hY x => value_eq_zero_of_forall v i fun g hg => by
      obtain ⟨hg, hT⟩ := hY g (List.mem_of_mem_erase hg)
      exact Nat.eq_zero_of_not_pos fun hpos => hT (hST i hi g hg hpos).symm
  constructor
  · intro g hg
    by_cases hT : T g = true
    · simp only [hT, ↓reduceIte]; exact (hS1 g hg hT).1
    · simp only [Bool.not_eq_true] at hT
      simp only [hT, Bool.false_eq_true, ↓reduceIte]; exact (hS2 g hg hT).1
  · intro i hi j hj hij g hg
    cases hSi : S i <;> cases hSj : S j
    · rw [hb2 i hSi, hb2 j hSj] at *
      exact hE2 i (List.mem_filter.mpr ⟨hi, by simp [hSi]⟩) j (List.mem_filter.mpr ⟨hj, by simp [hSj]⟩) hij g hg
    · rw [hb1 j hSj, hzero i hi _ (fun x hx => ?_) g]
      · exact Nat.zero_le _
      · have := List.mem_filter.mp (List.mem_filter.mp hx).1
        exact ⟨this.1, by rw [this.2, hSi]; simp⟩
    · rw [hb2 j hSj, hzero i hi _ (fun x hx => ?_) g]
      · exact Nat.zero_le _
      · have := List.mem_filter.mp (List.mem_filter.mp hx).1
        exact ⟨this.1, by rw [hSi]; simpa using this.2⟩
    · rw [hb1 i hSi, hb1 j hSj] at *
      exact hE1 i (List.mem_filter.mpr ⟨hi, hSi⟩) j (List.mem_filter.mpr ⟨hj, hSj⟩) hij g hg

end lemmas

/-- **The k = 4 CORE theorem with L6** (K4.CORE, `k4/SCOUT.md` §2). If every connected k = 4 core with at
most `N` agents has an EFX₀ allocation, then so does every instance with at most `N` agents in which every
agent has at most four relevant goods. -/
theorem core_reduction4_conn (v : A → G → Nat) (N : Nat)
    (hcore : ∀ (agents : List A) (goods : List G), agents.Nodup → goods.Nodup → agents.length ≤ N →
      IsCore4 v agents goods → Connected v agents goods →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X) :
    ∀ (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
      agents.length ≤ N → (∀ i ∈ agents, (relevant v i goods).length ≤ 4) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  suffices H : ∀ s (agents : List A) (goods : List G), agents.length + goods.length = s →
      agents ≠ [] → agents.Nodup → goods.Nodup → agents.length ≤ N →
      (∀ i ∈ agents, (relevant v i goods).length ≤ 4) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X from
    fun agents goods => H _ agents goods rfl
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
  intro agents goods hs hne hag hgd hN h4
  obtain ⟨i0, hi0⟩ := List.exists_mem_of_ne_nil agents hne
  -- no goods: nothing to allocate
  by_cases hg0 : goods = []
  · subst hg0
    exact ⟨fun _ => i0, fun g hg => by simp at hg, fun _ _ _ _ _ g hg => by simp [bundle] at hg⟩
  -- one agent: it takes everything
  by_cases h1 : agents.length ≤ 1
  · refine ⟨fun _ => i0, fun _ _ => hi0, fun x hx y hy hxy => ?_⟩
    exfalso
    have : x = y := by
      cases agents with
      | nil => simp at hx
      | cons a l =>
        cases l with
        | nil => simp at hx hy; rw [hx, hy]
        | cons b l => simp at h1
    exact hxy this
  -- 1. junk goods (L3)
  by_cases hjunk : ∃ g ∈ goods, isJunk v agents g = true
  · obtain ⟨g, hg, hgj⟩ := hjunk
    have hlt : (goods.filter (fun g => !isJunk v agents g)).length < goods.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g, hg, by simp [hgj]⟩
    obtain ⟨X', hX', hE'⟩ := ih _ (by omega) agents (goods.filter (fun g => !isJunk v agents g)) rfl hne
      hag (hgd.sublist List.filter_sublist) hN
      (fun i hi => Nat.le_trans (relevant_sublist v List.filter_sublist) (h4 i hi))
    exact junk v hne hX' hE'
  -- 2. peeling by R1
  by_cases hR1 : ∃ i ∈ agents, ∃ p ∈ goods, value v i (goods.erase p) ≤ v i p
  · obtain ⟨i, hi, p, hp, htop⟩ := hR1
    have hrest : agents.erase i ≠ [] := by
      intro h
      have := List.length_erase_of_mem hi
      rw [h] at this; simp at this; omega
    have hmeas : (agents.erase i).length + (goods.erase p).length < s := by
      rw [← hs, List.length_erase_of_mem hi, List.length_erase_of_mem hp]
      have := List.length_pos_of_mem hi
      have := List.length_pos_of_mem hp
      omega
    obtain ⟨X', hX', hE'⟩ := ih _ hmeas
      (agents.erase i) (goods.erase p) rfl hrest (hag.erase i) (hgd.erase p)
      (by rw [List.length_erase_of_mem hi]; omega)
      (fun j hj => Nat.le_trans (relevant_sublist v List.erase_sublist) (h4 j (List.mem_of_mem_erase hj)))
    obtain ⟨hX, hE⟩ := peel v (List.Nodup.not_mem_erase hag) hp hgd hX' hE' htop
    exact ⟨_, fun g hg => (mem_cons_erase hi _).mp (hX g hg), efx0L_congr v (mem_cons_erase hi) hE⟩
  -- every agent has at least three relevant goods and is strictly balanced
  have hbal : ∀ i ∈ agents, 3 ≤ (relevant v i goods).length ∧ ∀ g ∈ goods, 2 * v i g < value v i goods :=
    fun i hi => not_R1 v hg0 (fun ⟨p, hp, h⟩ => hR1 ⟨i, hi, p, hp, h⟩)
  -- 3. peeling by R2: an agent whose private goods `P` are worth at least `R_i ∖ P` leaves with them
  by_cases hR2 : ∃ i ∈ agents,
      value v i (relevant v i (goods.filter (fun g => !isPrivate v i (agents.erase i) g))) ≤
        value v i (goods.filter (isPrivate v i (agents.erase i)))
  · obtain ⟨i, hi, hb⟩ := hR2
    have hrest : agents.erase i ≠ [] := by
      intro h
      have := List.length_erase_of_mem hi
      rw [h] at this; simp at this; omega
    have hmeas : (agents.erase i).length +
        (goods.filter (fun g => !isPrivate v i (agents.erase i) g)).length < s := by
      rw [← hs, List.length_erase_of_mem hi]
      have := List.length_pos_of_mem hi
      have := (List.filter_sublist (p := fun g => !isPrivate v i (agents.erase i) g) (l := goods)).length_le
      omega
    obtain ⟨X', hX', hE'⟩ := ih _ hmeas
      (agents.erase i) (goods.filter (fun g => !isPrivate v i (agents.erase i) g)) rfl hrest (hag.erase i)
      (hgd.sublist List.filter_sublist) (by rw [List.length_erase_of_mem hi]; omega)
      (fun j hj => Nat.le_trans (relevant_sublist v List.filter_sublist) (h4 j (List.mem_of_mem_erase hj)))
    obtain ⟨hX, hE⟩ := peelR2 v (List.Nodup.not_mem_erase hag) hX' hE' hb
    exact ⟨_, fun g hg => (mem_cons_erase hi _).mp (hX g hg), efx0L_congr v (mem_cons_erase hi) hE⟩
  -- 4. components (L6): split along a disconnection and solve each side
  by_cases hconn : ¬ Connected v agents goods
  · obtain ⟨S, hS, a, ha, b, hb, hab⟩ : ∃ S : A → Bool,
        (∀ g ∈ goods, ∀ i ∈ agents, ∀ j ∈ agents, 0 < v i g → 0 < v j g → S i = S j) ∧
        ∃ a ∈ agents, ∃ b ∈ agents, S a = true ∧ S b = false := by
      refine Classical.byContradiction fun hno => hconn fun S hS i hi j hj => ?_
      cases hSi : S i <;> cases hSj : S j
      · rfl
      · exact absurd ⟨S, hS, j, hj, i, hi, hSj, hSi⟩ hno
      · exact absurd ⟨S, hS, i, hi, j, hj, hSi, hSj⟩ hno
      · rfl
    let T : G → Bool := fun g => decide (∃ a ∈ agents, S a = true ∧ 0 < v a g)
    have hST : ∀ i ∈ agents, ∀ g ∈ goods, 0 < v i g → S i = T g := by
      intro i hi g hg hpos
      cases hSi : S i
      · refine (decide_eq_false fun ⟨a', ha', hSa', hpa'⟩ => ?_).symm
        have := hS g hg i hi a' ha' hpos hpa'
        rw [hSi, hSa'] at this
        exact Bool.noConfusion this
      · exact (decide_eq_true ⟨i, hi, hSi, hpos⟩).symm
    have hlenS : (agents.filter S).length < agents.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨b, hb, by simp [hab.2]⟩
    have hlenN : (agents.filter (fun i => !S i)).length < agents.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨a, ha, by simp [hab.1]⟩
    have hgS := (List.filter_sublist (p := T) (l := goods)).length_le
    have hgN := (List.filter_sublist (p := fun g => !T g) (l := goods)).length_le
    obtain ⟨X1, hX1, hE1⟩ := ih _ (by omega) (agents.filter S) (goods.filter T) rfl
      (List.ne_nil_of_mem (List.mem_filter.mpr ⟨ha, hab.1⟩)) (hag.filter _) (hgd.filter _) (by omega)
      (fun i hi => Nat.le_trans (relevant_sublist v List.filter_sublist) (h4 i (List.mem_filter.mp hi).1))
    obtain ⟨X2, hX2, hE2⟩ := ih _ (by omega) (agents.filter (fun i => !S i)) (goods.filter (fun g => !T g))
      rfl (List.ne_nil_of_mem (List.mem_filter.mpr ⟨hb, by simp [hab.2]⟩)) (hag.filter _) (hgd.filter _)
      (by omega)
      (fun i hi => Nat.le_trans (relevant_sublist v List.filter_sublist) (h4 i (List.mem_filter.mp hi).1))
    exact ⟨_, efx0_split v S T hST hX1 hE1 hX2 hE2⟩
  have hconn : Connected v agents goods := Classical.byContradiction hconn
  -- 5. a connected k = 4 core
  have hq : ∀ i, ∀ g, isPrivate v i (agents.erase i) g = true → 0 < v i g :=
    fun i g hg => ((isPrivate_iff v hag).mp hg).1
  refine hcore agents goods hag hgd hN ⟨by omega, fun i hi => ⟨(hbal i hi).1, h4 i hi⟩,
    fun i hi => (hbal i hi).2, fun i hi => ?_, fun i hi _ => ?_, fun g hg => ?_⟩ hconn
  · -- (C3): at least two relevant goods are shared, or else R2 applies
    rw [privateGoods_eq v hag, length_relevant_split v i _ goods (hq i)]
    refine Nat.add_le_add_left (Nat.le_of_not_lt fun hlt => hR2 ⟨i, hi, ?_⟩) _
    exact R2_balance_of_le_one v _ (hbal i hi).2 (by omega)
  · -- (C4): the private goods are worth less than the shared ones, or else R2 applies
    rw [privateGoods_eq v hag, sharedGoods_eq v hag]
    exact Nat.lt_of_not_le fun hle => hR2 ⟨i, hi, hle⟩
  · refine Classical.byContradiction fun hno => hjunk ⟨g, hg, ?_⟩
    simp only [isJunk, List.all_eq_true, beq_iff_eq]
    intro j hj
    exact Nat.eq_zero_of_not_pos fun hpos => hno ⟨j, hj, hpos⟩

/-- **The k = 4 CORE theorem** (K4.CORE, `k4/SCOUT.md` §2). If every k = 4 core with at most `N` agents has
an EFX₀ allocation, then so does every instance with at most `N` agents in which every agent has at most
four relevant goods. -/
theorem core_reduction4 (v : A → G → Nat) (N : Nat)
    (hcore : ∀ (agents : List A) (goods : List G), agents.Nodup → goods.Nodup → agents.length ≤ N →
      IsCore4 v agents goods → ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X) :
    ∀ (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
      agents.length ≤ N → (∀ i ∈ agents, (relevant v i goods).length ≤ 4) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X :=
  core_reduction4_conn v N fun agents goods hag hgd hN hc _ => hcore agents goods hag hgd hN hc

omit [DecidableEq G] in
/-- A k = 4 core whose agents all have three relevant goods is a core (`EFX.IsCore`). -/
theorem isCore_of_isCore4 (v : A → G → Nat) {agents : List A} {goods : List G} (hc : IsCore4 v agents goods)
    (h3 : ∀ i ∈ agents, (relevant v i goods).length = 3) : IsCore v agents goods := by
  obtain ⟨h0, -, h2, h3', -, h5⟩ := hc
  exact ⟨h0, h3, h2, fun i hi => by have := h3' i hi; have := h3 i hi; omega, h5⟩

omit [DecidableEq G] in
/-- Conversely, a core (`EFX.IsCore`) is a k = 4 core. -/
theorem isCore4_of_isCore (v : A → G → Nat) {agents : List A} {goods : List G} (hc : IsCore v agents goods) :
    IsCore4 v agents goods := by
  obtain ⟨h0, h1, h2, h3, h5⟩ := hc
  refine ⟨h0, fun i hi => by have := h1 i hi; omega, h2, fun i hi => ?_, fun i hi h => ?_, h5⟩
  · have := h1 i hi; have := h3 i hi; omega
  · have := h3 i hi; omega

/-- **The k = 4 CORE theorem, new cores only.** It suffices to treat the connected k = 4 cores in which some
agent has four relevant goods: a k = 4 core whose agents all have three is a core (`EFX.IsCore`,
`isCore_of_isCore4`), and Corollary D covers it. -/
theorem core_reduction4_mixed (v : A → G → Nat) (N : Nat)
    (hcore : ∀ (agents : List A) (goods : List G), agents.Nodup → goods.Nodup → agents.length ≤ N →
      IsCore4 v agents goods → Connected v agents goods → (∃ i ∈ agents, (relevant v i goods).length = 4) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X) :
    ∀ (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
      agents.length ≤ N → (∀ i ∈ agents, (relevant v i goods).length ≤ 4) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  refine core_reduction4_conn v N fun agents goods hag hgd hN hc hconn => ?_
  by_cases h4 : ∃ i ∈ agents, (relevant v i goods).length = 4
  · exact hcore agents goods hag hgd hN hc hconn h4
  have h3 : ∀ i ∈ agents, (relevant v i goods).length = 3 := fun i hi => by
    have := (hc.2.1 i hi).1
    have := (hc.2.1 i hi).2
    have : (relevant v i goods).length ≠ 4 := fun h => h4 ⟨i, hi, h⟩
    omega
  obtain ⟨hlen, hk1, hk2, -, -⟩ := isCore_of_isCore4 v hc h3
  have hne : agents ≠ [] := fun h => by rw [h] at hlen; simp at hlen
  obtain ⟨X, hX, hE, -⟩ := LB.corollaryD_lists v hag hgd hne hk1 (fun i hi g hg => Nat.le_of_lt (hk2 i hi g hg))
  exact ⟨X, hX, hE⟩

/-- **The k = 4 CORE theorem in the model's terms.** If every connected k = 4 core of `I`'s agents and goods
with at most `N` agents, some agent having four relevant goods, has an EFX₀ allocation, and every agent of `I`
positively values at most four goods (`|R_i| ≤ 4`), then `I` has a complete EFX₀ allocation. -/
theorem target4_of_cores (I : Inst) (hn : 0 < I.n) (N : Nat) (hN : I.n ≤ N)
    (hcore : ∀ (agents : List (Fin I.n)) (goods : List (Fin I.m)), agents.Nodup → goods.Nodup →
      agents.length ≤ N → IsCore4 I.v agents goods → Connected I.v agents goods →
      (∃ i ∈ agents, (relevant I.v i goods).length = 4) →
      ∃ X : Fin I.m → Fin I.n, IsAllocation agents goods X ∧ EFX0L I.v agents goods X)
    (h : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X := by
  obtain ⟨X, -, hE⟩ := core_reduction4_mixed I.v N hcore (List.finRange I.n)
    (List.finRange I.m) (List.ne_nil_of_mem (List.mem_finRange ⟨0, hn⟩)) (List.nodup_finRange I.n)
    (List.nodup_finRange I.m) (by rw [List.length_finRange]; exact hN)
    (fun i _ => (numRelevant_eq I i) ▸ h i)
  exact ⟨X, (Inst.efx0_iff I X).mpr hE⟩

end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.length_relevant_split
#print axioms EFX.R2_balance_of_le_one
#print axioms EFX.sharedGoods_eq
#print axioms EFX.privateGoods_eq
#print axioms EFX.bundle_ite_left
#print axioms EFX.bundle_ite_right
#print axioms EFX.efx0_split
#print axioms EFX.core_reduction4_conn
#print axioms EFX.core_reduction4
#print axioms EFX.isCore_of_isCore4
#print axioms EFX.isCore4_of_isCore
#print axioms EFX.core_reduction4_mixed
#print axioms EFX.target4_of_cores
