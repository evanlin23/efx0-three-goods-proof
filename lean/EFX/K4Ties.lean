import EFX.K4Reduction

/-!
# Ties reduce to strict profiles at k = 4 (`k4/SCOUT.md` §2, K4.TIE)

- `Strict`: a *strict* profile: every agent values any two disjoint nonempty sets of its relevant goods
  differently (stated as: two disjoint sets of goods an agent values equally are both worthless to it).
- `tie_reduction`: **K4.TIE**. If every strict profile with the same relevant goods as a connected k = 4
  core has an EFX₀ allocation, so does the core itself.
- `target4_of_strict_cores`: K4.CORE with K4.TIE. If every connected, strict k = 4 core with at most `N`
  agents, some agent having four relevant goods, has an EFX₀ allocation, then so does every instance with at
  most `N` agents and at most four relevant goods per agent.

The written proof perturbs `v_i` to `v_i + ε w_i` and argues by closedness. Over ℕ the same perturbation is
`tieBreak v goods = M · v + w` with `M = 2 ^ |goods|` and `w_i(g) = 2 ^ (number of goods after g)` on `R_i`,
`0` elsewhere: every `w_i`-sum over goods is below `M`, so `M · v + w` orders any two sets as `v` does when
`v` separates them, and as `w` does (strictly, `w` being superincreasing) when `v` ties them. An EFX₀
allocation for `M · v + w` is therefore EFX₀ for `v`: that is the closedness step.
-/

set_option autoImplicit false

namespace EFX

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- A strict profile (`k4/SCOUT.md` §2, K4.TIE): for every agent `i`, two disjoint sets of goods that `i`
values equally are both worthless to `i`. Equivalently, disjoint nonempty `S, T ⊆ R_i` have
`v_i(S) ≠ v_i(T)`. -/
def Strict (v : A → G → Nat) (agents : List A) (goods : List G) : Prop :=
  ∀ i ∈ agents, ∀ S T : List G, S.Sublist goods → T.Sublist goods → (∀ g ∈ S, g ∉ T) →
    value v i S = value v i T → value v i S = 0

/-- The tie-breaking weight of a good in a list: `2 ^ (number of goods after it)`. -/
def tieWeight : List G → G → Nat
  | [], _ => 0
  | a :: rest, g => if g = a then 2 ^ rest.length else tieWeight rest g

/-- The perturbation `M · v + w` (`k4/SCOUT.md` §2, K4.TIE) with `M = 2 ^ |goods|` and
`w_i(g) = tieWeight goods g` on `R_i`, `0` elsewhere. -/
def tieBreak (v : A → G → Nat) (goods : List G) (i : A) (g : G) : Nat :=
  2 ^ goods.length * v i g + (if 0 < v i g then tieWeight goods g else 0)

section weights

theorem map_tieWeight_cons {a : G} {rest S : List G} (ha : a ∉ rest) (hS : S.Sublist rest)
    (f : G → Nat) :
    S.map (fun g => if 0 < f g then tieWeight (a :: rest) g else 0) =
      S.map (fun g => if 0 < f g then tieWeight rest g else 0) := by
  apply List.map_congr_left
  intro g hg
  have hga : g ≠ a := fun h => ha (h ▸ hS.subset hg)
  simp [tieWeight, hga]

/-- The weights of a duplicate-free list sum to less than `2 ^ length`, on any sublist. -/
theorem sum_tieWeight_lt (f : G → Nat) :
    ∀ {l : List G}, l.Nodup → ∀ {S : List G}, S.Sublist l →
      (S.map (fun g => if 0 < f g then tieWeight l g else 0)).sum < 2 ^ l.length
  | [], _, S, hS => by rw [List.sublist_nil.mp hS]; simp
  | a :: rest, hnd, S, hS => by
    have ha := (List.nodup_cons.mp hnd).1
    have hr := (List.nodup_cons.mp hnd).2
    rcases List.sublist_cons_iff.mp hS with hS | ⟨S', rfl, hS'⟩
    · rw [map_tieWeight_cons ha hS]
      have := sum_tieWeight_lt f hr hS
      simp only [List.length_cons, Nat.pow_succ]
      omega
    · rw [List.map_cons, List.sum_cons, map_tieWeight_cons ha hS']
      have := sum_tieWeight_lt f hr hS'
      have : (if 0 < f a then tieWeight (a :: rest) a else 0) ≤ 2 ^ rest.length := by
        split <;> simp [tieWeight]
      simp only [List.length_cons, Nat.pow_succ]
      omega

/-- The weights separate sets: if two disjoint sublists have the same weight on the goods relevant to `f`,
neither contains such a good. -/
theorem tieWeight_strict (f : G → Nat) :
    ∀ {l : List G}, l.Nodup → ∀ {S T : List G}, S.Sublist l → T.Sublist l → (∀ g ∈ S, g ∉ T) →
      (S.map (fun g => if 0 < f g then tieWeight l g else 0)).sum =
        (T.map (fun g => if 0 < f g then tieWeight l g else 0)).sum → ∀ g ∈ S, f g = 0
  | [], _, S, _, hS, _, _, _ => by rw [List.sublist_nil.mp hS]; simp
  | a :: rest, hnd, S, T, hS, hT, hdis, heq => by
    have ha := (List.nodup_cons.mp hnd).1
    have hr := (List.nodup_cons.mp hnd).2
    have htop : 0 < f a → (if 0 < f a then tieWeight (a :: rest) a else 0) = 2 ^ rest.length := by
      intro h; simp [h, tieWeight]
    have hzero : ¬ 0 < f a → (if 0 < f a then tieWeight (a :: rest) a else 0) = 0 := by
      intro h; simp [h]
    rcases List.sublist_cons_iff.mp hS with hS | ⟨S', rfl, hS'⟩ <;>
      rcases List.sublist_cons_iff.mp hT with hT | ⟨T', rfl, hT'⟩
    · rw [map_tieWeight_cons ha hS, map_tieWeight_cons ha hT] at heq
      exact tieWeight_strict f hr hS hT hdis heq
    · rw [List.map_cons, List.sum_cons, map_tieWeight_cons ha hS, map_tieWeight_cons ha hT'] at heq
      have hlt := sum_tieWeight_lt f hr hS
      by_cases hfa : 0 < f a
      · rw [htop hfa] at heq; omega
      · rw [hzero hfa, Nat.zero_add] at heq
        exact tieWeight_strict f hr hS hT' (fun g hg hgT => hdis g hg (List.mem_cons_of_mem _ hgT)) heq
    · rw [List.map_cons, List.sum_cons, map_tieWeight_cons ha hS', map_tieWeight_cons ha hT] at heq
      have hlt := sum_tieWeight_lt f hr hT
      by_cases hfa : 0 < f a
      · rw [htop hfa] at heq; omega
      · rw [hzero hfa, Nat.zero_add] at heq
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact Nat.eq_zero_of_not_pos hfa
        · exact tieWeight_strict f hr hS' hT (fun x hx => hdis x (List.mem_cons_of_mem _ hx)) heq g hg
    · exact absurd (List.mem_cons_self) (hdis a List.mem_cons_self)

end weights

section perturbation
variable (v : A → G → Nat) (goods : List G)

omit [DecidableEq A] in
theorem pos_tieBreak_iff (i : A) (g : G) : 0 < tieBreak v goods i g ↔ 0 < v i g := by
  unfold tieBreak
  constructor
  · intro h
    refine Nat.pos_of_ne_zero fun h0 => ?_
    simp [h0] at h
  · intro h
    have : 0 < 2 ^ goods.length * v i g := Nat.mul_pos (Nat.two_pow_pos _) h
    omega

omit [DecidableEq A] in
theorem tieBreak_eq_zero_iff (i : A) (g : G) : tieBreak v goods i g = 0 ↔ v i g = 0 := by
  have := pos_tieBreak_iff v goods i g
  omega

omit [DecidableEq A] in
theorem value_tieBreak (i : A) (S : List G) :
    value (tieBreak v goods) i S = 2 ^ goods.length * value v i S +
      (S.map (fun g => if 0 < v i g then tieWeight goods g else 0)).sum := by
  induction S with
  | nil => simp [value]
  | cons g S ih =>
    rw [value_cons, value_cons, ih, List.map_cons, List.sum_cons, tieBreak, Nat.mul_add]
    omega

omit [DecidableEq A] in
theorem relevant_tieBreak (i : A) (S : List G) : relevant (tieBreak v goods) i S = relevant v i S := by
  unfold relevant
  apply List.filter_congr
  intro g _
  simp [pos_tieBreak_iff]

/-- Removing the perturbation: an EFX₀ allocation for `tieBreak v goods` is EFX₀ for `v`. -/
theorem efx0_of_tieBreak {agents : List A} (hgd : goods.Nodup) {X : G → A}
    (hE : EFX0L (tieBreak v goods) agents goods X) : EFX0L v agents goods X := by
  intro i hi j hj hij g hg
  have h := hE i hi j hj hij g hg
  rw [value_tieBreak, value_tieBreak] at h
  have hlt : ((bundle goods X i).map (fun g => if 0 < v i g then tieWeight goods g else 0)).sum <
      2 ^ goods.length :=
    sum_tieWeight_lt (v i) hgd List.filter_sublist
  refine Nat.le_of_not_lt fun hgt => ?_
  have := Nat.mul_le_mul_left (2 ^ goods.length) (Nat.succ_le_of_lt hgt)
  rw [Nat.mul_succ] at this
  omega

theorem isCore4_tieBreak {agents : List A} (hgd : goods.Nodup) (hc : IsCore4 v agents goods) :
    IsCore4 (tieBreak v goods) agents goods := by
  obtain ⟨hlen, hk1, hk2, hk3, hk4, hk5⟩ := hc
  have hpriv : ∀ i, privateGoods (tieBreak v goods) agents i goods = privateGoods v agents i goods := by
    intro i
    unfold privateGoods
    apply List.filter_congr
    intro g _
    simp [pos_tieBreak_iff, tieBreak_eq_zero_iff]
  have hshared : ∀ i, sharedGoods (tieBreak v goods) agents i goods = sharedGoods v agents i goods := by
    intro i
    unfold sharedGoods
    apply List.filter_congr
    intro g _
    simp [pos_tieBreak_iff]
  refine ⟨hlen, fun i hi => ?_, fun i hi g hg => ?_, fun i hi => ?_, fun i hi h2 => ?_, fun g hg => ?_⟩
  · rw [relevant_tieBreak]; exact hk1 i hi
  · -- strict balance survives: `2 (M v(g) + w(g)) < M v(M) + w(M)` since `w(g) ≤ w(M) < M`
    have hb := Nat.mul_le_mul_left (2 ^ goods.length) (Nat.succ_le_of_lt (hk2 i hi g hg))
    rw [Nat.mul_succ, Nat.mul_left_comm] at hb
    have hlt := sum_tieWeight_lt (v i) hgd (List.Sublist.refl goods)
    have hle : (if 0 < v i g then tieWeight goods g else 0) ≤
        (goods.map (fun g => if 0 < v i g then tieWeight goods g else 0)).sum :=
      le_value_of_mem (fun i g => if 0 < v i g then tieWeight goods g else 0) i hg
    rw [value_tieBreak]
    unfold tieBreak
    omega
  · rw [hpriv, relevant_tieBreak]; exact hk3 i hi
  · rw [hpriv] at h2 ⊢
    rw [hshared, value_tieBreak, value_tieBreak]
    have hb := Nat.mul_le_mul_left (2 ^ goods.length) (Nat.succ_le_of_lt (hk4 i hi h2))
    rw [Nat.mul_succ] at hb
    have hlt : ((privateGoods v agents i goods).map
        (fun g => if 0 < v i g then tieWeight goods g else 0)).sum < 2 ^ goods.length :=
      sum_tieWeight_lt (v i) hgd List.filter_sublist
    omega
  · obtain ⟨i, hi, hpos⟩ := hk5 g hg
    exact ⟨i, hi, (pos_tieBreak_iff v goods i g).mpr hpos⟩

omit [DecidableEq A] in
theorem connected_tieBreak {agents : List A} (hconn : Connected v agents goods) :
    Connected (tieBreak v goods) agents goods := by
  intro S hS
  refine hconn S fun g hg i hi j hj hpi hpj => hS g hg i hi j hj ?_ ?_
  · exact (pos_tieBreak_iff v goods i g).mpr hpi
  · exact (pos_tieBreak_iff v goods j g).mpr hpj

omit [DecidableEq A] in
theorem strict_tieBreak {agents : List A} (hgd : goods.Nodup) : Strict (tieBreak v goods) agents goods := by
  intro i _ S T hS hT hdis heq
  rw [value_tieBreak, value_tieBreak] at heq
  rw [value_tieBreak]
  have hSlt := sum_tieWeight_lt (v i) hgd hS
  have hTlt := sum_tieWeight_lt (v i) hgd hT
  -- `M · a + b = M · c + d` with `b, d < M` forces `b = d`
  have hmod := congrArg (· % 2 ^ goods.length) heq
  simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt hSlt, Nat.mod_eq_of_lt hTlt] at hmod
  have hz := tieWeight_strict (v i) hgd hS hT hdis hmod
  rw [value_eq_zero_of_forall v i hz]
  have : (S.map (fun g => if 0 < v i g then tieWeight goods g else 0)).sum = 0 :=
    value_eq_zero_of_forall (fun i g => if 0 < v i g then tieWeight goods g else 0) i
      (fun g hg => by simp [hz g hg])
  rw [this]
  simp

end perturbation

/-- **K4.TIE** (`k4/SCOUT.md` §2). If every strict profile `w` with the same relevant goods as `v` that is
itself a connected k = 4 core has an EFX₀ allocation, then so does the connected k = 4 core `v`. -/
theorem tie_reduction (v : A → G → Nat) {agents : List A} {goods : List G} (hgd : goods.Nodup)
    (hstrict : ∀ w : A → G → Nat, (∀ i g, 0 < w i g ↔ 0 < v i g) → IsCore4 w agents goods →
      Connected w agents goods → Strict w agents goods →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L w agents goods X)
    (hc : IsCore4 v agents goods) (hconn : Connected v agents goods) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  obtain ⟨X, hX, hE⟩ := hstrict (tieBreak v goods) (pos_tieBreak_iff v goods) (isCore4_tieBreak v goods hgd hc)
    (connected_tieBreak v goods hconn) (strict_tieBreak v goods hgd)
  exact ⟨X, hX, efx0_of_tieBreak v goods hgd hE⟩

/-- **K4.CORE with K4.TIE.** If every connected, strict k = 4 core with at most `N` agents in which some agent
has four relevant goods has an EFX₀ allocation, then so does every instance with at most `N` agents in which
every agent has at most four relevant goods. -/
theorem core_reduction4_strict (N : Nat)
    (hcore : ∀ (w : A → G → Nat) (agents : List A) (goods : List G), agents.Nodup → goods.Nodup →
      agents.length ≤ N → IsCore4 w agents goods → Connected w agents goods → Strict w agents goods →
      (∃ i ∈ agents, (relevant w i goods).length = 4) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L w agents goods X)
    (v : A → G → Nat) :
    ∀ (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
      agents.length ≤ N → (∀ i ∈ agents, (relevant v i goods).length ≤ 4) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X :=
  core_reduction4_mixed v N fun agents goods hag hgd hN hc hconn ⟨i, hi, h4⟩ =>
    tie_reduction v hgd (fun w hw hcw hconnw hsw => hcore w agents goods hag hgd hN hcw hconnw hsw
      ⟨i, hi, by
        have : relevant w i goods = relevant v i goods := List.filter_congr fun g _ => by simp [hw]
        rw [this]; exact h4⟩) hc hconn

/-- **K4.CORE with K4.TIE in the model's terms.** If every connected, strict k = 4 core on `I`'s agents and
goods (any values) with at most `N` agents, some agent having four relevant goods, has an EFX₀ allocation, and
every agent of `I` positively values at most four goods (`|R_i| ≤ 4`), then `I` has a complete EFX₀
allocation. -/
theorem target4_of_strict_cores (I : Inst) (hn : 0 < I.n) (N : Nat) (hN : I.n ≤ N)
    (hcore : ∀ (w : Fin I.n → Fin I.m → Nat) (agents : List (Fin I.n)) (goods : List (Fin I.m)),
      agents.Nodup → goods.Nodup → agents.length ≤ N → IsCore4 w agents goods → Connected w agents goods →
      Strict w agents goods → (∃ i ∈ agents, (relevant w i goods).length = 4) →
      ∃ X : Fin I.m → Fin I.n, IsAllocation agents goods X ∧ EFX0L w agents goods X)
    (h : ∀ i, numRelevant I i ≤ 4) : ∃ X : I.Alloc, I.EFX0 X := by
  obtain ⟨X, -, hE⟩ := core_reduction4_strict N hcore I.v (List.finRange I.n) (List.finRange I.m)
    (List.ne_nil_of_mem (List.mem_finRange ⟨0, hn⟩)) (List.nodup_finRange I.n) (List.nodup_finRange I.m)
    (by rw [List.length_finRange]; exact hN) (fun i _ => (numRelevant_eq I i) ▸ h i)
  exact ⟨X, (Inst.efx0_iff I X).mpr hE⟩

end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.map_tieWeight_cons
#print axioms EFX.sum_tieWeight_lt
#print axioms EFX.tieWeight_strict
#print axioms EFX.pos_tieBreak_iff
#print axioms EFX.tieBreak_eq_zero_iff
#print axioms EFX.value_tieBreak
#print axioms EFX.relevant_tieBreak
#print axioms EFX.efx0_of_tieBreak
#print axioms EFX.isCore4_tieBreak
#print axioms EFX.connected_tieBreak
#print axioms EFX.strict_tieBreak
#print axioms EFX.tie_reduction
#print axioms EFX.core_reduction4_strict
#print axioms EFX.target4_of_strict_cores
