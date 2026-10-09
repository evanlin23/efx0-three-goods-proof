import EFX.Target

/-!
# Algorithm K3ALG: the specification and its correctness (`proofs/k3_algorithm.md` §2–§3)

A computable composition of proven constructions that returns an EFX₀ allocation of every instance in which
every agent positively values at most three goods:

1. `reduce`: while at least two agents and some goods remain, the first agent (in list order) to which rule R1
   applies is removed (`r1Step`, `findR1`). If it values no remaining good it leaves with nothing (R1 with
   `P = ∅`, `EFX.peelEmpty`); otherwise it leaves with its favourite remaining good `p`, which it values at
   least as much as all other remaining goods together (R1, `EFX.peel`). One agent left takes everything.
2. When R1 applies to nobody, every remaining agent has exactly three relevant goods and is strictly balanced
   (`EFX.not_R1`). Its ranking is computed by sorting its three goods (`sort3`, `profileOf`), Phase 1's order
   by `EFX.LB.r1Order`, and the allocation by construction LB⁺ (`EFX.LB.lbPlus`), which is EFX₀ by Theorem C
   (`EFX.LB.lbPlus_sound`). Goods that no remaining agent values are allowed there, so neither rule L3 nor rule
   R2 of the CORE reduction is needed.

- `reduce_sound`: the output of `reduce` is a complete allocation and EFX₀ (over lists).
- `algoSpec`, `algoSpec_efx0`: the same for the model's instances (`EFX.Inst`, `EFX.Inst.EFX0`).

`EFX.K3Cost` defines the algorithm `EFX.K3.algo` as this computation with tables and an operation counter, and
proves that it equals `algoSpec` and runs in `O((n + m)⁴)` counted operations.

Owner test (`proofs/k3_algorithm.md` §4): LB⁺ tests the owner `r` with `EFX.LB.hitSet`, one junk good per
exposed pair and one shared good for the first two pairs that meet. By `EFX.LB.validOwner_iff` this test is
exact: `r` is a valid owner (Lemma 1's condition holds for *some* set of junk goods, so a minimum hitting set
fits) iff `hitSet` fits. No minimum vertex cover is computed.
-/

set_option autoImplicit false

namespace EFX
namespace K3

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Rule R1 -/

/-- Rule R1 for agent `i` on the remaining `goods`: `some none` if `i` values no remaining good (it leaves with
nothing), `some (some p)` if its favourite `p` is worth at least all other remaining goods together (it leaves
with `p`), and `none` if R1 does not apply. -/
def r1Step (v : A → G → Nat) (goods : List G) (i : A) : Option (Option G) :=
  match favorite (v i) goods with
  | none => some none
  | some p =>
    if v i p = 0 then some none
    else if value v i (goods.erase p) ≤ v i p then some (some p) else none

/-- The first agent of `agents` to which R1 applies, with its bundle. -/
def findR1 (v : A → G → Nat) (agents : List A) (goods : List G) : Option (A × Option G) :=
  agents.findSome? (fun i => (r1Step v goods i).map (fun s => (i, s)))

/-! ## Rankings -/

/-- Three goods sorted by `f`, largest first, ties in list order; `(g0, g0, g0)` for a list that does not have
exactly three goods. -/
def sort3 (f : G → Nat) (g0 : G) : List G → G × G × G
  | [x, y, z] =>
    if f y ≤ f x then
      (if f z ≤ f y then (x, y, z) else if f z ≤ f x then (x, z, y) else (z, x, y))
    else
      (if f z ≤ f x then (y, x, z) else if f z ≤ f y then (y, z, x) else (z, y, x))
  | _ => (g0, g0, g0)

/-- The rankings: agent `i` ranks its relevant goods among `goods` by value (`sort3`). -/
def profileOf (v : A → G → Nat) (goods : List G) (g0 : G) : LB.Profile A G :=
  ⟨fun i => (sort3 (v i) g0 (relevant v i goods)).1, fun i => (sort3 (v i) g0 (relevant v i goods)).2.1,
    fun i => (sort3 (v i) g0 (relevant v i goods)).2.2⟩

/-! ## The algorithm -/

/-- LB⁺ with the computed rankings and Phase 1 in `r1Order` (the first agent with at most two goods left, else
the first agent). -/
def lbStage (v : A → G → Nat) (agents : List A) (goods : List G) (g0 : G) (d : A) : G → A :=
  LB.lbPlus (profileOf v goods g0) agents goods (LB.r1Order (profileOf v goods g0) agents.length agents goods) d

/-- **The algorithm, over lists**, with `fuel ≥` the number of agents: peel by R1 while it applies to some agent
(at least two agents and some goods left), then LB⁺. The agent `d` only receives goods in unreachable cases. -/
def reduce (v : A → G → Nat) (d : A) : Nat → List A → List G → G → A
  | 0, _, _ => fun _ => d
  | fuel + 1, agents, goods =>
    if agents.length ≤ 1 then fun _ => agents.headD d
    else
      match goods with
      | [] => fun _ => d
      | g0 :: gs =>
        match findR1 v agents (g0 :: gs) with
        | some (i, none) => reduce v d fuel (agents.erase i) (g0 :: gs)
        | some (i, some p) => extend i p (reduce v d fuel (agents.erase i) ((g0 :: gs).erase p))
        | none => lbStage v agents (g0 :: gs) g0 d

/-! ## Correctness -/

section proofs

omit [DecidableEq A] in
theorem findR1_some {v : A → G → Nat} {agents : List A} {goods : List G} {i : A} {s : Option G}
    (h : findR1 v agents goods = some (i, s)) : i ∈ agents ∧ r1Step v goods i = some s := by
  obtain ⟨j, hj, hm⟩ := List.exists_of_findSome?_eq_some h
  cases hr : r1Step v goods j with
  | none => rw [hr] at hm; cases hm
  | some s' =>
    rw [hr] at hm
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ⟨hj, hr⟩

omit [DecidableEq A] in
theorem findR1_none {v : A → G → Nat} {agents : List A} {goods : List G}
    (h : findR1 v agents goods = none) : ∀ i ∈ agents, r1Step v goods i = none := by
  intro i hi
  have := List.findSome?_eq_none_iff.mp h i hi
  cases hr : r1Step v goods i with
  | none => rfl
  | some s => rw [hr] at this; cases this

omit [DecidableEq A] in
/-- `r1Step` returns `some none` only when `i` values no remaining good. -/
theorem r1Step_none_zero {v : A → G → Nat} {goods : List G} {i : A}
    (h : r1Step v goods i = some none) : ∀ g ∈ goods, v i g = 0 := by
  unfold r1Step at h
  cases hf : favorite (v i) goods with
  | none =>
    rw [(favorite_eq_none_iff _).mp hf]
    intro g hg; simp at hg
  | some p =>
    rw [hf] at h
    simp only at h
    obtain ⟨-, hmax⟩ := favorite_spec _ hf
    by_cases h0 : v i p = 0
    · intro g hg; have := hmax g hg; omega
    · simp only [h0, ↓reduceIte] at h
      split at h <;> cases h

omit [DecidableEq A] in
/-- `r1Step` returns `some (some p)` only when R1 applies with `p`. -/
theorem r1Step_some {v : A → G → Nat} {goods : List G} {i : A} {p : G}
    (h : r1Step v goods i = some (some p)) : p ∈ goods ∧ value v i (goods.erase p) ≤ v i p := by
  unfold r1Step at h
  cases hf : favorite (v i) goods with
  | none => rw [hf] at h; cases h
  | some q =>
    rw [hf] at h
    simp only at h
    obtain ⟨hq, -⟩ := favorite_spec _ hf
    by_cases h0 : v i q = 0
    · simp [h0] at h
    · simp only [h0, ↓reduceIte] at h
      split at h
      · rename_i hle
        cases h
        exact ⟨hq, hle⟩
      · cases h

omit [DecidableEq A] in
/-- If `r1Step` returns `none`, R1 applies with no good: every good is worth less than the other goods together. -/
theorem r1Step_eq_none {v : A → G → Nat} {goods : List G} {i : A}
    (h : r1Step v goods i = none) : ¬ ∃ q ∈ goods, value v i (goods.erase q) ≤ v i q := by
  rintro ⟨q, hq, hle⟩
  unfold r1Step at h
  cases hf : favorite (v i) goods with
  | none => rw [hf] at h; cases h
  | some p =>
    rw [hf] at h
    simp only at h
    obtain ⟨hp, hmax⟩ := favorite_spec _ hf
    by_cases h0 : v i p = 0
    · simp [h0] at h
    · simp only [h0, ↓reduceIte] at h
      split at h
      · cases h
      · rename_i hgt
        have e1 := value_erase v (i := i) hp
        have e2 := value_erase v (i := i) hq
        have := hmax q hq
        omega

omit [DecidableEq A] [DecidableEq G] in
/-- `sort3` returns the three goods in some order, sorted by `f`. -/
theorem sort3_spec (f : G → Nat) (g0 x y z : G) :
    f (sort3 f g0 [x, y, z]).2.2 ≤ f (sort3 f g0 [x, y, z]).2.1 ∧
    f (sort3 f g0 [x, y, z]).2.1 ≤ f (sort3 f g0 [x, y, z]).1 ∧
    (sort3 f g0 [x, y, z] = (x, y, z) ∨ sort3 f g0 [x, y, z] = (x, z, y) ∨
      sort3 f g0 [x, y, z] = (y, x, z) ∨ sort3 f g0 [x, y, z] = (y, z, x) ∨
      sort3 f g0 [x, y, z] = (z, x, y) ∨ sort3 f g0 [x, y, z] = (z, y, x)) := by
  simp only [sort3]
  by_cases h1 : f y ≤ f x <;> by_cases h2 : f z ≤ f y <;> by_cases h3 : f z ≤ f x <;>
    simp [h1, h2, h3] <;> omega

omit [DecidableEq A] [DecidableEq G] in
/-- For an agent with exactly three relevant goods among distinct `goods`, balanced, `sort3` gives its ranking:
three distinct goods of `goods`, `a ≥ b ≥ c > 0`, `a ≤ b + c`, and every other good of `goods` is worthless. -/
theorem sort3_ranking (v : A → G → Nat) (i : A) {goods : List G} (g0 : G) (hgd : goods.Nodup)
    (h3 : (relevant v i goods).length = 3) (hbal : ∀ g ∈ goods, 2 * v i g ≤ value v i goods) :
    let t := sort3 (v i) g0 (relevant v i goods)
    t.1 ∈ goods ∧ t.2.1 ∈ goods ∧ t.2.2 ∈ goods ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
      0 < v i t.2.2 ∧ v i t.2.2 ≤ v i t.2.1 ∧ v i t.2.1 ≤ v i t.1 ∧ v i t.1 ≤ v i t.2.1 + v i t.2.2 ∧
      ∀ g ∈ goods, g ≠ t.1 → g ≠ t.2.1 → g ≠ t.2.2 → v i g = 0 := by
  obtain ⟨x, y, z, hxyz⟩ := LB.eq_of_length_three h3
  have hnd : (relevant v i goods).Nodup := hgd.sublist List.filter_sublist
  rw [hxyz] at hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
    not_or] at hnd
  obtain ⟨⟨hxy, hxz⟩, hyz, -⟩ := hnd
  have hmem : ∀ g, g ∈ relevant v i goods ↔ g ∈ goods ∧ 0 < v i g := by
    intro g; simp [relevant]
  have hx := (hmem x).mp (by rw [hxyz]; simp)
  have hy := (hmem y).mp (by rw [hxyz]; simp)
  have hz := (hmem z).mp (by rw [hxyz]; simp)
  have hother : ∀ g ∈ goods, g ≠ x → g ≠ y → g ≠ z → v i g = 0 := by
    intro g hg h1 h2 h3'
    refine Nat.eq_zero_of_not_pos fun hpos => ?_
    have := (hmem g).mpr ⟨hg, hpos⟩
    rw [hxyz] at this
    simp [h1, h2, h3'] at this
  have hsum : value v i goods = v i x + v i y + v i z := by
    rw [← value_relevant v i goods, hxyz]
    simp only [value_cons, value_nil]
    omega
  simp only [hxyz]
  obtain ⟨hcb, hba, hperm⟩ := sort3_spec (v i) g0 x y z
  generalize sort3 (v i) g0 [x, y, z] = t at hcb hba hperm ⊢
  have hbal_a : 2 * v i t.1 ≤ v i x + v i y + v i z := by
    rw [← hsum]
    apply hbal
    rcases hperm with h | h | h | h | h | h <;> rw [h] <;> simp [hx.1, hy.1, hz.1]
  rcases hperm with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only at hcb hba hbal_a ⊢
  · exact ⟨hx.1, hy.1, hz.1, hxy, hxz, hyz, hz.2, hcb, hba, by omega,
      fun g hg h1 h2 h3' => hother g hg h1 h2 h3'⟩
  · exact ⟨hx.1, hz.1, hy.1, hxz, hxy, Ne.symm hyz, hy.2, hcb, hba, by omega,
      fun g hg h1 h2 h3' => hother g hg h1 h3' h2⟩
  · exact ⟨hy.1, hx.1, hz.1, Ne.symm hxy, hyz, hxz, hz.2, hcb, hba, by omega,
      fun g hg h1 h2 h3' => hother g hg h2 h1 h3'⟩
  · exact ⟨hy.1, hz.1, hx.1, hyz, Ne.symm hxy, Ne.symm hxz, hx.2, hcb, hba, by omega,
      fun g hg h1 h2 h3' => hother g hg h3' h1 h2⟩
  · exact ⟨hz.1, hx.1, hy.1, Ne.symm hxz, Ne.symm hyz, hxy, hy.2, hcb, hba, by omega,
      fun g hg h1 h2 h3' => hother g hg h2 h3' h1⟩
  · exact ⟨hz.1, hy.1, hx.1, Ne.symm hyz, Ne.symm hxz, Ne.symm hxy, hx.2, hcb, hba, by omega,
      fun g hg h1 h2 h3' => hother g hg h3' h2 h1⟩

/-- **LB⁺ with the computed rankings is sound.** If every agent of `agents` has exactly three relevant goods
among `goods` and is balanced, `lbStage` is a complete EFX₀ allocation. -/
theorem lbStage_sound (v : A → G → Nat) {agents : List A} {goods : List G} (g0 : G) (d : A)
    (hag : agents.Nodup) (hgd : goods.Nodup) (hne : agents ≠ [])
    (h3 : ∀ i ∈ agents, (relevant v i goods).length = 3)
    (hbal : ∀ i ∈ agents, ∀ g ∈ goods, 2 * v i g ≤ value v i goods) :
    IsAllocation agents goods (lbStage v agents goods g0 d) ∧
      EFX0L v agents goods (lbStage v agents goods g0 d) := by
  let P := profileOf v goods g0
  let v' : A → G → Nat := fun j g => if g ∈ goods then v j g else 0
  have hWF : LB.WF P agents goods := fun i hi => by
    obtain ⟨h1, h2, h3', h4, h5, h6, -⟩ := sort3_ranking v i g0 hgd (h3 i hi) (hbal i hi)
    exact ⟨h1, h2, h3', h4, h5, h6⟩
  have hcons : P.Consistent agents v' := by
    intro i hi
    obtain ⟨h1, h2, h3', h4, h5, h6, h7, h8, h9, h10, h11⟩ := sort3_ranking v i g0 hgd (h3 i hi) (hbal i hi)
    refine ⟨by simp [v', P, profileOf, h3', h7], by simp [v', P, profileOf, h2, h3', h8],
      by simp [v', P, profileOf, h1, h2, h9], by simp [v', P, profileOf, h1, h2, h3', h10],
      fun g hg => ?_, h4, h5, h6⟩
    obtain ⟨ha, hb, hc⟩ := LB.ne_of_rank_three hg
    by_cases hgg : g ∈ goods
    · simp only [v', hgg, ↓reduceIte]; exact h11 g hgg ha hb hc
    · simp [v', hgg]
  obtain ⟨hord1, hord2, hord3⟩ := LB.r1Order_spec P agents.length agents goods hag (Nat.le_refl _)
  obtain ⟨hX, hE, -⟩ := LB.lbPlus_sound (P := P) d hag hgd hne hWF hord2 (fun x => hord1 x) hord3
  show IsAllocation agents goods (LB.lbPlus P agents goods (LB.r1Order P agents.length agents goods) d) ∧
    EFX0L v agents goods (LB.lbPlus P agents goods (LB.r1Order P agents.length agents goods) d)
  generalize LB.lbPlus P agents goods (LB.r1Order P agents.length agents goods) d = X at hX hE ⊢
  refine ⟨hX, fun x hx y hy hxy g hg => ?_⟩
  have := hE v' hcons x hx y hy hxy g hg
  have hsub : ∀ S : List G, S.Sublist goods → value v' x S = value v x S := fun S hS =>
    LB.value_restrict v goods x (fun g hg => hS.subset hg)
  rwa [hsub ((bundle goods X y).erase g) (List.erase_sublist.trans List.filter_sublist),
    hsub (bundle goods X x) List.filter_sublist] at this

/-- **Correctness of the algorithm, over lists.** For every instance in which every agent has at most three
relevant goods, `reduce` (with fuel at least the number of agents) returns a complete EFX₀ allocation. -/
theorem reduce_sound (v : A → G → Nat) (d : A) : ∀ (fuel : Nat) (agents : List A) (goods : List G),
    agents ≠ [] → agents.Nodup → goods.Nodup → agents.length ≤ fuel →
    (∀ i ∈ agents, (relevant v i goods).length ≤ 3) →
    IsAllocation agents goods (reduce v d fuel agents goods) ∧
      EFX0L v agents goods (reduce v d fuel agents goods)
  | 0, agents, _, hne, _, _, hl, _ => by
    exact absurd (List.length_eq_zero_iff.mp (by omega)) hne
  | fuel + 1, agents, goods, hne, hag, hgd, hl, h3 => by
    unfold reduce
    by_cases h1 : agents.length ≤ 1
    · simp only [h1, ↓reduceIte]
      obtain ⟨i0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
      have hrest : rest = [] := by
        cases rest with
        | nil => rfl
        | cons _ _ => simp at h1
      subst hrest
      refine ⟨fun _ _ => by simp, fun x hx y hy hxy => ?_⟩
      simp at hx hy
      exact absurd (hx.trans hy.symm) hxy
    simp only [h1, ↓reduceIte]
    cases goods with
    | nil =>
      simp only
      exact ⟨fun g hg => by simp at hg, fun _ _ _ _ _ g hg => by simp [bundle] at hg⟩
    | cons g0 gs =>
      simp only
      have hrest : ∀ i ∈ agents, agents.erase i ≠ [] := by
        intro i hi h
        have := List.length_erase_of_mem hi
        rw [h] at this; simp at this; omega
      cases hf : findR1 v agents (g0 :: gs) with
      | some q =>
        obtain ⟨i, s⟩ := q
        obtain ⟨hi, hs⟩ := findR1_some hf
        cases s with
        | none =>
          simp only
          obtain ⟨hX', hE'⟩ := reduce_sound v d fuel (agents.erase i) (g0 :: gs) (hrest i hi) (hag.erase i) hgd
            (by rw [List.length_erase_of_mem hi]; omega)
            (fun j hj => h3 j (List.mem_of_mem_erase hj))
          obtain ⟨hX, hE⟩ := peelEmpty v (List.Nodup.not_mem_erase hag) hX' hE' (r1Step_none_zero hs)
          exact ⟨fun g hg => (mem_cons_erase hi _).mp (hX g hg), efx0L_congr v (mem_cons_erase hi) hE⟩
        | some p =>
          simp only
          obtain ⟨hp, htop⟩ := r1Step_some hs
          obtain ⟨hX', hE'⟩ := reduce_sound v d fuel (agents.erase i) ((g0 :: gs).erase p) (hrest i hi)
            (hag.erase i) (hgd.erase p) (by rw [List.length_erase_of_mem hi]; omega)
            (fun j hj => Nat.le_trans (relevant_sublist v List.erase_sublist) (h3 j (List.mem_of_mem_erase hj)))
          obtain ⟨hX, hE⟩ := peel v (List.Nodup.not_mem_erase hag) hp hgd hX' hE' htop
          exact ⟨fun g hg => (mem_cons_erase hi _).mp (hX g hg), efx0L_congr v (mem_cons_erase hi) hE⟩
      | none =>
        simp only
        have hnone := findR1_none hf
        have hb : ∀ i ∈ agents, 3 ≤ (relevant v i (g0 :: gs)).length ∧
            ∀ g ∈ g0 :: gs, 2 * v i g < value v i (g0 :: gs) :=
          fun i hi => not_R1 v (by simp) (r1Step_eq_none (hnone i hi))
        exact lbStage_sound v g0 d hag hgd hne (fun i hi => Nat.le_antisymm (h3 i hi) (hb i hi).1)
          (fun i hi g hg => Nat.le_of_lt ((hb i hi).2 g hg))

end proofs

/-! ## The model's instances -/

/-- **The algorithm's specification** for an instance of the model with `n ≥ 1` agents: `reduce` on all agents
and all goods (in index order), with agent `0` as the default. -/
def algoSpec (I : Inst) (hn : 0 < I.n) : I.Alloc :=
  reduce I.v ⟨0, hn⟩ I.n (List.finRange I.n) (List.finRange I.m)

/-- **Correctness.** If every agent positively values at most three goods, `algoSpec` is EFX₀. -/
theorem algoSpec_efx0 (I : Inst) (hn : 0 < I.n) (h : ∀ i, numRelevant I i ≤ 3) : I.EFX0 (algoSpec I hn) :=
  (Inst.efx0_iff I _).mpr (reduce_sound I.v ⟨0, hn⟩ I.n (List.finRange I.n) (List.finRange I.m)
    (List.ne_nil_of_mem (List.mem_finRange ⟨0, hn⟩)) (List.nodup_finRange _) (List.nodup_finRange _)
    (by simp) (fun i _ => (numRelevant_eq I i) ▸ h i)).2

end K3
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.K3.sort3_ranking
#print axioms EFX.K3.lbStage_sound
#print axioms EFX.K3.reduce_sound
#print axioms EFX.K3.algoSpec_efx0
