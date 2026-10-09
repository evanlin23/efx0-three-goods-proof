import EFX.LBPlus

/-!
# Corollary D (`proofs/lb_last_step.md` §6)

Every instance in which every agent values exactly three goods and is balanced has an EFX₀ allocation with
at most one bundle of more than two goods. In particular conjecture D holds for every core, connected or
not.

- `r1Order`: a processing order with R1 priority (the first agent with at most two goods left, else the
  first agent); `r1Order_spec`: it is one.
- `sort3`: an agent's three goods sorted by value (ties broken arbitrarily) give its ranking.
- `corollaryD_lists`: Corollary D over lists (agents and goods of any types), by LB⁺ (`lbPlus_sound`).
- `corollaryD`: **Corollary D** in the model's terms (`EFX.Inst.EFX0`).

Balance is assumed in the weak form `2 v_i(g) ≤ v_i(M)` for every good `g` (for three goods `a ≥ b ≥ c` this
says `a ≤ b + c`); core agents satisfy it strictly. This is the form used by `EFX.Inst.safe_of_two_own`.
-/

set_option autoImplicit false

namespace EFX
namespace LB

variable {A G : Type} [DecidableEq A] [DecidableEq G]

open Profile

/-! ## An order with R1 priority -/

/-- A processing order with R1 priority: the first agent of `rem` that has at most two goods left in
`pool`, and the first agent of `rem` if there is none. -/
def r1Order (P : Profile A G) : Nat → List A → List G → List A
  | 0, _, _ => []
  | fuel + 1, rem, pool =>
    match rem.find? (fun j => !full P pool j) with
    | some i => i :: r1Order P fuel (rem.erase i) (removePick pool (fav P pool i))
    | none =>
      match rem with
      | [] => []
      | i :: rest => i :: r1Order P fuel rest (removePick pool (fav P pool i))

theorem r1Order_spec (P : Profile A G) : ∀ (fuel : Nat) (rem : List A) (pool : List G),
    rem.Nodup → rem.length ≤ fuel →
    (∀ x, x ∈ r1Order P fuel rem pool ↔ x ∈ rem) ∧ (r1Order P fuel rem pool).Nodup ∧
      R1Prio P (r1Order P fuel rem pool) pool
  | 0, rem, pool, _, hl => by
    have : rem = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    exact ⟨fun x => by simp [r1Order], List.nodup_nil, trivial⟩
  | fuel + 1, rem, pool, hnd, hl => by
    unfold r1Order
    cases hf : rem.find? (fun j => !full P pool j) with
    | some i =>
      simp only
      have hi : i ∈ rem := List.mem_of_find?_eq_some hf
      have hfi : full P pool i = false := by simpa using List.find?_some hf
      obtain ⟨h1, h2, h3⟩ := r1Order_spec P fuel (rem.erase i) (removePick pool (fav P pool i))
        (hnd.erase i) (by rw [List.length_erase_of_mem hi]; omega)
      refine ⟨fun x => ?_, List.nodup_cons.mpr ⟨fun h => ?_, h2⟩, ⟨fun h => ?_, h3⟩⟩
      · rw [List.mem_cons, h1]
        by_cases hx : x = i
        · simp [hx, hi]
        · simp [hx, List.mem_erase_of_ne hx]
      · exact ((List.Nodup.mem_erase_iff hnd).mp ((h1 i).mp h)).1 rfl
      · rw [hfi] at h; cases h
    | none =>
      simp only
      have hall : ∀ j ∈ rem, full P pool j = true := by
        intro j hj
        have := List.find?_eq_none.mp hf j hj
        simpa using this
      cases rem with
      | nil => exact ⟨fun x => by simp, List.nodup_nil, trivial⟩
      | cons i rest =>
        simp only
        obtain ⟨h1, h2, h3⟩ := r1Order_spec P fuel rest (removePick pool (fav P pool i))
          (List.nodup_cons.mp hnd).2 (by simp at hl; omega)
        refine ⟨fun x => by rw [List.mem_cons, List.mem_cons, h1], List.nodup_cons.mpr
          ⟨fun h => (List.nodup_cons.mp hnd).1 ((h1 i).mp h), h2⟩, ⟨fun _ j hj => ?_, h3⟩⟩
        exact hall j (List.mem_cons_of_mem _ ((h1 j).mp hj))

/-! ## Rankings from values -/

omit [DecidableEq A] [DecidableEq G] in
theorem eq_of_length_three : ∀ {l : List G}, l.length = 3 → ∃ x y z, l = [x, y, z]
  | [x, y, z], _ => ⟨x, y, z, rfl⟩
  | [], h | [_], h | [_, _], h | _ :: _ :: _ :: _ :: _, h => by simp at h

omit [DecidableEq A] in
theorem ne_of_rank_three {P : Profile A G} {i : A} {g : G} (h : P.rank i g = 3) :
    g ≠ P.a i ∧ g ≠ P.b i ∧ g ≠ P.c i := by
  unfold Profile.rank at h
  split at h
  · omega
  rename_i ha
  split at h
  · omega
  rename_i hb
  split at h
  · omega
  rename_i hc
  exact ⟨ha, hb, hc⟩

omit [DecidableEq A] [DecidableEq G] in
/-- Three goods sorted by value, ties broken arbitrarily. -/
theorem sort3 (f : G → Nat) (x y z : G) : ∃ a b c : G, f c ≤ f b ∧ f b ≤ f a ∧
    ((a = x ∧ b = y ∧ c = z) ∨ (a = x ∧ b = z ∧ c = y) ∨ (a = y ∧ b = x ∧ c = z) ∨
      (a = y ∧ b = z ∧ c = x) ∨ (a = z ∧ b = x ∧ c = y) ∨ (a = z ∧ b = y ∧ c = x)) := by
  by_cases h1 : f y ≤ f x <;> by_cases h2 : f z ≤ f y <;> by_cases h3 : f z ≤ f x
  · exact ⟨x, y, z, h2, h1, by simp⟩
  · exact ⟨x, y, z, h2, h1, by simp⟩
  · exact ⟨x, z, y, by omega, h3, by simp⟩
  · exact ⟨z, x, y, by omega, by omega, by simp⟩
  · exact ⟨y, x, z, by omega, by omega, by simp⟩
  · exact ⟨y, z, x, by omega, by omega, by simp⟩
  · exact ⟨y, x, z, by omega, by omega, by simp⟩
  · exact ⟨z, y, x, by omega, by omega, by simp⟩

omit [DecidableEq A] [DecidableEq G] in
/-- An agent with exactly three relevant goods among `goods`, balanced, has a ranking `a ≥ b ≥ c` of them:
distinct goods of `goods`, positive, `a ≤ b + c`, and every other good of `goods` is worthless to it. -/
theorem ranking_of_three (v : A → G → Nat) (i : A) {goods : List G} (hgd : goods.Nodup)
    (h3 : (relevant v i goods).length = 3) (hbal : ∀ g ∈ goods, 2 * v i g ≤ value v i goods) :
    ∃ a b c : G, a ∈ goods ∧ b ∈ goods ∧ c ∈ goods ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      0 < v i c ∧ v i c ≤ v i b ∧ v i b ≤ v i a ∧ v i a ≤ v i b + v i c ∧
      ∀ g ∈ goods, g ≠ a → g ≠ b → g ≠ c → v i g = 0 := by
  obtain ⟨x, y, z, hxyz⟩ := eq_of_length_three h3
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
  obtain ⟨a, b, c, hcb, hba, hperm⟩ := sort3 (v i) x y z
  have hbal_a := hbal a (by rcases hperm with h | h | h | h | h | h <;> rw [h.1] <;> simp [hx.1, hy.1, hz.1])
  rw [hsum] at hbal_a
  rcases hperm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact ⟨_, _, _, hx.1, hy.1, hz.1, hxy, hxz, hyz, hz.2, hcb, hba, by omega,
      fun g hg h1 h2 h3' => hother g hg h1 h2 h3'⟩
  · exact ⟨_, _, _, hx.1, hz.1, hy.1, hxz, hxy, Ne.symm hyz, hy.2, hcb, hba, by omega,
      fun g hg h1 h2 h3' => hother g hg h1 h3' h2⟩
  · exact ⟨_, _, _, hy.1, hx.1, hz.1, Ne.symm hxy, hyz, hxz, hz.2, hcb, hba, by omega,
      fun g hg h1 h2 h3' => hother g hg h2 h1 h3'⟩
  · exact ⟨_, _, _, hy.1, hz.1, hx.1, hyz, Ne.symm hxy, Ne.symm hxz, hx.2, hcb, hba, by omega,
      fun g hg h1 h2 h3' => hother g hg h3' h1 h2⟩
  · exact ⟨_, _, _, hz.1, hx.1, hy.1, Ne.symm hxz, Ne.symm hyz, hxy, hy.2, hcb, hba, by omega,
      fun g hg h1 h2 h3' => hother g hg h2 h3' h1⟩
  · exact ⟨_, _, _, hz.1, hy.1, hx.1, Ne.symm hyz, Ne.symm hxz, Ne.symm hxy, hx.2, hcb, hba, by omega,
      fun g hg h1 h2 h3' => hother g hg h3' h2 h1⟩

omit [DecidableEq A] in
/-- Values of lists of goods do not see the values of goods outside `goods`. -/
theorem value_restrict (v : A → G → Nat) (goods : List G) (i : A) :
    ∀ {S : List G}, (∀ g ∈ S, g ∈ goods) →
      value (fun j g => if g ∈ goods then v j g else 0) i S = value v i S
  | [], _ => rfl
  | g :: S, h => by
    simp only [value_cons, h g (by simp), ↓reduceIte]
    rw [value_restrict v goods i (fun x hx => h x (by simp [hx]))]

/-! ## Corollary D -/

/-- **Corollary D, over lists.** If every agent values exactly three goods among `goods` and is balanced
(`2 v_i(g) ≤ v_i(goods)`), some complete EFX₀ allocation of `goods` to `agents` has at most one bundle of more
than two goods. It is LB⁺'s output for the rankings sorted by value. -/
theorem corollaryD_lists (v : A → G → Nat) {agents : List A} {goods : List G} (hag : agents.Nodup)
    (hgd : goods.Nodup) (hne : agents ≠ [])
    (h3 : ∀ i ∈ agents, (relevant v i goods).length = 3)
    (hbal : ∀ i ∈ agents, ∀ g ∈ goods, 2 * v i g ≤ value v i goods) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X ∧
      ∃ o, ∀ j ∈ agents, j ≠ o → (bundle goods X j).length ≤ 2 := by
  obtain ⟨i0, hi0⟩ := List.exists_mem_of_ne_nil agents hne
  obtain ⟨g0, -⟩ : ∃ g, g ∈ goods := by
    obtain ⟨a, -, -, ha, -⟩ := ranking_of_three v i0 hgd (h3 i0 hi0) (hbal i0 hi0)
    exact ⟨a, ha⟩
  -- the rankings, by choice
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice (r := fun (i : A) (t : G × G × G) => i ∈ agents →
      t.1 ∈ goods ∧ t.2.1 ∈ goods ∧ t.2.2 ∈ goods ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
      0 < v i t.2.2 ∧ v i t.2.2 ≤ v i t.2.1 ∧ v i t.2.1 ≤ v i t.1 ∧ v i t.1 ≤ v i t.2.1 + v i t.2.2 ∧
      ∀ g ∈ goods, g ≠ t.1 → g ≠ t.2.1 → g ≠ t.2.2 → v i g = 0) (fun i => by
    by_cases hi : i ∈ agents
    · obtain ⟨a, b, c, h⟩ := ranking_of_three v i hgd (h3 i hi) (hbal i hi)
      exact ⟨(a, b, c), fun _ => h⟩
    · exact ⟨(g0, g0, g0), fun h => absurd h hi⟩)
  let P : Profile A G := ⟨fun i => (f i).1, fun i => (f i).2.1, fun i => (f i).2.2⟩
  let v' : A → G → Nat := fun j g => if g ∈ goods then v j g else 0
  have hWF : WF P agents goods := fun i hi => by
    obtain ⟨h1, h2, h3', h4, h5, h6, -⟩ := hf i hi
    exact ⟨h1, h2, h3', h4, h5, h6⟩
  have hcons : P.Consistent agents v' := by
    intro i hi
    obtain ⟨h1, h2, h3', h4, h5, h6, h7, h8, h9, h10, h11⟩ := hf i hi
    refine ⟨by simp [v', P, h3', h7], by simp [v', P, h2, h3', h8], by simp [v', P, h1, h2, h9],
      by simp [v', P, h1, h2, h3', h10], fun g hg => ?_, h4, h5, h6⟩
    obtain ⟨ha, hb, hc⟩ := ne_of_rank_three hg
    by_cases hgg : g ∈ goods
    · simp only [v', hgg, ↓reduceIte]; exact h11 g hgg ha hb hc
    · simp [v', hgg]
  obtain ⟨hord1, hord2, hord3⟩ := r1Order_spec P agents.length agents goods hag (Nat.le_refl _)
  obtain ⟨hX, hE, o, hlen⟩ := lbPlus_sound (P := P) i0 hag hgd hne hWF hord2
    (fun x => hord1 x) hord3
  generalize lbPlus P agents goods (r1Order P agents.length agents goods) i0 = X at hX hE hlen
  refine ⟨X, hX, fun x hx y hy hxy g hg => ?_, o, hlen⟩
  have := hE v' hcons x hx y hy hxy g hg
  have hsub : ∀ S : List G, S.Sublist goods → value v' x S = value v x S := fun S hS =>
    value_restrict v goods x (fun g hg => hS.subset hg)
  rwa [hsub ((bundle goods X y).erase g) (List.erase_sublist.trans List.filter_sublist),
    hsub (bundle goods X x) List.filter_sublist] at this

/-- **Corollary D.** Every instance in which every agent values exactly three goods and is balanced
(`2 v_i(g) ≤ v_i(M)` for every good `g`, i.e. `a ≤ b + c`; core agents have `a < b + c`) has an EFX₀
allocation in which at most one bundle has more than two goods. In particular conjecture D holds for every
core, connected or not. -/
theorem corollaryD (I : Inst) (hn : 0 < I.n) (h3 : ∀ i, numRelevant I i = 3)
    (hbal : ∀ i g, 2 * I.v i g ≤ finSum I.m (I.v i)) :
    ∃ X : I.Alloc, I.EFX0 X ∧ ∃ o, ∀ j, j ≠ o → finSum I.m (fun g => if X g = j then 1 else 0) ≤ 2 := by
  obtain ⟨X, -, hE, o, hlen⟩ := corollaryD_lists I.v (List.nodup_finRange I.n) (List.nodup_finRange I.m)
    (List.ne_nil_of_mem (List.mem_finRange ⟨0, hn⟩)) (fun i _ => (numRelevant_eq I i) ▸ h3 i)
    (fun i _ g _ => by have := hbal i g; rw [finSum_eq_sum] at this; exact this)
  refine ⟨X, (Inst.efx0_iff I X).mpr hE, o, fun j hj => ?_⟩
  rw [finSum_bundle_eq]
  exact hlen j (List.mem_finRange j) hj

end LB
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB.r1Order_spec
#print axioms EFX.LB.corollaryD_lists
#print axioms EFX.LB.corollaryD
