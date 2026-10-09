import EFX.Model
import EFX.SerialDictatorship

/-!
# Bridge: the model and the list layer agree

Over `List.finRange`, the list notions of `EFX.Lists` coincide with the model's (`EFX.Model`):
`finSum` is a list sum, `bundleVal` is the value of a bundle (with a good removed), and `EFX0L`
is `Inst.EFX0` (`efx0_iff`). Results proved over lists therefore hold in the model; the headline
`exists_efx0_of_count` is L2c in the model's terms.
-/

set_option autoImplicit false

namespace EFX

theorem finSum_eq_sum : ∀ (k : Nat) (f : Fin k → Nat), finSum k f = ((List.finRange k).map f).sum
  | 0, _ => by simp [finSum]
  | k + 1, f => by
    rw [finSum, finSum_eq_sum k, List.finRange_succ_last]
    simp [List.map_map, Function.comp_def]

/-- Summing `f` over the members satisfying `p` is summing `if p x then f x else 0` over all. -/
theorem sum_map_ite {α : Type} (p : α → Prop) [DecidablePred p] (f : α → Nat) :
    ∀ l : List α, (l.map (fun x => if p x then f x else 0)).sum = ((l.filter (fun x => p x)).map f).sum
  | [] => rfl
  | a :: l => by
    by_cases h : p a
    · simp [h, sum_map_ite p f l]
    · simp [h, sum_map_ite p f l]

theorem sum_map_one {α : Type} : ∀ l : List α, (l.map (fun _ => 1)).sum = l.length
  | [] => rfl
  | _ :: l => by simp [sum_map_one l]; omega

namespace Inst
variable (I : Inst)

theorem bundleVal_none (X : I.Alloc) (i j : Fin I.n) :
    I.bundleVal X i j none = value I.v i (bundle (List.finRange I.m) X j) := by
  unfold bundleVal value bundle
  rw [finSum_eq_sum, ← sum_map_ite (fun g => X g = j)]
  congr 1
  apply List.map_congr_left
  intro g _
  simp

theorem bundleVal_some (X : I.Alloc) (i j : Fin I.n) (g : Fin I.m) :
    I.bundleVal X i j (some g) = value I.v i ((bundle (List.finRange I.m) X j).erase g) := by
  have hnd : (bundle (List.finRange I.m) X j).Nodup :=
    (List.nodup_finRange _).sublist List.filter_sublist
  have hf : (List.finRange I.m).filter (fun a => a != g && decide (X a = j)) =
      (List.finRange I.m).filter (fun a => decide (a ≠ g ∧ X a = j)) := by
    apply List.filter_congr
    intro a _
    by_cases ha : a = g <;> simp [ha]
  unfold bundleVal value
  rw [List.Nodup.erase_eq_filter hnd g, bundle, List.filter_filter, hf, finSum_eq_sum,
    ← sum_map_ite (fun h => h ≠ g ∧ X h = j)]
  congr 1
  apply List.map_congr_left
  intro h _
  by_cases hh : h = g
  · subst hh; simp
  · have : some g ≠ some h := fun e => hh (Option.some.inj e).symm
    simp [hh, this, And.comm]

/-- The model's EFX₀ is the list layer's EFX₀ over `List.finRange`. -/
theorem efx0_iff (X : I.Alloc) :
    I.EFX0 X ↔ EFX0L I.v (List.finRange I.n) (List.finRange I.m) X := by
  constructor
  · intro h i _ j _ hij g hg
    have hXg : X g = j := of_decide_eq_true (List.mem_filter.mp hg).2
    have := h i j hij g hXg
    rwa [bundleVal_some, bundleVal_none] at this
  · intro h i j hij g hXg
    have hg : g ∈ bundle (List.finRange I.m) X j := by simp [bundle, hXg]
    have := h i (List.mem_finRange i) j (List.mem_finRange j) hij g hg
    rwa [bundleVal_some, bundleVal_none]

end Inst

/-- The model's count of relevant goods is the length of the list of relevant goods. -/
theorem numRelevant_eq (I : Inst) (i : Fin I.n) :
    numRelevant I i = (relevant I.v i (List.finRange I.m)).length := by
  unfold numRelevant relevant
  rw [finSum_eq_sum, sum_map_ite (fun g => 0 < I.v i g) (fun _ => 1), sum_map_one]

/-- **L2c.** If every agent has at most two relevant goods (`|R_i| ≤ 2`), a complete strongly EFX₀
allocation exists. Same hypotheses as `MRD.main_theorem_L` in evanlin23/mrd-efx, which also
proves the shape property; here the witness is serial dictatorship. -/
theorem exists_efx0_of_count (I : Inst) (hn : 0 < I.n) (h : ∀ i, numRelevant I i ≤ 2) :
    ∃ X : I.Alloc, I.EFX0 X := by
  obtain ⟨X, _, hE⟩ := serialDictatorship I.v (List.finRange I.n) (List.finRange I.m)
    (List.ne_nil_of_mem (List.mem_finRange ⟨0, hn⟩)) (List.nodup_finRange _)
    (List.nodup_finRange _) (fun i _ => (numRelevant_eq I i) ▸ h i)
  exact ⟨X, (Inst.efx0_iff I X).mpr hE⟩

end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.finSum_eq_sum
#print axioms EFX.Inst.bundleVal_none
#print axioms EFX.Inst.bundleVal_some
#print axioms EFX.Inst.efx0_iff
#print axioms EFX.numRelevant_eq
#print axioms EFX.exists_efx0_of_count
