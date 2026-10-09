import EFX.K3CostBound

/-!
# Algorithm K3ALG on three small instances (non-vacuity; not a ledger item)

The allocations below are checked by `decide` (kernel evaluation of the specification `EFX.K3.algoSpec`) and carried
over to `EFX.K3.algo` by `EFX.K3.algo_eq_spec`. The Python implementations `k3/k3algo.py` (`mirror` and `fast`)
compute the same allocations, and `#eval` prints them (`lean/scripts/k3_eval.lean`).

- `rot`: n = 3, m = 5, no agent is peeled; LB⁺ reaches Theorem A's bad case, rotates along a need chain and needs
  no owner afterwards.
- `rotOwner`: n = 3, m = 6; LB⁺ rotates and `k*` owns the large bundle.
- `peelOwner`: n = 3, m = 6; agent 1 values only good 1 and is peeled with it (rule R1); LB⁺ on the other two
  agents gives the large bundle to `r`.
-/

set_option autoImplicit false

namespace EFX
namespace K3
namespace Examples

/-- An instance from a table of values, agent by agent. -/
def mkInst (n m : Nat) (tbl : List (List Nat)) : Inst := ⟨n, m, fun i g => (tbl.getD i.val []).getD g.val 0⟩

/-- Agent 0 values goods 1, 3, 4 at 2 each; agent 1 values 1, 2 at 3 and 4 at 2; agent 2 values 1, 2, 4 at 2. -/
def rot : Inst := mkInst 3 5 [[0, 2, 0, 2, 2], [0, 3, 3, 0, 2], [0, 2, 2, 0, 2]]

/-- Agent 0: goods 1, 2, 0 at 5, 4, 2; agent 1: 3, 1, 2 at 3, 3, 2; agent 2: 1, 3, 2 at 3, 3, 2. -/
def rotOwner : Inst := mkInst 3 6 [[2, 5, 4, 0, 0, 0], [0, 3, 2, 3, 0, 0], [0, 3, 2, 3, 0, 0]]

/-- Agent 0: goods 2, 4, 5 at 84, 73, 54; agent 1: good 1 only; agent 2: goods 4, 2, 3 at 92, 83, 44. -/
def peelOwner : Inst := mkInst 3 6 [[0, 0, 84, 0, 73, 54], [0, 87, 0, 0, 0, 0], [0, 0, 83, 44, 92, 0]]

theorem rot_relevant : ∀ i, numRelevant rot i ≤ 3 := by decide
theorem rotOwner_relevant : ∀ i, numRelevant rotOwner i ≤ 3 := by decide
theorem peelOwner_relevant : ∀ i, numRelevant peelOwner i ≤ 3 := by decide

theorem rot_spec : (List.finRange 5).map (fun g => (algoSpec rot (by decide) g).val) = [2, 1, 2, 0, 0] := by
  decide

theorem rotOwner_spec :
    (List.finRange 6).map (fun g => (algoSpec rotOwner (by decide) g).val) = [0, 1, 0, 2, 2, 0] := by
  decide

theorem peelOwner_spec :
    (List.finRange 6).map (fun g => (algoSpec peelOwner (by decide) g).val) = [2, 1, 0, 2, 2, 0] := by
  decide

/-- The algorithm's output on `rot`, and it is EFX₀. -/
theorem rot_algo : (List.finRange 5).map (fun g => (algo rot (by decide) g).val) = [2, 1, 2, 0, 0] ∧
    rot.EFX0 (algo rot (by decide)) :=
  ⟨by simp only [algo_eq_spec]; exact rot_spec, algo_efx0 rot (by decide) rot_relevant⟩

theorem rotOwner_algo :
    (List.finRange 6).map (fun g => (algo rotOwner (by decide) g).val) = [0, 1, 0, 2, 2, 0] ∧
      rotOwner.EFX0 (algo rotOwner (by decide)) :=
  ⟨by simp only [algo_eq_spec]; exact rotOwner_spec, algo_efx0 rotOwner (by decide) rotOwner_relevant⟩

theorem peelOwner_algo :
    (List.finRange 6).map (fun g => (algo peelOwner (by decide) g).val) = [2, 1, 0, 2, 2, 0] ∧
      peelOwner.EFX0 (algo peelOwner (by decide)) :=
  ⟨by simp only [algo_eq_spec]; exact peelOwner_spec, algo_efx0 peelOwner (by decide) peelOwner_relevant⟩

end Examples
end K3
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.K3.Examples.rot_algo
#print axioms EFX.K3.Examples.rotOwner_algo
#print axioms EFX.K3.Examples.peelOwner_algo
