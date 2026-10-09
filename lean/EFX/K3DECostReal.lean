import EFX.K3DECostBound
import EFX.K3DEReal

/-!
# Draft and Exchange on ordered values: the count in the comparison model (ledger K3S.TIME)

`paper/k3-simple/long.tex` §6, paragraph "Real values", with Theorem `thm:algo` ("in time `O(n(n+m))`. On real
values, every decision of DE compares two sums of at most two values of one agent"): the count in the comparison
model. As for K3ALG
(`EFX.K3.algoOrdC`, `EFX/K3Real.lean`), the program `deOrdC` computes L12's natural-number surrogate with a comparison
oracle (`EFX.K3.surrogateC`, each oracle call charged one unit) and runs the counted DE (`EFX.DE.deC`,
`EFX/K3DECost*.lean`) on it.

- `deOrdC_val`: its value is `EFX.DE.deOrd`, which is EFX₀ for the original values (`EFX.DE.deOrd_correct`).
- `deOrdC_cost`: for a correct oracle, nonnegative values and at most three relevant goods per agent, it takes at most
  `n (m + 12) + 10 n m + 971 n + 750 (n + 1)(n + m + 1)` counted operations, `O(n (n + m))`; at most `n (m + 12)` of
  them are oracle calls (`EFX.K3.surrogateC_cost`, the coefficient of the charge per call).
-/

set_option autoImplicit false

namespace EFX
namespace DE

open Timed

section oracle
variable {V : Type} [OrderedValue V]

/-- **DE on ordered values, counted**: the surrogate, with one unit per oracle call, then the counted DE. -/
def deOrdC (le : V → V → Bool) (I : OInst V) (hn : 0 < I.n) : Timed I.Alloc := do
  let w ← K3.surrogateC 1 le I
  deC ⟨I.n, I.m, w⟩ hn

/-- The counted program computes `deOrd`. -/
theorem deOrdC_val (le : V → V → Bool) (I : OInst V) (hn : 0 < I.n) : (deOrdC le I hn).val = deOrd le I hn := by
  simp only [deOrdC, bind_val]
  rw [de_eq_spec, deOrd_eq_surrogateC 1]

/-- **The count in the comparison model**: `O(n (n + m))` counted operations, at most `n (m + 12)` of them oracle
calls. -/
theorem deOrdC_cost {le : V → V → Bool} (hle : ∀ x y, le x y = true ↔ x ≤ y) (I : OInst V) (hn : 0 < I.n)
    (hv : ∀ i g, 0 ≤ I.v i g) (h : ∀ i, I.numRelevant i ≤ 3) :
    (deOrdC le I hn).cost ≤
      I.n * (I.m + 12) + 10 * (I.n * I.m) + 971 * I.n + 750 * (I.n + 1) * (I.n + I.m + 1) := by
  have hw := K3.agree_surrogate hle I hv h
  have h1 := K3.surrogateC_cost 1 le I
  have h2 := deC_cost ⟨I.n, I.m, (K3.surrogateC 1 le I).val⟩ hn (fun i => by
    rw [K3.surrogateC_val]
    exact (numRelevant_eq_of_agree I _ hw i) ▸ h i)
  simp only at h2
  simp only [deOrdC, bind_cost]
  omega

end oracle

end DE
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE.deOrdC_val
#print axioms EFX.DE.deOrdC_cost
