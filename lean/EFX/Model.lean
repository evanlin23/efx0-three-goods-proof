/-!
# The model (trusted base)

These definitions are what a reader must accept to believe the theorems. They are copied verbatim
from `MRD.lean` in [evanlin23/mrd-efx](https://github.com/evanlin23/mrd-efx) (tag `v1.2.0`,
Apache-2.0), only moved from namespace `MRD` to `EFX`, so a statement here means exactly what the
same statement means there.

Additive instances with `n` agents, `m` goods and values `v i g : Nat`; a good is relevant to `i`
iff `0 < v i g`. Values are natural numbers: EFX₀ only compares sums of values, so rational
instances reduce to these by scaling each agent's values by a common denominator.
-/

set_option autoImplicit false

namespace EFX

/-- Sum of `f` over `Fin k`. -/
def finSum : (k : Nat) → (Fin k → Nat) → Nat
  | 0, _ => 0
  | k+1, f => finSum k (fun i => f i.castSucc) + f (Fin.last k)

/-- An additive fair-division instance. -/
structure Inst where
  n : Nat
  m : Nat
  v : Fin n → Fin m → Nat

namespace Inst
variable (I : Inst)

/-- A complete allocation is an owner map. -/
abbrev Alloc := Fin I.m → Fin I.n

/-- Value, for agent `i`, of agent `j`'s bundle with the good `ex` (if any) removed. -/
def bundleVal (X : I.Alloc) (i j : Fin I.n) (ex : Option (Fin I.m)) : Nat :=
  finSum I.m (fun g => if X g = j ∧ ex ≠ some g then I.v i g else 0)

/-- Strong EFX₀: for all `i ≠ j` and every good `g ∈ X_j`, `v_i(X_i) ≥ v_i(X_j \ {g})`. -/
def EFX0 (X : I.Alloc) : Prop :=
  ∀ i j : Fin I.n, i ≠ j → ∀ g : Fin I.m, X g = j →
    I.bundleVal X i j (some g) ≤ I.bundleVal X i i none

end Inst

/-- The counting form of 2-relevance used in the paper: `|R_i| ≤ 2`. -/
def numRelevant (I : Inst) (i : Fin I.n) : Nat := finSum I.m (fun g => if 0 < I.v i g then 1 else 0)

end EFX
