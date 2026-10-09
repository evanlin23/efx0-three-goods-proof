import EFX.K3DEAlgo

/-!
# Algorithm DE on small instances (non-vacuity; ledger K3S.PO.LEAN)

The outputs below are computed by kernel evaluation (`decide`) of `EFX.DE.deSpec` and `EFX.DE.deMoves`, and they are
EFX₀ with at most one large bundle by `EFX.DE.deSpec_correct`.

- `worked`: the worked example of `paper/k3-simple/long.tex` §7 (n = 6, m = 10, values 4, 3, 2): the draft state has
  no ring of want arrows and no chain applies, no free agent can finish, and one ring with two pair arrows
  (`o₁ → x₁ → o₂ → x₂ → o₁`) gives two pairs; then `x₁'` finishes (absorbs) with `H = ∅`. The output is the paper's.
- `small`: the small example at the end of §6 (n = 3, m = 5; the paper's `g₄`): `o` cannot finish (`H_o = {g₂}`, no
  other free agent), the ring `o → x → o` gives `x` its pair `{g₁, g₂}` and `o` the good `g₀`, then `z` finishes with
  `H = ∅`: `X_z = {g₄, g₃}`, `X_x = {g₁, g₂}`, `X_o = {g₀}`. The output is the paper's.
- `twoAgents`: the remark "the protecting goods cannot be dropped" of the earlier version of the paper (kept in Lean,
  `EFX/K3DERemarks.lean`; n = 2, m = 3): both agents hold their tops, each is exposed for (a blocker of) the other,
  and agent 0 absorbs with `H = {g₂}`, which goes to agent 1. No exchange.
- `chains`: n = 2, m = 5: (P) fails after the draft, a pair chain (agent 0 takes its pair, agent 1 takes `g₀`),
  then (P) fails at agent 1, a second pair chain of length 0, and every agent is a pair holder; agent 0 absorbs.
- `peeled`: `chains` with a third agent that values only `g₅`; rule R1 peels it with `g₅` first.
-/

set_option autoImplicit false

namespace EFX
namespace DE
namespace Examples

/-- An instance from a table of values, agent by agent. -/
def mkInst (n m : Nat) (tbl : List (List Nat)) : Inst := ⟨n, m, fun i g => (tbl.getD i.val []).getD g.val 0⟩

/-- Agents `x₁, x₁', x₂, x₂', o₁, o₂` (0 to 5), each valuing its `a, b, c` at 4, 3, 2. -/
def worked : Inst := mkInst 6 10
  [[4, 0, 0, 0, 3, 0, 2, 0, 0, 0], [0, 4, 0, 0, 3, 0, 0, 2, 0, 0], [0, 0, 4, 0, 0, 3, 0, 0, 2, 0],
   [0, 0, 0, 4, 0, 3, 0, 0, 0, 2], [0, 0, 4, 3, 2, 0, 0, 0, 0, 0], [4, 3, 0, 0, 0, 2, 0, 0, 0, 0]]

/-- The small example: agents `z, x, o` (0 to 2) rank `g₄ ≻ g₀ ≻ g₁`, `g₀ ≻ g₁ ≻ g₂` and `g₀ ≻ g₄ ≻ g₁`, with
values 4, 3, 2; nobody values `g₃`. -/
def small : Inst := mkInst 3 5 [[3, 2, 0, 0, 4], [4, 3, 2, 0, 0], [4, 2, 0, 0, 3]]

/-- Rankings `g₀ ≻ g₁ ≻ g₂` and `g₁ ≻ g₀ ≻ g₂`. -/
def twoAgents : Inst := mkInst 2 3 [[4, 3, 2], [3, 4, 2]]

/-- Rankings `g₀ ≻ g₁ ≻ g₂` and `g₀ ≻ g₃ ≻ g₄`. -/
def chains : Inst := mkInst 2 5 [[4, 3, 2, 0, 0], [4, 0, 0, 3, 2]]

/-- `chains`, with agent 2 valuing only `g₅`. -/
def peeled : Inst := mkInst 3 6 [[4, 3, 2, 0, 0, 0], [4, 0, 0, 3, 2, 0], [0, 0, 0, 0, 0, 7]]

theorem worked_relevant : ∀ i, numRelevant worked i ≤ 3 := by decide
theorem small_relevant : ∀ i, numRelevant small i ≤ 3 := by decide
theorem twoAgents_relevant : ∀ i, numRelevant twoAgents i ≤ 3 := by decide
theorem chains_relevant : ∀ i, numRelevant chains i ≤ 3 := by decide
theorem peeled_relevant : ∀ i, numRelevant peeled i ≤ 3 := by decide

/-- The worked example: `X_{x₁} = {g₄, g₆}`, `X_{x₁'} = {g₁, g₇, g₉}`, `X_{x₂} = {g₅, g₈}`, `X_{x₂'} = {g₃}`,
`X_{o₁} = {g₂}`, `X_{o₂} = {g₀}`, after one exchange. -/
theorem worked_spec :
    (List.finRange 10).map (fun g => (deSpec worked (by decide) g).val) = [5, 1, 4, 3, 0, 2, 0, 1, 2, 1] ∧
      deMoves worked (by decide) = 1 := by
  decide

/-- The small example: `X_z = {g₄, g₃}`, `X_x = {g₁, g₂}`, `X_o = {g₀}`, after one exchange (the ring `o → x → o`:
`x` takes its pair `{g₁, g₂}`, `o` takes `g₀`; then `z` absorbs with `H = ∅`). -/
theorem small_spec :
    (List.finRange 5).map (fun g => (deSpec small (by decide) g).val) = [2, 1, 1, 0, 0] ∧
      deMoves small (by decide) = 1 := by
  decide

theorem twoAgents_spec :
    (List.finRange 3).map (fun g => (deSpec twoAgents (by decide) g).val) = [0, 1, 1] ∧
      deMoves twoAgents (by decide) = 0 := by
  decide

theorem chains_spec :
    (List.finRange 5).map (fun g => (deSpec chains (by decide) g).val) = [0, 0, 0, 1, 1] ∧
      deMoves chains (by decide) = 2 := by
  decide

theorem peeled_spec :
    (List.finRange 6).map (fun g => (deSpec peeled (by decide) g).val) = [0, 0, 0, 1, 1, 2] ∧
      deMoves peeled (by decide) = 2 := by
  decide

end Examples
end DE
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE.Examples.worked_spec
#print axioms EFX.DE.Examples.small_spec
#print axioms EFX.DE.Examples.twoAgents_spec
#print axioms EFX.DE.Examples.chains_spec
#print axioms EFX.DE.Examples.peeled_spec
