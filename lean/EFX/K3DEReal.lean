import EFX.K3DEAlgo
import EFX.K3Real

/-!
# Draft and Exchange on ordered values, and the peeling bound (`paper/k3-simple/long.tex` §6)

`EFX/K3DEAlgo.lean` formalizes algorithm DE and Theorem "DE is correct" (`thm:de`) over natural-number values, with
the bound of `4n` exchanges. This file adds the two parts of §6 that it leaves out: the bound "DE peels at most
`n` agents" of `thm:de`, and the paragraph "Real values" with the proof of Theorems `thm:target`, `thm:D` and
`thm:algo`: the results "hold for nonnegative real values" (the count in the comparison model is
`EFX.DE.deOrdC_cost`, `EFX/K3DECostReal.lean`).
Core Lean has no reals: values lie in any `EFX.OrderedValue` type `V` (`ℝ≥0` satisfies its axioms by the textbook
fact), as in `EFX/RealValues.lean` and `EFX/K3Real.lean`.

**Peeling rounds.** `peels v fuel agents goods` follows the recursion of `EFX.DE.run` case by case and adds one in
the two cases in which `run` peels, those in which `EFX.K3.findR1` returns `some (i, s)`: agent `i` leaves with
nothing (`s = none`) or with its favourite remaining good (`s = some p`). `run` itself is unchanged.
- `peels_stop`, `run_peels_step` (**the rounds counted are `run`'s R1 rounds**): `peels` is `0` when `run` stops
  without consulting `findR1` (no fuel, at most one agent, or no goods); otherwise, with at least two agents and some
  goods, the one combined recursion lemma unfolds `run` and `peels` together: if `findR1` returns `some (i, none)` or
  `some (i, some p)`, `run` recurses on the agents without `i` (and the goods without `p`) and `peels` is one more
  than on those same arguments; if it returns `none`, `run` is the core stage `deStage` and `peels` is `0`.
- `peels_le`, `dePeels_le_pred`, `dePeels_le` (**DE peels at most `n` agents**): every round removes one agent and
  the rounds stop at one agent, so `peels ≤ |agents| - 1`; for the model (`dePeels`), at most `n - 1 ≤ n`.
- `de_correct` (**Theorem `thm:de`** over the natural numbers, in full): EFX₀, all bundles but at most one of at
  most two goods, at most `n` peeled agents and at most `4n` exchanges (`EFX.DE.deSpec_correct` plus `dePeels_le`).

**DE on ordered values** (`deOrd le I hn`), as K3ALG in `EFX.K3.algoOrd`: compute the natural-number surrogate
`w = EFX.K3.surrogate le I` of Lemma L12 with the comparison oracle `le : V → V → Bool`, and run DE
(`EFX.DE.deSpec`) on the instance `⟨n, m, w⟩`. `deOrdMoves` and `deOrdPeels` are its exchanges and peeling rounds.
- `deOrd_eq_surrogateC`: the surrogate is the value of the counted program `EFX.K3.surrogateC`, which asks the
  oracle at most `n (m + 12)` times (`EFX.K3.surrogateC_cost`, the coefficient of the charge `c` per call); DE then
  runs on `w` and asks the oracle nothing.
- `deOrd_correct` (**Theorem `thm:de` on ordered values**): for a correct oracle (`∀ x y, le x y = true ↔ x ≤ y`),
  nonnegative values and at most three relevant goods per agent, `deOrd le I hn` is EFX₀ for the *original* values
  (`OInst.EFX0`), all its bundles but at most one have at most two goods, and DE peels at most `n` agents and
  applies at most `4n` exchanges on the surrogate. Proof: `w` agrees with `v` on every comparison of two subset sums
  (`EFX.K3.agree_surrogate`), so it has the same relevant goods (`EFX.numRelevant_eq_of_agree`) and the same EFX₀
  allocations (`EFX.efx0_iff_of_agree`), and `de_correct` applies to `w`.
- `thmD_ordered` (**Theorems `thm:target` and `thm:D` on ordered values, in general**): every instance with
  `n ≥ 1` agents, nonnegative values in `V` and at most three relevant goods per agent has an EFX₀ allocation in
  which all bundles but at most one have at most two goods. It needs neither exactly three relevant goods nor
  balance, unlike `EFX.corollaryD_ordered`, and it implies `EFX.target_ordered`. Proof: L12 (`EFX.l12`) and
  `EFX.DE.deSpec_correct`.
- `Examples.peeledZ_surrogate`, `Examples.peeledZ_deOrd`: an instance with values in `Int` (one peel, then two pair
  chains): its surrogate and DE's output, checked by `decide`.

**Choices where the prose leaves room.**
1. *The comparison model.* The paper counts each decision of DE on real values as one comparison of two sums of at
   most two values of one agent. Here, as for K3ALG, the oracle is asked only while the surrogate is computed
   (`m + 12` calls per agent, comparisons of sums of at most two values of one agent, with repetition for the
   phantom slots: see `EFX/K3Real.lean`), and DE's decisions are then made on the natural numbers `w`. Every
   decision of DE on `w` (the favourite and R1's test `w_i(p) ≥ w_i(G ∖ {p})`, the zero test, the rankings) is a
   comparison of two subset sums of one agent's values, which `w` answers as `v` does; this per-decision
   correspondence is the reason the outcome is right, but what is formalized is the outcome (`deOrd_correct`), not
   a trace of DE's comparisons on `V`.
2. *Peeling with no goods left.* `run` stops when no goods remain; the paper's loop would go on peeling agents
   with `P = ∅` until one is left. With no goods there is nothing to allocate, so the allocations agree; `peels`
   counts `run`'s rounds, and both counts are at most `n`.
3. `peels` takes no default agent: the control flow of `run` does not depend on it.
4. The running time `O(n(n + m))` of the paper, and the cost of DE on the surrogate, are formalized in
   `EFX/K3DECost*.lean` (ledger K3S.TIME: `EFX.DE.deC_cost`, and `EFX.DE.deOrdC_cost` on ordered values); this file
   proves the outcome and the counts of oracle calls, peeling rounds and exchanges.
-/

set_option autoImplicit false

namespace EFX
namespace DE

/-! ## Peeling rounds -/

section peeling
variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- **The number of peeling rounds of `run`**: the recursion of `EFX.DE.run`, case by case, counting one for each
case in which `EFX.K3.findR1` returns `some (i, s)` (rule R1 applies, first to agent `i`, which leaves with `s`). -/
def peels (v : A → G → Nat) : Nat → List A → List G → Nat
  | 0, _, _ => 0
  | fuel + 1, agents, goods =>
    if agents.length ≤ 1 then 0
    else
      match goods with
      | [] => 0
      | g0 :: gs =>
        match K3.findR1 v agents (g0 :: gs) with
        | some (i, none) => peels v fuel (agents.erase i) (g0 :: gs) + 1
        | some (i, some p) => peels v fuel (agents.erase i) ((g0 :: gs).erase p) + 1
        | none => 0

/-- `peels` is `0` when `run` stops without consulting `findR1`: no fuel, at most one agent, or no goods. -/
theorem peels_stop (v : A → G → Nat) (fuel : Nat) (agents : List A) (goods : List G)
    (h : fuel = 0 ∨ agents.length ≤ 1 ∨ goods = []) : peels v fuel agents goods = 0 := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    unfold peels
    rcases h with h | h | h
    · exact absurd h (Nat.succ_ne_zero fuel)
    · simp [h]
    · subst h
      by_cases h1 : agents.length ≤ 1 <;> simp [h1]

/-- **The rounds that `peels` counts are the R1 rounds of `run`** (a combined recursion lemma). With at least two
agents and some goods: if `findR1` returns `some (i, none)`, `run` continues without `i` and `peels` counts one
round more than on the same arguments; if it returns `some (i, some p)`, `run` gives `p` to `i` and continues
without `i` and `p`, and `peels` counts one round more than on the same arguments; if it returns `none`, `run` is
the core stage and `peels` is `0`. -/
theorem run_peels_step (v : A → G → Nat) (d : A) (fuel : Nat) (agents : List A) (g0 : G) (gs : List G)
    (h2 : 2 ≤ agents.length) :
    (∀ i, K3.findR1 v agents (g0 :: gs) = some (i, none) →
      run v d (fuel + 1) agents (g0 :: gs) = run v d fuel (agents.erase i) (g0 :: gs) ∧
        peels v (fuel + 1) agents (g0 :: gs) = peels v fuel (agents.erase i) (g0 :: gs) + 1) ∧
    (∀ i p, K3.findR1 v agents (g0 :: gs) = some (i, some p) →
      run v d (fuel + 1) agents (g0 :: gs) =
          (extend i p (run v d fuel (agents.erase i) ((g0 :: gs).erase p)).1,
            (run v d fuel (agents.erase i) ((g0 :: gs).erase p)).2) ∧
        peels v (fuel + 1) agents (g0 :: gs) = peels v fuel (agents.erase i) ((g0 :: gs).erase p) + 1) ∧
    (K3.findR1 v agents (g0 :: gs) = none →
      run v d (fuel + 1) agents (g0 :: gs) = deStage v agents (g0 :: gs) g0 d ∧
        peels v (fuel + 1) agents (g0 :: gs) = 0) := by
  have h1 : ¬ agents.length ≤ 1 := by omega
  refine ⟨fun i hf => ?_, fun i p hf => ?_, fun hf => ?_⟩ <;>
    exact ⟨by simp only [run, h1, ↓reduceIte, hf], by simp only [peels, h1, ↓reduceIte, hf]⟩

/-- **Every peeling round removes an agent**, and the rounds stop at one agent: at most `|agents| - 1` rounds. -/
theorem peels_le (v : A → G → Nat) : ∀ (fuel : Nat) (agents : List A) (goods : List G),
    peels v fuel agents goods ≤ agents.length - 1
  | 0, _, _ => Nat.zero_le _
  | fuel + 1, agents, goods => by
    by_cases h1 : agents.length ≤ 1
    · rw [peels_stop v _ agents goods (Or.inr (Or.inl h1))]; exact Nat.zero_le _
    cases goods with
    | nil => rw [peels_stop v _ agents [] (Or.inr (Or.inr rfl))]; exact Nat.zero_le _
    | cons g0 gs =>
      unfold peels
      simp only [h1, ↓reduceIte]
      cases hf : K3.findR1 v agents (g0 :: gs) with
      | none => exact Nat.zero_le _
      | some q =>
        obtain ⟨i, s⟩ := q
        have hl := List.length_erase_of_mem (K3.findR1_some hf).1
        cases s with
        | none =>
          have := peels_le v fuel (agents.erase i) (g0 :: gs)
          simp only
          omega
        | some p =>
          have := peels_le v fuel (agents.erase i) ((g0 :: gs).erase p)
          simp only
          omega

end peeling

/-! ## The model's instances: Theorem "DE is correct" in full -/

/-- The number of agents that DE peels on an instance of the model (the rounds of `run` in `deSpec`). -/
def dePeels (I : Inst) : Nat := peels I.v I.n (List.finRange I.n) (List.finRange I.m)

/-- DE peels at most `n - 1` agents: the last agent is never peeled. -/
theorem dePeels_le_pred (I : Inst) : dePeels I ≤ I.n - 1 := by
  have := peels_le I.v I.n (List.finRange I.n) (List.finRange I.m)
  rwa [List.length_finRange] at this

/-- **DE peels at most `n` agents** (`paper/k3-simple/long.tex`, Theorem `thm:de`). -/
theorem dePeels_le (I : Inst) : dePeels I ≤ I.n := Nat.le_trans (dePeels_le_pred I) (Nat.sub_le _ _)

/-- **Theorem DE is correct, in full** (`paper/k3-simple/long.tex` §6, Theorem `thm:de`). On every instance in
which every agent positively values at most three goods, DE returns an EFX₀ allocation in which all bundles but at
most one have at most two goods; it peels at most `n` agents and applies at most `4n` exchanges. -/
theorem de_correct (I : Inst) (hn : 0 < I.n) (h : ∀ i, numRelevant I i ≤ 3) :
    I.EFX0 (deSpec I hn) ∧
      (∃ o, ∀ j, j ≠ o → finSum I.m (fun g => if deSpec I hn g = j then 1 else 0) ≤ 2) ∧
      dePeels I ≤ I.n ∧ deMoves I hn ≤ 4 * I.n := by
  obtain ⟨hE, hS, hM⟩ := deSpec_correct I hn h
  exact ⟨hE, hS, dePeels_le I, hM⟩

/-! ## DE on ordered values in the comparison model -/

section ordered
variable {V : Type} [OrderedValue V]

/-- **Algorithm DE on ordered values** (comparison model): DE (`EFX.DE.deSpec`) on the natural-number surrogate
instance `⟨n, m, w⟩`, where `w = EFX.K3.surrogate le I` is computed with the comparison oracle `le` (as K3ALG in
`EFX.K3.algoOrd`). -/
def deOrd (le : V → V → Bool) (I : OInst V) (hn : 0 < I.n) : I.Alloc :=
  deSpec ⟨I.n, I.m, K3.surrogate le I⟩ hn

/-- The number of exchanges that `deOrd` applies (on the surrogate). -/
def deOrdMoves (le : V → V → Bool) (I : OInst V) (hn : 0 < I.n) : Nat :=
  deMoves ⟨I.n, I.m, K3.surrogate le I⟩ hn

/-- The number of agents that `deOrd` peels (on the surrogate). -/
def deOrdPeels (le : V → V → Bool) (I : OInst V) : Nat :=
  dePeels ⟨I.n, I.m, K3.surrogate le I⟩

/-- `deOrd` runs DE on the value of the counted program `EFX.K3.surrogateC` (each oracle call charged `c` units),
which asks the oracle at most `n (m + 12)` times (`EFX.K3.surrogateC_cost`); DE then asks it nothing. -/
theorem deOrd_eq_surrogateC (c : Nat) (le : V → V → Bool) (I : OInst V) (hn : 0 < I.n) :
    deOrd le I hn = deSpec ⟨I.n, I.m, (K3.surrogateC c le I).val⟩ hn := by
  rw [K3.surrogateC_val]; rfl

/-- **Theorem DE is correct, on ordered values** (`paper/k3-simple/long.tex` §6, the proof of Theorems
`thm:target`, `thm:D` and `thm:algo` for nonnegative real values). For a correct comparison oracle, every instance
with `n ≥ 1` agents, nonnegative values in an `EFX.OrderedValue` type (e.g. `ℝ≥0`) and at most three relevant goods
per agent: `deOrd le I hn` is EFX₀ for the original values, all its bundles but at most one have at most two goods,
and DE peels at most `n` agents and applies at most `4n` exchanges. -/
theorem deOrd_correct {le : V → V → Bool} (hle : ∀ x y, le x y = true ↔ x ≤ y) (I : OInst V) (hn : 0 < I.n)
    (hv : ∀ i g, 0 ≤ I.v i g) (h : ∀ i, I.numRelevant i ≤ 3) :
    I.EFX0 (deOrd le I hn) ∧
      (∃ o, ∀ j, j ≠ o → finSum I.m (fun g => if deOrd le I hn g = j then 1 else 0) ≤ 2) ∧
      deOrdPeels le I ≤ I.n ∧ deOrdMoves le I hn ≤ 4 * I.n := by
  have hw := K3.agree_surrogate hle I hv h
  obtain ⟨hE, hS, hP, hM⟩ := de_correct ⟨I.n, I.m, K3.surrogate le I⟩ hn
    (fun i => (numRelevant_eq_of_agree I _ hw i) ▸ h i)
  exact ⟨(efx0_iff_of_agree I _ hw _).mpr hE, hS, hP, hM⟩

/-- **Theorems existence and one large bundle on ordered values, in general** (`paper/k3-simple/long.tex`,
Theorems `thm:target` and `thm:D`, for nonnegative real values). Every instance with `n ≥ 1` agents, nonnegative
values in an `EFX.OrderedValue` type (e.g. `ℝ≥0`) and at most three relevant goods per agent has an EFX₀
allocation in which all bundles but at most one have at most two goods. (`EFX.corollaryD_ordered` needs exactly
three relevant goods per agent and balance.) -/
theorem thmD_ordered (I : OInst V) (hn : 0 < I.n) (hv : ∀ i g, 0 ≤ I.v i g) (h : ∀ i, I.numRelevant i ≤ 3) :
    ∃ X : I.Alloc, I.EFX0 X ∧ ∃ o, ∀ j, j ≠ o → finSum I.m (fun g => if X g = j then 1 else 0) ≤ 2 := by
  obtain ⟨w, -, hw⟩ := l12 I hv h
  obtain ⟨hE, hS, -⟩ := deSpec_correct ⟨I.n, I.m, w⟩ hn (fun i => (numRelevant_eq_of_agree I w hw i) ▸ h i)
  exact ⟨deSpec ⟨I.n, I.m, w⟩ hn, (efx0_iff_of_agree I w hw _).mpr hE, hS⟩

end ordered

/-! ## An example (non-vacuity; values in `Int`)

The instance `EFX.DE.Examples.peeled` with other values, in `Int`, and the oracle `EFX.K3.Examples.leZ`
(`decide (x ≤ y)`). Agent 2 values `g₄` at `3` and `g₅` at `7`, so rule R1 peels it first, with `g₅`; its surrogate
values are `1, 3` (`7 > 3 + 3`). Agents 0 and 1 value three goods each and are strictly balanced (`40 < 30 + 20`,
`41 < 29 + 23`), with surrogate values `4, 3, 2` and the rankings of `peeled`. The output is that of
`EFX.DE.Examples.peeled_spec`: one peel, then two pair chains. -/

namespace Examples

/-- `EFX.DE.Examples.peeled` with other values, in `Int`. -/
def peeledZ : OInst Int :=
  ⟨3, 6, fun i g => (([[40, 30, 20, 0, 0, 0], [41, 0, 0, 29, 23, 0], [0, 0, 0, 0, 3, 7]] : List (List Int)).getD
    i.val []).getD g.val 0⟩

/-- The surrogate values that the oracle computes. -/
theorem peeledZ_surrogate :
    (List.finRange 3).map (fun i => (List.finRange 6).map (fun g => K3.surrogate K3.Examples.leZ peeledZ i g)) =
      [[4, 3, 2, 0, 0, 0], [4, 0, 0, 3, 2, 0], [0, 0, 0, 0, 1, 3]] := by
  decide

/-- DE on the `Int` values: its output, one peel and two exchanges, and it is EFX₀ with at most one large bundle. -/
theorem peeledZ_deOrd :
    (List.finRange 6).map (fun g => (deOrd K3.Examples.leZ peeledZ (by decide) g).val) = [0, 0, 0, 1, 1, 2] ∧
      deOrdPeels K3.Examples.leZ peeledZ = 1 ∧ deOrdMoves K3.Examples.leZ peeledZ (by decide) = 2 ∧
      peeledZ.EFX0 (deOrd K3.Examples.leZ peeledZ (by decide)) ∧
      ∃ o, ∀ j, j ≠ o →
        finSum peeledZ.m (fun g => if deOrd K3.Examples.leZ peeledZ (by decide) g = j then 1 else 0) ≤ 2 := by
  obtain ⟨hE, hS, -, -⟩ := deOrd_correct K3.Examples.leZ_spec peeledZ (by decide) (by decide)
    (fun i => (K3.numRelevant_eq_relOf K3.Examples.leZ_spec peeledZ i) ▸ (by revert i; decide))
  exact ⟨by decide, by decide, by decide, hE, hS⟩

end Examples

end DE
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE.peels_stop
#print axioms EFX.DE.run_peels_step
#print axioms EFX.DE.peels_le
#print axioms EFX.DE.dePeels_le_pred
#print axioms EFX.DE.dePeels_le
#print axioms EFX.DE.de_correct
#print axioms EFX.DE.deOrd_eq_surrogateC
#print axioms EFX.DE.deOrd_correct
#print axioms EFX.DE.thmD_ordered
#print axioms EFX.DE.Examples.peeledZ_surrogate
#print axioms EFX.DE.Examples.peeledZ_deOrd
