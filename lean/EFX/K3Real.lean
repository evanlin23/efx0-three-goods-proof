import EFX.K3CostBound
import EFX.RealValues

/-!
# K3ALG on ordered values in the comparison model (Corollary "real values")

`EFX.K3.algo` takes natural-number values. This file runs it on values in any `EFX.OrderedValue` type `V` (the
axioms of a linearly ordered cancellative commutative monoid; `ℝ≥0` satisfies them by the textbook fact, core Lean
has no reals) through the integer surrogate of Lemma L12 (`EFX.l12`), which it *computes* with a comparison oracle.

**The oracle.** The program receives `le : V → V → Bool` and inspects the values only through it; otherwise it only
reads them and adds two values of one agent in `V` (six additions per agent, `patC`, one unit each). It asks whether
`v_i(g) ≤ 0`, and whether `x ≤ y` for `x, y` single values or sums of two values of one agent. With three relevant
goods these are comparisons of two subset sums; with one or two, the phantom slot repeats the first good, so a side
can be `2 v_i(g₁)` (e.g. `v_i(g₂) ≤ v_i(g₁) + v_i(g₁)`), a sum with repetition that subset-sum comparisons do not
determine. So the oracle compares sums of one agent's values with repetition, as in the real-RAM model of
`proofs/k3_algorithm.md` §3. The theorems assume the oracle is correct, `∀ x y, le x y = true ↔ x ≤ y`.
A call is charged `c` units (`askC`); the algorithm fixes `c = 1`, and `surrogateC_cost` is stated for every `c`,
so its coefficient of `c` bounds the number of calls.

**The surrogate** (`surrogate`, the constructive content of `EFX.OrderedValue.exists_agree`). For each agent `i`:
- its relevant goods, in index order: one oracle call `v_i(g) ≤ 0` per good (`relOf`, `relC`);
- the pattern (`EFX.Pat`) of the values `x₁, x₂, x₃` of its first three relevant goods (with one or two relevant
  goods, the phantom-slot values of `exists_agree`): twelve oracle calls (`patOf`, `patC`);
- the first row of the 31-row table `EFX.Pat.reps` with that pattern (`repOf`, `repC`; no oracle call), whose
  entries become `w_i` on those goods, and `w_i(g) = 0` elsewhere (`wOf`).
`surrogateC` stores `w` as an `n × m` table (arrays filled once, `EFX.Timed.mkTable`), so K3ALG reads it at unit
cost, as it reads its input.

**The algorithm** `algoOrd le I hn := (algoOrdC le I hn).val`, where `algoOrdC` computes the surrogate and runs
`EFX.K3.algoC` on the instance `⟨n, m, w⟩` (`algoOrd_eq`: `algoOrd` is `EFX.K3.algo` on the surrogate).

- `agree_surrogate`: for a correct oracle, nonnegative values and at most three relevant goods per agent, `w_i`
  agrees with `v_i` on every comparison of two subset sums (`EFX.Agree`).
- `algoOrd_efx0`: **correctness**: under the same hypotheses `algoOrd le I hn` is EFX₀ for the original values
  (via `EFX.efx0_iff_of_agree` and `EFX.K3.algo_efx0`).
- `surrogateC_cost`: with each oracle call charged `c` units, computing `w` costs at most
  `c · n (m + 12) + 10 n m + 971 n`: the program asks `m + 12` oracle calls per agent (the coefficient of `c`), and
  does `O(nm)` other operations.
- `algoOrdC_cost`: **the cost** (`c = 1`): at most `n (m + 12) + 10 n m + 971 n + 400 (n + m + 1)⁴` counted
  operations on every instance with `n ≥ 1`, each oracle call counted as one unit, whatever the number of relevant
  goods (with the finer count of K3ALG: `EFX.K3.algoOrdC_cost_fine` in `EFX.K3CostFine`).
- `Examples.peelOwnerZ_algoOrd`: an instance with values in `Int`, checked by `decide`.

What a unit counts is `EFX.K3CostLB`'s list, plus: one oracle call (`askC`), one addition of two values in `V`
(`patC`'s `tick 6`), one read of an input value `v i g` (`relC`'s `tick 1`).
-/

set_option autoImplicit false

namespace EFX
namespace K3

open Timed OrderedValue

section oracle
variable {V : Type} [OrderedValue V]

/-! ## The counted program -/

/-- One call of the comparison oracle `le` (is `x ≤ y`?), charged `c` units (`c = 1` in the comparison model). -/
def askC (c : Nat) (le : V → V → Bool) (x y : V) : Timed Bool := do
  tick c
  pure (le x y)

/-- The pattern of three values as the oracle answers it (`EFX.Pat`: the twelve basic comparisons). -/
def patOf (le : V → V → Bool) (x1 x2 x3 : V) : Pat :=
  ⟨le x1 x2, le x2 x1, le x1 x3, le x3 x1, le x2 x3, le x3 x2, le x1 (x2 + x3), le (x2 + x3) x1,
   le x2 (x1 + x3), le (x1 + x3) x2, le x3 (x1 + x2), le (x1 + x2) x3⟩

/-- The pattern: six additions of two values (`tick 6`) and twelve oracle calls. -/
def patC (c : Nat) (le : V → V → Bool) (x1 x2 x3 : V) : Timed Pat := do
  tick 6
  let p12 ← askC c le x1 x2
  let p21 ← askC c le x2 x1
  let p13 ← askC c le x1 x3
  let p31 ← askC c le x3 x1
  let p23 ← askC c le x2 x3
  let p32 ← askC c le x3 x2
  let q1 ← askC c le x1 (x2 + x3)
  let r1 ← askC c le (x2 + x3) x1
  let q2 ← askC c le x2 (x1 + x3)
  let r2 ← askC c le (x1 + x3) x2
  let q3 ← askC c le x3 (x1 + x2)
  let r3 ← askC c le (x1 + x2) x3
  pure ⟨p12, p21, p13, p31, p23, p32, q1, r1, q2, r2, q3, r3⟩

/-- The representative of a pattern: the first row of the table `EFX.Pat.reps` with that pattern (`(1, 1, 1)` if
there is none, which does not happen for a pattern of positive values). -/
def repOf (b : Pat) : Nat × Nat × Nat :=
  (Pat.reps.find? (fun A => decide (Pat.ofNat A.1 A.2.1 A.2.2 = b))).getD (1, 1, 1)

/-- The representative, by a scan of the 31 rows. Each row: its pattern (six additions and twelve comparisons of
natural numbers) and the comparison of the two patterns (twelve Boolean comparisons): `tick 30`. -/
def repC (b : Pat) : Timed (Nat × Nat × Nat) := do
  let r ← findC (fun A => do tick 30; pure (decide (Pat.ofNat A.1 A.2.1 A.2.2 = b))) Pat.reps
  pure (r.getD (1, 1, 1))

/-- The relevant goods of an agent with values `f`, in index order, as the oracle answers `f g ≤ 0`. -/
def relOf (le : V → V → Bool) {m : Nat} (f : Fin m → V) : List (Fin m) :=
  (List.finRange m).filter (fun g => !le (f g) 0)

/-- The relevant goods: for each good, one read of its value (`tick 1`) and one oracle call. -/
def relC (c : Nat) (le : V → V → Bool) {m : Nat} (f : Fin m → V) : Timed (List (Fin m)) := do
  let gs ← finRangeC m
  filterC (fun g => do
    tick 1
    let z ← askC c le (f g) 0
    pure (!z)) gs

/-- The values of the three slots of the pattern: those of the first three relevant goods; with one or two
relevant goods, the phantom slots repeat the first good (as in `EFX.OrderedValue.exists_agree`). -/
def slotVals {m : Nat} (f : Fin m → V) : List (Fin m) → V × V × V
  | [] => (0, 0, 0)
  | [g1] => (f g1, f g1, f g1)
  | [g1, g2] => (f g1, f g2, f g1)
  | g1 :: g2 :: g3 :: _ => (f g1, f g2, f g3)

end oracle

/-- The surrogate values of one agent: the representative `A` on its (first three) relevant goods `L`, `0` elsewhere. -/
def wOf {m : Nat} (L : List (Fin m)) (A : Nat × Nat × Nat) (g : Fin m) : Nat :=
  match L with
  | [] => 0
  | [g1] => if g = g1 then A.1 else 0
  | [g1, g2] => if g = g1 then A.1 else if g = g2 then A.2.1 else 0
  | g1 :: g2 :: g3 :: _ => if g = g1 then A.1 else if g = g2 then A.2.1 else if g = g3 then A.2.2 else 0

section oracle
variable {V : Type} [OrderedValue V]

/-- The surrogate values of an agent with values `f` and relevant goods `L`. -/
def surrOfL (le : V → V → Bool) {m : Nat} (f : Fin m → V) (L : List (Fin m)) : Fin m → Nat :=
  wOf L (repOf (patOf le (slotVals f L).1 (slotVals f L).2.1 (slotVals f L).2.2))

/-- **The integer surrogate** of an instance (L12, computed): `w_i = surrOfL le v_i (relOf le v_i)`. -/
def surrogate (le : V → V → Bool) (I : OInst V) : Fin I.n → Fin I.m → Nat :=
  fun i => surrOfL le (I.v i) (relOf le (I.v i))

/-- One agent's surrogate values, stored in an array: the relevant goods, the three slot values (at most three list
cells and three value reads: `tick 3`), the pattern, the representative, and for each good up to three comparisons
of goods and three list cells (`tick 6`). -/
def agentC (c : Nat) (le : V → V → Bool) {m : Nat} (f : Fin m → V) : Timed (Fin m → Nat) := do
  let L ← relC c le f
  tick 3
  let b ← patC c le (slotVals f L).1 (slotVals f L).2.1 (slotVals f L).2.2
  let A ← repC b
  mkTable m (fun g => do tick 6; pure (wOf L A g))

/-- **The surrogate as a counted program**: an `n × m` table, each oracle call charged `c` units. -/
def surrogateC (c : Nat) (le : V → V → Bool) (I : OInst V) : Timed (Fin I.n → Fin I.m → Nat) :=
  mkTable I.n (fun i => agentC c le (I.v i))

/-- **Algorithm K3ALG on ordered values, as a counted program** (comparison model: one unit per oracle call):
compute the surrogate `w`, then run `EFX.K3.algoC` on `⟨n, m, w⟩`. -/
def algoOrdC (le : V → V → Bool) (I : OInst V) (hn : 0 < I.n) : Timed I.Alloc := do
  let w ← surrogateC 1 le I
  algoC ⟨I.n, I.m, w⟩ hn

/-- **Algorithm K3ALG on ordered values**: the allocation `algoOrdC` computes. -/
def algoOrd (le : V → V → Bool) (I : OInst V) (hn : 0 < I.n) : I.Alloc := (algoOrdC le I hn).val

/-! ## Value lemmas -/

omit [OrderedValue V] in
@[simp] theorem askC_val (c : Nat) (le : V → V → Bool) (x y : V) : (askC c le x y).val = le x y := rfl

@[simp] theorem patC_val (c : Nat) (le : V → V → Bool) (x1 x2 x3 : V) :
    (patC c le x1 x2 x3).val = patOf le x1 x2 x3 := rfl

@[simp] theorem repC_val (b : Pat) : (repC b).val = repOf b := by
  simp [repC, repOf]

@[simp] theorem relC_val (c : Nat) (le : V → V → Bool) {m : Nat} (f : Fin m → V) :
    (relC c le f).val = relOf le f := by
  simp [relC, relOf, finRangeC, askC]

theorem agentC_val (c : Nat) (le : V → V → Bool) {m : Nat} (f : Fin m → V) :
    (agentC c le f).val = surrOfL le f (relOf le f) := by
  simp only [agentC, bind_val, relC_val, patC_val, repC_val, mkTable_val, pure_val, surrOfL]

theorem surrogateC_val (c : Nat) (le : V → V → Bool) (I : OInst V) : (surrogateC c le I).val = surrogate le I := by
  funext i
  simp only [surrogateC, mkTable_val, agentC_val, surrogate]

/-- `algoOrd` is algorithm K3ALG (`EFX.K3.algo`) run on the surrogate instance. -/
theorem algoOrd_eq (le : V → V → Bool) (I : OInst V) (hn : 0 < I.n) :
    algoOrd le I hn = algo ⟨I.n, I.m, surrogate le I⟩ hn := by
  have e : ∀ w w' : Fin I.n → Fin I.m → Nat, w = w' →
      (algoC ⟨I.n, I.m, w⟩ hn).val = (algoC ⟨I.n, I.m, w'⟩ hn).val := by
    intro w w' h; subst h; rfl
  exact e _ _ (surrogateC_val 1 le I)

/-! ## Correctness -/

/-- **The representative is right** (constructive `EFX.OrderedValue.tri_rep`): for positive `x₁, x₂, x₃` and a
correct oracle, the representative of the oracle's pattern answers every comparison of two subsets of slots as
`x₁, x₂, x₃` do, and is positive. -/
theorem repOf_spec {le : V → V → Bool} (hle : ∀ x y, le x y = true ↔ x ≤ y) {x1 x2 x3 : V}
    (h1 : ¬ x1 ≤ 0) (h2 : ¬ x2 ≤ 0) (h3 : ¬ x3 ≤ 0) :
    0 < (repOf (patOf le x1 x2 x3)).1 ∧ 0 < (repOf (patOf le x1 x2 x3)).2.1 ∧
      0 < (repOf (patOf le x1 x2 x3)).2.2 ∧ ∀ s1 s2 s3 t1 t2 t3 : Bool,
      (tri s1 s2 s3 x1 x2 x3 ≤ tri t1 t2 t3 x1 x2 x3 ↔
        tri s1 s2 s3 (repOf (patOf le x1 x2 x3)).1 (repOf (patOf le x1 x2 x3)).2.1 (repOf (patOf le x1 x2 x3)).2.2 ≤
          tri t1 t2 t3 (repOf (patOf le x1 x2 x3)).1 (repOf (patOf le x1 x2 x3)).2.1
            (repOf (patOf le x1 x2 x3)).2.2) := by
  have hR : Realizes x1 x2 x3 (patOf le x1 x2 x3) := by constructor <;> exact hle _ _
  have hok := Pat.ok_of_realizes hR h1 h2 h3
  have hany := Pat.all_spec Pat.table.1 (patOf le x1 x2 x3)
  rw [hok, Bool.not_true, Bool.false_or] at hany
  unfold repOf
  cases hf : Pat.reps.find? (fun A => decide (Pat.ofNat A.1 A.2.1 A.2.2 = patOf le x1 x2 x3)) with
  | none =>
    obtain ⟨A, hA, hAd⟩ := List.any_eq_true.mp hany
    exact absurd hAd (by simpa using List.find?_eq_none.mp hf A hA)
  | some A =>
    have hmem := List.mem_of_find?_eq_some hf
    have hA := List.find?_some hf
    have hpos := of_decide_eq_true (List.all_eq_true.mp Pat.table.2 _ hmem)
    have hRA : Realizes A.1 A.2.1 A.2.2 (patOf le x1 x2 x3) :=
      of_decide_eq_true hA ▸ Pat.realizes_ofNat A.1 A.2.1 A.2.2
    simp only [Option.getD_some]
    refine ⟨hpos.1, hpos.2.1, hpos.2.2, fun s1 s2 s3 t1 t2 t3 => ?_⟩
    rw [tri_le_iff hR h1 h2 h3, tri_le_iff hRA (Nat.not_le.mpr hpos.1) (Nat.not_le.mpr hpos.2.1)
      (Nat.not_le.mpr hpos.2.2)]

/-- **One agent** (constructive `EFX.OrderedValue.exists_agree`): if `L` lists, without repetition, exactly the
goods of positive value (at most three), the surrogate values agree with `f` on every comparison of two subset
sums. -/
theorem agree_surrOfL {le : V → V → Bool} (hle : ∀ x y, le x y = true ↔ x ≤ y) {m : Nat} (f : Fin m → V)
    (L : List (Fin m)) (hnd : L.Nodup) (hmem : ∀ g ∈ L, ¬ f g ≤ 0) (hout : ∀ g, g ∉ L → f g = 0)
    (hlen : L.length ≤ 3) : Agree f (surrOfL le f L) := by
  rcases L with _ | ⟨g1, _ | ⟨g2, _ | ⟨g3, _ | ⟨g4, L⟩⟩⟩⟩
  · -- no relevant good
    have e : surrOfL le f [] = fun _ => 0 := rfl
    rw [e]
    intro S T _ _
    rw [finSumO_support m [] _ hnd (fun g hg => by simp [hout g hg]),
      finSumO_support m [] _ hnd (fun g hg => by simp [hout g hg])]
    simp [listSum, finSum_eq_sum, le_refl]
  · -- one relevant good
    have h1 := hmem g1 (by simp)
    have e : surrOfL le f [g1] = fun g => if g = g1 then (repOf (patOf le (f g1) (f g1) (f g1))).1 else 0 := rfl
    rw [e]
    obtain ⟨-, -, -, hA⟩ := repOf_spec hle h1 h1 h1
    generalize repOf (patOf le (f g1) (f g1) (f g1)) = A at hA ⊢
    obtain ⟨A1, A2, A3⟩ := A
    exact agree_of_slots f _ [g1] hnd hout (fun g hg => by simp at hg; simp [hg]) _ _ _ A1 A2 A3 hA
      (fun S => (S g1, false, false)) (fun S => by simp [listSum, tri, add_zero])
      (fun S => by simp [listSum, tri, add_zero])
  · -- two relevant goods (the third slot is a phantom that no set contains)
    have h21 : g2 ≠ g1 := fun e => by subst e; simp at hnd
    have e : surrOfL le f [g1, g2] = fun g => if g = g1 then (repOf (patOf le (f g1) (f g2) (f g1))).1
        else if g = g2 then (repOf (patOf le (f g1) (f g2) (f g1))).2.1 else 0 := rfl
    rw [e]
    obtain ⟨-, -, -, hA⟩ := repOf_spec hle (hmem g1 (by simp)) (hmem g2 (by simp)) (hmem g1 (by simp))
    generalize repOf (patOf le (f g1) (f g2) (f g1)) = A at hA ⊢
    obtain ⟨A1, A2, A3⟩ := A
    exact agree_of_slots f _ [g1, g2] hnd hout (fun g hg => by simp at hg; simp [hg]) _ _ _ A1 A2 A3 hA
      (fun S => (S g1, S g2, false)) (fun S => by simp [listSum, tri, add_zero])
      (fun S => by simp [listSum, tri, add_zero, h21])
  · -- three relevant goods
    have h21 : g2 ≠ g1 := fun e => by subst e; simp at hnd
    have h31 : g3 ≠ g1 := fun e => by subst e; simp at hnd
    have h32 : g3 ≠ g2 := fun e => by subst e; simp at hnd
    have e : surrOfL le f [g1, g2, g3] = fun g => if g = g1 then (repOf (patOf le (f g1) (f g2) (f g3))).1
        else if g = g2 then (repOf (patOf le (f g1) (f g2) (f g3))).2.1
        else if g = g3 then (repOf (patOf le (f g1) (f g2) (f g3))).2.2 else 0 := rfl
    rw [e]
    obtain ⟨-, -, -, hA⟩ :=
      repOf_spec hle (hmem g1 (by simp)) (hmem g2 (by simp)) (hmem g3 (by simp))
    generalize repOf (patOf le (f g1) (f g2) (f g3)) = A at hA ⊢
    obtain ⟨A1, A2, A3⟩ := A
    exact agree_of_slots f _ [g1, g2, g3] hnd hout (fun g hg => by simp at hg; simp [hg]) _ _ _
      A1 A2 A3 hA (fun S => (S g1, S g2, S g3)) (fun S => by simp [listSum, tri, add_zero])
      (fun S => by simp [listSum, tri, add_zero, h21, h31, h32])
  · simp at hlen

open Classical in
/-- The oracle finds the relevant goods: `relOf` lists `numRelevant` goods. -/
theorem numRelevant_eq_relOf {le : V → V → Bool} (hle : ∀ x y, le x y = true ↔ x ≤ y) (I : OInst V)
    (i : Fin I.n) : I.numRelevant i = (relOf le (I.v i)).length := by
  unfold OInst.numRelevant
  rw [finSum_eq_sum, sum_map_ite (fun g => ¬ I.v i g ≤ 0) (fun _ => 1), sum_map_one]
  congr 1
  refine List.filter_congr (fun g _ => ?_)
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.not_eq_true', ← Bool.not_eq_true, hle]

/-- **The surrogate agrees with the values** (L12, computed): for a correct oracle, nonnegative values and at most
three relevant goods per agent, `surrogate le I i` agrees with `I.v i` on every comparison of two subset sums. -/
theorem agree_surrogate {le : V → V → Bool} (hle : ∀ x y, le x y = true ↔ x ≤ y) (I : OInst V)
    (hv : ∀ i g, 0 ≤ I.v i g) (h : ∀ i, I.numRelevant i ≤ 3) : ∀ i, Agree (I.v i) (surrogate le I i) := by
  intro i
  have hrel : ∀ g, (!le (I.v i g) 0) = true ↔ ¬ I.v i g ≤ 0 := fun g => by
    rw [Bool.not_eq_true', ← Bool.not_eq_true, hle]
  refine agree_surrOfL hle (I.v i) (relOf le (I.v i)) ((List.nodup_finRange _).sublist List.filter_sublist)
    (fun g hg => (hrel g).mp (List.mem_filter.mp hg).2) (fun g hg => ?_) ((numRelevant_eq_relOf hle I i) ▸ h i)
  refine le_antisymm _ _ (Classical.byContradiction fun hc => hg ?_) (hv i g)
  exact List.mem_filter.mpr ⟨List.mem_finRange g, (hrel g).mpr hc⟩

/-- **Correctness of K3ALG on ordered values.** For a correct comparison oracle, every instance with `n ≥ 1` agents,
nonnegative values in an `EFX.OrderedValue` type (e.g. `ℝ≥0`), and at most three relevant goods per agent,
`algoOrd le I hn` is an EFX₀ allocation for the original values. -/
theorem algoOrd_efx0 {le : V → V → Bool} (hle : ∀ x y, le x y = true ↔ x ≤ y) (I : OInst V) (hn : 0 < I.n)
    (hv : ∀ i g, 0 ≤ I.v i g) (h : ∀ i, I.numRelevant i ≤ 3) : I.EFX0 (algoOrd le I hn) := by
  have hw := agree_surrogate hle I hv h
  rw [algoOrd_eq]
  exact (efx0_iff_of_agree I (surrogate le I) hw _).mpr
    (algo_efx0 _ hn (fun i => (numRelevant_eq_of_agree I _ hw i) ▸ h i))

/-! ## Cost -/

omit [OrderedValue V] in
theorem askC_cost (c : Nat) (le : V → V → Bool) (x y : V) : (askC c le x y).cost = c := rfl

/-- The pattern: exactly twelve oracle calls and six additions. -/
theorem patC_cost (c : Nat) (le : V → V → Bool) (x1 x2 x3 : V) : (patC c le x1 x2 x3).cost = 12 * c + 6 := by
  simp only [patC, askC, bind_cost, tick_cost, pure_cost]
  omega

theorem repC_cost (b : Pat) : (repC b).cost ≤ 961 := by
  have h := findC_cost (fun A => do tick 30; pure (decide (Pat.ofNat A.1 A.2.1 A.2.2 = b))) 30 Pat.reps
    (fun _ _ => by simp)
  have hl : Pat.reps.length = 31 := rfl
  rw [hl] at h
  simp only [repC, bind_cost, pure_cost]
  omega

/-- The relevant goods: exactly `m` oracle calls, and `3m` other operations. -/
theorem relC_cost (c : Nat) (le : V → V → Bool) {m : Nat} (f : Fin m → V) :
    (relC c le f).cost ≤ c * m + 3 * m := by
  have h := filterC_cost (fun g => do
    tick 1
    let z ← askC c le (f g) 0
    pure (!z)) (c + 1) (List.finRange m) (fun _ _ => by simp only [askC, bind_cost, tick_cost, pure_cost]; omega)
  rw [List.length_finRange] at h
  have e : m * (c + 1 + 1) = c * m + 2 * m := by rw [Nat.mul_comm m, Nat.add_mul, Nat.add_mul]; omega
  simp only [relC, finRangeC, bind_cost, tick_cost, pure_cost, pure_val, bind_val]
  omega

/-- One agent: `m + 12` oracle calls, and `10 m + 970` other operations. -/
theorem agentC_cost (c : Nat) (le : V → V → Bool) {m : Nat} (f : Fin m → V) :
    (agentC c le f).cost ≤ c * (m + 12) + 10 * m + 970 := by
  have h1 := relC_cost c le f
  have h3 := mkTable_cost m (fun g => do tick 6; pure (wOf (relC c le f).val
    (repC (patC c le (slotVals f (relC c le f).val).1 (slotVals f (relC c le f).val).2.1
      (slotVals f (relC c le f).val).2.2).val).val g)) 6 (fun _ => by simp)
  have h4 := repC_cost (patC c le (slotVals f (relC c le f).val).1 (slotVals f (relC c le f).val).2.1
      (slotVals f (relC c le f).val).2.2).val
  simp only [agentC, bind_cost, tick_cost, patC_cost]
  rw [Nat.mul_add]
  omega

/-- **The cost of the surrogate**, each oracle call charged `c` units: at most `n (m + 12)` oracle calls (the
coefficient of `c`), and at most `10 n m + 971 n` other operations. -/
theorem surrogateC_cost (c : Nat) (le : V → V → Bool) (I : OInst V) :
    (surrogateC c le I).cost ≤ c * (I.n * (I.m + 12)) + 10 * (I.n * I.m) + 971 * I.n := by
  have h := mkTable_cost I.n (fun i => agentC c le (I.v i)) (c * (I.m + 12) + 10 * I.m + 970)
    (fun i => agentC_cost c le (I.v i))
  have e1 : I.n * (c * (I.m + 12)) = c * (I.n * (I.m + 12)) := Nat.mul_left_comm _ _ _
  have e2 : I.n * (10 * I.m) = 10 * (I.n * I.m) := Nat.mul_left_comm _ _ _
  have e3 : I.n * (c * (I.m + 12) + 10 * I.m + 970 + 1) =
      I.n * (c * (I.m + 12)) + I.n * (10 * I.m) + I.n * 970 + I.n * 1 := by simp only [Nat.mul_add]
  unfold surrogateC
  omega

/-- **The cost of K3ALG on ordered values** (comparison model, one unit per oracle call): at most
`n (m + 12) + 10 n m + 971 n` operations for the surrogate (of which `n (m + 12)` oracle calls,
`surrogateC_cost`), plus `EFX.K3.algoC_cost`'s `400 (n + m + 1)⁴` for K3ALG on it, on every instance with
`n ≥ 1` (whatever the number of relevant goods). -/
theorem algoOrdC_cost (le : V → V → Bool) (I : OInst V) (hn : 0 < I.n) :
    (algoOrdC le I hn).cost ≤
      I.n * (I.m + 12) + 10 * (I.n * I.m) + 971 * I.n + 400 * (I.n + I.m + 1) ^ 4 := by
  have h1 := surrogateC_cost 1 le I
  have h2 := algoC_cost ⟨I.n, I.m, (surrogateC 1 le I).val⟩ hn
  simp only at h2
  simp only [algoOrdC, bind_cost]
  omega

end oracle

/-! ## An example (non-vacuity; values in `Int`)

The instance `EFX.K3.Examples.peelOwner` (the paper's example of a peel followed by owner `r`) with values in `Int`
and the oracle `decide (x ≤ y)`. Agent 0's values `84, 73, 54` have the pattern `a > b > c`, `a < b + c`, so its
surrogate is `4, 3, 2`; the output is the allocation `EFX.K3.Examples.peelOwner_algo` finds on the natural-number
values, and it is EFX₀ for the `Int` values by `algoOrd_efx0`. -/

namespace Examples

/-- `EFX.K3.Examples.peelOwner` with values in `Int`. -/
def peelOwnerZ : OInst Int :=
  ⟨3, 6, fun i g => (([[0, 0, 84, 0, 73, 54], [0, 87, 0, 0, 0, 0], [0, 0, 83, 44, 92, 0]] : List (List Int)).getD
    i.val []).getD g.val 0⟩

/-- The comparison oracle on `Int`. -/
def leZ (x y : Int) : Bool := decide (x ≤ y)

theorem leZ_spec (x y : Int) : leZ x y = true ↔ x ≤ y := decide_eq_true_iff

theorem peelOwnerZ_surrogate :
    (List.finRange 6).map (fun g => surrogate leZ peelOwnerZ ⟨0, by decide⟩ g) = [0, 0, 4, 0, 3, 2] ∧
    (List.finRange 6).map (fun g => surrogate leZ peelOwnerZ ⟨1, by decide⟩ g) = [0, 1, 0, 0, 0, 0] ∧
    (List.finRange 6).map (fun g => surrogate leZ peelOwnerZ ⟨2, by decide⟩ g) = [0, 0, 3, 2, 4, 0] := by
  decide

theorem peelOwnerZ_spec :
    (List.finRange 6).map (fun g => (algoSpec ⟨3, 6, surrogate leZ peelOwnerZ⟩ (by decide) g).val) =
      [2, 1, 0, 2, 2, 0] := by
  decide

/-- K3ALG on the `Int` values: its output, and it is EFX₀. -/
theorem peelOwnerZ_algoOrd :
    (List.finRange 6).map (fun g => (algoOrd leZ peelOwnerZ (by decide) g).val) = [2, 1, 0, 2, 2, 0] ∧
      peelOwnerZ.EFX0 (algoOrd leZ peelOwnerZ (by decide)) :=
  ⟨by simp only [algoOrd_eq, algo_eq_spec]; exact peelOwnerZ_spec,
    algoOrd_efx0 leZ_spec peelOwnerZ (by decide) (by decide)
      (fun i => (numRelevant_eq_relOf leZ_spec peelOwnerZ i) ▸ (by revert i; decide))⟩

end Examples
end K3
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.K3.repOf_spec
#print axioms EFX.K3.agree_surrOfL
#print axioms EFX.K3.numRelevant_eq_relOf
#print axioms EFX.K3.agree_surrogate
#print axioms EFX.K3.algoOrd_eq
#print axioms EFX.K3.algoOrd_efx0
#print axioms EFX.K3.surrogateC_cost
#print axioms EFX.K3.algoOrdC_cost
#print axioms EFX.K3.Examples.peelOwnerZ_algoOrd
