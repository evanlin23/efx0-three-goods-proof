import EFX.Target
import EFX.CorollaryD

/-!
# L12: TARGET and conjecture D over any ordered value type

`EFX.target` and `EFX.LB.corollaryD` are stated over natural-number values (`EFX.Model`). This file
proves them over any type of values `V` with `0`, `+` and `≤` satisfying the axioms of
`OrderedValue` below: `+` associative and commutative with identity `0`, `≤` a total order, and
`a ≤ b ↔ a + c ≤ b + c`. These axioms hold in `ℝ≥0`, `ℚ≥0` and `ℕ` (and in `ℝ`, `ℚ`, `ℤ`);
nonnegativity of the values is a hypothesis of the theorems (`∀ i g, 0 ≤ v i g`), not an axiom.
Core Lean has no `ℝ`, so the `ℝ≥0` instance is the textbook fact that `ℝ≥0` is a linearly ordered
cancellative commutative monoid; the instances for `Nat` and `Int` are below.

The V-valued model (`OInst`, `OInst.bundleVal`, `OInst.EFX0`, `OInst.numRelevant`) mirrors
`EFX.Model` word for word, with `Nat` replaced by `V` and relevance `0 < v i g` by `¬ v i g ≤ 0`.

**L12** (`EFX.l12`, proofs/real_values.md). If every agent has at most three relevant goods, there
are natural-number values `w` with the same relevant goods and the same answer to every comparison
between two subset sums (`Agree`). Proof: for an agent with relevant goods of values `x₁, x₂, x₃`,
every comparison of two subset sums is, after cancelling the common goods, a comparison between
disjoint subsets (`tri_cancel`), hence decided by twelve basic comparisons (`Pat`, `Realizes`,
`tri_le_iff`). Those twelve answers satisfy the constraints `Pat.ok` (totality, transitivity,
positivity), and every pattern satisfying them is realized by one of 31 natural-number triples, the
permutations of the representatives of proofs/real_values.md (`table`, checked by `decide +kernel`). Agents
with one or two relevant goods use the same table with a phantom slot that no subset contains.

**Consequences.** EFX₀, the relevant-goods count and balance transfer along `Agree`
(`efx0_iff_of_agree`, `numRelevant_eq_of_agree`, `balanced_iff_of_agree`), so `EFX.target` and
`EFX.LB.corollaryD` applied to `w` give `target_ordered` and `corollaryD_ordered`. At `V = Nat`
the model is `EFX.Model` (`efx0_nat_iff`, `numRelevant_nat`), and `target_ordered` specializes to
the statement of `EFX.target` (`target_of_ordered`).
-/

set_option autoImplicit false

namespace EFX

/-! ## The value class -/

/-- A type of values: a commutative monoid `(V, +, 0)` with a total order `≤` compatible with `+` in
both directions (a linearly ordered cancellative commutative monoid). `ℝ≥0`, `ℚ≥0`, `ℕ` satisfy
these axioms; nonnegativity of the values is a hypothesis of the theorems below. -/
class OrderedValue (V : Type) extends Zero V, Add V, LE V where
  add_assoc : ∀ a b c : V, a + b + c = a + (b + c)
  add_comm : ∀ a b : V, a + b = b + a
  zero_add : ∀ a : V, 0 + a = a
  le_refl : ∀ a : V, a ≤ a
  le_trans : ∀ a b c : V, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ a b : V, a ≤ b → b ≤ a → a = b
  le_total : ∀ a b : V, a ≤ b ∨ b ≤ a
  add_le_add_iff_right : ∀ a b c : V, a ≤ b ↔ a + c ≤ b + c

instance : OrderedValue Nat where
  add_assoc := Nat.add_assoc
  add_comm := Nat.add_comm
  zero_add := Nat.zero_add
  le_refl := Nat.le_refl
  le_trans _ _ _ := Nat.le_trans
  le_antisymm _ _ := Nat.le_antisymm
  le_total := Nat.le_total
  add_le_add_iff_right _ _ _ := by omega

/-- `Int` satisfies the axioms too (the theorems then assume nonnegative values). -/
instance : OrderedValue Int where
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_add := Int.zero_add
  le_refl := Int.le_refl
  le_trans _ _ _ := Int.le_trans
  le_antisymm _ _ := Int.le_antisymm
  le_total := Int.le_total
  add_le_add_iff_right _ _ _ := by omega

namespace OrderedValue
variable {V : Type} [OrderedValue V]

theorem add_zero (a : V) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_le_add_iff_left (a b c : V) : a ≤ b ↔ c + a ≤ c + b := by
  rw [add_comm c a, add_comm c b]; exact add_le_add_iff_right a b c

theorem add4 (a b c d : V) : a + b + (c + d) = a + c + (b + d) := by
  rw [add_assoc, ← add_assoc b, add_comm b c, add_assoc c, ← add_assoc]

theorem nonneg_of_pos {a : V} (h : ¬ a ≤ 0) : 0 ≤ a := (le_total a 0).resolve_left h

theorem le_add_right {a b : V} (hb : 0 ≤ b) : a ≤ a + b := by
  have := (add_le_add_iff_left 0 b a).mp hb; rwa [add_zero] at this

theorem le_add_left {a b : V} (hb : 0 ≤ b) : a ≤ b + a := by
  rw [add_comm]; exact le_add_right hb

theorem add_nonneg {a b : V} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
  le_trans _ _ _ ha (le_add_right hb)

theorem add_pos {a b : V} (ha : ¬ a ≤ 0) (hb : 0 ≤ b) : ¬ a + b ≤ 0 :=
  fun h => ha (le_trans _ _ _ (le_add_right hb) h)

/-- `a + b ≤ a` forces `b ≤ 0`. -/
theorem not_add_le_left {a b : V} (hb : ¬ b ≤ 0) : ¬ a + b ≤ a := fun h =>
  hb ((add_le_add_iff_left b 0 a).mpr (by rwa [add_zero]))

/-- `a + b ≤ b` forces `a ≤ 0`. -/
theorem not_add_le_right {a b : V} (ha : ¬ a ≤ 0) : ¬ a + b ≤ b := by
  rw [add_comm]; exact not_add_le_left ha

end OrderedValue

open OrderedValue

/-! ## The V-valued model (mirrors `EFX.Model`) -/

section model
variable {V : Type} [OrderedValue V]

/-- Sum of `f` over `Fin k` (as `finSum`). -/
def finSumO : (k : Nat) → (Fin k → V) → V
  | 0, _ => 0
  | k+1, f => finSumO k (fun i => f i.castSucc) + f (Fin.last k)

end model

/-- An additive fair-division instance with values in `V` (as `Inst`). -/
structure OInst (V : Type) where
  n : Nat
  m : Nat
  v : Fin n → Fin m → V

namespace OInst
variable {V : Type} [OrderedValue V] (I : OInst V)

/-- A complete allocation is an owner map. -/
abbrev Alloc := Fin I.m → Fin I.n

/-- Value, for agent `i`, of agent `j`'s bundle with the good `ex` (if any) removed. -/
def bundleVal (X : I.Alloc) (i j : Fin I.n) (ex : Option (Fin I.m)) : V :=
  finSumO I.m (fun g => if X g = j ∧ ex ≠ some g then I.v i g else 0)

/-- Strong EFX₀: for all `i ≠ j` and every good `g ∈ X_j`, `v_i(X_i) ≥ v_i(X_j \ {g})`. -/
def EFX0 (X : I.Alloc) : Prop :=
  ∀ i j : Fin I.n, i ≠ j → ∀ g : Fin I.m, X g = j →
    I.bundleVal X i j (some g) ≤ I.bundleVal X i i none

open Classical in
/-- The number of relevant goods `|R_i|`, where `g` is relevant to `i` iff `v i g > 0`, i.e.
`¬ v i g ≤ 0`. -/
noncomputable def numRelevant (i : Fin I.n) : Nat :=
  finSum I.m (fun g => if ¬ I.v i g ≤ 0 then 1 else 0)

end OInst

/-! ## Sums -/

namespace OrderedValue
variable {V : Type} [OrderedValue V]

/-- Sum of a list (right fold). -/
def listSum : List V → V
  | [] => 0
  | a :: l => a + listSum l

theorem finSumO_zero : ∀ k : Nat, finSumO k (fun _ => (0 : V)) = 0
  | 0 => rfl
  | k + 1 => by rw [finSumO, finSumO_zero k, add_zero]

theorem finSumO_add : ∀ (k : Nat) (f h : Fin k → V),
    finSumO k (fun g => f g + h g) = finSumO k f + finSumO k h
  | 0, _, _ => by simp only [finSumO, add_zero]
  | k + 1, f, h => by
    simp only [finSumO]; rw [finSumO_add k, add4]

theorem finSumO_single : ∀ (k : Nat) (a : Fin k) (x : V),
    finSumO k (fun g => if g = a then x else 0) = x
  | 0, a, _ => a.elim0
  | k + 1, a, x => by
    rw [finSumO]
    by_cases ha : a = Fin.last k
    · subst ha
      have h0 : (fun i : Fin k => if i.castSucc = Fin.last k then x else 0) = fun _ => 0 :=
        funext fun i => by simp [Fin.ne_of_lt (Fin.castSucc_lt_last i)]
      rw [h0, finSumO_zero]; simp [zero_add]
    · have hlt : a.val < k := by
        have := a.isLt; have : a.val ≠ k := fun h => ha (Fin.ext (by simp [h])); omega
      have h0 : (fun i : Fin k => if i.castSucc = a then x else 0) =
          fun i => if i = ⟨a.val, hlt⟩ then x else 0 :=
        funext fun i => by simp [Fin.ext_iff]
      rw [h0, finSumO_single k]; simp [Ne.symm ha, add_zero]

/-- A sum over `Fin k` of a function vanishing outside a duplicate-free list is the sum over the
list. -/
theorem finSumO_support (k : Nat) : ∀ (L : List (Fin k)) (h : Fin k → V), L.Nodup →
    (∀ g, g ∉ L → h g = 0) → finSumO k h = listSum (L.map h)
  | [], h, _, hs => by
    rw [show h = fun _ => 0 from funext fun g => hs g List.not_mem_nil, finSumO_zero]; rfl
  | a :: L, h, hnd, hs => by
    obtain ⟨haL, hnd⟩ := List.nodup_cons.mp hnd
    have hsplit : h = fun g => (if g = a then h a else 0) + (if g = a then 0 else h g) :=
      funext fun g => by by_cases hg : g = a <;> simp [hg, add_zero, zero_add]
    have e : finSumO k h = h a + finSumO k (fun g => if g = a then 0 else h g) :=
      calc finSumO k h
          = finSumO k (fun g => (if g = a then h a else 0) + (if g = a then 0 else h g)) :=
            congrArg _ hsplit
        _ = _ := by rw [finSumO_add, finSumO_single]
    rw [e, finSumO_support k L _ hnd (fun g hg => by
        by_cases hga : g = a
        · simp [hga]
        · simp only [hga]; exact hs g (by simp [hga, hg]))]
    simp only [List.map_cons, listSum]
    congr 2
    exact List.map_congr_left fun g hg => by simp [show g ≠ a from fun e => haL (e ▸ hg)]

/-- Splitting off one good: `v(M) = v(g) + v(M \ {g})`. -/
theorem finSumO_split (k : Nat) (f : Fin k → V) (a : Fin k) :
    finSumO k f = finSumO k (fun g => if g = a then f g else 0) +
      finSumO k (fun g => if ¬ g = a then f g else 0) := by
  rw [← finSumO_add]; congr 1; funext g; by_cases hg : g = a <;> simp [hg, add_zero, zero_add]

/-- At `V = Nat`, `finSumO` is `finSum`. -/
theorem finSumO_nat : ∀ (k : Nat) (f : Fin k → Nat), finSumO k f = finSum k f
  | 0, _ => rfl
  | k + 1, f => by rw [finSumO, finSum, finSumO_nat k]

end OrderedValue

/-! ## Three slots: every subset comparison is decided by twelve basic comparisons -/

namespace OrderedValue
variable {V : Type} [OrderedValue V]

/-- The value of the subset `{k : s_k}` of three slots with values `x₁, x₂, x₃`. -/
def tri (s1 s2 s3 : Bool) (x1 x2 x3 : V) : V :=
  (if s1 then x1 else 0) + ((if s2 then x2 else 0) + (if s3 then x3 else 0))

theorem add6 (a1 b1 a2 b2 a3 b3 : V) :
    a1 + b1 + (a2 + b2 + (a3 + b3)) = a1 + (a2 + a3) + (b1 + (b2 + b3)) := by
  rw [add4 a2 b2 a3 b3, add4 a1 b1]

theorem ite_split (s t : Bool) (x : V) :
    (if s then x else 0) = (if (s && t) then x else 0) + (if (s && !t) then x else 0) := by
  cases s <;> cases t <;> simp [zero_add, add_zero]

theorem tri_split (s1 s2 s3 t1 t2 t3 : Bool) (x1 x2 x3 : V) :
    tri s1 s2 s3 x1 x2 x3 = tri (s1 && t1) (s2 && t2) (s3 && t3) x1 x2 x3 +
      tri (s1 && !t1) (s2 && !t2) (s3 && !t3) x1 x2 x3 := by
  unfold tri; rw [ite_split s1 t1, ite_split s2 t2, ite_split s3 t3, add6]

/-- Cancelling the common slots: `S ≤ T` iff `S \ T ≤ T \ S`. -/
theorem tri_cancel (s1 s2 s3 t1 t2 t3 : Bool) (x1 x2 x3 : V) :
    tri s1 s2 s3 x1 x2 x3 ≤ tri t1 t2 t3 x1 x2 x3 ↔
      tri (s1 && !t1) (s2 && !t2) (s3 && !t3) x1 x2 x3 ≤
        tri (t1 && !s1) (t2 && !s2) (t3 && !s3) x1 x2 x3 := by
  rw [tri_split s1 s2 s3 t1 t2 t3, tri_split t1 t2 t3 s1 s2 s3, Bool.and_comm t1,
    Bool.and_comm t2, Bool.and_comm t3]
  exact (add_le_add_iff_left _ _ _).symm

end OrderedValue

/-- The answers to the twelve basic comparisons of three values: `pkl` is `x_k ≤ x_l`, `qk` is
`x_k ≤` (sum of the other two), `rk` is (sum of the other two) `≤ x_k`. -/
structure Pat where
  (p12 p21 p13 p31 p23 p32 q1 r1 q2 r2 q3 r3 : Bool)
  deriving DecidableEq

/-- `b` records the basic comparisons of `x₁, x₂, x₃`. -/
structure Realizes {V : Type} [OrderedValue V] (x1 x2 x3 : V) (b : Pat) : Prop where
  p12 : b.p12 = true ↔ x1 ≤ x2
  p21 : b.p21 = true ↔ x2 ≤ x1
  p13 : b.p13 = true ↔ x1 ≤ x3
  p31 : b.p31 = true ↔ x3 ≤ x1
  p23 : b.p23 = true ↔ x2 ≤ x3
  p32 : b.p32 = true ↔ x3 ≤ x2
  q1 : b.q1 = true ↔ x1 ≤ x2 + x3
  r1 : b.r1 = true ↔ x2 + x3 ≤ x1
  q2 : b.q2 = true ↔ x2 ≤ x1 + x3
  r2 : b.r2 = true ↔ x1 + x3 ≤ x2
  q3 : b.q3 = true ↔ x3 ≤ x1 + x2
  r3 : b.r3 = true ↔ x1 + x2 ≤ x3

namespace Pat

/-- The answer to "`S ≤ T`" for disjoint sets of slots `S = {k : s_k}` and `T = {k : t_k}`. -/
def le (b : Pat) : Bool → Bool → Bool → Bool → Bool → Bool → Bool
  | false, false, false, _, _, _ => true
  | _, _, _, false, false, false => false
  | true, false, false, false, true, false => b.p12
  | true, false, false, false, false, true => b.p13
  | false, true, false, true, false, false => b.p21
  | false, true, false, false, false, true => b.p23
  | false, false, true, true, false, false => b.p31
  | false, false, true, false, true, false => b.p32
  | true, false, false, false, true, true => b.q1
  | false, true, true, true, false, false => b.r1
  | false, true, false, true, false, true => b.q2
  | true, false, true, false, true, false => b.r2
  | false, false, true, true, true, false => b.q3
  | true, true, false, false, false, true => b.r3
  | _, _, _, _, _, _ => false

/-- The constraints every pattern of positive values satisfies: totality, transitivity, and
`x_k ≤ x_l → x_k < x_l + x_m`. -/
def ok (b : Pat) : Bool :=
  [b.p12 || b.p21, b.p13 || b.p31, b.p23 || b.p32,
   !(b.p12 && b.p23) || b.p13, !(b.p13 && b.p32) || b.p12, !(b.p21 && b.p13) || b.p23,
   !(b.p23 && b.p31) || b.p21, !(b.p31 && b.p12) || b.p32, !(b.p32 && b.p21) || b.p31,
   b.q1 || b.r1, b.q2 || b.r2, b.q3 || b.r3,
   !b.p12 || b.q1, !b.p13 || b.q1, !b.p21 || b.q2, !b.p23 || b.q2, !b.p31 || b.q3, !b.p32 || b.q3,
   !b.p12 || !b.r1, !b.p13 || !b.r1, !b.p21 || !b.r2, !b.p23 || !b.r2, !b.p31 || !b.r3,
   !b.p32 || !b.r3].all id

/-- The pattern of a natural-number triple. -/
def ofNat (a b c : Nat) : Pat :=
  ⟨decide (a ≤ b), decide (b ≤ a), decide (a ≤ c), decide (c ≤ a), decide (b ≤ c), decide (c ≤ b),
   decide (a ≤ b + c), decide (b + c ≤ a), decide (b ≤ a + c), decide (a + c ≤ b),
   decide (c ≤ a + b), decide (a + b ≤ c)⟩

open Classical in
/-- The pattern of a triple of values. -/
noncomputable def of {V : Type} [OrderedValue V] (x1 x2 x3 : V) : Pat :=
  ⟨decide (x1 ≤ x2), decide (x2 ≤ x1), decide (x1 ≤ x3), decide (x3 ≤ x1), decide (x2 ≤ x3),
   decide (x3 ≤ x2), decide (x1 ≤ x2 + x3), decide (x2 + x3 ≤ x1), decide (x2 ≤ x1 + x3),
   decide (x1 + x3 ≤ x2), decide (x3 ≤ x1 + x2), decide (x1 + x2 ≤ x3)⟩

open Classical in
theorem realizes_of {V : Type} [OrderedValue V] (x1 x2 x3 : V) : Realizes x1 x2 x3 (of x1 x2 x3) := by
  constructor <;> exact decide_eq_true_iff

theorem realizes_ofNat (a b c : Nat) : Realizes a b c (ofNat a b c) := by
  constructor <;> exact decide_eq_true_iff

end Pat

namespace OrderedValue
variable {V : Type} [OrderedValue V]

/-- **Every subset comparison is decided by the pattern.** For positive `x₁, x₂, x₃`, the comparison
of two subsets of slots is the pattern's answer for their differences. -/
theorem tri_le_iff {x1 x2 x3 : V} {b : Pat} (hR : Realizes x1 x2 x3 b)
    (h1 : ¬ x1 ≤ 0) (h2 : ¬ x2 ≤ 0) (h3 : ¬ x3 ≤ 0) (s1 s2 s3 t1 t2 t3 : Bool) :
    tri s1 s2 s3 x1 x2 x3 ≤ tri t1 t2 t3 x1 x2 x3 ↔
      b.le (s1 && !t1) (s2 && !t2) (s3 && !t3) (t1 && !s1) (t2 && !s2) (t3 && !s3) = true := by
  have n1 := nonneg_of_pos h1
  have n2 := nonneg_of_pos h2
  have n3 := nonneg_of_pos h3
  have n12 := add_nonneg n1 n2
  have n13 := add_nonneg n1 n3
  have n23 := add_nonneg n2 n3
  have n123 := add_nonneg n1 n23
  have h12 := add_pos h1 n2
  have h13 := add_pos h1 n3
  have h23 := add_pos h2 n3
  have h123 := add_pos h1 n23
  rw [tri_cancel]
  cases s1 <;> cases s2 <;> cases s3 <;> cases t1 <;> cases t2 <;> cases t3 <;>
    simp [tri, Pat.le, zero_add, add_zero, le_refl, hR.p12, hR.p21, hR.p13, hR.p31, hR.p23, hR.p32,
      hR.q1, hR.r1, hR.q2, hR.r2, hR.q3, hR.r3, h1, h2, h3, h12, h13, h23, h123,
      n1, n2, n3, n12, n13, n23, n123]

end OrderedValue

/-! ## The table: every pattern of positive values is realized by a natural-number triple -/

namespace Pat

/-- The 31 permutations of the representatives of proofs/real_values.md: (4,3,2), (3,2,1), (5,2,1),
(2,2,1), (3,2,2), (2,1,1), (3,1,1), (1,1,1). -/
def reps : List (Nat × Nat × Nat) :=
  [(4, 3, 2), (4, 2, 3), (3, 4, 2), (3, 2, 4), (2, 4, 3), (2, 3, 4), (3, 2, 1), (3, 1, 2),
   (2, 3, 1), (2, 1, 3), (1, 3, 2), (1, 2, 3), (5, 2, 1), (5, 1, 2), (2, 5, 1), (2, 1, 5),
   (1, 5, 2), (1, 2, 5), (2, 2, 1), (2, 1, 2), (1, 2, 2), (3, 2, 2), (2, 3, 2), (2, 2, 3),
   (2, 1, 1), (1, 2, 1), (1, 1, 2), (3, 1, 1), (1, 3, 1), (1, 1, 3), (1, 1, 1)]

/-- `p` holds for both Booleans. -/
def allB (p : Bool → Bool) : Bool := p true && p false

theorem allB_spec {p : Bool → Bool} (h : allB p = true) (a : Bool) : p a = true := by
  simp only [allB, Bool.and_eq_true] at h; cases a
  · exact h.2
  · exact h.1

/-- `p` holds for all 4096 patterns. -/
def all (p : Pat → Bool) : Bool :=
  allB fun a1 => allB fun a2 => allB fun a3 => allB fun a4 => allB fun a5 => allB fun a6 =>
  allB fun a7 => allB fun a8 => allB fun a9 => allB fun a10 => allB fun a11 => allB fun a12 =>
    p ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩

theorem all_spec {p : Pat → Bool} (h : all p = true) (b : Pat) : p b = true := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := b
  exact allB_spec (allB_spec (allB_spec (allB_spec (allB_spec (allB_spec (allB_spec (allB_spec
    (allB_spec (allB_spec (allB_spec (allB_spec h a1) a2) a3) a4) a5) a6) a7) a8) a9) a10) a11) a12

/-- **The table** (a finite check): every pattern satisfying `ok` is the pattern of a triple in
`reps`, and the triples in `reps` are positive. -/
theorem table :
    all (fun b => !b.ok || reps.any (fun A => decide (ofNat A.1 A.2.1 A.2.2 = b))) = true ∧
      reps.all (fun A => decide (0 < A.1 ∧ 0 < A.2.1 ∧ 0 < A.2.2)) = true := by
  constructor <;> decide +kernel

theorem cl_or {b1 b2 : Bool} {P Q : Prop} (h1 : b1 = true ↔ P) (h2 : b2 = true ↔ Q) (h : P ∨ Q) :
    (b1 || b2) = true := by
  rcases h with h | h
  · simp [h1.mpr h]
  · simp [h2.mpr h]

theorem cl_imp {b1 b2 : Bool} {P Q : Prop} (h1 : b1 = true ↔ P) (h2 : b2 = true ↔ Q) (h : P → Q) :
    (!b1 || b2) = true := by
  cases hb : b1
  · rfl
  · simp [h2.mpr (h (h1.mp hb))]

theorem cl_trans {b1 b2 b3 : Bool} {P Q R : Prop} (h1 : b1 = true ↔ P) (h2 : b2 = true ↔ Q)
    (h3 : b3 = true ↔ R) (h : P → Q → R) : (!(b1 && b2) || b3) = true := by
  cases hb1 : b1 <;> cases hb2 : b2 <;> simp
  exact h3.mpr (h (h1.mp hb1) (h2.mp hb2))

theorem cl_nand {b1 b2 : Bool} {P Q : Prop} (h1 : b1 = true ↔ P) (h2 : b2 = true ↔ Q)
    (h : P → ¬ Q) : (!b1 || !b2) = true := by
  cases hb1 : b1 <;> cases hb2 : b2 <;> simp
  exact h (h1.mp hb1) (h2.mp hb2)

/-- The pattern of positive values satisfies the constraints `ok`. -/
theorem ok_of_realizes {V : Type} [OrderedValue V] {x1 x2 x3 : V} {b : Pat}
    (hR : Realizes x1 x2 x3 b) (h1 : ¬ x1 ≤ 0) (h2 : ¬ x2 ≤ 0) (h3 : ¬ x3 ≤ 0) : b.ok = true := by
  have n1 := OrderedValue.nonneg_of_pos h1
  have n2 := OrderedValue.nonneg_of_pos h2
  have n3 := OrderedValue.nonneg_of_pos h3
  have tr := fun {a b c : V} => OrderedValue.le_trans a b c
  have tot := fun a b : V => OrderedValue.le_total a b
  simp only [ok, List.all_cons, List.all_nil, id, Bool.and_true, Bool.and_eq_true]
  exact ⟨cl_or hR.p12 hR.p21 (tot _ _), cl_or hR.p13 hR.p31 (tot _ _), cl_or hR.p23 hR.p32 (tot _ _),
    cl_trans hR.p12 hR.p23 hR.p13 tr, cl_trans hR.p13 hR.p32 hR.p12 tr,
    cl_trans hR.p21 hR.p13 hR.p23 tr, cl_trans hR.p23 hR.p31 hR.p21 tr,
    cl_trans hR.p31 hR.p12 hR.p32 tr, cl_trans hR.p32 hR.p21 hR.p31 tr,
    cl_or hR.q1 hR.r1 (tot _ _), cl_or hR.q2 hR.r2 (tot _ _), cl_or hR.q3 hR.r3 (tot _ _),
    cl_imp hR.p12 hR.q1 fun h => tr h (OrderedValue.le_add_right n3),
    cl_imp hR.p13 hR.q1 fun h => tr h (OrderedValue.le_add_left n2),
    cl_imp hR.p21 hR.q2 fun h => tr h (OrderedValue.le_add_right n3),
    cl_imp hR.p23 hR.q2 fun h => tr h (OrderedValue.le_add_left n1),
    cl_imp hR.p31 hR.q3 fun h => tr h (OrderedValue.le_add_right n2),
    cl_imp hR.p32 hR.q3 fun h => tr h (OrderedValue.le_add_left n1),
    cl_nand hR.p12 hR.r1 fun h hr => OrderedValue.not_add_le_left h3 (tr hr h),
    cl_nand hR.p13 hR.r1 fun h hr => OrderedValue.not_add_le_right h2 (tr hr h),
    cl_nand hR.p21 hR.r2 fun h hr => OrderedValue.not_add_le_left h3 (tr hr h),
    cl_nand hR.p23 hR.r2 fun h hr => OrderedValue.not_add_le_right h1 (tr hr h),
    cl_nand hR.p31 hR.r3 fun h hr => OrderedValue.not_add_le_left h2 (tr hr h),
    cl_nand hR.p32 hR.r3 fun h hr => OrderedValue.not_add_le_right h1 (tr hr h)⟩

end Pat

namespace OrderedValue
variable {V : Type} [OrderedValue V]

/-- **Three positive values have a natural-number representative**: positive `A₁, A₂, A₃` with the
same answer to every comparison between two subsets of slots. -/
theorem tri_rep {x1 x2 x3 : V} (h1 : ¬ x1 ≤ 0) (h2 : ¬ x2 ≤ 0) (h3 : ¬ x3 ≤ 0) :
    ∃ A1 A2 A3 : Nat, 0 < A1 ∧ 0 < A2 ∧ 0 < A3 ∧ ∀ s1 s2 s3 t1 t2 t3 : Bool,
      (tri s1 s2 s3 x1 x2 x3 ≤ tri t1 t2 t3 x1 x2 x3 ↔
        tri s1 s2 s3 A1 A2 A3 ≤ tri t1 t2 t3 A1 A2 A3) := by
  have hR := Pat.realizes_of x1 x2 x3
  have hok := Pat.ok_of_realizes hR h1 h2 h3
  have hany := Pat.all_spec Pat.table.1 (Pat.of x1 x2 x3)
  rw [hok, Bool.not_true, Bool.false_or, List.any_eq_true] at hany
  obtain ⟨⟨A1, A2, A3⟩, hmem, hA⟩ := hany
  have hpos := of_decide_eq_true (List.all_eq_true.mp Pat.table.2 _ hmem)
  have hRA : Realizes A1 A2 A3 (Pat.of x1 x2 x3) := of_decide_eq_true hA ▸ Pat.realizes_ofNat A1 A2 A3
  refine ⟨A1, A2, A3, hpos.1, hpos.2.1, hpos.2.2, fun s1 s2 s3 t1 t2 t3 => ?_⟩
  rw [tri_le_iff hR h1 h2 h3, tri_le_iff hRA (Nat.not_le.mpr hpos.1) (Nat.not_le.mpr hpos.2.1)
    (Nat.not_le.mpr hpos.2.2)]

end OrderedValue

/-! ## Per agent: natural-number values with the same subset comparisons -/

/-- `f` (values in `V`) and `w` (natural numbers) give the same answer to every comparison between
two subset sums. -/
def Agree {V : Type} [OrderedValue V] {k : Nat} (f : Fin k → V) (w : Fin k → Nat) : Prop :=
  ∀ (S T : Fin k → Prop) [DecidablePred S] [DecidablePred T],
    (finSumO k (fun g => if S g then f g else 0) ≤ finSumO k (fun g => if T g then f g else 0) ↔
      finSum k (fun g => if S g then w g else 0) ≤ finSum k (fun g => if T g then w g else 0))

namespace OrderedValue
variable {V : Type} [OrderedValue V]

/-- If `f` and `w` vanish off a list `L` of goods, and their sums over `L` are three-slot sums
(`sl` gives each set's slots) with the same comparisons, then `f` and `w` agree. -/
theorem agree_of_slots {k : Nat} (f : Fin k → V) (w : Fin k → Nat) (L : List (Fin k))
    (hnd : L.Nodup) (hf : ∀ g, g ∉ L → f g = 0) (hw : ∀ g, g ∉ L → w g = 0)
    (x1 x2 x3 : V) (A1 A2 A3 : Nat)
    (hA : ∀ s1 s2 s3 t1 t2 t3 : Bool, (tri s1 s2 s3 x1 x2 x3 ≤ tri t1 t2 t3 x1 x2 x3 ↔
      tri s1 s2 s3 A1 A2 A3 ≤ tri t1 t2 t3 A1 A2 A3))
    (sl : (Fin k → Bool) → Bool × Bool × Bool)
    (hLf : ∀ S : Fin k → Bool, listSum (L.map fun g => if S g then f g else 0) =
      tri (sl S).1 (sl S).2.1 (sl S).2.2 x1 x2 x3)
    (hLw : ∀ S : Fin k → Bool, listSum (L.map fun g => if S g then w g else 0) =
      tri (sl S).1 (sl S).2.1 (sl S).2.2 A1 A2 A3) : Agree f w := by
  have ef : ∀ (S : Fin k → Prop) [DecidablePred S], finSumO k (fun g => if S g then f g else 0) =
      tri (sl fun g => S g).1 (sl fun g => S g).2.1 (sl fun g => S g).2.2 x1 x2 x3 := fun S _ => by
    rw [finSumO_support k L _ hnd (fun g hg => by simp [hf g hg]), ← hLf]; simp
  have ew : ∀ (S : Fin k → Prop) [DecidablePred S], finSum k (fun g => if S g then w g else 0) =
      tri (sl fun g => S g).1 (sl fun g => S g).2.1 (sl fun g => S g).2.2 A1 A2 A3 := fun S _ => by
    rw [← finSumO_nat, finSumO_support k L _ hnd (fun g hg => by simp [hw g hg]), ← hLw]; simp
  intro S T _ _
  rw [ef S, ef T, ew S, ew T]
  exact hA _ _ _ _ _ _

open Classical in
/-- **L12 for one agent.** Values with at most three relevant goods have natural-number values that
agree with them on every subset comparison. -/
theorem exists_agree {k : Nat} (f : Fin k → V) (hf : ∀ g, 0 ≤ f g)
    (h3 : finSum k (fun g => if ¬ f g ≤ 0 then 1 else 0) ≤ 3) : ∃ w : Fin k → Nat, Agree f w := by
  obtain ⟨L, hnd, hmem, hout, hlen⟩ : ∃ L : List (Fin k), L.Nodup ∧ (∀ g ∈ L, ¬ f g ≤ 0) ∧
      (∀ g, g ∉ L → f g = 0) ∧ L.length ≤ 3 := by
    refine ⟨(List.finRange k).filter (fun g => decide (¬ f g ≤ 0)),
      (List.nodup_finRange k).sublist List.filter_sublist,
      fun g hg => of_decide_eq_true (List.mem_filter.mp hg).2, fun g hg => ?_, ?_⟩
    · refine le_antisymm _ _ (Classical.byContradiction fun hc => hg ?_) (hf g)
      exact List.mem_filter.mpr ⟨List.mem_finRange g, decide_eq_true hc⟩
    · rw [finSum_eq_sum, sum_map_ite (fun g => ¬ f g ≤ 0) (fun _ => 1), sum_map_one] at h3
      exact h3
  rcases L with _ | ⟨g1, _ | ⟨g2, _ | ⟨g3, _ | ⟨g4, L⟩⟩⟩⟩
  · -- no relevant good
    refine ⟨fun _ => 0, fun S T _ _ => ?_⟩
    rw [finSumO_support k [] _ hnd (fun g hg => by simp [hout g hg]),
      finSumO_support k [] _ hnd (fun g hg => by simp [hout g hg])]
    simp [listSum, finSum_eq_sum, le_refl]
  · -- one relevant good
    have h1 := hmem g1 (by simp)
    obtain ⟨A1, A2, A3, -, -, -, hA⟩ := tri_rep h1 h1 h1
    refine ⟨fun g => if g = g1 then A1 else 0, agree_of_slots f _ [g1] hnd hout
      (fun g hg => by simp at hg; simp [hg]) _ _ _ A1 A2 A3 hA (fun S => (S g1, false, false))
      (fun S => by simp [listSum, tri, add_zero]) (fun S => by simp [listSum, tri, add_zero])⟩
  · -- two relevant goods (the third slot is a phantom that no set contains)
    have h21 : g2 ≠ g1 := fun e => by subst e; simp at hnd
    obtain ⟨A1, A2, A3, -, -, -, hA⟩ := tri_rep (hmem g1 (by simp)) (hmem g2 (by simp)) (hmem g1 (by simp))
    refine ⟨fun g => if g = g1 then A1 else if g = g2 then A2 else 0,
      agree_of_slots f _ [g1, g2] hnd hout (fun g hg => by simp at hg; simp [hg]) _ _ _ A1 A2 A3 hA
      (fun S => (S g1, S g2, false)) (fun S => by simp [listSum, tri, add_zero])
      (fun S => by simp [listSum, tri, add_zero, h21])⟩
  · -- three relevant goods
    have h21 : g2 ≠ g1 := fun e => by subst e; simp at hnd
    have h31 : g3 ≠ g1 := fun e => by subst e; simp at hnd
    have h32 : g3 ≠ g2 := fun e => by subst e; simp at hnd
    obtain ⟨A1, A2, A3, -, -, -, hA⟩ :=
      tri_rep (hmem g1 (by simp)) (hmem g2 (by simp)) (hmem g3 (by simp))
    refine ⟨fun g => if g = g1 then A1 else if g = g2 then A2 else if g = g3 then A3 else 0,
      agree_of_slots f _ [g1, g2, g3] hnd hout (fun g hg => by simp at hg; simp [hg]) _ _ _
      A1 A2 A3 hA (fun S => (S g1, S g2, S g3)) (fun S => by simp [listSum, tri, add_zero])
      (fun S => by simp [listSum, tri, add_zero, h21, h31, h32])⟩
  · simp at hlen

end OrderedValue

/-! ## Transfer along `Agree` -/

namespace OrderedValue
variable {V : Type} [OrderedValue V]

theorem finSumO_single' (k : Nat) (f : Fin k → V) (a : Fin k) :
    finSumO k (fun g => if g = a then f g else 0) = f a := by
  rw [show (fun g => if g = a then f g else 0) = fun g => if g = a then f a else 0 from
    funext fun g => by by_cases hg : g = a <;> simp [hg]]
  exact finSumO_single k a (f a)

theorem finSumO_false (k : Nat) (f : Fin k → V) : finSumO k (fun g => if False then f g else 0) = 0 := by
  simp only [ite_false]; exact finSumO_zero k

/-- Relevance is preserved: `v(g) > 0 ↔ w(g) > 0`. -/
theorem relevant_iff_of_agree {k : Nat} {f : Fin k → V} {w : Fin k → Nat} (h : Agree f w)
    (g : Fin k) : ¬ f g ≤ 0 ↔ 0 < w g := by
  have := h (· = g) (fun _ => False)
  rw [finSumO_single', finSumO_false, ← finSumO_nat, ← finSumO_nat, finSumO_single',
    finSumO_false] at this
  rw [this]; exact Nat.not_le

/-- Balance is a subset comparison: `2 v(a) ≤ v(M)` iff `v({a}) ≤ v(M \ {a})`. -/
theorem double_le_iff {k : Nat} (f : Fin k → V) (a : Fin k) :
    f a + f a ≤ finSumO k f ↔ finSumO k (fun g => if g = a then f g else 0) ≤
      finSumO k (fun g => if ¬ g = a then f g else 0) := by
  rw [finSumO_split k f a, finSumO_single']; exact (add_le_add_iff_left _ _ _).symm

/-- Balance is preserved. -/
theorem balanced_iff_of_agree {k : Nat} {f : Fin k → V} {w : Fin k → Nat} (h : Agree f w)
    (a : Fin k) : f a + f a ≤ finSumO k f ↔ 2 * w a ≤ finSum k w := by
  rw [double_le_iff, h, Nat.two_mul, ← finSumO_nat k w, double_le_iff, finSumO_nat, finSumO_nat]

end OrderedValue

open OrderedValue

/-- EFX₀ is preserved: an allocation is EFX₀ for `v` iff it is EFX₀ for `w`. -/
theorem efx0_iff_of_agree {V : Type} [OrderedValue V] (I : OInst V) (w : Fin I.n → Fin I.m → Nat)
    (hw : ∀ i, Agree (I.v i) (w i)) (X : I.Alloc) :
    I.EFX0 X ↔ (⟨I.n, I.m, w⟩ : Inst).EFX0 X := by
  constructor
  · intro h i j hij g hg
    exact (hw i (fun g' => X g' = j ∧ some g ≠ some g') (fun g' => X g' = i ∧ none ≠ some g')).mp
      (h i j hij g hg)
  · intro h i j hij g hg
    exact (hw i (fun g' => X g' = j ∧ some g ≠ some g') (fun g' => X g' = i ∧ none ≠ some g')).mpr
      (h i j hij g hg)

/-- The relevant-goods count is preserved. -/
theorem numRelevant_eq_of_agree {V : Type} [OrderedValue V] (I : OInst V)
    (w : Fin I.n → Fin I.m → Nat) (hw : ∀ i, Agree (I.v i) (w i)) (i : Fin I.n) :
    numRelevant ⟨I.n, I.m, w⟩ i = I.numRelevant i := by
  unfold numRelevant OInst.numRelevant
  congr 1; funext g
  by_cases h : 0 < w i g
  · simp [h, (relevant_iff_of_agree (hw i) g).mpr h]
  · simp [h, show ¬ ¬ I.v i g ≤ 0 from fun h' => h ((relevant_iff_of_agree (hw i) g).mp h')]

/-! ## Main theorems -/

/-- **L12.** If every agent has at most three relevant goods (and nonnegative values), there are
natural-number values `w` with the same relevant goods that agree with `v` on every comparison
between two subset sums. -/
theorem l12 {V : Type} [OrderedValue V] (I : OInst V) (hv : ∀ i g, 0 ≤ I.v i g)
    (h : ∀ i, I.numRelevant i ≤ 3) :
    ∃ w : Fin I.n → Fin I.m → Nat, (∀ i g, 0 < w i g ↔ ¬ I.v i g ≤ 0) ∧ ∀ i, Agree (I.v i) (w i) := by
  have hex := fun i => exists_agree (I.v i) (hv i) (h i)
  refine ⟨fun i => Classical.choose (hex i), fun i g => ?_, fun i => Classical.choose_spec (hex i)⟩
  exact (relevant_iff_of_agree (Classical.choose_spec (hex i)) g).symm

/-- **TARGET over any ordered value type** (Corollary T; `ℝ≥0` by the textbook fact that it
satisfies the axioms of `OrderedValue`). Every additive instance with nonnegative values in which every
agent positively values at most three goods has a complete EFX₀ allocation. -/
theorem target_ordered {V : Type} [OrderedValue V] (I : OInst V) (hn : 0 < I.n)
    (hv : ∀ i g, 0 ≤ I.v i g) (h : ∀ i, I.numRelevant i ≤ 3) : ∃ X : I.Alloc, I.EFX0 X := by
  obtain ⟨w, -, hw⟩ := l12 I hv h
  obtain ⟨X, hX⟩ := target ⟨I.n, I.m, w⟩ hn (fun i => (numRelevant_eq_of_agree I w hw i) ▸ h i)
  exact ⟨X, (efx0_iff_of_agree I w hw X).mpr hX⟩

/-- **Corollary D over any ordered value type.** Every instance with nonnegative values in which every
agent values exactly three goods and is balanced (`2 v_i(g) ≤ v_i(M)`) has an EFX₀ allocation in
which at most one bundle has more than two goods. -/
theorem corollaryD_ordered {V : Type} [OrderedValue V] (I : OInst V) (hn : 0 < I.n)
    (hv : ∀ i g, 0 ≤ I.v i g) (h3 : ∀ i, I.numRelevant i = 3)
    (hbal : ∀ i g, I.v i g + I.v i g ≤ finSumO I.m (I.v i)) :
    ∃ X : I.Alloc, I.EFX0 X ∧ ∃ o, ∀ j, j ≠ o → finSum I.m (fun g => if X g = j then 1 else 0) ≤ 2 := by
  obtain ⟨w, -, hw⟩ := l12 I hv (fun i => Nat.le_of_eq (h3 i))
  obtain ⟨X, hX, o, ho⟩ := LB.corollaryD ⟨I.n, I.m, w⟩ hn
    (fun i => (numRelevant_eq_of_agree I w hw i).trans (h3 i))
    (fun i g => (balanced_iff_of_agree (hw i) g).mp (hbal i g))
  exact ⟨X, (efx0_iff_of_agree I w hw X).mpr hX, o, ho⟩

/-! ## Sanity: at `V = Nat` this is `EFX.Model` -/

/-- At `V = Nat`, `OInst.EFX0` is `Inst.EFX0`. -/
theorem efx0_nat_iff (I : Inst) (X : I.Alloc) :
    OInst.EFX0 (⟨I.n, I.m, I.v⟩ : OInst Nat) X ↔ I.EFX0 X := by
  unfold OInst.EFX0 Inst.EFX0 OInst.bundleVal Inst.bundleVal
  simp only [finSumO_nat]

/-- At `V = Nat`, `OInst.numRelevant` is `numRelevant`. -/
theorem numRelevant_nat (I : Inst) (i : Fin I.n) :
    OInst.numRelevant (⟨I.n, I.m, I.v⟩ : OInst Nat) i = numRelevant I i := by
  unfold OInst.numRelevant numRelevant
  congr 1; funext g
  by_cases h : 0 < I.v i g
  · simp [h, Nat.not_le.mpr h]
  · simp [h, show I.v i g ≤ 0 from Nat.le_of_not_lt h]

/-- `target_ordered` at `V = Nat` is `EFX.target` (same statement; see the `example` below). -/
theorem target_of_ordered (I : Inst) (hn : 0 < I.n) (h : ∀ i, numRelevant I i ≤ 3) :
    ∃ X : I.Alloc, I.EFX0 X := by
  obtain ⟨X, hX⟩ := target_ordered (V := Nat) ⟨I.n, I.m, I.v⟩ hn (fun _ _ => Nat.zero_le _)
    (fun i => (numRelevant_nat I i) ▸ h i)
  exact ⟨X, (efx0_nat_iff I X).mp hX⟩

/-- `corollaryD_ordered` at `V = Nat` is `EFX.LB.corollaryD` (same statement). -/
theorem corollaryD_of_ordered (I : Inst) (hn : 0 < I.n) (h3 : ∀ i, numRelevant I i = 3)
    (hbal : ∀ i g, 2 * I.v i g ≤ finSum I.m (I.v i)) :
    ∃ X : I.Alloc, I.EFX0 X ∧ ∃ o, ∀ j, j ≠ o → finSum I.m (fun g => if X g = j then 1 else 0) ≤ 2 := by
  obtain ⟨X, hX, o, ho⟩ := corollaryD_ordered (V := Nat) ⟨I.n, I.m, I.v⟩ hn
    (fun _ _ => Nat.zero_le _) (fun i => (numRelevant_nat I i).trans (h3 i))
    (fun i g => by
      show I.v i g + I.v i g ≤ finSumO I.m (I.v i)
      rw [finSumO_nat]; have := hbal i g; omega)
  exact ⟨X, (efx0_nat_iff I X).mp hX, o, ho⟩

/-- The specializations have exactly the statements of the natural-number theorems. -/
example : @target_of_ordered = @target := rfl
example : @corollaryD_of_ordered = @LB.corollaryD := rfl

end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.OrderedValue.tri_le_iff
#print axioms EFX.OrderedValue.tri_rep
#print axioms EFX.OrderedValue.exists_agree
#print axioms EFX.efx0_iff_of_agree
#print axioms EFX.numRelevant_eq_of_agree
#print axioms EFX.OrderedValue.balanced_iff_of_agree
#print axioms EFX.l12
#print axioms EFX.target_ordered
#print axioms EFX.corollaryD_ordered
#print axioms EFX.target_of_ordered
#print axioms EFX.corollaryD_of_ordered
