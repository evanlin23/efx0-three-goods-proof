import EFX.Peeling
import EFX.PreAlloc
import EFX.Timed

/-!
# Rule R1 as a search, rankings from values, and their counted versions

Parts of algorithm K3ALG (the research repository's earlier, longer algorithm for the same theorem,
`proofs/k3_algorithm.md`) that Draft and Exchange reuses (`EFX/K3DEAlgo.lean`, `EFX/K3DECost*.lean`):

- `r1Step`, `findR1`: rule R1 for one agent (`some none`: it values no remaining good and leaves with nothing,
  `EFX.peelEmpty`; `some (some p)`: its favourite `p` is worth at least all other remaining goods together and
  it leaves with `p`, `EFX.peel`; `none`: R1 does not apply), and the first agent of a list to which it applies;
  `findR1_some`, `findR1_none`, `r1Step_none_zero`, `r1Step_some`, `r1Step_eq_none`.
- `sort3`, `profileOf`: an agent's ranking, computed by sorting its three relevant goods by value;
  `sort3_ranking`: for an agent with exactly three relevant goods, balanced, it is a ranking consistent with the
  values.
- Counted versions in the cost monad `EFX.Timed` (units as in `EFX.K3DECost`), with value lemmas (`fooC_val`:
  `fooC` computes `foo`) and cost lemmas: `rankC`, `pickRankC`, `prefersC` (`Profile.rank`, `Profile.pickRank`,
  `Profile.Prefers`), `favoriteC`, `valueC` (`favorite`, `value`), `sort3C`, and `finRangeC` (`List.finRange k`,
  one unit per element).
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
/-! ## Properties -/

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

end proofs

end K3
end EFX

/-! ## Counted versions -/

namespace EFX
namespace K3

open Timed LB

section
variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- `P.rank i g`: three table reads (`a i`, `b i`, `c i`) and at most three comparisons. -/
def rankC (P : Profile A G) (i : A) (g : G) : Timed Nat := do
  tick 6
  pure (P.rank i g)

/-- `P.pickRank Y i`: one table read (`Y i`) and a rank. -/
def pickRankC (P : Profile A G) (Y : A → Option G) (i : A) : Timed Nat := do
  tick 1
  match Y i with
  | none => pure 3
  | some y => rankC P i y

/-- `P.Prefers Y i g`: two ranks and one comparison. -/
def prefersC (P : Profile A G) (Y : A → Option G) (i : A) (g : G) : Timed Bool := do
  let r ← rankC P i g
  let q ← pickRankC P Y i
  tick 1
  pure (decide (r < q))

omit [DecidableEq A] in
@[simp] theorem rankC_val (P : Profile A G) (i : A) (g : G) : (rankC P i g).val = P.rank i g := rfl

omit [DecidableEq A] in
@[simp] theorem pickRankC_val (P : Profile A G) (Y : A → Option G) (i : A) :
    (pickRankC P Y i).val = P.pickRank Y i := by
  unfold pickRankC Profile.pickRank
  cases Y i <;> rfl

omit [DecidableEq A] in
@[simp] theorem prefersC_val (P : Profile A G) (Y : A → Option G) (i : A) (g : G) :
    (prefersC P Y i g).val = decide (P.Prefers Y i g) := by
  simp only [prefersC, bind_val, rankC_val, pickRankC_val, pure_val]
  rfl

end

section generic
variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- `favorite f S` with `f` a counted function (a value read): one comparison per good. -/
def favoriteC (f : G → Timed Nat) : List G → Timed (Option G)
  | [] => pure none
  | g :: S => do
    let r ← favoriteC f S
    match r with
    | none => do tick 1; pure (some g)
    | some h => do
      let fh ← f h
      let fg ← f g
      tick 1
      pure (if fh ≤ fg then some g else some h)

/-- `value v i S`: one value read per good (and one addition, counted by `sumMapC`). -/
def valueC (v : A → G → Nat) (i : A) (S : List G) : Timed Nat :=
  sumMapC (fun g => do tick 1; pure (v i g)) S

omit [DecidableEq G] in
@[simp] theorem favoriteC_val (f : G → Timed Nat) : ∀ S : List G,
    (favoriteC f S).val = favorite (fun g => (f g).val) S
  | [] => rfl
  | g :: S => by
    unfold favoriteC favorite
    simp only [bind_val, favoriteC_val f S]
    cases favorite (fun g => (f g).val) S with
    | none => rfl
    | some h => simp only [bind_val, pure_val]

omit [DecidableEq A] [DecidableEq G] in
@[simp] theorem valueC_val (v : A → G → Nat) (i : A) (S : List G) : (valueC v i S).val = value v i S := by
  simp [valueC, value]

end generic

section fin
variable {n m : Nat}

/-- `sort3` of a list: at most four list cells inspected, three value reads, three comparisons. -/
def sort3C (f : Fin m → Nat) (g0 : Fin m) (l : List (Fin m)) : Timed (Fin m × Fin m × Fin m) := do
  tick 10
  pure (sort3 f g0 l)

/-- `List.finRange k`, one unit per element. -/
def finRangeC (k : Nat) : Timed (List (Fin k)) := do
  tick k
  pure (List.finRange k)

end fin

section generic
variable {A G : Type} [DecidableEq A] [DecidableEq G] {N : Nat}

omit [DecidableEq A] in
theorem rankC_cost (P : Profile A G) (i : A) (g : G) : (rankC P i g).cost = 6 := rfl

omit [DecidableEq A] in
theorem pickRankC_cost (P : Profile A G) (Y : A → Option G) (i : A) : (pickRankC P Y i).cost ≤ 7 := by
  unfold pickRankC; cases Y i <;> simp [rankC]

omit [DecidableEq A] in
theorem prefersC_cost (P : Profile A G) (Y : A → Option G) (i : A) (g : G) : (prefersC P Y i g).cost ≤ 14 := by
  have := pickRankC_cost P Y i
  simp only [prefersC, bind_cost, rankC_cost, tick_cost, pure_cost]
  omega

end generic

end K3
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.K3.sort3_ranking
