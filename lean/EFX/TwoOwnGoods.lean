import EFX.Bridge

/-!
# Two own goods (LEDGER L8)

An agent `i` with at most three relevant goods, none worth more than the other two together
(`a ≤ b + c`; core agents are balanced, `a < b + c`), that holds at least two of them envies nobody,
so it is safe (EFX₀ toward every other bundle) whatever the rest of the allocation is.

Proof: every other bundle is disjoint from `i`'s, so it contains at most one good relevant to `i`,
say `x`. If `i` holds all its relevant goods, other bundles are worth `0` to it. Otherwise `i` holds
the relevant goods other than `x`, and balance gives `v_i(x) ≤ v_i(R_i \ {x}) = v_i(X_i)`.

The balance hypothesis is stated as `2 v_i(g) ≤ v_i(M)` for every good `g`, which for three relevant
goods `a ≥ b ≥ c` says exactly `a ≤ b + c`. It is needed: a top-heavy agent (`a > b + c`) holding
`{b, c}` strongly envies a bundle made of `a` and a good worthless to it (`EFX.balance_needed`).

- `EFX.envyFree_of_two_own`, `EFX.safe_of_two_own`: over lists.
- `EFX.Inst.safe_of_two_own`: in the model's terms.
- `EFX.Inst.efx0_of_two_own`: an allocation in which every agent holds two of its (at most three,
  balanced) relevant goods is EFX₀. This is how L8 solves the β = 1 cores; that such an allocation
  exists for them (orient the cycle) is not formalized.
-/

set_option autoImplicit false

namespace EFX

variable {A G : Type}

section values
variable (v : A → G → Nat)

/-- Splitting a list by a test splits its value. -/
theorem value_filter_add (i : A) (p : G → Bool) (S : List G) :
    value v i (S.filter p) + value v i (S.filter (fun g => !p g)) = value v i S := by
  induction S with
  | nil => simp
  | cons g S ih =>
    by_cases hp : p g = true
    · simp only [List.filter_cons, hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte, value_cons]
      omega
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
        value_cons]
      omega

end values

variable [DecidableEq A]

/-- **L8** (envy-freeness form). Agent `i` has at most three relevant goods, each worth at most
the other goods together, and holds at least two of them. Then `i` envies nobody. -/
theorem envyFree_of_two_own (v : A → G → Nat) {i : A} {goods : List G} {X : G → A}
    (h3 : (relevant v i goods).length ≤ 3)
    (hbal : ∀ g ∈ goods, 2 * v i g ≤ value v i goods)
    (h2 : 2 ≤ (relevant v i (bundle goods X i)).length) :
    ∀ j, j ≠ i → value v i (bundle goods X j) ≤ value v i (bundle goods X i) := by
  intro j hji
  -- `T`: the goods `i` does not hold
  let T := goods.filter (fun g => !decide (X g = i))
  have hsplit : value v i (bundle goods X i) + value v i T = value v i goods :=
    value_filter_add v i _ goods
  -- at most one good of `T` is relevant to `i`
  have hcount : T.countP (fun g => decide (0 < v i g)) ≤ 1 := by
    have e := List.countP_eq_countP_filter_add goods (fun g => decide (0 < v i g))
      (fun g => decide (X g = i))
    rw [relevant, ← List.countP_eq_length_filter] at h3
    rw [relevant, bundle, ← List.countP_eq_length_filter] at h2
    have : T.countP (fun g => decide (0 < v i g)) =
        (goods.filter (fun g => !decide (X g = i))).countP (fun g => decide (0 < v i g)) := rfl
    omega
  -- `j`'s bundle lies inside `T`
  have hjT : value v i (bundle goods X j) ≤ value v i T := by
    apply value_sublist
    have : bundle goods X j = T.filter (fun g => decide (X g = j)) := by
      unfold bundle
      show _ = (goods.filter _).filter _
      rw [List.filter_filter]
      apply List.filter_congr
      intro g _
      by_cases h : X g = j
      · simp [h, hji]
      · simp [h]
    rw [this]
    exact List.filter_sublist
  -- `T` is worth at most its best good `x`, and balance bounds `x` by `i`'s bundle
  have hT : value v i T ≤ value v i (bundle goods X i) := by
    cases hfav : favorite (v i) T with
    | none =>
      rw [(favorite_eq_none_iff _).mp hfav, value_nil]
      exact Nat.zero_le _
    | some x =>
      obtain ⟨hxT, hmax⟩ := favorite_spec _ hfav
      have hTx : value v i T ≤ v i x := value_le_of_countP_le_one v i (v i x) hmax hcount
      have := hbal x (List.mem_filter.mp hxT).1
      omega
  omega

/-- **L8.** Under the same hypotheses, agent `i` is safe: EFX₀ holds for `i` toward every other
bundle. -/
theorem safe_of_two_own [DecidableEq G] (v : A → G → Nat) {i : A} {goods : List G} {X : G → A}
    (h3 : (relevant v i goods).length ≤ 3)
    (hbal : ∀ g ∈ goods, 2 * v i g ≤ value v i goods)
    (h2 : 2 ≤ (relevant v i (bundle goods X i)).length) :
    ∀ j, j ≠ i → ∀ g ∈ bundle goods X j,
      value v i ((bundle goods X j).erase g) ≤ value v i (bundle goods X i) := by
  intro j hji g _
  exact Nat.le_trans (value_sublist v i List.erase_sublist) (envyFree_of_two_own v h3 hbal h2 j hji)

/-! ## In the model's terms -/

namespace Inst
variable (I : Inst)

/-- The number of relevant goods an agent holds, as a length. -/
theorem finSum_held_eq (X : I.Alloc) (i : Fin I.n) :
    finSum I.m (fun g => if X g = i ∧ 0 < I.v i g then 1 else 0) =
      (relevant I.v i (bundle (List.finRange I.m) X i)).length := by
  rw [finSum_eq_sum, sum_map_ite (fun g => X g = i ∧ 0 < I.v i g) (fun _ => 1), sum_map_one]
  unfold relevant bundle
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro g _
  by_cases h1 : X g = i <;> by_cases h2 : 0 < I.v i g <;> simp [h1, h2]

/-- **L8** in the model's terms. Agent `i` has at most three relevant goods, none worth more than
all its other goods together, and holds at least two of them. Then `i` envies nobody, so the EFX₀
condition holds for `i` toward every other agent, whatever the rest of `X` is. -/
theorem safe_of_two_own (X : I.Alloc) (i : Fin I.n) (h3 : numRelevant I i ≤ 3)
    (hbal : ∀ g, 2 * I.v i g ≤ finSum I.m (I.v i))
    (h2 : 2 ≤ finSum I.m (fun g => if X g = i ∧ 0 < I.v i g then 1 else 0)) :
    (∀ j, j ≠ i → I.bundleVal X i j none ≤ I.bundleVal X i i none) ∧
      (∀ j, j ≠ i → ∀ g, X g = j → I.bundleVal X i j (some g) ≤ I.bundleVal X i i none) := by
  have hv : finSum I.m (I.v i) = value I.v i (List.finRange I.m) := finSum_eq_sum _ _
  have hef := envyFree_of_two_own I.v (i := i) (goods := List.finRange I.m) (X := X)
    (numRelevant_eq I i ▸ h3) (fun g _ => hv ▸ hbal g) (finSum_held_eq I X i ▸ h2)
  refine ⟨fun j hji => ?_, fun j hji g hg => ?_⟩
  · rw [bundleVal_none, bundleVal_none]
    exact hef j hji
  · rw [bundleVal_some, bundleVal_none]
    exact EFX.safe_of_two_own I.v (numRelevant_eq I i ▸ h3) (fun g _ => hv ▸ hbal g)
      (finSum_held_eq I X i ▸ h2) j hji g (by simp [bundle, hg])

/-- **L8, all agents.** If every agent has at most three relevant goods, none worth more than its
other goods together, and holds at least two of them, the allocation is EFX₀ (indeed envy-free).
This is the argument that solves the β = 1 cores. -/
theorem efx0_of_two_own (X : I.Alloc)
    (h : ∀ i, numRelevant I i ≤ 3 ∧ (∀ g, 2 * I.v i g ≤ finSum I.m (I.v i)) ∧
      2 ≤ finSum I.m (fun g => if X g = i ∧ 0 < I.v i g then 1 else 0)) :
    I.EFX0 X := by
  intro i j hij g hg
  obtain ⟨h3, hbal, h2⟩ := h i
  exact (safe_of_two_own I X i h3 hbal h2).2 j (Ne.symm hij) g hg

end Inst

/-- The balance hypothesis cannot be dropped. Agent `0` values goods `0, 1, 2` at `3, 1, 1`
(top-heavy: `3 > 1 + 1`) and holds goods `1` and `2`; agent `1` holds good `0` together with good `3`,
which agent `0` does not value. Without good `3`, agent `1`'s bundle is worth `3 > 2` to agent `0`. -/
theorem balance_needed : ∃ (I : Inst) (X : I.Alloc) (i : Fin I.n),
    numRelevant I i ≤ 3 ∧ 2 ≤ finSum I.m (fun g => if X g = i ∧ 0 < I.v i g then 1 else 0) ∧
      ¬ I.EFX0 X := by
  refine ⟨⟨2, 4, fun i g => if i.val = 0 then [3, 1, 1, 0].getD g.val 0 else 1⟩,
    fun g => if g.val = 1 ∨ g.val = 2 then ⟨0, by decide⟩ else ⟨1, by decide⟩, ⟨0, by decide⟩,
    by decide, by decide, ?_⟩
  intro h
  have := h ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) ⟨3, by decide⟩ (by decide)
  revert this
  decide

end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.envyFree_of_two_own
#print axioms EFX.safe_of_two_own
#print axioms EFX.Inst.safe_of_two_own
#print axioms EFX.Inst.efx0_of_two_own
#print axioms EFX.balance_needed
