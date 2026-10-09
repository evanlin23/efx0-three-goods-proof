import EFX.Lists

/-!
# Peeling, rule R1 (LEDGER L2)

Remove agent `i` together with one good `p`. If the remaining agents have an EFX₀ allocation of
the remaining goods, and `i` values `p` at least as much as all remaining goods together
(`v i p ≥ v i (M \ {p})`: at most one other relevant good remains, or `i` is top-heavy), then
giving `p` to `i` keeps the allocation EFX₀.

Proof: every other bundle is part of `M \ {p}`, so `i` envies nobody; `i`'s bundle is the single
good `p`, which nobody can envy in the EFX₀ sense; bundles among the others are unchanged.
-/

set_option autoImplicit false

namespace EFX

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- Give good `p` to agent `i`, and every other good to whoever `X'` gives it to. -/
def extend (i : A) (p : G) (X' : G → A) : G → A := fun g => if g = p then i else X' g

/-- A duplicate-free list whose elements all equal `p` is empty after erasing any member. -/
theorem erase_eq_nil_of_forall_eq {p g : G} :
    ∀ {S : List G}, S.Nodup → (∀ x ∈ S, x = p) → g ∈ S → S.erase g = []
  | [], _, _, hg => by simp at hg
  | a :: S, hnd, hall, hg => by
    have ha : a = p := hall a (by simp)
    have hS : S = [] := by
      cases S with
      | nil => rfl
      | cons b S' =>
        have hb : b = p := hall b (by simp)
        have := (List.nodup_cons.mp hnd).1
        exact absurd (by simp [ha, hb]) this
    subst hS
    have : g = a := by simpa using hg
    subst this; simp

/-- The other agents keep their bundles. -/
theorem bundle_extend_of_ne {i j : A} {p : G} {X' : G → A} {goods : List G}
    (hnd : goods.Nodup) (hj : j ≠ i) :
    bundle goods (extend i p X') j = bundle (goods.erase p) X' j := by
  unfold bundle extend
  rw [List.Nodup.erase_eq_filter hnd p, List.filter_filter]
  apply List.filter_congr
  intro g _
  by_cases hg : g = p
  · subst hg; simp [Ne.symm hj]
  · simp [hg]

theorem mem_bundle_extend_self {i : A} {p : G} {X' : G → A} {goods : List G} (hp : p ∈ goods) :
    p ∈ bundle goods (extend i p X') i := by
  simp [bundle, extend, hp]

/-- Agent `i`'s bundle holds nothing but `p`. -/
theorem eq_of_mem_bundle_extend_self {i : A} {rest : List A} {p : G} {X' : G → A}
    {goods : List G} (hi : i ∉ rest) (hX' : IsAllocation rest (goods.erase p) X') :
    ∀ g ∈ bundle goods (extend i p X') i, g = p := by
  intro g hg
  have hg' := List.mem_filter.mp hg
  have hXg : extend i p X' g = i := of_decide_eq_true hg'.2
  by_cases hgp : g = p
  · exact hgp
  · have h1 : extend i p X' g = X' g := by simp [extend, hgp]
    have := hX' g ((List.mem_erase_of_ne hgp).mpr hg'.1)
    rw [← h1, hXg] at this
    exact absurd this hi

/-- **Peeling rule R1.** -/
theorem peel (v : A → G → Nat) {i : A} {rest : List A} {goods : List G} {p : G} {X' : G → A}
    (hi : i ∉ rest) (hp : p ∈ goods) (hnd : goods.Nodup)
    (hX' : IsAllocation rest (goods.erase p) X') (hE : EFX0L v rest (goods.erase p) X')
    (htop : value v i (goods.erase p) ≤ v i p) :
    IsAllocation (i :: rest) goods (extend i p X') ∧ EFX0L v (i :: rest) goods (extend i p X') := by
  constructor
  · intro g hg
    by_cases hgp : g = p
    · simp [extend, hgp]
    · have h1 : extend i p X' g = X' g := by simp [extend, hgp]
      rw [h1]
      exact List.mem_cons_of_mem _ (hX' g ((List.mem_erase_of_ne hgp).mpr hg))
  · intro a ha b hb hab g hg
    rcases List.mem_cons.mp ha with hai | ha' <;> rcases List.mem_cons.mp hb with hbi | hb'
    · exact absurd (hai.trans hbi.symm) hab
    · -- `i` looks at another agent's bundle: all of it lies in `goods \ {p}`
      subst hai
      have hba : b ≠ a := fun h => hi (h ▸ hb')
      rw [bundle_extend_of_ne hnd hba] at hg ⊢
      calc value v a ((bundle (goods.erase p) X' b).erase g)
          _ ≤ value v a (bundle (goods.erase p) X' b) := value_sublist v a List.erase_sublist
          _ ≤ value v a (goods.erase p) := value_sublist v a List.filter_sublist
          _ ≤ v a p := htop
          _ ≤ value v a (bundle goods (extend a p X') a) := le_value_of_mem v a (mem_bundle_extend_self hp)
    · -- another agent looks at `i`'s bundle `{p}`: removing its good leaves nothing
      subst hbi
      have hbnd : (bundle goods (extend b p X') b).Nodup := hnd.sublist List.filter_sublist
      rw [erase_eq_nil_of_forall_eq hbnd (eq_of_mem_bundle_extend_self hi hX') hg, value_nil]
      exact Nat.zero_le _
    · -- two other agents: both bundles are unchanged
      have hai : a ≠ i := fun h => hi (h ▸ ha')
      have hbi : b ≠ i := fun h => hi (h ▸ hb')
      rw [bundle_extend_of_ne hnd hai, bundle_extend_of_ne hnd hbi] at *
      exact hE a ha' b hb' hab g hg

end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.peel
