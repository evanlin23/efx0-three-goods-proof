import EFX.Peeling

/-!
# Peeling a bundle; rule R2 (LEDGER L2)

Remove agent `i` together with a bundle `P` of goods. If the remaining agents have an EFX₀ allocation
of the remaining goods, then giving `P` to `i` keeps the allocation EFX₀, provided

- `i` values `P` at least as much as all remaining goods together, so `i` envies nobody; and
- every other agent values `P` minus any one of its goods at `0` (`P` is a single good, or worthless
  to everyone else), so nobody strongly envies `P`.

This is the proof of L2 in `proofs/lemmas.md` (`EFX.peelBundle`). Its instances:

- rule R2 (`EFX.peelR2`): `P` is the set of goods relevant to `i` and to no other remaining agent,
  and `v_i(P) ≥ v_i(R_i \ P)`. The written rule also asks `|P| ≥ 2`; the proof does not use it.
- rule R1 when nothing relevant to `i` remains (`EFX.peelEmpty`): `P = ∅`.
- rule R1 itself is `EFX.peel` (`P` is `i`'s favorite remaining good), proved in `EFX.Peeling`.

The bundle is given by a test `q : G → Bool`: `P` is `goods.filter q`, and the remaining goods are
`goods.filter (fun g => !q g)`.
-/

set_option autoImplicit false

namespace EFX

variable {A G : Type}

section values
variable (v : A → G → Nat)

/-- A list of goods each worth `0` to `i` is worth `0` to `i`. -/
theorem value_eq_zero_of_forall (i : A) {S : List G} (h : ∀ g ∈ S, v i g = 0) : value v i S = 0 := by
  induction S with
  | nil => simp
  | cons g S ih =>
    rw [value_cons, h g (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- Goods that `i` does not value do not count: `v_i(R_i ∩ S) = v_i(S)`. -/
theorem value_relevant (i : A) (S : List G) : value v i (relevant v i S) = value v i S := by
  induction S with
  | nil => simp [relevant]
  | cons g S ih =>
    by_cases hg : 0 < v i g
    · simp only [relevant, List.filter_cons, hg, decide_true, ↓reduceIte, value_cons] at ih ⊢
      rw [ih]
    · simp only [relevant, List.filter_cons, hg, decide_false, Bool.false_eq_true, ↓reduceIte,
        value_cons] at ih ⊢
      rw [ih]; omega

end values

variable [DecidableEq A] [DecidableEq G]

/-- Give agent `i` the goods passing the test `q`, and every other good to whoever `X'` gives it to. -/
def extendBy (i : A) (q : G → Bool) (X' : G → A) : G → A := fun g => if q g then i else X' g

omit [DecidableEq G] in
/-- The other agents keep their bundles. -/
theorem bundle_extendBy_of_ne {i j : A} {q : G → Bool} {X' : G → A} {goods : List G} (hj : j ≠ i) :
    bundle goods (extendBy i q X') j = bundle (goods.filter (fun g => !q g)) X' j := by
  unfold bundle extendBy
  rw [List.filter_filter]
  apply List.filter_congr
  intro g _
  by_cases hg : q g = true
  · simp [hg, Ne.symm hj]
  · simp [hg]

omit [DecidableEq G] in
/-- Agent `i`'s bundle is exactly `P`, the goods passing `q`. -/
theorem bundle_extendBy_self {i : A} {rest : List A} {q : G → Bool} {X' : G → A} {goods : List G}
    (hi : i ∉ rest) (hX' : IsAllocation rest (goods.filter (fun g => !q g)) X') :
    bundle goods (extendBy i q X') i = goods.filter q := by
  unfold bundle extendBy
  apply List.filter_congr
  intro g hg
  by_cases hq : q g = true
  · simp [hq]
  · have hmem : X' g ∈ rest := hX' g (List.mem_filter.mpr ⟨hg, by simp [hq]⟩)
    have hne : X' g ≠ i := fun h => hi (h ▸ hmem)
    simp [hq, hne]

/-- **Peeling a bundle** (the proof of L2). Agent `i` takes `P = goods.filter q`; the agents `rest`
have an EFX₀ allocation `X'` of the remaining goods. If `i` values `P` at least as much as all
remaining goods together, and every other agent values `P` minus any one of its goods at `0`, then
the combined allocation is an EFX₀ allocation of `goods` to `i :: rest`. -/
theorem peelBundle (v : A → G → Nat) {i : A} {rest : List A} {goods : List G} {q : G → Bool}
    {X' : G → A} (hi : i ∉ rest)
    (hX' : IsAllocation rest (goods.filter (fun g => !q g)) X')
    (hE : EFX0L v rest (goods.filter (fun g => !q g)) X')
    (hown : value v i (goods.filter (fun g => !q g)) ≤ value v i (goods.filter q))
    (hothers : ∀ j ∈ rest, ∀ g ∈ goods.filter q, value v j ((goods.filter q).erase g) = 0) :
    IsAllocation (i :: rest) goods (extendBy i q X') ∧
      EFX0L v (i :: rest) goods (extendBy i q X') := by
  constructor
  · intro g hg
    by_cases hq : q g = true
    · simp [extendBy, hq]
    · have h1 : extendBy i q X' g = X' g := by simp [extendBy, hq]
      rw [h1]
      exact List.mem_cons_of_mem _ (hX' g (List.mem_filter.mpr ⟨hg, by simp [hq]⟩))
  · intro a ha b hb hab g hg
    rcases List.mem_cons.mp ha with hai | ha' <;> rcases List.mem_cons.mp hb with hbi | hb'
    · exact absurd (hai.trans hbi.symm) hab
    · -- `i` looks at another agent's bundle: all of it lies among the remaining goods
      subst hai
      have hba : b ≠ a := fun h => hi (h ▸ hb')
      rw [bundle_extendBy_of_ne hba] at hg ⊢
      rw [bundle_extendBy_self hi hX']
      calc value v a ((bundle (goods.filter (fun g => !q g)) X' b).erase g)
          _ ≤ value v a (bundle (goods.filter (fun g => !q g)) X' b) :=
            value_sublist v a List.erase_sublist
          _ ≤ value v a (goods.filter (fun g => !q g)) := value_sublist v a List.filter_sublist
          _ ≤ value v a (goods.filter q) := hown
    · -- another agent looks at `P`: without any one of its goods it is worth nothing to them
      subst hbi
      rw [bundle_extendBy_self hi hX'] at hg ⊢
      rw [hothers a ha' g hg]
      exact Nat.zero_le _
    · -- two other agents: both bundles are unchanged
      have hai : a ≠ i := fun h => hi (h ▸ ha')
      have hbi : b ≠ i := fun h => hi (h ▸ hb')
      rw [bundle_extendBy_of_ne hai, bundle_extendBy_of_ne hbi] at *
      exact hE a ha' b hb' hab g hg

/-- Rule R2's test: the good `g` is relevant to `i` and to no agent of `rest`. -/
def isPrivate (v : A → G → Nat) (i : A) (rest : List A) (g : G) : Bool :=
  decide (0 < v i g) && rest.all (fun j => v j g == 0)

/-- **Peeling rule R2.** Agent `i` takes `P`, the goods relevant to it and to no other remaining
agent; the other agents `rest` have an EFX₀ allocation `X'` of the remaining goods. If
`v_i(P) ≥ v_i(R_i \ P)`, where `R_i \ P` is the set of remaining goods relevant to `i`, then the
combined allocation is an EFX₀ allocation of `goods` to `i :: rest`.

The written rule also asks `|P| ≥ 2`; this statement drops that hypothesis. -/
theorem peelR2 (v : A → G → Nat) {i : A} {rest : List A} {goods : List G} {X' : G → A}
    (hi : i ∉ rest)
    (hX' : IsAllocation rest (goods.filter (fun g => !isPrivate v i rest g)) X')
    (hE : EFX0L v rest (goods.filter (fun g => !isPrivate v i rest g)) X')
    (hbal : value v i (relevant v i (goods.filter (fun g => !isPrivate v i rest g))) ≤
      value v i (goods.filter (isPrivate v i rest))) :
    IsAllocation (i :: rest) goods (extendBy i (isPrivate v i rest) X') ∧
      EFX0L v (i :: rest) goods (extendBy i (isPrivate v i rest) X') := by
  refine peelBundle v hi hX' hE (by rwa [value_relevant] at hbal) ?_
  -- every good of `P` is worthless to every other agent
  intro j hj g _
  apply value_eq_zero_of_forall
  intro x hx
  have hxP := (List.mem_filter.mp (List.mem_of_mem_erase hx)).2
  simp only [isPrivate, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hxP
  exact hxP.2 j hj

/-- **Peeling rule R1 with `P = ∅`.** If no remaining good is relevant to agent `i`, then `i` can
leave with nothing: an EFX₀ allocation `X'` of all remaining goods to the other agents is still
EFX₀ with `i` added. -/
theorem peelEmpty (v : A → G → Nat) {i : A} {rest : List A} {goods : List G} {X' : G → A}
    (hi : i ∉ rest) (hX' : IsAllocation rest goods X') (hE : EFX0L v rest goods X')
    (hzero : ∀ g ∈ goods, v i g = 0) :
    IsAllocation (i :: rest) goods X' ∧ EFX0L v (i :: rest) goods X' := by
  have hext : extendBy i (fun _ => false) X' = X' := by funext g; simp [extendBy]
  have hall : goods.filter (fun _ => !false) = goods := by simp
  have hnone : goods.filter (fun _ => false) = [] := by simp
  rw [← hext]
  refine peelBundle v (q := fun _ => false) hi (by rwa [hall]) (by rwa [hall]) ?_ ?_
  · rw [hall, hnone, value_nil, value_eq_zero_of_forall v i hzero]
    exact Nat.le_refl 0
  · intro j _ g hg
    rw [hnone] at hg
    simp at hg

end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.peelBundle
#print axioms EFX.peelR2
#print axioms EFX.peelEmpty
