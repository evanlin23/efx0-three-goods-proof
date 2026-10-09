import EFX.Lists

/-!
# Peeling (LEDGER L2): rule R1, and peeling a bundle

**Rule R1** (`EFX.peel`). Remove agent `i` together with one good `p`. If the remaining agents have an EFX₀
allocation of the remaining goods, and `i` values `p` at least as much as all remaining goods together
(`v i p ≥ v i (M \ {p})`: at most one other relevant good remains, or `i` is top-heavy), then giving `p` to `i`
keeps the allocation EFX₀.

Proof: every other bundle is part of `M \ {p}`, so `i` envies nobody; `i`'s bundle is the single
good `p`, which nobody can envy in the EFX₀ sense; bundles among the others are unchanged.

**Peeling a bundle** (`EFX.peelBundle`). Remove agent `i` together with a bundle `P` of goods. If the remaining
agents have an EFX₀ allocation of the remaining goods, then giving `P` to `i` keeps the allocation EFX₀, provided

- `i` values `P` at least as much as all remaining goods together, so `i` envies nobody; and
- every other agent values `P` minus any one of its goods at `0` (`P` is a single good, or worthless
  to everyone else), so nobody strongly envies `P`.

This is the proof of L2 in `proofs/lemmas.md`. Its instances: rule R1 when nothing relevant to `i` remains
(`EFX.peelEmpty`: `P = ∅`), and rule R1 itself (`EFX.peel`, proved directly above it: `P` is `i`'s favorite
remaining good). The bundle is given by a test `q : G → Bool`: `P` is `goods.filter q`, and the remaining goods
are `goods.filter (fun g => !q g)`.

**When R1 applies to nobody** (`EFX.not_R1`): an agent to which R1 does not apply has at least three relevant
goods, each worth less than half of all remaining goods together.
-/

set_option autoImplicit false

namespace EFX

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Rule R1 -/

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

/-! ## Peeling a bundle -/

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

/-! ## When rule R1 applies to nobody -/

namespace EFX

variable {A G : Type} [DecidableEq A] [DecidableEq G]

section lemmas
variable (v : A → G → Nat)


omit [DecidableEq A] in
/-- If R1 does not apply to `i` (no remaining good is worth at least all the others), then `i` has at
least three relevant goods and each good is worth less than half of all goods together. -/
theorem not_R1 {i : A} {goods : List G} (hne : goods ≠ [])
    (h : ¬ ∃ p ∈ goods, value v i (goods.erase p) ≤ v i p) :
    3 ≤ (relevant v i goods).length ∧ ∀ g ∈ goods, 2 * v i g < value v i goods := by
  have hlt : ∀ g ∈ goods, 2 * v i g < value v i goods := by
    intro g hg
    have := value_erase v (i := i) hg
    have : ¬ value v i (goods.erase g) ≤ v i g := fun h' => h ⟨g, hg, h'⟩
    omega
  refine ⟨Nat.lt_of_not_le fun hle => h ?_, hlt⟩
  cases hfav : favorite (v i) goods with
  | none => exact absurd ((favorite_eq_none_iff _).mp hfav) hne
  | some p =>
    obtain ⟨hp, hmax⟩ := favorite_spec _ hfav
    refine ⟨p, hp, value_le_of_countP_le_one v i (v i p) (fun g hg => hmax g (List.mem_of_mem_erase hg)) ?_⟩
    rw [relevant, ← List.countP_eq_length_filter] at hle
    by_cases hpos : 0 < v i p
    · have := countP_erase_add_one (p := fun g => decide (0 < v i g)) hp (by simp [hpos])
      omega
    · have h0 : goods.countP (fun g => decide (0 < v i g)) = 0 := by
        rw [List.countP_eq_zero]
        intro g hg
        have := hmax g hg
        simp only [decide_eq_true_eq]
        omega
      have := (List.erase_sublist (a := p) (l := goods)).countP_le (p := fun g => decide (0 < v i g))
      omega

end lemmas

end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.peel
#print axioms EFX.peelBundle
#print axioms EFX.peelEmpty
