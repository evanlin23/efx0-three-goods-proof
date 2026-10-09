/-!
# Allocations over explicit lists (working layer)

The model in `EFX.Model` indexes agents and goods by `Fin n` and `Fin m`. Arguments that remove an
agent or a good (peeling, induction on the agents) are easier over explicit lists: agents and
goods are arbitrary types with decidable equality, and an instance lists them. `EFX.Bridge` proves
that, over `List.finRange`, the notions here coincide with the model's.
-/

set_option autoImplicit false

namespace EFX

variable {A G : Type}

/-- Agent `i`'s (additive) value for a list of goods. -/
def value (v : A → G → Nat) (i : A) (S : List G) : Nat := (S.map (v i)).sum

/-- The bundle of agent `j` under `X`: the goods of `goods` that `X` gives to `j`. -/
def bundle [DecidableEq A] (goods : List G) (X : G → A) (j : A) : List G :=
  goods.filter (fun g => X g = j)

/-- `X` allocates `goods` to `agents`: every good goes to a listed agent. -/
def IsAllocation (agents : List A) (goods : List G) (X : G → A) : Prop :=
  ∀ g ∈ goods, X g ∈ agents

/-- EFX₀ over lists: for listed agents `i ≠ j` and every good `g` in `j`'s bundle, `i` values its own
bundle at least as much as `j`'s bundle without `g`. -/
def EFX0L [DecidableEq A] [DecidableEq G] (v : A → G → Nat) (agents : List A) (goods : List G)
    (X : G → A) : Prop :=
  ∀ i ∈ agents, ∀ j ∈ agents, i ≠ j → ∀ g ∈ bundle goods X j,
    value v i ((bundle goods X j).erase g) ≤ value v i (bundle goods X i)

/-- The goods of `goods` that agent `i` values positively. -/
def relevant (v : A → G → Nat) (i : A) (goods : List G) : List G :=
  goods.filter (fun g => 0 < v i g)

section values
variable (v : A → G → Nat)

@[simp] theorem value_nil (i : A) : value v i [] = 0 := rfl

@[simp] theorem value_cons (i : A) (g : G) (S : List G) :
    value v i (g :: S) = v i g + value v i S := by
  simp [value]

/-- Values are monotone along sublists. -/
theorem value_sublist (i : A) {S T : List G} (h : S.Sublist T) : value v i S ≤ value v i T := by
  induction h with
  | slnil => simp
  | cons g _ ih => rw [value_cons]; omega
  | cons_cons g _ ih => rw [value_cons, value_cons]; omega

theorem le_value_of_mem (i : A) {g : G} {S : List G} (h : g ∈ S) : v i g ≤ value v i S := by
  induction S with
  | nil => simp at h
  | cons a S ih =>
    rw [value_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

/-- A list none of whose goods agent `i` values positively is worth `0` to `i`. -/
theorem value_eq_zero_of_countP_eq_zero (i : A) {S : List G}
    (h : S.countP (fun g => 0 < v i g) = 0) : value v i S = 0 := by
  induction S with
  | nil => simp
  | cons g S ih =>
    rw [List.countP_cons] at h
    have h1 : S.countP (fun g => 0 < v i g) = 0 := by omega
    have h2 : ¬ (0 < v i g) := by intro hg; simp [hg] at h
    rw [value_cons, ih h1]
    omega

/-- A list with at most one good that `i` values positively, every good worth at most `c` to `i`,
is worth at most `c` to `i`. -/
theorem value_le_of_countP_le_one (i : A) (c : Nat) {S : List G}
    (hle : ∀ g ∈ S, v i g ≤ c) (hcount : S.countP (fun g => 0 < v i g) ≤ 1) :
    value v i S ≤ c := by
  induction S with
  | nil => simp
  | cons g S ih =>
    rw [value_cons]
    rw [List.countP_cons] at hcount
    by_cases hg : 0 < v i g
    · have e : (if decide (0 < v i g) = true then 1 else 0) = 1 := by simp [hg]
      have h0 : S.countP (fun g => 0 < v i g) = 0 := by rw [e] at hcount; omega
      rw [value_eq_zero_of_countP_eq_zero v i h0]
      have := hle g (by simp); omega
    · have e : (if decide (0 < v i g) = true then 1 else 0) = 0 := by simp [hg]
      have h1 : S.countP (fun g => 0 < v i g) ≤ 1 := by rw [e] at hcount; omega
      have := ih (fun x hx => hle x (by simp [hx])) h1
      omega

end values

/-- Erasing a member that satisfies `p` lowers `countP p` by exactly one. -/
theorem countP_erase_add_one [DecidableEq G] {p : G → Bool} {a : G} :
    ∀ {l : List G}, a ∈ l → p a = true → (l.erase a).countP p + 1 = l.countP p
  | [], ha, _ => by simp at ha
  | b :: l, ha, hp => by
    by_cases hab : b = a
    · subst hab; simp [hp]
    · have ha' : a ∈ l := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h.symm hab
        · exact h
      have ih := countP_erase_add_one ha' hp
      have hba : (b == a) = false := by simp [hab]
      simp only [List.erase_cons, hba, Bool.false_eq_true, ↓reduceIte, List.countP_cons]
      omega

/-! ## A favorite good -/

/-- The first good of `S` with the largest value under `f`; `none` iff `S = []`. -/
def favorite (f : G → Nat) : List G → Option G
  | [] => none
  | g :: S =>
    match favorite f S with
    | none => some g
    | some h => if f h ≤ f g then some g else some h

theorem favorite_eq_none_iff (f : G → Nat) {S : List G} : favorite f S = none ↔ S = [] := by
  cases S with
  | nil => simp [favorite]
  | cons g S =>
    simp only [favorite, reduceCtorEq, iff_false]
    split
    · simp
    · split <;> simp

theorem favorite_spec (f : G → Nat) :
    ∀ {S : List G} {p : G}, favorite f S = some p → p ∈ S ∧ ∀ g ∈ S, f g ≤ f p
  | [], p, h => by simp [favorite] at h
  | g :: S, p, h => by
    simp only [favorite] at h
    split at h
    · rename_i hnone
      have hS : S = [] := (favorite_eq_none_iff f).mp hnone
      subst hS
      simp at h; subst h
      simp
    · rename_i q hq
      have ⟨hqS, hqmax⟩ := favorite_spec f hq
      split at h
      · simp at h; subst h
        refine ⟨by simp, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.le_refl _
        · have := hqmax x hx; omega
      · simp at h; subst h
        refine ⟨by simp [hqS], ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · exact hqmax x hx

end EFX
