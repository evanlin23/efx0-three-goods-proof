/-!
# Allocations over explicit lists (working layer)

The model in `EFX.Model` indexes agents and goods by `Fin n` and `Fin m`. Arguments that remove an
agent or a good (peeling, induction on the agents) are easier over explicit lists: agents and
goods are arbitrary types with decidable equality, and an instance lists them. `EFX.Bridge` proves
that, over `List.finRange`, the notions here coincide with the model's.

Also: lemmas on values of lists, `favorite` (the first good of largest value), and list lemmas used by the other
files (pigeonhole `length_le_of_nodup_of_subset`, iterates `iter`, `sum_map_le`, `sum_map_lt`, `value_erase`,
`efx0L_congr`, `mem_cons_erase`, `relevant_sublist`).
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

/-! ## Pigeonhole, iterates of a map, sums -/

/-- Pigeonhole: a duplicate-free list inside `m` is no longer than `m`. -/
theorem length_le_of_nodup_of_subset [DecidableEq A] :
    ∀ {l m : List A}, l.Nodup → (∀ x ∈ l, x ∈ m) → l.length ≤ m.length
  | [], _, _, _ => Nat.zero_le _
  | x :: l, m, hnd, hsub => by
    have hx : x ∈ m := hsub x (by simp)
    have hxl : x ∉ l := (List.nodup_cons.mp hnd).1
    have ih := length_le_of_nodup_of_subset (m := m.erase x) (List.nodup_cons.mp hnd).2 (by
      intro y hy
      have hyx : y ≠ x := fun h => hxl (h ▸ hy)
      exact (List.mem_erase_of_ne hyx).mpr (hsub y (by simp [hy])))
    rw [List.length_erase_of_mem hx] at ih
    have := List.length_pos_of_mem hx
    simp only [List.length_cons]
    omega

/-- `iter e k a`: the map `e` applied `k` times to `a`. -/
def iter (e : A → A) : Nat → A → A
  | 0, a => a
  | k + 1, a => e (iter e k a)

theorem iter_add (e : A → A) (a : A) : ∀ j k : Nat, iter e (j + k) a = iter e j (iter e k a)
  | 0, k => by simp [iter]
  | j + 1, k => by rw [Nat.add_right_comm, iter, iter_add e a j k, iter]

theorem iter_mem (e : A → A) {S : List A} (he : ∀ a ∈ S, e a ∈ S) {a : A} (ha : a ∈ S) :
    ∀ k : Nat, iter e k a ∈ S
  | 0 => ha
  | k + 1 => he _ (iter_mem e he ha k)

theorem sum_map_le {l : List A} {f g : A → Nat} (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h a (by simp)
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

theorem sum_map_lt {l : List A} {f g : A → Nat} (h : ∀ a ∈ l, f a ≤ g a)
    (hlt : ∃ a ∈ l, f a < g a) : (l.map f).sum < (l.map g).sum := by
  induction l with
  | nil => obtain ⟨a, ha, _⟩ := hlt; simp at ha
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    obtain ⟨b, hb, hfg⟩ := hlt
    rcases List.mem_cons.mp hb with rfl | hb
    · have := sum_map_le (l := l) (fun x hx => h x (List.mem_cons_of_mem _ hx))
      omega
    · have := h a (by simp)
      have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) ⟨b, hb, hfg⟩
      omega

/-! ## Erasing a good, changing the list of agents -/

section lemmas
variable [DecidableEq A] [DecidableEq G] (v : A → G → Nat)

omit [DecidableEq A] in
theorem value_erase {i : A} {p : G} : ∀ {S : List G}, p ∈ S → value v i S = v i p + value v i (S.erase p)
  | [], h => by simp at h
  | g :: S, h => by
    by_cases hg : g = p
    · subst hg; simp
    · have hp : p ∈ S := (List.mem_cons.mp h).resolve_left (Ne.symm hg)
      have hne : (g == p) = false := by simp [hg]
      simp only [List.erase_cons, hne, Bool.false_eq_true, ↓reduceIte, value_cons]
      rw [value_erase hp]
      omega

theorem efx0L_congr {l l' : List A} {goods : List G} {X : G → A} (h : ∀ x, x ∈ l ↔ x ∈ l')
    (hE : EFX0L v l goods X) : EFX0L v l' goods X :=
  fun i hi j hj hij g hg => hE i ((h i).mpr hi) j ((h j).mpr hj) hij g hg

omit [DecidableEq G] in
theorem mem_cons_erase {agents : List A} {i : A} (hi : i ∈ agents) :
    ∀ x, x ∈ i :: agents.erase i ↔ x ∈ agents := by
  intro x
  constructor
  · intro hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hi
    · exact List.mem_of_mem_erase hx
  · intro hx
    by_cases hxi : x = i
    · simp [hxi]
    · exact List.mem_cons_of_mem _ (List.mem_erase_of_ne hxi |>.mpr hx)

omit [DecidableEq A] [DecidableEq G] in
theorem relevant_sublist {i : A} {S T : List G} (h : S.Sublist T) :
    (relevant v i S).length ≤ (relevant v i T).length :=
  (h.filter _).length_le

end lemmas

end EFX
