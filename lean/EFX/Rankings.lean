import EFX.Bridge

/-!
# Ranking profiles and consistent valuations (`proofs/construction.md` §3)

The rankings of the rank-based states of Draft and Exchange (`EFX/K3DE*.lean`), from the research repository's
construction LB (`EFX.LB`).

A ranking profile `P` (`Profile`) gives each agent `i` three goods `a i`, `b i`, `c i` (`WF`: distinct goods of
the instance). A valuation is consistent with `P` (`Profile.Consistent`) if agent `i` values exactly these three
goods, with `a i ≥ b i ≥ c i > 0` (ties allowed) and `a i ≤ b i + c i` (every core agent has `a i < b i + c i`).
`Profile.rank` is the rank of a good (`3` for a good `i` does not value), `Profile.pickRank` the rank of a pick
(`3` for none), `Profile.Prefers` "ranks above its pick", and `Profile.NA` is the set of goods that some listed agent
outside a set `U` ranks above its pick (all three of its goods if it has no pick).

Also: counting lemmas for short lists (`length_le_one`, `length_le_two`), bundles (`mem_bundle`, `nodup_bundle`,
`bundle_length_le_two`: a bundle has at most two goods if its holder holds only its pair, only its pick, or at
most its slots beyond its pick), and `finSum_bundle_eq` (the model's count of a bundle is a length).
-/

set_option autoImplicit false

namespace EFX
namespace LB

variable {A G : Type}

/-- A ranking profile: agent `i` ranks its three goods `a i`, `b i`, `c i` in this order. -/
structure Profile (A G : Type) where
  a : A → G
  b : A → G
  c : A → G

namespace Profile
variable [DecidableEq G] (P : Profile A G)

/-- The rank of `g` for `i`: `0`, `1`, `2` for `a i`, `b i`, `c i`, and `3` for a good `i` does not
value. -/
def rank (i : A) (g : G) : Nat :=
  if g = P.a i then 0 else if g = P.b i then 1 else if g = P.c i then 2 else 3

/-- An additive valuation consistent with the profile on `agents`: agent `i` values its three distinct
goods `a i ≥ b i ≥ c i > 0` (ties allowed), `a i ≤ b i + c i` (core agents are balanced,
`a i < b i + c i`), and values nothing else. -/
def Consistent (agents : List A) (v : A → G → Nat) : Prop :=
  ∀ i ∈ agents, 0 < v i (P.c i) ∧ v i (P.c i) ≤ v i (P.b i) ∧ v i (P.b i) ≤ v i (P.a i) ∧
    v i (P.a i) ≤ v i (P.b i) + v i (P.c i) ∧ (∀ g, P.rank i g = 3 → v i g = 0) ∧
    P.a i ≠ P.b i ∧ P.a i ≠ P.c i ∧ P.b i ≠ P.c i

variable {P}

theorem value_eq {agents : List A} {v : A → G → Nat} (hv : P.Consistent agents v) {i : A}
    (hi : i ∈ agents) : ∀ {S : List G}, S.Nodup →
    value v i S = (if P.a i ∈ S then v i (P.a i) else 0) + (if P.b i ∈ S then v i (P.b i) else 0) +
      (if P.c i ∈ S then v i (P.c i) else 0)
  | [], _ => by simp
  | g :: S, h => by
    have ih := value_eq hv hi (List.nodup_cons.mp h).2
    have hg := (List.nodup_cons.mp h).1
    obtain ⟨h1, h2, h3, h4, h0, hab, hac, hbc⟩ := hv i hi
    rw [value_cons, ih]
    unfold rank at h0
    by_cases ha : g = P.a i <;> by_cases hb : g = P.b i <;> by_cases hc : g = P.c i <;>
      simp_all <;> grind

/-- The rank of `i`'s pick, `3` if it has none. -/
def pickRank (P : Profile A G) (Y : A → Option G) (i : A) : Nat :=
  match Y i with
  | none => 3
  | some y => P.rank i y

/-- `i` ranks `g` above its pick `Y i`; every good `i` values if it has no pick. -/
def Prefers (P : Profile A G) (Y : A → Option G) (i : A) (g : G) : Prop :=
  P.rank i g < P.pickRank Y i

instance (P : Profile A G) (Y : A → Option G) (i : A) (g : G) : Decidable (P.Prefers Y i g) :=
  inferInstanceAs (Decidable (_ < _))

/-- `NA`: the goods that some listed agent outside `U` (not upgraded) ranks above its pick. -/
def NA (P : Profile A G) (agents : List A) (U : A → Prop) (Y : A → Option G) (g : G) : Prop :=
  ∃ i ∈ agents, ¬ U i ∧ P.Prefers Y i g

theorem rank_le {agents : List A} {v : A → G → Nat} (hv : P.Consistent agents v) {i : A}
    (hi : i ∈ agents) {g h : G} (hgh : P.rank i g ≤ P.rank i h) : v i h ≤ v i g := by
  obtain ⟨h1, h2, h3, h4, h0, hab, hac, hbc⟩ := hv i hi
  have e3 : P.rank i g = 3 → v i g = 0 := h0 g
  have f3 : P.rank i h = 3 → v i h = 0 := h0 h
  unfold rank at hgh e3 f3
  by_cases ha : g = P.a i <;> by_cases hb : g = P.b i <;> by_cases hc : g = P.c i <;>
    by_cases ha' : h = P.a i <;> by_cases hb' : h = P.b i <;> by_cases hc' : h = P.c i <;>
    simp_all <;> omega

theorem rank_a (i : A) : P.rank i (P.a i) = 0 := by simp [rank]

theorem rank_b {agents : List A} {v : A → G → Nat} (hv : P.Consistent agents v) {i : A}
    (hi : i ∈ agents) : P.rank i (P.b i) = 1 := by
  obtain ⟨-, -, -, -, -, hab, -, -⟩ := hv i hi
  simp [rank, Ne.symm hab]

theorem rank_c {agents : List A} {v : A → G → Nat} (hv : P.Consistent agents v) {i : A}
    (hi : i ∈ agents) : P.rank i (P.c i) = 2 := by
  obtain ⟨-, -, -, -, -, -, hac, hbc⟩ := hv i hi
  simp [rank, Ne.symm hac, Ne.symm hbc]

end Profile

open Profile

/-! ## Counting lemmas -/

theorem length_le_one {S : List G} (hS : S.Nodup) {y : G} (h : ∀ g ∈ S, g = y) : S.length ≤ 1 := by
  match S, hS, h with
  | [], _, _ => simp
  | [_], _, _ => simp
  | g :: g' :: t, hS, h =>
    have e1 := h g (by simp)
    have e2 := h g' (by simp)
    subst e1
    exact absurd (by simp [e2]) (List.nodup_cons.mp hS).1

theorem length_filter_add (S : List G) (p : G → Bool) :
    S.length = (S.filter p).length + (S.filter (fun g => !p g)).length := by
  induction S with
  | nil => simp
  | cons g S ih => by_cases hp : p g = true <;> simp [hp, ih] <;> omega

theorem length_le_two [DecidableEq G] {S : List G} (hS : S.Nodup) {x y : G}
    (h : ∀ g ∈ S, g = x ∨ g = y) : S.length ≤ 2 := by
  rw [length_filter_add S (fun g => decide (g = x))]
  have h1 := length_le_one (hS.sublist List.filter_sublist) (y := x) (S := S.filter (fun g => decide (g = x)))
    (fun g hg => by simpa using (List.mem_filter.mp hg).2)
  have h2 := length_le_one (hS.sublist List.filter_sublist) (y := y)
    (S := S.filter (fun g => !decide (g = x)))
    (fun g hg => by
      have ⟨hgS, hgx⟩ := List.mem_filter.mp hg
      simp at hgx
      exact (h g hgS).resolve_left hgx)
  omega

/-! ## Well-formed profiles and ranks -/

section
variable [DecidableEq G]

/-- The profile is well formed on `agents` and `goods`: each agent's three goods are distinct goods of
`goods`. -/
def WF (P : Profile A G) (agents : List A) (goods : List G) : Prop :=
  ∀ i ∈ agents, P.a i ∈ goods ∧ P.b i ∈ goods ∧ P.c i ∈ goods ∧
    P.a i ≠ P.b i ∧ P.a i ≠ P.c i ∧ P.b i ≠ P.c i

theorem mem_of_rank_lt {P : Profile A G} {i : A} {g : G} (h : P.rank i g < 3) :
    g = P.a i ∨ g = P.b i ∨ g = P.c i := by
  unfold Profile.rank at h
  by_cases ha : g = P.a i <;> by_cases hb : g = P.b i <;> by_cases hc : g = P.c i <;> simp_all

end

/-! ## Bundles -/

variable [DecidableEq A]

theorem mem_bundle {goods : List G} {X : G → A} {j : A} {g : G} :
    g ∈ bundle goods X j ↔ g ∈ goods ∧ X g = j := by
  simp [bundle]

theorem nodup_bundle {goods : List G} (hg : goods.Nodup) (X : G → A) (j : A) :
    (bundle goods X j).Nodup :=
  hg.sublist List.filter_sublist

variable [DecidableEq G]

/-! ## Lists of three goods, goods of rank 3, restricted values -/

omit [DecidableEq A] [DecidableEq G] in
theorem eq_of_length_three : ∀ {l : List G}, l.length = 3 → ∃ x y z, l = [x, y, z]
  | [x, y, z], _ => ⟨x, y, z, rfl⟩
  | [], h | [_], h | [_, _], h | _ :: _ :: _ :: _ :: _, h => by simp at h

omit [DecidableEq A] in
theorem ne_of_rank_three {P : Profile A G} {i : A} {g : G} (h : P.rank i g = 3) :
    g ≠ P.a i ∧ g ≠ P.b i ∧ g ≠ P.c i := by
  unfold Profile.rank at h
  split at h
  · omega
  rename_i ha
  split at h
  · omega
  rename_i hb
  split at h
  · omega
  rename_i hc
  exact ⟨ha, hb, hc⟩

omit [DecidableEq A] in
/-- Values of lists of goods do not see the values of goods outside `goods`. -/
theorem value_restrict (v : A → G → Nat) (goods : List G) (i : A) :
    ∀ {S : List G}, (∀ g ∈ S, g ∈ goods) →
      value (fun j g => if g ∈ goods then v j g else 0) i S = value v i S
  | [], _ => rfl
  | g :: S, h => by
    simp only [value_cons, h g (by simp), ↓reduceIte]
    rw [value_restrict v goods i (fun x hx => h x (by simp [hx]))]

/-! ## Bundles of at most two goods -/

variable {P : Profile A G} {agents : List A} {goods : List G} {X : G → A} {Y : A → Option G}
  {U : A → Prop} {o : A}

/-- A bundle has at most two goods if its holder, when upgraded, holds only its `b` and `c`; when
frozen, only its pick; and otherwise at most its slots beyond its pick. -/
theorem bundle_length_le_two (hg : goods.Nodup) {j : A}
    (hup : U j → ∀ g ∈ goods, X g = j → g = P.b j ∨ g = P.c j)
    (hfz : ¬ U j → ∀ y, Y j = some y → P.NA agents U Y y → ∀ g ∈ goods, X g = j → g = y)
    (hsl : ¬ U j → (∀ y, Y j = some y → ¬ P.NA agents U Y y) →
      ((bundle goods X j).filter (fun g => Y j ≠ some g)).length ≤ (if Y j = none then 2 else 1)) :
    (bundle goods X j).length ≤ 2 := by
  have hnd := nodup_bundle hg X j
  by_cases hU : U j
  · exact EFX.LB.length_le_two hnd
      (fun g hg' => hup hU g (mem_bundle.mp hg').1 (mem_bundle.mp hg').2)
  by_cases hfz' : ∃ y, Y j = some y ∧ P.NA agents U Y y
  · obtain ⟨y, hy, hna⟩ := hfz'
    have := length_le_one hnd (y := y)
      (fun g hg' => hfz hU y hy hna g (mem_bundle.mp hg').1 (mem_bundle.mp hg').2)
    omega
  have hsl := hsl hU (fun y hy hna => hfz' ⟨y, hy, hna⟩)
  rw [length_filter_add (bundle goods X j) (fun g => decide (Y j ≠ some g))]
  cases hY : Y j with
  | none =>
    rw [hY] at hsl
    have h0 : (bundle goods X j).filter (fun g => !decide ((none : Option G) ≠ some g)) = [] := by
      rw [List.filter_eq_nil_iff]; intro g _; simp
    have h2 : (if (none : Option G) = none then 2 else 1) = 2 := by simp
    rw [h0]; simp only [List.length_nil]; omega
  | some y =>
    rw [hY] at hsl
    have h1 := length_le_one (hnd.sublist List.filter_sublist) (y := y)
      (S := (bundle goods X j).filter (fun g => !decide (some y ≠ some g)))
      (fun g hg' => by
        have := (List.mem_filter.mp hg').2
        simp at this
        exact this.symm)
    have h2 : (if some y = none then 2 else 1) = 1 := by simp
    omega

/-- The number of goods in `j`'s bundle, as a length. -/
theorem finSum_bundle_eq (m n : Nat) (X : Fin m → Fin n) (j : Fin n) :
    finSum m (fun g => if X g = j then 1 else 0) = (bundle (List.finRange m) X j).length := by
  rw [finSum_eq_sum, sum_map_ite (fun g => X g = j) (fun _ => 1), sum_map_one]
  rfl

end LB
end EFX
