import EFX.K3Extras

/-!
# Draft and Exchange, preliminaries: threats, safety and peeling

The preliminaries of the short proof of the k = 3 result (`paper/k3-simple/long.tex`: the model of §1, §2 "Peeling",
and the threats `θ_i` of Appendix B; Lemmas threats and safety are those of §3.1 "Model, threats and safety" of the
earlier version of the paper, kept here; the soundness proof of §4 now argues the cases of safety inline), over the
list layer of `EFX/Lists.lean` (agents and goods are lists, an allocation is an owner map `X : G → A`, the bundle of
`j` is `bundle goods X j`).

**Definitions.**
- `leastValue`, `threat`: the threat `θ_i(B) = v_i(B) − min_{h ∈ B} v_i(h)` of a list of goods `B` to agent `i`
  (`θ_i(∅) = 0`); `threat_eq_max`: by additivity it is the largest value of `v_i(B ∖ {h})` over `h ∈ B`
  (`threat_le_iff`: `θ_i(B) ≤ x` iff `v_i(B ∖ {h}) ≤ x` for every `h ∈ B`).
- `Safe`: agent `i` is safe in `X` if `v_i(X_i) ≥ θ_i(X_j)` for every listed agent `j ≠ i`.
- `Alone`: a good is alone in `X` if it is the only good of its bundle.
- `rankO`, `Gy`: the rank of `y` (`3` for `⊥`), and `G_y`, the goods that `i` ranks above `y` (`G_⊥ = R_i`,
  `gy_none_iff`).

**Results.**
- `efx0L_iff_safe` (lists), `efx0_iff_safe` (the model's `EFX.Inst.EFX0`): `X` is EFX₀ iff every agent is safe.
- **Lemma threats**: (a) `threat_of_length_le_one`; (b) `threat_le_relevant` (`B ∩ R_i` is `relevant v i B`);
  (c) `threat_pair`, and `threat_of_perm_pair` for any list holding the two goods (`threat_perm`).
- **Lemma safety** for a balanced agent with exactly three relevant goods: (a) `safe_of_pair`; (b) `safe_of_gy`.
- **§2 (Peeling), mapped to existing theorems** (the last section of this file):
  - Lemma peeling is `EFX.peel` (`P = {p}`) and `EFX.peelEmpty` (`P = ∅`), both instances of `EFX.peelBundle`;
    `peeling` states the paper's version, `|P| ≤ 1`, in one theorem.
  - Rule R1 is `EFX.K3.r1Step` (favourite with ties in list order, so by index over `List.finRange`): `some none`
    (leave with nothing, `EFX.K3.r1Step_none_zero`), `some (some p)` (leave with `p`, `EFX.K3.r1Step_some`), or
    `none` (R1 does not apply).
  - Corollary "two relevant goods" is `EFX.Inst.sdRun_efx0` (and `EFX.sdRun_efx0` over lists, `EFX/K3Extras.lean`):
    `EFX.SDRun` is every run of serial dictatorship in any order of the agents, with any favourite at every step,
    nothing once no good is left, the last agent taking all remaining goods. This is the paper's statement; the
    `example`s below check the type. (`EFX.serialDictatorship` and `EFX.exists_efx0_of_count` are only the
    existence form.)
  - Lemma "when nobody can leave" (`lem:R1fail`; "when R1 applies to nobody" in the earlier version) is
    `EFX.not_R1` with `EFX.K3.r1Step_eq_none`. `EFX.not_R1`'s hypothesis is "no good `p` has `v_i(G ∖ {p}) ≤ v_i(p)`" (not rule R1 itself) and its conclusion "at least three relevant
    goods, and `2 v_i(g) < v_i(G)` for every `g`", so `R1fail` states the paper's version: R1 as `EFX.K3.r1Step`,
    at most three relevant goods; conclusion exactly three, and strictly balanced. `r1_of_two` is the paper's
    remark that R1 applies to every agent valuing at most two remaining goods.

**Choices where the prose leaves room.**
1. Sets of goods are lists: a bundle is `bundle goods X j`, a filter of the duplicate-free list `goods`;
   `B ∩ R_i` is `relevant v i B`; the set `{g, h}` is any list that is a permutation of `[g, h]`.
2. Lemma threats (c) is proved for every two goods (for `g = h` the list `[g, g]` is not a set, and the formula
   still holds); the paper assumes `g ≠ h`.
3. Lemma safety: "a balanced agent with `|R_i| = 3`" is an agent of a ranking profile `P` (`EFX.LB.Profile`) with
   `P.Consistent agents v`: it values exactly `a i`, `b i`, `c i`, with `a ≥ b ≥ c > 0` and `a ≤ b + c`. Ties are
   allowed and the ranking may be any ranking consistent with the values (the paper's tie-break by index is one).
   `y : Option G` with `none = ⊥`; "`y ∈ X_i ∩ R_i`" is `y ∈ X_i` and `v_i(y) > 0`; "`i` is safe, unless `E`" is
   `¬ E → Safe`.
4. Safety and EFX₀ are towards the listed agents; the agents need not be distinct.
5. Peeling: `P` is a list of at most one good of `goods`, `M ∖ P` is `goods.filter (· ∉ P)`, and "`Z` together with
   `X_i = P`" is the owner map `fun g => if g ∈ P then i else Z g`.
-/

set_option autoImplicit false

namespace EFX
namespace DE

variable {A G : Type}

/-! ## Threats -/

/-- The least value under `f` of a good of `B`, and `0` if `B` is empty. -/
def leastValue (f : G → Nat) : List G → Nat
  | [] => 0
  | [g] => f g
  | g :: h :: t => min (f g) (leastValue f (h :: t))

theorem leastValue_le (f : G → Nat) : ∀ {B : List G} {g : G}, g ∈ B → leastValue f B ≤ f g
  | [], _, hg => by simp at hg
  | [x], g, hg => by
    rw [List.mem_singleton] at hg; subst hg; exact Nat.le_refl _
  | x :: y :: t, g, hg => by
    show min (f x) (leastValue f (y :: t)) ≤ f g
    rcases List.mem_cons.mp hg with rfl | hg
    · exact Nat.min_le_left _ _
    · exact Nat.le_trans (Nat.min_le_right _ _) (leastValue_le f hg)

theorem exists_leastValue (f : G → Nat) : ∀ {B : List G}, B ≠ [] → ∃ g ∈ B, f g = leastValue f B
  | [], h => absurd rfl h
  | [x], _ => ⟨x, by simp, rfl⟩
  | x :: y :: t, _ => by
    obtain ⟨g, hg, e⟩ := exists_leastValue f (B := y :: t) (by simp)
    show ∃ g ∈ x :: y :: t, f g = min (f x) (leastValue f (y :: t))
    by_cases hle : f x ≤ leastValue f (y :: t)
    · exact ⟨x, by simp, by omega⟩
    · exact ⟨g, List.mem_cons_of_mem _ hg, by omega⟩

/-- **The threat** `θ_i(B)` of the goods `B` to agent `i`: `v_i(B)` minus the least value to `i` of a good of `B`,
and `θ_i(∅) = 0`. -/
def threat (v : A → G → Nat) (i : A) (B : List G) : Nat := value v i B - leastValue (v i) B

section threats
variable (v : A → G → Nat)

@[simp] theorem threat_nil (i : A) : threat v i [] = 0 := rfl

theorem value_of_perm (i : A) {S T : List G} (h : S.Perm T) : value v i S = value v i T := by
  unfold value; exact (h.map (v i)).sum_nat

/-- Values of lists of at most one good are bounded by the values of their goods. -/
theorem value_le_of_length_le_one (i : A) {S : List G} (hS : S.length ≤ 1) {x : Nat}
    (hx : ∀ g ∈ S, v i g ≤ x) : value v i S ≤ x := by
  match S, hS with
  | [], _ => exact Nat.zero_le _
  | [g], _ => rw [value_cons, value_nil]; have := hx g (by simp); omega
  | _ :: _ :: _, h => simp at h

/-- **Lemma threats (a).** A list of at most one good threatens nobody. -/
theorem threat_of_length_le_one (i : A) {B : List G} (hB : B.length ≤ 1) : threat v i B = 0 := by
  match B, hB with
  | [], _ => rfl
  | [g], _ => show value v i [g] - v i g = 0; rw [value_cons, value_nil]; omega
  | _ :: _ :: _, h => simp at h

/-- **Lemma threats (b).** `θ_i(B) ≤ v_i(B ∩ R_i)`. -/
theorem threat_le_relevant (i : A) (B : List G) : threat v i B ≤ value v i (relevant v i B) := by
  rw [value_relevant]; unfold threat; omega

/-- **Lemma threats (c).** `θ_i({g, h}) = max(v_i(g), v_i(h))`. -/
theorem threat_pair (i : A) (g h : G) : threat v i [g, h] = max (v i g) (v i h) := by
  show value v i [g, h] - min (v i g) (v i h) = max (v i g) (v i h)
  rw [value_cons, value_cons, value_nil]; omega

variable [DecidableEq G]

/-- By additivity, `θ_i(B) ≤ x` iff `v_i(B ∖ {h}) ≤ x` for every good `h ∈ B`. -/
theorem threat_le_iff (i : A) (B : List G) (x : Nat) :
    threat v i B ≤ x ↔ ∀ h ∈ B, value v i (B.erase h) ≤ x := by
  unfold threat
  constructor
  · intro hx h hh
    have e := value_erase v (i := i) hh
    have := leastValue_le (v i) hh
    omega
  · intro hx
    by_cases hB : B = []
    · subst hB; exact Nat.zero_le _
    · obtain ⟨h, hh, e⟩ := exists_leastValue (v i) hB
      have e2 := value_erase v (i := i) hh
      have := hx h hh
      omega

/-- `θ_i(B)` is the largest value of `v_i(B ∖ {h})` over `h ∈ B` (the paper's remark after the definition). -/
theorem threat_eq_max (i : A) (B : List G) :
    (∀ h ∈ B, value v i (B.erase h) ≤ threat v i B) ∧
      (B ≠ [] → ∃ h ∈ B, value v i (B.erase h) = threat v i B) := by
  refine ⟨(threat_le_iff v i B _).mp (Nat.le_refl _), fun hB => ?_⟩
  obtain ⟨h, hh, e⟩ := exists_leastValue (v i) hB
  refine ⟨h, hh, ?_⟩
  have e2 := value_erase v (i := i) hh
  unfold threat
  omega

/-- The threat depends only on the goods, not on their order. -/
theorem threat_perm (i : A) {B B' : List G} (hp : B.Perm B') : threat v i B = threat v i B' := by
  have key : ∀ {B B' : List G}, B.Perm B' → threat v i B ≤ threat v i B' := by
    intro B B' hp
    rw [threat_le_iff]
    intro h hh
    rw [value_of_perm v i (hp.erase h)]
    exact (threat_eq_max v i B').1 h (hp.subset hh)
  exact Nat.le_antisymm (key hp) (key hp.symm)

/-- **Lemma threats (c)**, for any list holding exactly the two goods. -/
theorem threat_of_perm_pair (i : A) {B : List G} {g h : G} (hp : B.Perm [g, h]) :
    threat v i B = max (v i g) (v i h) := by
  rw [threat_perm v i hp, threat_pair]

end threats

/-! ## Safety -/

section safety
variable [DecidableEq A] (v : A → G → Nat)

/-- Agent `i` is **safe** in `X`: `v_i(X_i) ≥ θ_i(X_j)` for every listed agent `j ≠ i`. -/
def Safe (agents : List A) (goods : List G) (X : G → A) (i : A) : Prop :=
  ∀ j ∈ agents, j ≠ i → threat v i (bundle goods X j) ≤ value v i (bundle goods X i)

/-- A good `g` is **alone** in `X` if it is the only good of its bundle. -/
def Alone (goods : List G) (X : G → A) (g : G) : Prop := ∀ h ∈ bundle goods X (X g), h = g

theorem alone_iff {goods : List G} {X : G → A} {g : G} :
    Alone goods X g ↔ ∀ h ∈ goods, X h = X g → h = g := by
  simp [Alone, bundle]

variable [DecidableEq G]

/-- **`X` is EFX₀ iff every agent is safe** (over lists). -/
theorem efx0L_iff_safe (agents : List A) (goods : List G) (X : G → A) :
    EFX0L v agents goods X ↔ ∀ i ∈ agents, Safe v agents goods X i := by
  constructor
  · intro h i hi j hj hji
    exact (threat_le_iff v i _ _).mpr (h i hi j hj (Ne.symm hji))
  · intro h i hi j hj hij g hg
    exact (threat_le_iff v i _ _).mp (h i hi j hj (Ne.symm hij)) g hg

end safety

/-- **`X` is EFX₀ iff every agent is safe**, in the model's terms. -/
theorem efx0_iff_safe (I : Inst) (X : I.Alloc) :
    I.EFX0 X ↔ ∀ i, Safe I.v (List.finRange I.n) (List.finRange I.m) X i := by
  rw [Inst.efx0_iff, efx0L_iff_safe]
  exact ⟨fun h i => h i (List.mem_finRange i), fun h i _ => h i⟩

/-! ## Lemma safety -/

section ranks
variable [DecidableEq G]

open LB Profile

/-- The rank of `y` for `i` (`EFX.LB.Profile.rank`), and `3` for `⊥` (`none`). -/
def rankO (P : Profile A G) (i : A) : Option G → Nat
  | none => 3
  | some y => P.rank i y

/-- `G_y`: the goods that `i` ranks above `y`; for `y = ⊥`, all of `R_i` (`gy_none_iff`). -/
def Gy (P : Profile A G) (i : A) (y : Option G) (g : G) : Prop := P.rank i g < rankO P i y

variable {P : Profile A G} {i : A}

theorem rank_le_three (P : Profile A G) (i : A) (g : G) : P.rank i g ≤ 3 := by
  unfold Profile.rank; split <;> (try split) <;> (try split) <;> omega

theorem eq_a_of_rank {g : G} (h : P.rank i g = 0) : g = P.a i := by
  unfold Profile.rank at h
  split at h
  · assumption
  · split at h <;> (try split at h) <;> omega

theorem eq_b_of_rank {g : G} (h : P.rank i g = 1) : g = P.b i := by
  unfold Profile.rank at h
  split at h
  · omega
  · split at h
    · assumption
    · split at h <;> omega

theorem eq_c_of_rank {g : G} (h : P.rank i g = 2) : g = P.c i := by
  unfold Profile.rank at h
  split at h
  · omega
  · split at h
    · omega
    · split at h
      · assumption
      · omega

end ranks

section lemmaSafe
variable [DecidableEq A] [DecidableEq G]

open LB Profile

variable {v : A → G → Nat} {P : Profile A G} {agents : List A} {i : A}

omit [DecidableEq A] in
/-- Under a consistent valuation, the goods of rank below `3` are the relevant goods. -/
theorem rank_lt_three_iff (hv : P.Consistent agents v) (hi : i ∈ agents) {g : G} :
    P.rank i g < 3 ↔ 0 < v i g := by
  obtain ⟨h1, h2, h3, -, h0, -, -, -⟩ := hv i hi
  constructor
  · intro h
    have := rank_le_three P i g
    by_cases e0 : P.rank i g = 0
    · rw [eq_a_of_rank e0]; omega
    · by_cases e1 : P.rank i g = 1
      · rw [eq_b_of_rank e1]; omega
      · rw [eq_c_of_rank (by omega : P.rank i g = 2)]; exact h1
  · intro h
    have := rank_le_three P i g
    refine Nat.lt_of_le_of_ne this fun e => ?_
    rw [h0 g e] at h; exact Nat.lt_irrefl 0 h

omit [DecidableEq A] in
/-- `G_⊥ = R_i`. -/
theorem gy_none_iff (hv : P.Consistent agents v) (hi : i ∈ agents) {g : G} : Gy P i none g ↔ 0 < v i g :=
  rank_lt_three_iff hv hi

/-- **Lemma safety (a).** A balanced agent with three relevant goods that holds `b_i` and `c_i` is safe. -/
theorem safe_of_pair (hv : P.Consistent agents v) (hi : i ∈ agents) {goods : List G} (hgd : goods.Nodup)
    {X : G → A} (hb : P.b i ∈ bundle goods X i) (hc : P.c i ∈ bundle goods X i) :
    Safe v agents goods X i := by
  intro j _ hji
  obtain ⟨-, -, h3, h4, -, -, -, -⟩ := hv i hi
  have hbj : P.b i ∉ bundle goods X j := fun h => hji ((mem_bundle.mp h).2.symm.trans (mem_bundle.mp hb).2)
  have hcj : P.c i ∉ bundle goods X j := fun h => hji ((mem_bundle.mp h).2.symm.trans (mem_bundle.mp hc).2)
  have eB := Profile.value_eq hv hi (nodup_bundle hgd X j)
  have eI := Profile.value_eq hv hi (nodup_bundle hgd X i)
  have hthr : threat v i (bundle goods X j) ≤ value v i (bundle goods X j) := Nat.sub_le _ _
  rw [eB, ite_eq_right hbj, ite_eq_right hcj] at hthr
  rw [eI, ite_eq_left hb, ite_eq_left hc]
  split at hthr <;> split <;> omega

/-- **Lemma safety (b).** Let `i` be a balanced agent with three relevant goods, and `y ∈ X_i ∩ R_i` or `y = ⊥`
(`none`). If no bundle `X_j` with `j ≠ i` and `|X_j| ≥ 2` contains a good of `G_y`, then `i` is safe, unless
`y = a_i` and some bundle `X_j` with `j ≠ i` and `|X_j| ≥ 3` contains both `b_i` and `c_i`. -/
theorem safe_of_gy (hv : P.Consistent agents v) (hi : i ∈ agents) {goods : List G} (hgd : goods.Nodup)
    {X : G → A} (y : Option G) (hy : ∀ g, y = some g → g ∈ bundle goods X i ∧ 0 < v i g)
    (hG : ∀ j ∈ agents, j ≠ i → 2 ≤ (bundle goods X j).length → ∀ g ∈ bundle goods X j, ¬ Gy P i y g)
    (hexc : ¬ (y = some (P.a i) ∧ ∃ j ∈ agents, j ≠ i ∧ 3 ≤ (bundle goods X j).length ∧
      P.b i ∈ bundle goods X j ∧ P.c i ∈ bundle goods X j)) :
    Safe v agents goods X i := by
  intro j hj hji
  obtain ⟨h1, h2, h3, h4, h0, hab, hac, hbc⟩ := hv i hi
  by_cases hlen : (bundle goods X j).length ≤ 1
  · rw [threat_of_length_le_one v i hlen]; exact Nat.zero_le _
  have hnot := hG j hj hji (by omega)
  have eB := Profile.value_eq hv hi (nodup_bundle hgd X j)
  have hthr : threat v i (bundle goods X j) ≤ value v i (bundle goods X j) := Nat.sub_le _ _
  rw [eB] at hthr
  have rb := rank_b hv hi
  have rc := rank_c hv hi
  have ra : P.rank i (P.a i) = 0 := rank_a i
  cases y with
  | none =>
    have ha : P.a i ∉ bundle goods X j := fun h => hnot _ h (by simp [Gy, rankO, ra])
    have hb : P.b i ∉ bundle goods X j := fun h => hnot _ h (by simp [Gy, rankO, rb])
    have hc : P.c i ∉ bundle goods X j := fun h => hnot _ h (by simp [Gy, rankO, rc])
    rw [ite_eq_right ha, ite_eq_right hb, ite_eq_right hc] at hthr
    omega
  | some y0 =>
    obtain ⟨hy0, hpos⟩ := hy y0 rfl
    have hown : v i y0 ≤ value v i (bundle goods X i) := le_value_of_mem v i hy0
    have hy0j : y0 ∉ bundle goods X j := fun h => hji ((mem_bundle.mp h).2.symm.trans (mem_bundle.mp hy0).2)
    have hr3 : P.rank i y0 < 3 := (rank_lt_three_iff hv hi).mpr hpos
    by_cases e0 : P.rank i y0 = 0
    · -- `y = a_i`
      have hya := eq_a_of_rank e0
      subst hya
      have ha : P.a i ∉ bundle goods X j := hy0j
      by_cases hlen3 : 3 ≤ (bundle goods X j).length
      · -- not both `b_i` and `c_i`, by the exception
        have hnb : ¬ (P.b i ∈ bundle goods X j ∧ P.c i ∈ bundle goods X j) :=
          fun hbc' => hexc ⟨rfl, j, hj, hji, hlen3, hbc'.1, hbc'.2⟩
        rw [ite_eq_right ha] at hthr
        by_cases hb : P.b i ∈ bundle goods X j
        · have hc : P.c i ∉ bundle goods X j := fun hc => hnb ⟨hb, hc⟩
          rw [ite_eq_left hb, ite_eq_right hc] at hthr; omega
        · rw [ite_eq_right hb] at hthr; split at hthr <;> omega
      · -- `|X_j| = 2`: removing one good leaves one good, worth at most `v_i(a_i)`
        refine (threat_le_iff v i _ _).mpr fun h hh => ?_
        have hl : ((bundle goods X j).erase h).length ≤ 1 := by
          rw [List.length_erase_of_mem hh]; omega
        refine Nat.le_trans (value_le_of_length_le_one v i hl (x := v i (P.a i)) fun g _ => ?_) hown
        exact Profile.rank_le hv hi (by rw [ra]; exact Nat.zero_le _)
    · by_cases e1 : P.rank i y0 = 1
      · -- `y = b_i`: `a_i` is in `G_y`, so `X_j` holds at most `c_i`
        have hyb := eq_b_of_rank e1
        subst hyb
        have ha : P.a i ∉ bundle goods X j := fun h => hnot _ h (by simp [Gy, rankO, ra, rb])
        rw [ite_eq_right ha, ite_eq_right hy0j] at hthr
        split at hthr <;> omega
      · -- `y = c_i`: `a_i` and `b_i` are in `G_y`
        have hyc := eq_c_of_rank (by omega : P.rank i y0 = 2)
        subst hyc
        have ha : P.a i ∉ bundle goods X j := fun h => hnot _ h (by simp [Gy, rankO, ra, rc])
        have hb : P.b i ∉ bundle goods X j := fun h => hnot _ h (by simp [Gy, rankO, rb, rc])
        rw [ite_eq_right ha, ite_eq_right hb, ite_eq_right hy0j] at hthr
        omega

end lemmaSafe

/-! ## Peeling (§2), mapped to the existing theorems -/

section peeling
variable [DecidableEq A] [DecidableEq G] (v : A → G → Nat)

/-- **Lemma peeling** (the paper's statement; `EFX.peel` is the case `P = {p}`, `EFX.peelEmpty` the case `P = ∅`).
Let `P` be a list of at most one good of `goods` with `v_i(P) ≥ v_i(M ∖ P)`. If the agents `rest` (without `i`) have
an EFX₀ allocation `Z` of the goods `M ∖ P`, then `Z` together with `X_i = P` is an EFX₀ allocation of `goods` to
`i :: rest`. -/
theorem peeling {i : A} {rest : List A} {goods P : List G} {Z : G → A} (hi : i ∉ rest) (hgd : goods.Nodup)
    (hPM : ∀ g ∈ P, g ∈ goods) (hP : P.length ≤ 1)
    (hval : value v i (goods.filter (fun g => g ∉ P)) ≤ value v i P)
    (hZ : IsAllocation rest (goods.filter (fun g => g ∉ P)) Z)
    (hE : EFX0L v rest (goods.filter (fun g => g ∉ P)) Z) :
    IsAllocation (i :: rest) goods (fun g => if g ∈ P then i else Z g) ∧
      EFX0L v (i :: rest) goods (fun g => if g ∈ P then i else Z g) := by
  have hrest : goods.filter (fun g => !decide (g ∈ P)) = goods.filter (fun g => g ∉ P) :=
    List.filter_congr fun g _ => by simp
  have hPnd : P.Nodup := by
    match P, hP with
    | [], _ => exact List.nodup_nil
    | [p], _ => simp
    | _ :: _ :: _, h => simp at h
  have hperm : (goods.filter (fun g => decide (g ∈ P))).Perm P := by
    refine (List.perm_ext_iff_of_nodup (hgd.sublist List.filter_sublist) hPnd).mpr fun g => ?_
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hPM g h, h⟩⟩
  have hX : (fun g => if g ∈ P then i else Z g) = extendBy i (fun g => decide (g ∈ P)) Z := by
    funext g; simp [extendBy]
  rw [hX]
  refine peelBundle v hi (by rw [hrest]; exact hZ) (by rw [hrest]; exact hE) ?_ ?_
  · rw [hrest, value_of_perm v i hperm]; exact hval
  · intro j _ g hg
    have hl : ((goods.filter (fun g => decide (g ∈ P))).erase g).length = 0 := by
      rw [List.length_erase_of_mem hg, hperm.length_eq]; omega
    rw [List.eq_nil_of_length_eq_zero hl, value_nil]

omit [DecidableEq A] in
/-- **Lemma "when nobody can leave"** (`lem:R1fail`). Let agent `i` value at most three goods of the remaining goods
`G`, and suppose that rule R1 (`EFX.K3.r1Step`: the favourite `p`, ties in list order; `i` leaves with nothing if
`v_i(p) = 0` and with `p` if `v_i(G ∖ {p}) ≤ v_i(p)`) does not apply to `i`. Then `i` values exactly three goods of
`G` and is strictly balanced: every good of `G` is worth less to `i` than the other goods of `G` together (for its
top `a`, `v_i(a) < v_i(b) + v_i(c)`). -/
theorem R1fail {i : A} {goods : List G} (h3 : (relevant v i goods).length ≤ 3)
    (h : K3.r1Step v goods i = none) :
    (relevant v i goods).length = 3 ∧ ∀ g ∈ goods, v i g < value v i (goods.erase g) := by
  have hne : goods ≠ [] := by
    rintro rfl
    simp [K3.r1Step, favorite] at h
  obtain ⟨h3', hlt⟩ := not_R1 v hne (K3.r1Step_eq_none h)
  refine ⟨Nat.le_antisymm h3 h3', fun g hg => ?_⟩
  have := value_erase v (i := i) hg
  have := hlt g hg
  omega

omit [DecidableEq A] in
/-- Rule R1 applies to every agent that values at most two remaining goods (the paper's remark after rule R1). -/
theorem r1_of_two {i : A} {goods : List G} (h2 : (relevant v i goods).length ≤ 2) :
    K3.r1Step v goods i ≠ none := fun h => by
  have := (R1fail v (Nat.le_succ_of_le h2) h).1
  omega

/-- **Corollary "two relevant goods"** is `EFX.Inst.sdRun_efx0`: every run of serial dictatorship (`EFX.SDRun`),
in any order of all agents, each agent taking a favourite remaining good (or nothing once no good is left) and the
last agent taking all remaining goods, is EFX₀ when every agent values at most two goods. -/
example : ∀ (I : Inst), (∀ i, numRelevant I i ≤ 2) → ∀ {order : List (Fin I.n)}, order.Nodup →
    (∀ i, i ∈ order) → ∀ {X : I.Alloc}, SDRun I.v order (List.finRange I.m) X → I.EFX0 X :=
  @Inst.sdRun_efx0

/-- The same over lists (`EFX.sdRun_efx0`): distinct agents, duplicate-free goods. -/
example : ∀ {order : List A} {goods : List G} {X : G → A}, SDRun v order goods X → order.Nodup → goods.Nodup →
    (∀ i ∈ order, (relevant v i goods).length ≤ 2) → IsAllocation order goods X ∧ EFX0L v order goods X :=
  @sdRun_efx0 A G _ _ v

end peeling

end DE
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE.threat_le_iff
#print axioms EFX.DE.threat_eq_max
#print axioms EFX.DE.efx0L_iff_safe
#print axioms EFX.DE.efx0_iff_safe
#print axioms EFX.DE.threat_of_length_le_one
#print axioms EFX.DE.threat_le_relevant
#print axioms EFX.DE.threat_pair
#print axioms EFX.DE.threat_of_perm_pair
#print axioms EFX.DE.gy_none_iff
#print axioms EFX.DE.safe_of_pair
#print axioms EFX.DE.safe_of_gy
#print axioms EFX.DE.peeling
#print axioms EFX.DE.R1fail
#print axioms EFX.DE.r1_of_two
