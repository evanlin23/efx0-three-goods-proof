import EFX.K3DEPrelim

/-!
# Limits of the shape

The statements of Appendix B of the short proof of the k = 3 result (`paper/k3-simple/long.tex`, Appendix B "Limits of
the Shape"):
the full description of safety for an agent with three relevant goods of distinct values (Lemma "cases of safety",
`lem:L5`), and Proposition "limits of the shape" (`prop:neg`): an EFX₀ allocation may need a bundle of three goods,
and the large bundle may need four.

**Definitions.**
- `Strict3 v i a b c`: agent `i` values exactly `a`, `b`, `c`, with `v(a) > v(b) > v(c) > 0` and
  `v(a) < v(b) + v(c)` (`Strict3O`: the same for values in an ordered type, `EFX.OrderedValue`).
- `Together3`: `b` and `c` lie together in a bundle of at least three goods. `Cases`: the disjunction
  (T) ∨ (BC) ∨ (B) ∨ (C) ∨ (E) of the Lemma (alone: `EFX.DE.Alone`, the only good of its bundle).
- `casesB`, `aloneB`, `sizeB`: Boolean forms over `Fin m`, for `decide` (`casesB_iff`, `aloneB_iff`, `sizeB_eq`).

**Results.**
- `safe_iff_cases` (**Lemma cases of safety**, over lists): for an allocation `X` of a duplicate-free list of goods
  holding `a`, `b`, `c`, agent `i` is safe iff `Cases`. `efx0_iff_cases`: in the model (`EFX.Inst.EFX0`), when every
  agent is such an agent, `X` is EFX₀ iff every agent is in one of the cases; so EFX₀ becomes an ordinal predicate,
  the same for every valuation with the given rankings.
- **Proposition limits (a)** `limits_a`: agents `0, 1, 2`, goods `g₀ = 0`, `g₁ = 1`, `p_i = 2 + i`, agent `i`
  ranking `g₀ ≻ g₁ ≻ p_i`, for every valuation with `Strict3`: no EFX₀ allocation has all bundles of at most two
  goods, and `{g₀}`, `{g₁}`, `{p₀, p₁, p₂}` to the three agents in any order is EFX₀.
- **Proposition limits (b)** `limits_b`: agents `0, …, 3`, goods `g₀ = 0`, `g₁ = 1`, `g₂ = 2`, `p_i = 3 + i`, rankings
  `g₀ ≻ g₂ ≻ p_i` (`i = 0, 1`) and `g₁ ≻ g₂ ≻ p_i` (`i = 2, 3`), for every valuation with `Strict3`: every EFX₀
  allocation has bundle sizes `4, 1, 1, 1` (one bundle of four goods, the others of one), and `g₀` to agent 0, `g₁`
  to agent 2, `g₂` to agent 1, the `p_i` to agent 3 is EFX₀. `limits_b_shape`: in every EFX₀ allocation `g₀`, `g₁`,
  `g₂` are alone (so held by three different agents) and the four `p_i` are together (the paper's proof).
- `limits_a_ordered`, `limits_b_ordered`, `limits_b_shape_ordered`: the same for values in any type with
  `EFX.OrderedValue` (`ℝ≥0`, `ℚ≥0`, `ℕ`, and `ℝ`, `ℚ`, `ℤ` with these hypotheses), through `agree432`: every
  comparison of two subset sums of such an agent's values has the same answer as for the values `4, 3, 2`
  (`EFX.Agree`), so EFX₀ is the same (`efx0_iff_432`, by `EFX.efx0_iff_of_agree`).

The finite checks (`checkA`, `checkB`, `checkA2`, `checkB2`) are kernel evaluations (`decide +kernel`) of `casesB`
over all `3⁵ = 243` and `4⁷ = 16384` owner maps, which are written as `mk5 x₀ … x₄` and `mk7 x₀ … x₆`; `mk5_eq`,
`mk7_eq` show that every owner map is one of them. The check of (b) takes about half a minute.

**Choices where the prose leaves room.**
1. Over lists, "`i` holds `g`" is `X g = i`, and the allocation is complete for the listed agents
   (`IsAllocation`); goods are a duplicate-free list containing `a`, `b`, `c`.
2. "`b` and `c` together in a bundle of at least three goods" is `X b = X c ∧ 3 ≤ |X_{X b}|` (`Together3`).
3. In the Proposition the instance is `⟨n, m, v⟩` of the model with agents `Fin n` and goods `Fin m`; "all bundles
   of at most two goods" and the bundle sizes count `finSum m (fun g => if X g = j then 1 else 0)`, as in
   `EFX.LB.corollaryD`; "bundle sizes `4, 1, 1, 1`" is "some bundle has four goods and every other bundle one".
4. In (a), "in any order" is: any three pairwise distinct agents `x`, `y`, `z` receive `{g₀}`, `{g₁}`, `{p₀, p₁, p₂}`.
5. The paper's proof of (b) says "with at most one bundle of more than two goods"; that hypothesis is not needed
   (and not used): once `g₀`, `g₁`, `g₂` are alone, the fourth agent holds the four `p_i`.
-/

set_option autoImplicit false

namespace EFX
namespace DE
namespace Limits

open LB Profile

/-! ## Lemma "cases of safety" -/

/-- Agent `i` values exactly `a`, `b`, `c`, with `v(a) > v(b) > v(c) > 0` and `v(a) < v(b) + v(c)`. -/
structure Strict3 {A G : Type} (v : A → G → Nat) (i : A) (a b c : G) : Prop where
  c_pos : 0 < v i c
  c_lt_b : v i c < v i b
  b_lt_a : v i b < v i a
  bal : v i a < v i b + v i c
  zero : ∀ g, g ≠ a → g ≠ b → g ≠ c → v i g = 0

section cases
variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- `b` and `c` lie together in a bundle of at least three goods. -/
def Together3 (goods : List G) (X : G → A) (b c : G) : Prop :=
  X b = X c ∧ 3 ≤ (bundle goods X (X b)).length

/-- The cases of Lemma "cases of safety" for agent `i` with goods `a ≻ b ≻ c`:
(T) `i` holds `a`, and also `b` or `c`, or `b` and `c` are not together in a bundle of at least three goods;
(BC) `i` holds `b` and `c`; (B) `i` holds `b`, and `a` is alone; (C) `i` holds `c`, and `a` and `b` are alone;
(E) `a`, `b` and `c` are all alone. -/
def Cases (goods : List G) (X : G → A) (i : A) (a b c : G) : Prop :=
  (X a = i ∧ (X b = i ∨ X c = i ∨ ¬ Together3 goods X b c)) ∨
  (X b = i ∧ X c = i) ∨
  (X b = i ∧ Alone goods X a) ∨
  (X c = i ∧ Alone goods X a ∧ Alone goods X b) ∨
  (Alone goods X a ∧ Alone goods X b ∧ Alone goods X c)

variable {v : A → G → Nat} {i : A} {a b c : G}

omit [DecidableEq A] [DecidableEq G] in
theorem Strict3.ne_ab (hv : Strict3 v i a b c) : a ≠ b := fun e => by
  have := hv.b_lt_a; rw [e] at this; omega

omit [DecidableEq A] [DecidableEq G] in
theorem Strict3.ne_ac (hv : Strict3 v i a b c) : a ≠ c := fun e => by
  have := hv.b_lt_a; have := hv.c_lt_b; rw [e] at *; omega

omit [DecidableEq A] [DecidableEq G] in
theorem Strict3.ne_bc (hv : Strict3 v i a b c) : b ≠ c := fun e => by
  have := hv.c_lt_b; rw [e] at this; omega

/-- The ranking `a ≻ b ≻ c`, as a profile (the same for every agent). -/
def prof (a b c : G) : Profile A G := ⟨fun _ => a, fun _ => b, fun _ => c⟩

omit [DecidableEq A] in
theorem Strict3.consistent (hv : Strict3 v i a b c) : (prof a b c : Profile A G).Consistent [i] v := by
  intro k hk
  rw [List.mem_singleton] at hk
  subst hk
  refine ⟨hv.c_pos, Nat.le_of_lt hv.c_lt_b, Nat.le_of_lt hv.b_lt_a, Nat.le_of_lt hv.bal, fun g hg => ?_,
    hv.ne_ab, hv.ne_ac, hv.ne_bc⟩
  unfold Profile.rank at hg
  split at hg
  · omega
  · split at hg
    · omega
    · split at hg
      · omega
      · rename_i h1 h2 h3
        exact hv.zero g h1 h2 h3

omit [DecidableEq A] in
/-- The value of a duplicate-free list is the sum of the values of `a`, `b`, `c` it contains. -/
theorem Strict3.value_eq (hv : Strict3 v i a b c) {S : List G} (hS : S.Nodup) :
    value v i S = (if a ∈ S then v i a else 0) + (if b ∈ S then v i b else 0) + (if c ∈ S then v i c else 0) :=
  Profile.value_eq (P := (prof a b c : Profile A G)) hv.consistent (List.mem_singleton_self i) hS

omit [DecidableEq A] in
theorem add_le_value (v : A → G → Nat) (i : A) {S : List G} {x y : G} (hxy : x ≠ y) (hx : x ∈ S)
    (hy : y ∈ S) : v i x + v i y ≤ value v i S := by
  rw [value_erase v (i := i) hx]
  have := le_value_of_mem v i ((List.mem_erase_of_ne (Ne.symm hxy)).mpr hy)
  omega

omit [DecidableEq A] in
/-- A duplicate-free list of at least three goods has a good other than `b` and `c`. -/
theorem exists_third {S : List G} (hS : S.Nodup) (h3 : 3 ≤ S.length) (b c : G) :
    ∃ h ∈ S, h ≠ b ∧ h ≠ c := by
  have l1 : S.length ≤ (S.erase b).length + 1 := by
    by_cases hb : b ∈ S
    · rw [List.length_erase_of_mem hb]; omega
    · rw [List.erase_of_not_mem hb]; omega
  have l2 : (S.erase b).length ≤ ((S.erase b).erase c).length + 1 := by
    by_cases hc : c ∈ S.erase b
    · rw [List.length_erase_of_mem hc]; omega
    · rw [List.erase_of_not_mem hc]; omega
  obtain ⟨h, hh⟩ := List.exists_mem_of_length_pos (by omega : 0 < ((S.erase b).erase c).length)
  rw [(hS.erase b).mem_erase_iff, hS.mem_erase_iff] at hh
  exact ⟨h, hh.2.2, hh.2.1, hh.1⟩

omit [DecidableEq A] in
/-- A duplicate-free list holding three distinct goods has at least three goods. -/
theorem three_le_length {S : List G} {h x y : G} (hh : h ∈ S) (hx : x ∈ S) (hy : y ∈ S) (hxh : x ≠ h)
    (hyh : y ≠ h) (hxy : x ≠ y) : 3 ≤ S.length := by
  have e1 := List.length_erase_of_mem hh
  have hx' : x ∈ S.erase h := (List.mem_erase_of_ne hxh).mpr hx
  have hy' : y ∈ S.erase h := (List.mem_erase_of_ne hyh).mpr hy
  have e2 := List.length_erase_of_mem hx'
  have := List.length_pos_of_mem ((List.mem_erase_of_ne (Ne.symm hxy)).mpr hy')
  have := List.length_pos_of_mem hh
  omega

/-- **Lemma "cases of safety".** Let agent `i` value exactly `a`, `b`, `c`, with `v(a) > v(b) > v(c) > 0` and
`v(a) < v(b) + v(c)`, and let `X` be an allocation of `goods` (duplicate-free, holding `a`, `b`, `c`) to `agents`.
Then `i` is safe in `X` iff (T), (BC), (B), (C) or (E) holds. -/
theorem safe_iff_cases (v : A → G → Nat) {agents : List A} {goods : List G} {X : G → A} {i : A} {a b c : G}
    (hv : Strict3 v i a b c) (hgd : goods.Nodup) (ha : a ∈ goods) (hb : b ∈ goods) (hc : c ∈ goods)
    (hX : IsAllocation agents goods X) :
    Safe v agents goods X i ↔ Cases goods X i a b c := by
  have hab := hv.ne_ab
  have hac := hv.ne_ac
  have hbc := hv.ne_bc
  have h1 := hv.c_pos
  have h2 := hv.c_lt_b
  have h3 := hv.b_lt_a
  have h4 := hv.bal
  have memB : ∀ {x : G}, x ∈ goods → ∀ j, (x ∈ bundle goods X j ↔ X x = j) := fun hx j => by
    rw [mem_bundle]; exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  have eI := hv.value_eq (nodup_bundle hgd X i)
  constructor
  · intro hS
    have viol : ∀ j ∈ agents, j ≠ i → ∀ h ∈ bundle goods X j,
        value v i ((bundle goods X j).erase h) ≤ value v i (bundle goods X i) :=
      fun j hj hji => (threat_le_iff v i _ _).mp (hS j hj hji)
    -- a good worth more than `i`'s bundle, outside it, is alone
    have alone_of : ∀ {x : G}, x ∈ goods → X x ≠ i → value v i (bundle goods X i) < v i x →
        Alone goods X x := by
      intro x hx hxi hlt h hh
      refine Classical.byContradiction fun hne => ?_
      have hxL : x ∈ (bundle goods X (X x)).erase h :=
        (List.mem_erase_of_ne fun e => hne e.symm).mpr ((memB hx _).mpr rfl)
      have := le_value_of_mem v i hxL
      have := viol (X x) (hX x hx) hxi h hh
      omega
    by_cases hia : X a = i
    · refine Or.inl ⟨hia, ?_⟩
      by_cases hib : X b = i
      · exact Or.inl hib
      by_cases hic : X c = i
      · exact Or.inr (Or.inl hic)
      refine Or.inr (Or.inr fun ⟨hbc', h3'⟩ => ?_)
      have hown : value v i (bundle goods X i) = v i a := by
        rw [eI, ite_eq_left ((memB ha i).mpr hia), ite_eq_right (mt (memB hb i).mp hib),
          ite_eq_right (mt (memB hc i).mp hic)]
        omega
      obtain ⟨h, hh, hhb, hhc⟩ := exists_third (nodup_bundle hgd X (X b)) h3' b c
      have hbL : b ∈ (bundle goods X (X b)).erase h :=
        (List.mem_erase_of_ne fun e => hhb e.symm).mpr ((memB hb _).mpr rfl)
      have hcL : c ∈ (bundle goods X (X b)).erase h :=
        (List.mem_erase_of_ne fun e => hhc e.symm).mpr ((memB hc _).mpr hbc'.symm)
      have := add_le_value v i hbc hbL hcL
      have := viol (X b) (hX b hb) hib h hh
      omega
    · by_cases hib : X b = i
      · by_cases hic : X c = i
        · exact Or.inr (Or.inl ⟨hib, hic⟩)
        · have hown : value v i (bundle goods X i) = v i b := by
            rw [eI, ite_eq_right (mt (memB ha i).mp hia), ite_eq_left ((memB hb i).mpr hib),
              ite_eq_right (mt (memB hc i).mp hic)]
            omega
          exact Or.inr (Or.inr (Or.inl ⟨hib, alone_of ha hia (by omega)⟩))
      · by_cases hic : X c = i
        · have hown : value v i (bundle goods X i) = v i c := by
            rw [eI, ite_eq_right (mt (memB ha i).mp hia), ite_eq_right (mt (memB hb i).mp hib),
              ite_eq_left ((memB hc i).mpr hic)]
            omega
          exact Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hic, alone_of ha hia (by omega), alone_of hb hib (by omega)⟩)))
        · have hown : value v i (bundle goods X i) = 0 := by
            rw [eI, ite_eq_right (mt (memB ha i).mp hia), ite_eq_right (mt (memB hb i).mp hib),
              ite_eq_right (mt (memB hc i).mp hic)]
          exact Or.inr (Or.inr (Or.inr (Or.inr
            ⟨alone_of ha hia (by omega), alone_of hb hib (by omega), alone_of hc hic (by omega)⟩)))
  · intro hC j _ hji
    rw [threat_le_iff]
    intro h hh
    have hnd := nodup_bundle hgd X j
    have eL := hv.value_eq (hnd.erase h)
    have hXh : X h = j := (mem_bundle.mp hh).2
    -- what `X_j ∖ {h}` cannot contain
    have notL_own : ∀ {x : G}, X x = i → x ∉ (bundle goods X j).erase h := fun hxi hx =>
      hji ((mem_bundle.mp (List.mem_of_mem_erase hx)).2.symm.trans hxi)
    have notL_alone : ∀ {x : G}, Alone goods X x → x ∉ (bundle goods X j).erase h := by
      intro x hA hx
      obtain ⟨hxh, hxj⟩ := hnd.mem_erase_iff.mp hx
      exact hxh (hA h (mem_bundle.mpr ⟨(mem_bundle.mp hh).1, hXh.trans (mem_bundle.mp hxj).2.symm⟩)).symm
    have own1 : ∀ {x : G}, x ∈ goods → X x = i → v i x ≤ value v i (bundle goods X i) :=
      fun hx hxi => le_value_of_mem v i ((memB hx i).mpr hxi)
    have own2 : ∀ {x y : G}, x ≠ y → x ∈ goods → y ∈ goods → X x = i → X y = i →
        v i x + v i y ≤ value v i (bundle goods X i) :=
      fun hxy hx hy hxi hyi => add_le_value v i hxy ((memB hx i).mpr hxi) ((memB hy i).mpr hyi)
    rw [eL]
    rcases hC with ⟨hia, hib | hic | hT⟩ | ⟨hib, hic⟩ | ⟨hib, hA⟩ | ⟨hic, hA, hB⟩ | ⟨hA, hB, hC'⟩
    · -- (T), holding `a` and `b`
      have := own2 hab ha hb hia hib
      rw [ite_eq_right (notL_own hia), ite_eq_right (notL_own hib)]
      split <;> omega
    · -- (T), holding `a` and `c`
      have := own2 hac ha hc hia hic
      rw [ite_eq_right (notL_own hia), ite_eq_right (notL_own hic)]
      split <;> omega
    · -- (T), holding `a`; `b` and `c` are not together in a bundle of at least three goods
      have := own1 ha hia
      have hnot : ¬ (b ∈ (bundle goods X j).erase h ∧ c ∈ (bundle goods X j).erase h) := by
        rintro ⟨hbL, hcL⟩
        obtain ⟨hbh, hbj⟩ := hnd.mem_erase_iff.mp hbL
        obtain ⟨hch, hcj⟩ := hnd.mem_erase_iff.mp hcL
        have hXb := (mem_bundle.mp hbj).2
        have hXc := (mem_bundle.mp hcj).2
        refine hT ⟨hXb.trans hXc.symm, ?_⟩
        rw [hXb]
        exact three_le_length hh hbj hcj hbh hch hbc
      rw [ite_eq_right (notL_own hia)]
      by_cases hbL : b ∈ (bundle goods X j).erase h
      · rw [ite_eq_left hbL, ite_eq_right fun hcL => hnot ⟨hbL, hcL⟩]; omega
      · rw [ite_eq_right hbL]; split <;> omega
    · -- (BC)
      have := own2 hbc hb hc hib hic
      rw [ite_eq_right (notL_own hib), ite_eq_right (notL_own hic)]
      split <;> omega
    · -- (B)
      have := own1 hb hib
      rw [ite_eq_right (notL_alone hA), ite_eq_right (notL_own hib)]
      split <;> omega
    · -- (C)
      rw [ite_eq_right (notL_alone hA), ite_eq_right (notL_alone hB), ite_eq_right (notL_own hic)]
      omega
    · -- (E)
      rw [ite_eq_right (notL_alone hA), ite_eq_right (notL_alone hB), ite_eq_right (notL_alone hC')]
      omega

end cases

/-- **Lemma "cases of safety", in the model.** If every agent `i` values exactly `a i`, `b i`, `c i` with
`Strict3`, an allocation is EFX₀ iff every agent is in one of the cases. -/
theorem efx0_iff_cases (I : Inst) (a b c : Fin I.n → Fin I.m) (hv : ∀ i, Strict3 I.v i (a i) (b i) (c i))
    (X : I.Alloc) : I.EFX0 X ↔ ∀ i, Cases (List.finRange I.m) X i (a i) (b i) (c i) := by
  rw [efx0_iff_safe]
  exact forall_congr' fun i => safe_iff_cases I.v (hv i) (List.nodup_finRange _) (List.mem_finRange _)
    (List.mem_finRange _) (List.mem_finRange _) (fun _ _ => List.mem_finRange _)

/-! ## Boolean forms, for `decide` -/

section bool
variable {n m : Nat}

/-- Equality of `Fin n`, by `Nat.beq` on the values (cheap for the kernel). -/
def eqB (x y : Fin n) : Bool := Nat.beq x.val y.val

theorem eqB_iff {x y : Fin n} : eqB x y = true ↔ x = y := by
  rw [eqB, Nat.beq_eq, Fin.ext_iff]

/-- `g` is alone, as a Boolean. -/
def aloneB (goods : List (Fin m)) (X : Fin m → Fin n) (g : Fin m) : Bool :=
  goods.all (fun h => !eqB (X h) (X g) || Nat.beq h.val g.val)

theorem aloneB_iff {goods : List (Fin m)} {X : Fin m → Fin n} {g : Fin m} :
    aloneB goods X g = true ↔ Alone goods X g := by
  rw [alone_iff, aloneB, List.all_eq_true]
  refine forall_congr' fun h => imp_congr_right fun _ => ?_
  rw [Bool.or_eq_true, Bool.not_eq_true', Nat.beq_eq, ← Fin.ext_iff]
  constructor
  · rintro (e | e) he
    · rw [(eqB_iff).mpr he] at e; cases e
    · exact e
  · intro e
    by_cases he : X h = X g
    · exact Or.inr (e he)
    · left; cases hb : eqB (X h) (X g)
      · rfl
      · exact absurd (eqB_iff.mp hb) he

/-- The number of goods of `j`'s bundle. -/
def sizeB (goods : List (Fin m)) (X : Fin m → Fin n) (j : Fin n) : Nat :=
  goods.countP (fun h => eqB (X h) j)

theorem sizeB_eq {goods : List (Fin m)} {X : Fin m → Fin n} {j : Fin n} :
    sizeB goods X j = (bundle goods X j).length := by
  rw [sizeB, List.countP_eq_length_filter, bundle]
  congr 1
  apply List.filter_congr
  intro g _
  rw [Bool.eq_iff_iff, eqB_iff, decide_eq_true_iff]

/-- The model's bundle size is `sizeB`. -/
theorem finSum_size (X : Fin m → Fin n) (j : Fin n) :
    finSum m (fun g => if X g = j then 1 else 0) = sizeB (List.finRange m) X j := by
  rw [finSum_eq_sum, sum_map_ite (fun g => X g = j) (fun _ => 1), sum_map_one, sizeB_eq]
  rfl

/-- `Together3`, as a Boolean. -/
def together3B (goods : List (Fin m)) (X : Fin m → Fin n) (b c : Fin m) : Bool :=
  eqB (X b) (X c) && Nat.ble 3 (sizeB goods X (X b))

theorem together3B_iff {goods : List (Fin m)} {X : Fin m → Fin n} {b c : Fin m} :
    together3B goods X b c = true ↔ Together3 goods X b c := by
  rw [together3B, Bool.and_eq_true, eqB_iff, Nat.ble_eq, sizeB_eq]
  rfl

/-- `Cases`, as a Boolean. -/
def casesB (goods : List (Fin m)) (X : Fin m → Fin n) (i : Fin n) (a b c : Fin m) : Bool :=
  (eqB (X a) i && (eqB (X b) i || (eqB (X c) i || !together3B goods X b c))) ||
  ((eqB (X b) i && eqB (X c) i) ||
  ((eqB (X b) i && aloneB goods X a) ||
  ((eqB (X c) i && (aloneB goods X a && aloneB goods X b)) ||
  (aloneB goods X a && (aloneB goods X b && aloneB goods X c)))))

theorem not_eq_true_iff {x : Bool} : (!x) = true ↔ ¬ x = true := by cases x <;> simp

theorem casesB_iff {goods : List (Fin m)} {X : Fin m → Fin n} {i : Fin n} {a b c : Fin m} :
    casesB goods X i a b c = true ↔ Cases goods X i a b c := by
  simp only [casesB, Cases, Bool.or_eq_true, Bool.and_eq_true, not_eq_true_iff, eqB_iff, aloneB_iff,
    together3B_iff]

/-- Every agent is in one of the cases, as a Boolean. -/
def allCasesB (agents : List (Fin n)) (goods : List (Fin m)) (X : Fin m → Fin n) (a b c : Fin n → Fin m) : Bool :=
  agents.all fun i => casesB goods X i (a i) (b i) (c i)

theorem allCasesB_of (I : Inst) (a b c : Fin I.n → Fin I.m) (hv : ∀ i, Strict3 I.v i (a i) (b i) (c i))
    {X : I.Alloc} (hX : I.EFX0 X) : allCasesB (List.finRange I.n) (List.finRange I.m) X a b c = true :=
  List.all_eq_true.mpr fun i _ => casesB_iff.mpr ((efx0_iff_cases I a b c hv X).mp hX i)

theorem efx0_of_allCasesB (I : Inst) (a b c : Fin I.n → Fin I.m) (hv : ∀ i, Strict3 I.v i (a i) (b i) (c i))
    {X : I.Alloc} (h : allCasesB (List.finRange I.n) (List.finRange I.m) X a b c = true) : I.EFX0 X :=
  (efx0_iff_cases I a b c hv X).mpr fun i => casesB_iff.mp (List.all_eq_true.mp h i (List.mem_finRange i))

end bool

/-! ## Owner maps as tuples -/

/-- The owner map `g ↦ x_g` on five goods. -/
def mk5 {n : Nat} (x0 x1 x2 x3 x4 : Fin n) (g : Fin 5) : Fin n :=
  match g.val with
  | 0 => x0 | 1 => x1 | 2 => x2 | 3 => x3 | _ => x4

theorem mk5_eq {n : Nat} (X : Fin 5 → Fin n) : mk5 (X 0) (X 1) (X 2) (X 3) (X 4) = X := by
  funext g
  match g with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨k + 5, h⟩ => exact absurd h (by omega)

/-- The owner map `g ↦ x_g` on seven goods. -/
def mk7 {n : Nat} (x0 x1 x2 x3 x4 x5 x6 : Fin n) (g : Fin 7) : Fin n :=
  match g.val with
  | 0 => x0 | 1 => x1 | 2 => x2 | 3 => x3 | 4 => x4 | 5 => x5 | _ => x6

theorem mk7_eq {n : Nat} (X : Fin 7 → Fin n) : mk7 (X 0) (X 1) (X 2) (X 3) (X 4) (X 5) (X 6) = X := by
  funext g
  match g with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨6, _⟩ => rfl
  | ⟨k + 7, h⟩ => exact absurd h (by omega)

/-! ## Proposition "limits of the shape" (a) -/

/-- Part (a): `p_i = 2 + i` (goods `g₀ = 0`, `g₁ = 1`). -/
def pA (i : Fin 3) : Fin 5 := ⟨i.val + 2, by omega⟩

/-- `{g₀}` to `x`, `{g₁}` to `y`, `{p₀, p₁, p₂}` to `z`. -/
def allocA (x y z : Fin 3) (g : Fin 5) : Fin 3 := if g = 0 then x else if g = 1 then y else z

/-- The finite check of (a), over all `3⁵` owner maps: if every agent is in one of the cases, some bundle has at
least three goods. -/
theorem checkA : ∀ x0 x1 x2 x3 x4 : Fin 3,
    (!allCasesB (List.finRange 3) (List.finRange 5) (mk5 x0 x1 x2 x3 x4) (fun _ => 0) (fun _ => 1) pA ||
      (List.finRange 3).any fun j => Nat.blt 2 (sizeB (List.finRange 5) (mk5 x0 x1 x2 x3 x4) j)) = true := by
  decide +kernel

/-- The finite check of (a), second part: with `{g₀}`, `{g₁}`, `{p₀, p₁, p₂}` to distinct agents, every agent is in
one of the cases. -/
theorem checkA2 : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z →
    allCasesB (List.finRange 3) (List.finRange 5) (allocA x y z) (fun _ => 0) (fun _ => 1) pA = true := by
  decide +kernel

/-- **Proposition "limits of the shape" (a).** Agents `0, 1, 2` rank `g₀ ≻ g₁ ≻ p_i`, where `p_i` is valued only by
agent `i`, with `v_i(g₀) > v_i(g₁) > v_i(p_i) > 0` and `v_i(g₀) < v_i(g₁) + v_i(p_i)`, for any such values. No EFX₀
allocation has all bundles of at most two goods, and `{g₀}`, `{g₁}`, `{p₀, p₁, p₂}`, to the three agents in any
order, is EFX₀. -/
theorem limits_a (v : Fin 3 → Fin 5 → Nat) (hv : ∀ i, Strict3 v i 0 1 (pA i)) :
    (∀ X : Fin 5 → Fin 3, (⟨3, 5, v⟩ : Inst).EFX0 X →
      ¬ ∀ j, finSum 5 (fun g => if X g = j then 1 else 0) ≤ 2) ∧
    (∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z → (⟨3, 5, v⟩ : Inst).EFX0 (allocA x y z)) := by
  refine ⟨fun X hX hsmall => ?_, fun x y z hxy hxz hyz => ?_⟩
  · have hc := checkA (X 0) (X 1) (X 2) (X 3) (X 4)
    rw [mk5_eq X, allCasesB_of ⟨3, 5, v⟩ (fun _ => 0) (fun _ => 1) pA hv hX, Bool.not_true, Bool.false_or,
      List.any_eq_true] at hc
    obtain ⟨j, -, hj⟩ := hc
    have := hsmall j
    rw [finSum_size] at this
    rw [Nat.blt_eq] at hj
    omega
  · exact efx0_of_allCasesB ⟨3, 5, v⟩ (fun _ => 0) (fun _ => 1) pA hv (checkA2 x y z hxy hxz hyz)

/-! ## Proposition "limits of the shape" (b) -/

/-- Part (b): agent `i`'s top, `g₀ = 0` for agents `0, 1` and `g₁ = 1` for agents `2, 3`. -/
def aB (i : Fin 4) : Fin 7 := if i.val < 2 then 0 else 1

/-- Part (b): `p_i = 3 + i` (`g₂ = 2` is everyone's second good). -/
def pB (i : Fin 4) : Fin 7 := ⟨i.val + 3, by omega⟩

/-- `g₀` to agent 0, `g₁` to agent 2, `g₂` to agent 1, the four `p_i` to agent 3. -/
def allocB (g : Fin 7) : Fin 4 := if g = 0 then 0 else if g = 1 then 2 else if g = 2 then 1 else 3

/-- Bundle sizes `4, 1, 1, 1`, as a Boolean. -/
def sizes4111B (X : Fin 7 → Fin 4) : Bool :=
  (List.finRange 4).any fun j => Nat.beq (sizeB (List.finRange 7) X j) 4 &&
    (List.finRange 4).all fun k => eqB k j || Nat.beq (sizeB (List.finRange 7) X k) 1

/-- `g₀`, `g₁`, `g₂` are alone and the four `p_i` are together, as a Boolean. -/
def shapeB (X : Fin 7 → Fin 4) : Bool :=
  aloneB (List.finRange 7) X 0 && aloneB (List.finRange 7) X 1 && aloneB (List.finRange 7) X 2 &&
    eqB (X 3) (X 4) && eqB (X 3) (X 5) && eqB (X 3) (X 6)

/-- The finite check of (b), over all `4⁷` owner maps: if every agent is in one of the cases, the bundle sizes are
`4, 1, 1, 1`, `g₀`, `g₁`, `g₂` are alone and the `p_i` are together. -/
theorem checkB : ∀ x0 x1 x2 x3 x4 x5 x6 : Fin 4,
    (!allCasesB (List.finRange 4) (List.finRange 7) (mk7 x0 x1 x2 x3 x4 x5 x6) aB (fun _ => 2) pB ||
      (sizes4111B (mk7 x0 x1 x2 x3 x4 x5 x6) && shapeB (mk7 x0 x1 x2 x3 x4 x5 x6))) = true := by
  decide +kernel

/-- The finite check of (b), second part: in `allocB` every agent is in one of the cases (T, B, T, C). -/
theorem checkB2 : allCasesB (List.finRange 4) (List.finRange 7) allocB aB (fun _ => 2) pB = true := by
  decide +kernel

/-- `checkB` for an EFX₀ allocation of an instance of (b). -/
theorem checkB_of (v : Fin 4 → Fin 7 → Nat) (hv : ∀ i, Strict3 v i (aB i) 2 (pB i)) {X : Fin 7 → Fin 4}
    (hX : (⟨4, 7, v⟩ : Inst).EFX0 X) : sizes4111B X = true ∧ shapeB X = true := by
  have hc := checkB (X 0) (X 1) (X 2) (X 3) (X 4) (X 5) (X 6)
  rw [mk7_eq X, allCasesB_of ⟨4, 7, v⟩ aB (fun _ => 2) pB hv hX, Bool.not_true, Bool.false_or,
    Bool.and_eq_true] at hc
  exact hc

/-- **Proposition "limits of the shape" (b).** Agents `0, 1, 2, 3` rank `g₀ ≻ g₂ ≻ p₀`, `g₀ ≻ g₂ ≻ p₁`,
`g₁ ≻ g₂ ≻ p₂` and `g₁ ≻ g₂ ≻ p₃`, with `p_i` valued only by agent `i`, `v_i(a_i) > v_i(b_i) > v_i(c_i) > 0` and
`v_i(a_i) < v_i(b_i) + v_i(c_i)`, for any such values. Every EFX₀ allocation has bundle sizes `4, 1, 1, 1`, and one
exists: `g₀` to agent 0, `g₁` to agent 2, `g₂` to agent 1 and the four goods `p_i` to agent 3. -/
theorem limits_b (v : Fin 4 → Fin 7 → Nat) (hv : ∀ i, Strict3 v i (aB i) 2 (pB i)) :
    (∀ X : Fin 7 → Fin 4, (⟨4, 7, v⟩ : Inst).EFX0 X →
      ∃ j, finSum 7 (fun g => if X g = j then 1 else 0) = 4 ∧
        ∀ k, k ≠ j → finSum 7 (fun g => if X g = k then 1 else 0) = 1) ∧
    (⟨4, 7, v⟩ : Inst).EFX0 allocB := by
  refine ⟨fun X hX => ?_, efx0_of_allCasesB ⟨4, 7, v⟩ aB (fun _ => 2) pB hv checkB2⟩
  have hs := (checkB_of v hv hX).1
  rw [sizes4111B, List.any_eq_true] at hs
  obtain ⟨j, -, hj⟩ := hs
  rw [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at hj
  refine ⟨j, by rw [finSum_size]; exact hj.1, fun k hk => ?_⟩
  have := hj.2 k (List.mem_finRange k)
  rw [Bool.or_eq_true, eqB_iff, Nat.beq_eq] at this
  rw [finSum_size]
  exact this.resolve_left hk

/-- **The shape in (b)** (the paper's proof): in every EFX₀ allocation, `g₀`, `g₁` and `g₂` are alone (so they are
held by three different agents) and the four goods `p_i` are in one bundle. -/
theorem limits_b_shape (v : Fin 4 → Fin 7 → Nat) (hv : ∀ i, Strict3 v i (aB i) 2 (pB i)) (X : Fin 7 → Fin 4)
    (hX : (⟨4, 7, v⟩ : Inst).EFX0 X) :
    Alone (List.finRange 7) X 0 ∧ Alone (List.finRange 7) X 1 ∧ Alone (List.finRange 7) X 2 ∧
      X 3 = X 4 ∧ X 3 = X 5 ∧ X 3 = X 6 := by
  have hs := (checkB_of v hv hX).2
  simp only [shapeB, Bool.and_eq_true, aloneB_iff, eqB_iff] at hs
  exact ⟨hs.1.1.1.1.1, hs.1.1.1.1.2, hs.1.1.1.2, hs.1.1.2, hs.1.2, hs.2⟩

/-! ## Ordered values -/

section ordered
open OrderedValue

variable {V : Type} [OrderedValue V]

/-- `Strict3` for values in an ordered type: agent `i` values exactly `a`, `b`, `c`, with `v(a) > v(b) > v(c) > 0`
and `v(a) < v(b) + v(c)`. -/
structure Strict3O {A G : Type} (v : A → G → V) (i : A) (a b c : G) : Prop where
  c_pos : ¬ v i c ≤ 0
  c_lt_b : ¬ v i b ≤ v i c
  b_lt_a : ¬ v i a ≤ v i b
  bal : ¬ v i b + v i c ≤ v i a
  zero : ∀ g, g ≠ a → g ≠ b → g ≠ c → v i g = 0

/-- The values `4, 3, 2` on `a`, `b`, `c`, and `0` elsewhere. -/
def w432 {G : Type} [DecidableEq G] (a b c : G) (g : G) : Nat :=
  if g = a then 4 else if g = b then 3 else if g = c then 2 else 0

section
variable {A G : Type} {v : A → G → V} {i : A} {a b c : G}

theorem Strict3O.ne_ab (hv : Strict3O v i a b c) : a ≠ b := fun e =>
  hv.b_lt_a (by rw [e]; exact OrderedValue.le_refl _)

theorem Strict3O.ne_bc (hv : Strict3O v i a b c) : b ≠ c := fun e =>
  hv.c_lt_b (by rw [e]; exact OrderedValue.le_refl _)

theorem Strict3O.ne_ac (hv : Strict3O v i a b c) : a ≠ c := fun e => by
  have cb := (OrderedValue.le_total _ _).resolve_left hv.c_lt_b
  rw [← e] at cb
  exact hv.b_lt_a cb

end

/-- **Agreement with `4, 3, 2`.** For an agent with `Strict3O`, every comparison of two subset sums of its values
has the same answer as for the values `4, 3, 2` on `a, b, c`. -/
theorem agree432 {A : Type} {k : Nat} (v : A → Fin k → V) (i : A) {a b c : Fin k} (hv : Strict3O v i a b c) :
    Agree (v i) (w432 a b c) := by
  have hab := hv.ne_ab
  have hac := hv.ne_ac
  have hbc := hv.ne_bc
  have hc := hv.c_pos
  have cb : v i c ≤ v i b := (le_total _ _).resolve_left hv.c_lt_b
  have ba : v i b ≤ v i a := (le_total _ _).resolve_left hv.b_lt_a
  have ca : v i c ≤ v i a := le_trans _ _ _ cb ba
  have hbpos : ¬ v i b ≤ 0 := fun h => hc (le_trans _ _ _ cb h)
  have hapos : ¬ v i a ≤ 0 := fun h => hbpos (le_trans _ _ _ ba h)
  have hR : Realizes (v i a) (v i b) (v i c) (Pat.ofNat 4 3 2) :=
    { p12 := iff_of_false (by decide) hv.b_lt_a
      p21 := iff_of_true (by decide) ba
      p13 := iff_of_false (by decide) fun h => hv.b_lt_a (le_trans _ _ _ h cb)
      p31 := iff_of_true (by decide) ca
      p23 := iff_of_false (by decide) hv.c_lt_b
      p32 := iff_of_true (by decide) cb
      q1 := iff_of_true (by decide) ((le_total _ _).resolve_right hv.bal)
      r1 := iff_of_false (by decide) hv.bal
      q2 := iff_of_true (by decide) (le_trans _ _ _ ba (le_add_right (nonneg_of_pos hc)))
      r2 := iff_of_false (by decide) fun h => not_add_le_left hc (le_trans _ _ _ h ba)
      q3 := iff_of_true (by decide) (le_trans _ _ _ ca (le_add_right (nonneg_of_pos hbpos)))
      r3 := iff_of_false (by decide) fun h => not_add_le_left hbpos (le_trans _ _ _ h ca) }
  have hA : ∀ s1 s2 s3 t1 t2 t3 : Bool, (tri s1 s2 s3 (v i a) (v i b) (v i c) ≤ tri t1 t2 t3 (v i a) (v i b) (v i c) ↔
      tri s1 s2 s3 (4 : Nat) 3 2 ≤ tri t1 t2 t3 (4 : Nat) 3 2) := fun s1 s2 s3 t1 t2 t3 => by
    rw [tri_le_iff hR hapos hbpos hc, tri_le_iff (Pat.realizes_ofNat 4 3 2) (Nat.not_le.mpr (by decide))
      (Nat.not_le.mpr (by decide)) (Nat.not_le.mpr (by decide))]
  have hnd : [a, b, c].Nodup := by simp [hab, hac, hbc]
  refine agree_of_slots (v i) (w432 a b c) [a, b, c] hnd ?_ ?_ (v i a) (v i b) (v i c) 4 3 2 hA
    (fun S => (S a, S b, S c)) (fun S => by simp [listSum, tri, add_zero])
    (fun S => by simp [listSum, tri, add_zero, w432, Ne.symm hab, Ne.symm hac, Ne.symm hbc])
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hg
    exact hv.zero g hg.1 hg.2.1 hg.2.2
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hg
    simp [w432, hg.1, hg.2.1, hg.2.2]

/-- An allocation is EFX₀ for values with `Strict3O` iff it is EFX₀ for the values `4, 3, 2`. -/
theorem efx0_iff_432 (I : OInst V) (a b c : Fin I.n → Fin I.m) (hv : ∀ i, Strict3O I.v i (a i) (b i) (c i))
    (X : I.Alloc) : I.EFX0 X ↔ (⟨I.n, I.m, fun i => w432 (a i) (b i) (c i)⟩ : Inst).EFX0 X :=
  efx0_iff_of_agree I _ (fun i => agree432 I.v i (hv i)) X

/-- The values `4, 3, 2` satisfy `Strict3`. -/
theorem strict3_w432 {A G : Type} [DecidableEq G] (a b c : A → G) (hab : ∀ i, a i ≠ b i) (hac : ∀ i, a i ≠ c i)
    (hbc : ∀ i, b i ≠ c i) (i : A) : Strict3 (fun i => w432 (a i) (b i) (c i)) i (a i) (b i) (c i) where
  c_pos := by simp [w432, Ne.symm (hac i), Ne.symm (hbc i)]
  c_lt_b := by simp [w432, Ne.symm (hab i), Ne.symm (hac i), Ne.symm (hbc i)]
  b_lt_a := by simp [w432, Ne.symm (hab i)]
  bal := by simp [w432, Ne.symm (hab i), Ne.symm (hac i), Ne.symm (hbc i)]
  zero := fun g h1 h2 h3 => by simp [w432, h1, h2, h3]

/-- **Proposition "limits of the shape" (a)**, for values in any ordered type. -/
theorem limits_a_ordered (v : Fin 3 → Fin 5 → V) (hv : ∀ i, Strict3O v i 0 1 (pA i)) :
    (∀ X : Fin 5 → Fin 3, (⟨3, 5, v⟩ : OInst V).EFX0 X →
      ¬ ∀ j, finSum 5 (fun g => if X g = j then 1 else 0) ≤ 2) ∧
    (∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z → (⟨3, 5, v⟩ : OInst V).EFX0 (allocA x y z)) := by
  have hw := limits_a _ (strict3_w432 (fun _ => (0 : Fin 5)) (fun _ => 1) pA (by decide) (by decide) (by decide))
  have e := efx0_iff_432 (⟨3, 5, v⟩ : OInst V) (fun _ => 0) (fun _ => 1) pA hv
  exact ⟨fun X hX => hw.1 X ((e X).mp hX), fun x y z h1 h2 h3 => (e _).mpr (hw.2 x y z h1 h2 h3)⟩

/-- **Proposition "limits of the shape" (b)**, for values in any ordered type. -/
theorem limits_b_ordered (v : Fin 4 → Fin 7 → V) (hv : ∀ i, Strict3O v i (aB i) 2 (pB i)) :
    (∀ X : Fin 7 → Fin 4, (⟨4, 7, v⟩ : OInst V).EFX0 X →
      ∃ j, finSum 7 (fun g => if X g = j then 1 else 0) = 4 ∧
        ∀ k, k ≠ j → finSum 7 (fun g => if X g = k then 1 else 0) = 1) ∧
    (⟨4, 7, v⟩ : OInst V).EFX0 allocB := by
  have hw := limits_b _ (strict3_w432 aB (fun _ => (2 : Fin 7)) pB (by decide) (by decide) (by decide))
  have e := efx0_iff_432 (⟨4, 7, v⟩ : OInst V) aB (fun _ => 2) pB hv
  exact ⟨fun X hX => hw.1 X ((e X).mp hX), (e _).mpr hw.2⟩

/-- **The shape in (b)**, for values in any ordered type. -/
theorem limits_b_shape_ordered (v : Fin 4 → Fin 7 → V) (hv : ∀ i, Strict3O v i (aB i) 2 (pB i))
    (X : Fin 7 → Fin 4) (hX : (⟨4, 7, v⟩ : OInst V).EFX0 X) :
    Alone (List.finRange 7) X 0 ∧ Alone (List.finRange 7) X 1 ∧ Alone (List.finRange 7) X 2 ∧
      X 3 = X 4 ∧ X 3 = X 5 ∧ X 3 = X 6 :=
  limits_b_shape _ (strict3_w432 aB (fun _ => (2 : Fin 7)) pB (by decide) (by decide) (by decide)) X
    ((efx0_iff_432 (⟨4, 7, v⟩ : OInst V) aB (fun _ => 2) pB hv X).mp hX)

end ordered

end Limits
end DE
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE.Limits.safe_iff_cases
#print axioms EFX.DE.Limits.efx0_iff_cases
#print axioms EFX.DE.Limits.casesB_iff
#print axioms EFX.DE.Limits.checkA
#print axioms EFX.DE.Limits.checkB
#print axioms EFX.DE.Limits.limits_a
#print axioms EFX.DE.Limits.limits_b
#print axioms EFX.DE.Limits.limits_b_shape
#print axioms EFX.DE.Limits.agree432
#print axioms EFX.DE.Limits.efx0_iff_432
#print axioms EFX.DE.Limits.limits_a_ordered
#print axioms EFX.DE.Limits.limits_b_ordered
#print axioms EFX.DE.Limits.limits_b_shape_ordered
