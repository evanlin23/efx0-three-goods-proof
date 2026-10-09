import EFX.K3Algo
import EFX.Junk
import EFX.Blocks

/-!
# Draft and Exchange, part 1: states, soundness, transfers and exchanges (ledger K3S.PO.LEAN)

The objects of the short proof of the k = 3 result (`paper/k3-simple/long.tex` §3–§5, `k3/simplify/po/hall/NOTES.md`),
over the valid pre-allocations of `EFX/PreAlloc.lean`. In the core case every agent `i` values exactly three goods,
ranked `a i`, `b i`, `c i` (`EFX.LB.Profile`, well formed: `EFX.LB.WF`).

**Names.** The Lean files keep the names of an earlier version of the paper: *needs* for the paper's wants, *utility*
for score, *exposed* (`Exposed o x`) for "`x` is a blocker of `o`", *protecting good* (`hOf x`) for the blocker's
leftover good `h_x`, *junk* for the leftover goods `J`, *valid absorber* (`Absorber o H`) for "`o` can finish with
`H`", *need arcs* and *exposure arcs* for want and pair arrows, *need cycles* and *exchange cycles* for rings, *pair
chain* for chain, and (P) (`EFX.DE.PropP`) for (NC).

**States.** A state is a pick map `Y` and a list `up` of pair holders, as in `EFX.LB.Valid`: an agent holds nothing,
one of its three goods (`Y i`), or, if `i ∈ up`, its pair `{b i, c i}` (then `Y i = some (b i)`). The needs are
rank-based (`EFX.LB.Profile.NA`), and `EFX.LB.Valid` is the paper's validity: every needed good is the only good of
some agent (`EFX.LB.Valid.na_picked`). The utilities (the paper's scores) are `4, 3, 2, 1, 0` for the pair, `a`, `b`,
`c`, nothing (`util`); `Dominates` is Pareto domination, `total` the sum of utilities.

**Definitions.**
- `Free`: a listed agent outside `up` whose pick, if any, nobody needs (`freeB` decides it).
- `Exposed o x` (the paper's Definition blockers, finishing: `x` is a blocker of `o`): `x ≠ o` holds only its top
  `a x`, is not a pair holder, and each of `b x`, `c x` is junk or held by `o` (the premise of
  `EFX.LB.complete_some`).
- `Absorber o H` (Definition blockers, finishing: `o` can finish with `H`; also a pair holder `o`, for the case
  where every agent holds its pair): `o` is a pair holder or free, `H` is a list of junk goods that meets
  `{b x, c x}` for every `x` exposed for `o`, and `|H| ≤ |F ∖ {o}|` (`nFreeExcept`).
- `completeDE o H`: the paper's completion: picks to their pickers, `c u` to each pair holder `u`, the goods of `H`,
  in the order of the list `H`, to different free agents other than `o`, in the order of `agents` (`fill` with one
  slot each, `slot1`), and every other junk good to `o`.

**Results.**
- `completeDE_completion`, `soundness` (**Theorem soundness**): the completion is a completion of the valid state in
  the sense of `EFX.LB.Completion`, so by Theorem 1′ (`EFX.LB.Valid.sound`) it is EFX₀ for every valuation
  consistent with the rankings, and every bundle but `o`'s has at most two goods.
- `transfer` (**Lemma staying valid**, `lem:stay`; Lemma transfer of the earlier version): a state whose utilities are
  all at least those of a valid state, and in which every good needed in the old state is the only good of a
  non-pair holder, is valid (the needs only shrink, `na_of_util`).
- `exchange`, `exchange_scores` (**Lemma ring**, and **Lemma chain** through choice 3: one lemma for both moves): let
  `onC` mark a set of agents outside `up` on which `σ` and `π` are inverse bijections (`Cycle`). Every agent `z` of
  the set hands its holding to `σ z`: if `z` is not free, `σ z` needs `z`'s good and takes it alone (a want arrow); if
  `z` is free, `σ z` takes its pair, whose goods are junk or `z`'s good (a pair arrow, or the last arc of a chain; the
  paper's receiver holds only its top, which the proof does not need), and the junk goods taken by different
  receivers are different. The result `exchY`, `exchUp` is valid and Pareto-dominates the state (`exchange`); every
  agent of the set gets a strictly higher utility and every other agent the same utility (`exchange_scores`). The
  rings and chains of the paper are instances (`EFX/K3DEImprove.lean`, `EFX.DE.step_next_scores`).

**Choices where the prose leaves room.**
1. The pair holder `u` keeps `Y u = some (b u)` and holds `c u` through `up` (the representation of
   `EFX.LB.Valid`); the junk is computed (`EFX.LB.junkList`), so an exchange only changes `Y` and `up`.
2. `|F ∖ {o}|` counts the listed free agents other than `o` (`agents` is duplicate-free where it matters).
3. A chain `x = j₀ → j₁ → ⋯ → j_k` is closed into a cycle by the arc `j_k → x` from the free agent `j_k` (or the
   loop `x → x` when `k = 0`): `x` takes its pair from the junk, and `j_k`'s good becomes junk. So one lemma covers it,
   and the agents of the cycle are `x, j₁, …, j_k`, those whose scores rise in Lemma chain.
-/

set_option autoImplicit false

namespace EFX
namespace DE

open LB Profile

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Utilities and Pareto domination -/

/-- The utility of `i`: `4` for its pair, `3`, `2`, `1` for `a i`, `b i`, `c i` alone, `0` for nothing. -/
def util (P : Profile A G) (up : List A) (Y : A → Option G) (i : A) : Nat :=
  if i ∈ up then 4 else 3 - P.pickRank Y i

/-- The state `(Y', up')` Pareto-dominates `(Y, up)`: no listed agent's utility drops, one rises. -/
def Dominates (P : Profile A G) (agents : List A) (Y' : A → Option G) (up' : List A) (Y : A → Option G)
    (up : List A) : Prop :=
  (∀ i ∈ agents, util P up Y i ≤ util P up' Y' i) ∧ ∃ i ∈ agents, util P up Y i < util P up' Y' i

/-- The sum of utilities. -/
def total (P : Profile A G) (agents : List A) (Y : A → Option G) (up : List A) : Nat :=
  (agents.map (util P up Y)).sum

variable {P : Profile A G} {agents : List A} {goods : List G} {Y : A → Option G} {up : List A}

omit [DecidableEq A] in
theorem pickRank_le (Y : A → Option G) (i : A) : P.pickRank Y i ≤ 3 := by
  unfold Profile.pickRank Profile.rank
  cases Y i with
  | none => simp
  | some y => simp only; split <;> (try split) <;> (try split) <;> omega

theorem util_le (i : A) : util P up Y i ≤ 4 := by
  unfold util; split <;> omega

theorem total_le : total P agents Y up ≤ 4 * agents.length := by
  unfold total
  induction agents with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := util_le (P := P) (up := up) (Y := Y) i
    omega

theorem total_lt {Y' : A → Option G} {up' : List A} (h : Dominates P agents Y' up' Y up) :
    total P agents Y up < total P agents Y' up' :=
  sum_map_lt h.1 h.2

/-! ## Free agents, junk, exposure and absorbers -/

/-- `k` is free: listed, not a pair holder, and nobody needs its pick (if it has one). -/
def Free (P : Profile A G) (agents up : List A) (Y : A → Option G) (k : A) : Prop :=
  k ∈ agents ∧ k ∉ up ∧ ∀ y, Y k = some y → ¬ P.NA agents (· ∈ up) Y y

/-- `Free`, as a Boolean. -/
def freeB (P : Profile A G) (agents up : List A) (Y : A → Option G) (k : A) : Bool :=
  agents.contains k && !(up.contains k) && !(frozenB P agents up Y k)

theorem freeB_iff {k : A} : freeB P agents up Y k = true ↔ Free P agents up Y k := by
  unfold freeB Free frozenB
  cases hY : Y k with
  | none => simp
  | some y =>
    simp only [Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true']
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, by simpa using h2, fun y' hy' hna => ?_⟩
      cases hy'
      rw [naB_iff.mpr hna] at h3; cases h3
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h1, by simpa using h2⟩, ?_⟩
      cases hb : naB P agents up Y y with
      | false => rfl
      | true => exact absurd (naB_iff.mp hb) (h3 y rfl)

/-- `x` is exposed for `o`: `x ≠ o` is listed, not a pair holder, holds only its top `a x`, and each of `b x`, `c x`
is junk or in `o`'s holding. -/
def Exposed (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (o x : A) : Prop :=
  x ∈ agents ∧ x ≠ o ∧ x ∉ up ∧ Y x = some (P.a x) ∧
    (P.b x ∈ junkList P agents up Y goods ∨ InBase P up Y o (P.b x)) ∧
    (P.c x ∈ junkList P agents up Y goods ∨ InBase P up Y o (P.c x))

/-- `|F ∖ {o}|`: the listed free agents other than `o`. -/
def nFreeExcept (P : Profile A G) (agents up : List A) (Y : A → Option G) (o : A) : Nat :=
  (agents.filter (fun k => k != o && freeB P agents up Y k)).length

/-- **A valid absorber `o` with set `H`** (the paper's Definition blockers, finishing: `o` can finish with `H`; or `o`
is a pair holder): `o` is a listed pair holder or free; `H` is a list of junk goods, at most one per free agent other
than `o`, that meets `{b x, c x}` for every agent `x` exposed for `o`. -/
structure Absorber (P : Profile A G) (agents : List A) (goods : List G) (Y : A → Option G) (up : List A) (o : A)
    (H : List G) : Prop where
  mem : o ∈ agents
  ok : o ∈ up ∨ Free P agents up Y o
  junk : ∀ h ∈ H, h ∈ junkList P agents up Y goods
  fit : H.length ≤ nFreeExcept P agents up Y o
  hit : ∀ x, Exposed P agents up Y goods o x → P.b x ∈ H ∨ P.c x ∈ H

/-- One slot for each free agent other than `o`. -/
def slot1 (P : Profile A G) (agents up : List A) (Y : A → Option G) (o k : A) : Nat :=
  if k ≠ o ∧ freeB P agents up Y k = true then 1 else 0

/-- **The completion** with absorber `o` and set `H`: picks go to their pickers, `c u` to each pair holder `u`, the
goods of `H` (in the order of the list `H`) to different free agents other than `o` (one each, in the order of
`agents`), and every other good to `o`: `X_o = Y_o ∪ (J ∖ H)`. -/
def completeDE (P : Profile A G) (agents up : List A) (Y : A → Option G) (o : A) (H : List G) (g : G) : A :=
  match picker agents Y g with
  | some k => k
  | none =>
    match upOf P up g with
    | some u => u
    | none => (fill (slot1 P agents up Y o) agents H g).getD o

theorem sum_slot1 (o : A) : ∀ l : List A,
    (l.map (slot1 P agents up Y o)).sum = (l.filter (fun k => k != o && freeB P agents up Y k)).length
  | [] => rfl
  | k :: l => by
    have ih := sum_slot1 o l
    simp only [List.map_cons, List.sum_cons, List.filter_cons, ih, slot1]
    by_cases h1 : k = o
    · simp [h1]
    · by_cases h2 : freeB P agents up Y k = true
      · simp [h1, h2]; omega
      · simp [h1, h2]

omit [DecidableEq A] in
/-- A junk good is nobody's pick and not the `c` of a pair holder. -/
theorem junk_iff (hV : Valid P agents goods Y up) {g : G} :
    g ∈ junkList P agents up Y goods ↔ g ∈ goods ∧ (∀ k, Y k ≠ some g) ∧ ∀ u ∈ up, P.c u ≠ g := by
  rw [mem_junkList]
  constructor
  · rintro ⟨hg, hp, hu⟩
    exact ⟨hg, fun k hk => picker_none hp k (hV.pick k g hk).1 hk, upOf_none hu⟩
  · rintro ⟨hg, hp, hu⟩
    refine ⟨hg, ?_, ?_⟩
    · unfold picker
      exact List.find?_eq_none.mpr fun k _ => by simp [hp k]
    · unfold upOf
      exact List.find?_eq_none.mpr fun k hk => by simp [hu k hk]

/-- **The completion is a completion** (`EFX.LB.Completion`) of the valid state, with owner `o`. -/
theorem completeDE_completion (hV : Valid P agents goods Y up) (hag : agents.Nodup) (hgd : goods.Nodup) {o : A}
    {H : List G}
    (hA : Absorber P agents goods Y up o H) :
    Completion P agents goods Y up (some o) (completeDE P agents up Y o H) := by
  have hpicker : ∀ k y, Y k = some y → picker agents Y y = some k := by
    intro k y hk
    cases hp : picker agents Y y with
    | none => exact absurd hk (picker_none hp k (hV.pick k y hk).1)
    | some k' => rw [hV.pick_inj k' k y (picker_some hp).2 hk]
  have hfillj : ∀ {g j}, fill (slot1 P agents up Y o) agents H g = some j → j ≠ o ∧ Free P agents up Y j := by
    intro g j hf
    have h3 := (fill_some hf).2.2
    unfold slot1 at h3
    by_cases hj : j ≠ o ∧ freeB P agents up Y j = true
    · exact ⟨hj.1, freeB_iff.mp hj.2⟩
    · simp [hj] at h3
  -- the three ways a good is placed
  have hcases : ∀ g, (∃ k, picker agents Y g = some k ∧ completeDE P agents up Y o H g = k) ∨
      (picker agents Y g = none ∧ ∃ u, upOf P up g = some u ∧ completeDE P agents up Y o H g = u) ∨
      (picker agents Y g = none ∧ upOf P up g = none ∧ ∃ j, fill (slot1 P agents up Y o) agents H g = some j ∧
        completeDE P agents up Y o H g = j) ∨
      (picker agents Y g = none ∧ upOf P up g = none ∧ fill (slot1 P agents up Y o) agents H g = none ∧
        completeDE P agents up Y o H g = o) := by
    intro g
    unfold completeDE
    cases hp : picker agents Y g with
    | some k => exact Or.inl ⟨k, rfl, rfl⟩
    | none =>
      cases hu : upOf P up g with
      | some u => exact Or.inr (Or.inl ⟨rfl, u, rfl, rfl⟩)
      | none =>
        cases hf : fill (slot1 P agents up Y o) agents H g with
        | some j => exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, j, rfl, by simp⟩))
        | none => exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, by simp⟩))
  -- every good of `H` is placed by `fill`, so not with `o`
  have hHfill : ∀ h ∈ H, ∃ j, fill (slot1 P agents up Y o) agents H h = some j := by
    intro h hh
    apply fill_cover hh
    rw [sum_slot1]
    exact hA.fit
  refine ⟨fun g hg => ?_, fun k y hk => ?_, fun u hu => ?_, fun j _ hj y hy hna g hg hX => ?_,
    fun u hu hou g hg hX => ?_, fun j _ hoj hj hnf => ?_, fun w hw x hx hxw hxu hxa hboth => ?_⟩
  · -- `alloc`
    rcases hcases g with ⟨k, hp, hX⟩ | ⟨-, u, hu, hX⟩ | ⟨-, -, j, hf, hX⟩ | ⟨-, -, -, hX⟩
    · rw [hX]; exact (picker_some hp).1
    · rw [hX]; exact hV.up_mem u (upOf_some hu).1
    · rw [hX]; exact (fill_some hf).1
    · rw [hX]; exact hA.mem
  · -- `pick`
    unfold completeDE; rw [hpicker k y hk]
  · -- `upc`
    have hp : picker agents Y (P.c u) = none := by
      cases hp : picker agents Y (P.c u) with
      | none => rfl
      | some k => exact absurd (picker_some hp).2 ((hV.up_c u hu).2 k)
    unfold completeDE; rw [hp]
    cases hu' : upOf P up (P.c u) with
    | none => exact absurd rfl (upOf_none hu' u hu)
    | some u' => exact hV.up_c_inj u' (upOf_some hu').1 u hu (upOf_some hu').2
  · -- `frozen`
    rcases hcases g with ⟨k, hp, hX'⟩ | ⟨-, u, hu, hX'⟩ | ⟨-, -, j', hf, hX'⟩ | ⟨-, -, -, hX'⟩
    · rw [hX'] at hX; subst hX
      have := (picker_some hp).2
      rw [hy] at this; cases this; rfl
    · rw [hX'] at hX; subst hX; exact absurd (upOf_some hu).1 hj
    · rw [hX'] at hX; subst hX
      exact absurd hna ((hfillj hf).2.2.2 y hy)
    · rw [hX'] at hX; subst hX
      rcases hA.ok with ho | ho
      · exact absurd ho hj
      · exact absurd hna (ho.2.2 y hy)
  · -- `upOnly`
    rcases hcases g with ⟨k, hp, hX'⟩ | ⟨-, u', hu', hX'⟩ | ⟨-, -, j', hf, hX'⟩ | ⟨-, -, -, hX'⟩
    · rw [hX'] at hX; subst hX
      have := (picker_some hp).2
      rw [hV.up_b k hu] at this; cases this; exact Or.inl rfl
    · rw [hX'] at hX; subst hX; exact Or.inr (upOf_some hu').2.symm
    · rw [hX'] at hX; subst hX; exact absurd hu (hfillj hf).2.2.1
    · rw [hX'] at hX; subst hX; exact absurd rfl hou
  · -- `slots`: a free agent other than `o` receives at most one good of `H`
    have hS : ∀ g ∈ (bundle goods (completeDE P agents up Y o H) j).filter (fun g => Y j ≠ some g),
        fill (slot1 P agents up Y o) agents H g = some j := by
      intro g hgS
      obtain ⟨hgb, hne⟩ := List.mem_filter.mp hgS
      obtain ⟨-, hX⟩ := mem_bundle.mp hgb
      rcases hcases g with ⟨k, hp, hX'⟩ | ⟨-, u, hu, hX'⟩ | ⟨-, -, j', hf, hX'⟩ | ⟨-, -, -, hX'⟩
      · rw [hX'] at hX; subst hX; simp [(picker_some hp).2] at hne
      · rw [hX'] at hX; subst hX; exact absurd (upOf_some hu).1 hj
      · rw [hX'] at hX; subst hX; exact hf
      · rw [hX'] at hX; subst hX; exact absurd rfl hoj
    have hc := fill_count hag ((nodup_bundle hgd _ j).sublist List.filter_sublist) hS
    have h1 : slot1 P agents up Y o j ≤ 1 := by unfold slot1; split <;> omega
    split <;> omega
  · -- `oc`: each of `b x`, `c x` in `o`'s bundle is junk or in `o`'s holding, so `x` is exposed for `o`
    cases hw
    have hsrc : ∀ g, g ∈ bundle goods (completeDE P agents up Y o H) o →
        (g ∈ junkList P agents up Y goods ∨ InBase P up Y o g) := by
      intro g hgb
      obtain ⟨hg, hX⟩ := mem_bundle.mp hgb
      rcases hcases g with ⟨k, hp, hX'⟩ | ⟨hp, u, hu, hX'⟩ | ⟨-, -, j', hf, hX'⟩ | ⟨hp, hu, -, -⟩
      · rw [hX'] at hX; subst hX; exact Or.inr (Or.inl (picker_some hp).2)
      · rw [hX'] at hX; subst hX; exact Or.inr (Or.inr (upOf_some hu))
      · rw [hX'] at hX; subst hX; exact absurd rfl (hfillj hf).1
      · exact Or.inl (mem_junkList.mpr ⟨hg, hp, hu⟩)
    have hHout : ∀ h ∈ H, h ∉ bundle goods (completeDE P agents up Y o H) o := by
      intro h hh hhb
      obtain ⟨-, hp, hu⟩ := mem_junkList.mp (hA.junk h hh)
      obtain ⟨j, hj⟩ := hHfill h hh
      have hX := (mem_bundle.mp hhb).2
      unfold completeDE at hX
      rw [hp, hu] at hX
      simp only [hj, Option.getD_some] at hX
      exact (hfillj hj).1 hX
    rcases hA.hit x ⟨hx, hxw, hxu, hxa, hsrc _ hboth.1, hsrc _ hboth.2⟩ with hb | hc
    · exact hHout _ hb hboth.1
    · exact hHout _ hc hboth.2

/-- **Theorem soundness** (the paper's Theorem soundness): the completion of a valid state with a valid absorber `o`
is a complete allocation, EFX₀ for every valuation consistent with the rankings, and every bundle but `o`'s has at
most two goods. -/
theorem soundness (hV : Valid P agents goods Y up) (hag : agents.Nodup) (hgd : goods.Nodup) {o : A} {H : List G}
    (hA : Absorber P agents goods Y up o H) :
    IsAllocation agents goods (completeDE P agents up Y o H) ∧
      (∀ v : A → G → Nat, P.Consistent agents v → EFX0L v agents goods (completeDE P agents up Y o H)) ∧
      ∀ j ∈ agents, j ≠ o → (bundle goods (completeDE P agents up Y o H) j).length ≤ 2 := by
  have hC := completeDE_completion hV hag hgd hA
  obtain ⟨h1, h2⟩ := hV.sound hC hgd
  exact ⟨hC.alloc, h1, fun j hj hjo => h2 j hj (fun e => hjo (Option.some.inj e).symm)⟩

/-! ## Lemma staying valid (transfer) -/

/-- The structural conditions of a state: `EFX.LB.Valid` without (V1) and (V2). -/
structure IsState (P : Profile A G) (agents : List A) (goods : List G) (Y : A → Option G) (up : List A) :
    Prop where
  pick : ∀ k y, Y k = some y → k ∈ agents ∧ y ∈ goods ∧ P.rank k y < 3
  pick_inj : ∀ k k' y, Y k = some y → Y k' = some y → k = k'
  up_mem : ∀ u ∈ up, u ∈ agents
  up_b : ∀ u ∈ up, Y u = some (P.b u)
  up_c : ∀ u ∈ up, P.c u ∈ goods ∧ ∀ k, Y k ≠ some (P.c u)
  up_c_inj : ∀ u ∈ up, ∀ u' ∈ up, P.c u = P.c u' → u = u'

/-- **(F1)**: if no listed agent's utility drops, the needs only shrink. -/
theorem na_of_util {Y' : A → Option G} {up' : List A} (hle : ∀ i ∈ agents, util P up Y i ≤ util P up' Y' i)
    {g : G} (h : P.NA agents (· ∈ up') Y' g) : P.NA agents (· ∈ up) Y g := by
  obtain ⟨i, hi, hnu, hp⟩ := h
  have hl := hle i hi
  have h3 := pickRank_le (P := P) Y i
  have h3' := pickRank_le (P := P) Y' i
  unfold util at hl
  have hnu' : i ∉ up' := hnu
  by_cases hu : i ∈ up
  · simp only [hu, hnu', ↓reduceIte] at hl; omega
  · simp only [hu, hnu', ↓reduceIte] at hl
    refine ⟨i, hi, hu, ?_⟩
    unfold Profile.Prefers at hp ⊢
    omega

/-- **Lemma staying valid** (`lem:stay`; Lemma transfer of the earlier version). Let `(Y', up')` be a state in which
no listed agent's utility is smaller than in `(Y, up)`, and every good needed in `(Y, up)` is the only good of an agent
outside `up'`. Then `(Y', up')` is valid. (The paper assumes `(Y, up)` valid; the proof does not use it.) -/
theorem transfer {Y' : A → Option G} {up' : List A}
    (hS : IsState P agents goods Y' up') (hle : ∀ i ∈ agents, util P up Y i ≤ util P up' Y' i)
    (hna : ∀ g ∈ goods, P.NA agents (· ∈ up) Y g → ∃ k, k ∉ up' ∧ Y' k = some g) :
    Valid P agents goods Y' up' where
  pick := hS.pick
  pick_inj := hS.pick_inj
  up_mem := hS.up_mem
  up_b := hS.up_b
  up_c := hS.up_c
  up_c_inj := hS.up_c_inj
  v1 := fun g hg hp _ h => by
    obtain ⟨k, -, hk⟩ := hna g hg (na_of_util hle h)
    exact hp k hk
  v2 := fun u hu => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hb := (hS.pick u _ (hS.up_b u hu)).2.1
      obtain ⟨k, hk, hk'⟩ := hna _ hb (na_of_util hle h)
      have := hS.pick_inj k u _ hk' (hS.up_b u hu)
      subst this; exact hk hu
    · obtain ⟨k, -, hk⟩ := hna _ (hS.up_c u hu).1 (na_of_util hle h)
      exact (hS.up_c u hu).2 k hk

/-! ## Lemma ring: exchanges along a cycle -/

/-- The holdings after the exchange: an agent `w` of the set (`onC w`) takes its pair if its predecessor `π w` is
free, and `π w`'s good otherwise; every other agent keeps its holding. -/
def exchY (P : Profile A G) (agents up : List A) (Y : A → Option G) (onC : A → Bool) (π : A → A) (w : A) :
    Option G :=
  if onC w then (if freeB P agents up Y (π w) then some (P.b w) else Y (π w)) else Y w

/-- The pair holders after the exchange: the old ones and the agents of the set whose predecessor is free. -/
def exchUp (P : Profile A G) (agents up : List A) (Y : A → Option G) (onC : A → Bool) (π : A → A) : List A :=
  up ++ agents.filter (fun w => onC w && freeB P agents up Y (π w))

/-- **An exchange cycle** (the paper's rings, cycles of want and pair arrows, and chains closed by their last arc):
`onC` marks a nonempty set of listed agents outside `up` on which `σ` (successor) and `π` (predecessor) are inverse
bijections. A non-free agent `z` holds a good that `σ z` needs (a want arrow); a free agent `z` points to an agent
`σ z` whose `b` and `c` are each junk or `z`'s good (a pair arrow, or the arc that closes a chain); different
receivers from free agents use different junk goods. -/
structure Cycle (P : Profile A G) (agents : List A) (goods : List G) (Y : A → Option G) (up : List A)
    (onC : A → Bool) (σ π : A → A) : Prop where
  mem : ∀ w, onC w = true → w ∈ agents ∧ w ∉ up
  ne : ∃ w, onC w = true
  σ_mem : ∀ z, onC z = true → onC (σ z) = true
  π_mem : ∀ w, onC w = true → onC (π w) = true
  σπ : ∀ w, onC w = true → σ (π w) = w
  πσ : ∀ z, onC z = true → π (σ z) = z
  need : ∀ z, onC z = true → ¬ Free P agents up Y z → ∃ y, Y z = some y ∧ P.Prefers Y (σ z) y
  free : ∀ z, onC z = true → Free P agents up Y z →
    (P.b (σ z) ∈ junkList P agents up Y goods ∨ Y z = some (P.b (σ z))) ∧
    (P.c (σ z) ∈ junkList P agents up Y goods ∨ Y z = some (P.c (σ z)))
  disj : ∀ z z', onC z = true → onC z' = true → Free P agents up Y z → Free P agents up Y z' → σ z ≠ σ z' →
    ∀ g ∈ junkList P agents up Y goods, (g = P.b (σ z) ∨ g = P.c (σ z)) → (g = P.b (σ z') ∨ g = P.c (σ z')) →
      False

theorem mem_exchUp {onC : A → Bool} {π : A → A} (w : A) : w ∈ exchUp P agents up Y onC π ↔
    w ∈ up ∨ (w ∈ agents ∧ onC w = true ∧ Free P agents up Y (π w)) := by
  simp [exchUp, List.mem_filter, freeB_iff]

theorem exchY_off {onC : A → Bool} {π : A → A} {w : A} (h : onC w = false) :
    exchY P agents up Y onC π w = Y w := by
  simp [exchY, h]

theorem exchY_free {onC : A → Bool} {π : A → A} {w : A} (h : onC w = true) (hf : Free P agents up Y (π w)) :
    exchY P agents up Y onC π w = some (P.b w) := by
  simp [exchY, h, freeB_iff.mpr hf]

theorem exchY_need {onC : A → Bool} {π : A → A} {w : A} (h : onC w = true) (hf : ¬ Free P agents up Y (π w)) :
    exchY P agents up Y onC π w = Y (π w) := by
  have : freeB P agents up Y (π w) = false := by
    cases hb : freeB P agents up Y (π w) with
    | false => rfl
    | true => exact absurd (freeB_iff.mp hb) hf
  simp [exchY, h, this]

/-- **The scores of an exchange** (Lemma ring and Lemma chain, the scores): along a `Cycle`, every agent of the set
`onC` gets a strictly higher utility, and every other agent the same utility. An agent whose predecessor is free goes
from at most its top (`3`) to its pair (`4`); any other agent of the set receives its predecessor's good, which it
needs. Only the structure of the cycle is used. -/
theorem exchange_scores {onC : A → Bool} {σ π : A → A} (hC : Cycle P agents goods Y up onC σ π) :
    (∀ w, onC w = true →
      util P up Y w < util P (exchUp P agents up Y onC π) (exchY P agents up Y onC π) w) ∧
    (∀ w, onC w = false →
      util P (exchUp P agents up Y onC π) (exchY P agents up Y onC π) w = util P up Y w) := by
  refine ⟨fun i hci => ?_, fun i hci => ?_⟩
  · have hi := (hC.mem i hci).1
    have hiu := (hC.mem i hci).2
    have h3 := pickRank_le (P := P) Y i
    by_cases hf : Free P agents up Y (π i)
    · have : i ∈ exchUp P agents up Y onC π := (mem_exchUp i).mpr (Or.inr ⟨hi, hci, hf⟩)
      simp only [util, hiu, this, ↓reduceIte]; omega
    · have hnotU : i ∉ exchUp P agents up Y onC π := fun h => by
        rcases (mem_exchUp i).mp h with h | ⟨-, -, h⟩
        · exact hiu h
        · exact hf h
      obtain ⟨y, hy, hp⟩ := hC.need (π i) (hC.π_mem i hci) hf
      rw [hC.σπ i hci] at hp
      have hY'i : exchY P agents up Y onC π i = some y := by rw [exchY_need hci hf, hy]
      have hpr : P.pickRank (exchY P agents up Y onC π) i = P.rank i y := by
        unfold Profile.pickRank; rw [hY'i]
      unfold Profile.Prefers at hp
      simp only [util, hiu, hnotU, ↓reduceIte, hpr]
      omega
  · have hiff : i ∈ exchUp P agents up Y onC π ↔ i ∈ up := by
      rw [mem_exchUp]
      constructor
      · rintro (h | ⟨-, h, -⟩)
        · exact h
        · rw [hci] at h; cases h
      · exact Or.inl
    have hpr : P.pickRank (exchY P agents up Y onC π) i = P.pickRank Y i := by
      unfold Profile.pickRank; rw [exchY_off hci]
    by_cases h : i ∈ up
    · simp [util, h, hiff.mpr h]
    · simp [util, h, mt hiff.mp h, hpr]

/-- **Lemma ring** (with chains): the exchange along a `Cycle` is a valid state that Pareto-dominates the state. The
scores (every agent of the cycle strictly gains, every other agent keeps its utility) are `exchange_scores`. -/
theorem exchange (hV : Valid P agents goods Y up) (hWF : WF P agents goods) {onC : A → Bool} {σ π : A → A}
    (hC : Cycle P agents goods Y up onC σ π) :
    Valid P agents goods (exchY P agents up Y onC π) (exchUp P agents up Y onC π) ∧
      Dominates P agents (exchY P agents up Y onC π) (exchUp P agents up Y onC π) Y up := by
  have hjunk : ∀ {g}, g ∈ junkList P agents up Y goods ↔
      g ∈ goods ∧ (∀ k, Y k ≠ some g) ∧ ∀ u ∈ up, P.c u ≠ g := junk_iff hV
  have hmemU : ∀ w, w ∈ exchUp P agents up Y onC π ↔
      w ∈ up ∨ (w ∈ agents ∧ onC w = true ∧ Free P agents up Y (π w)) := mem_exchUp
  have hoff : ∀ w, onC w = false → exchY P agents up Y onC π w = Y w := fun _ h => exchY_off h
  have hon_free : ∀ w, onC w = true → Free P agents up Y (π w) → exchY P agents up Y onC π w = some (P.b w) :=
    fun _ h hf => exchY_free h hf
  have hon_need : ∀ w, onC w = true → ¬ Free P agents up Y (π w) → exchY P agents up Y onC π w = Y (π w) :=
    fun _ h hf => exchY_need h hf
  -- where a new pick comes from: a junk good taken as `b`, or an old pick
  have hsrc : ∀ k y, exchY P agents up Y onC π k = some y →
      (onC k = true ∧ Free P agents up Y (π k) ∧ y = P.b k ∧ y ∈ junkList P agents up Y goods) ∨
      (∃ z, Y z = some y ∧ ((z = k ∧ onC k = false) ∨ (onC k = true ∧ z = π k))) := by
    intro k y hk
    cases hck : onC k with
    | false => exact Or.inr ⟨k, by rw [← hoff k hck]; exact hk, Or.inl ⟨rfl, rfl⟩⟩
    | true =>
      by_cases hf : Free P agents up Y (π k)
      · rw [hon_free k hck hf] at hk
        cases hk
        have := (hC.free (π k) (hC.π_mem k hck) hf).1
        rw [hC.σπ k hck] at this
        rcases this with hj | hz
        · exact Or.inl ⟨rfl, hf, rfl, hj⟩
        · exact Or.inr ⟨π k, hz, Or.inr ⟨rfl, rfl⟩⟩
      · rw [hon_need k hck hf] at hk
        exact Or.inr ⟨π k, hk, Or.inr ⟨rfl, rfl⟩⟩
  have hsrc_inj : ∀ k k' z, ((z = k ∧ onC k = false) ∨ (onC k = true ∧ z = π k)) →
      ((z = k' ∧ onC k' = false) ∨ (onC k' = true ∧ z = π k')) → k = k' := by
    intro k k' z h h'
    rcases h with ⟨e, hk⟩ | ⟨hk, e⟩ <;> rcases h' with ⟨e', hk'⟩ | ⟨hk', e'⟩
    · exact e.symm.trans e'
    · have := hC.π_mem k' hk'; rw [← e', e, hk] at this; cases this
    · have := hC.π_mem k hk; rw [← e, e', hk'] at this; cases this
    · calc k = σ (π k) := (hC.σπ k hk).symm
        _ = σ (π k') := by rw [← e, ← e']
        _ = k' := hC.σπ k' hk'
  have hinj : ∀ k k' y, exchY P agents up Y onC π k = some y → exchY P agents up Y onC π k' = some y → k = k' := by
    intro k k' y hk hk'
    rcases hsrc k y hk with ⟨hck, hf, hyb, hyj⟩ | ⟨z, hz, hzk⟩ <;>
      rcases hsrc k' y hk' with ⟨hck', hf', hyb', hyj'⟩ | ⟨z', hz', hzk'⟩
    · refine Classical.byContradiction fun hne => ?_
      exact hC.disj (π k) (π k') (hC.π_mem k hck) (hC.π_mem k' hck') hf hf'
        (by rw [hC.σπ k hck, hC.σπ k' hck']; exact hne) y hyj
        (Or.inl (by rw [hC.σπ k hck]; exact hyb)) (Or.inl (by rw [hC.σπ k' hck']; exact hyb'))
    · exact absurd hz' ((hjunk.mp hyj).2.1 z')
    · exact absurd hz ((hjunk.mp hyj').2.1 z)
    · have := hV.pick_inj z z' y hz hz'; subst this
      exact hsrc_inj k k' z hzk hzk'
  -- the `c` of a new pair holder is junk or its predecessor's good
  have hnew : ∀ u, onC u = true → Free P agents up Y (π u) →
      P.c u ∈ junkList P agents up Y goods ∨ Y (π u) = some (P.c u) := by
    intro u hcu hfu
    have hc := (hC.free (π u) (hC.π_mem u hcu) hfu).2
    rwa [hC.σπ u hcu] at hc
  have hupc : ∀ u ∈ exchUp P agents up Y onC π, P.c u ∈ goods ∧
      ∀ k, exchY P agents up Y onC π k ≠ some (P.c u) := by
    intro u hu
    rcases (hmemU u).mp hu with hu | ⟨hua, hcu, hfu⟩
    · refine ⟨(hV.up_c u hu).1, fun k hk => ?_⟩
      rcases hsrc k _ hk with ⟨-, -, -, hj⟩ | ⟨z, hz, -⟩
      · exact (hjunk.mp hj).2.2 u hu rfl
      · exact (hV.up_c u hu).2 z hz
    · refine ⟨(hWF u hua).2.2.1, fun k hk => ?_⟩
      rcases hsrc k _ hk with ⟨hck, hfk, hcb, hj⟩ | ⟨z, hz, hzk⟩
      · by_cases hku : k = u
        · subst hku; exact (hWF k hua).2.2.2.2.2 hcb.symm
        · exact hC.disj (π u) (π k) (hC.π_mem u hcu) (hC.π_mem k hck) hfu hfk
            (by rw [hC.σπ u hcu, hC.σπ k hck]; exact Ne.symm hku) _ hj
            (Or.inr (by rw [hC.σπ u hcu])) (Or.inl (by rw [hC.σπ k hck]; exact hcb))
      · rcases hnew u hcu hfu with hj | hzu
        · exact (hjunk.mp hj).2.1 z hz
        · have hzz := hV.pick_inj z (π u) _ hz hzu
          subst hzz
          have hku := hsrc_inj k u (π u) hzk (Or.inr ⟨hcu, rfl⟩)
          subst hku
          rw [hon_free k hcu hfu] at hk
          exact (hWF k hua).2.2.2.2.2 (Option.some.inj hk)
  have hupcinj : ∀ u ∈ exchUp P agents up Y onC π, ∀ u' ∈ exchUp P agents up Y onC π, P.c u = P.c u' → u = u' := by
    intro u hu u' hu' he
    rcases (hmemU u).mp hu with hu | ⟨hua, hcu, hfu⟩ <;>
      rcases (hmemU u').mp hu' with hu' | ⟨hua', hcu', hfu'⟩
    · exact hV.up_c_inj u hu u' hu' he
    · exfalso
      rcases hnew u' hcu' hfu' with hj | hz
      · exact (hjunk.mp hj).2.2 u hu he
      · rw [← he] at hz; exact (hV.up_c u hu).2 _ hz
    · exfalso
      rcases hnew u hcu hfu with hj | hz
      · exact (hjunk.mp hj).2.2 u' hu' he.symm
      · rw [he] at hz; exact (hV.up_c u' hu').2 _ hz
    · refine Classical.byContradiction fun hne => ?_
      rcases hnew u hcu hfu with hj | hz <;> rcases hnew u' hcu' hfu' with hj' | hz'
      · exact hC.disj (π u) (π u') (hC.π_mem u hcu) (hC.π_mem u' hcu') hfu hfu'
          (by rw [hC.σπ u hcu, hC.σπ u' hcu']; exact hne) _ hj
          (Or.inr (by rw [hC.σπ u hcu])) (Or.inr (by rw [hC.σπ u' hcu', he]))
      · rw [← he] at hz'; exact (hjunk.mp hj).2.1 _ hz'
      · rw [he] at hz; exact (hjunk.mp hj').2.1 _ hz
      · rw [← he] at hz'
        have := hV.pick_inj _ _ _ hz hz'
        exact hne (by rw [← hC.σπ u hcu, ← hC.σπ u' hcu', this])
  have hS : IsState P agents goods (exchY P agents up Y onC π) (exchUp P agents up Y onC π) := {
    pick := fun k y hk => by
      have hrb : ∀ k ∈ agents, P.rank k (P.b k) < 3 := fun k hka => by
        simp [Profile.rank, Ne.symm (hWF k hka).2.2.2.1]
      rcases hsrc k y hk with ⟨hck, -, hyb, -⟩ | ⟨z, hz, hzk⟩
      · subst hyb
        have hka := (hC.mem k hck).1
        exact ⟨hka, (hWF k hka).2.1, hrb k hka⟩
      · rcases hzk with ⟨rfl, hck⟩ | ⟨hck, rfl⟩
        · exact hV.pick z y hz
        · obtain ⟨-, hyg, -⟩ := hV.pick _ y hz
          have hka := (hC.mem k hck).1
          by_cases hf : Free P agents up Y (π k)
          · rw [hon_free k hck hf] at hk; cases hk
            exact ⟨hka, (hWF k hka).2.1, hrb k hka⟩
          · refine ⟨hka, hyg, ?_⟩
            obtain ⟨y', hy', hp⟩ := hC.need (π k) (hC.π_mem k hck) hf
            rw [hC.σπ k hck] at hp
            rw [hz] at hy'; cases hy'
            unfold Profile.Prefers at hp
            have := pickRank_le (P := P) Y k
            omega
    pick_inj := hinj
    up_mem := fun u hu => by
      rcases (hmemU u).mp hu with h | ⟨h, -, -⟩
      · exact hV.up_mem u h
      · exact h
    up_b := fun u hu => by
      rcases (hmemU u).mp hu with h | ⟨-, hc, hf⟩
      · have : onC u = false := by
          cases hcu : onC u with
          | false => rfl
          | true => exact absurd h (hC.mem u hcu).2
        rw [hoff u this]; exact hV.up_b u h
      · exact hon_free u hc hf
    up_c := hupc
    up_c_inj := hupcinj }
  -- utilities
  obtain ⟨hlt, heq⟩ := exchange_scores hC
  have hle : ∀ i ∈ agents, util P up Y i ≤ util P (exchUp P agents up Y onC π) (exchY P agents up Y onC π) i := by
    intro i _
    cases hci : onC i with
    | false => exact Nat.le_of_eq (heq i hci).symm
    | true => exact Nat.le_of_lt (hlt i hci)
  -- the needed goods stay alone
  have hna : ∀ g ∈ goods, P.NA agents (· ∈ up) Y g →
      ∃ k, k ∉ exchUp P agents up Y onC π ∧ exchY P agents up Y onC π k = some g := by
    intro g hg hng
    obtain ⟨j, hj⟩ := hV.na_picked hg hng
    have hju : j ∉ up := fun h => by
      rw [hV.up_b j h] at hj; cases hj
      exact (hV.v2 j h).1 hng
    have hjf : ¬ Free P agents up Y j := fun h => h.2.2 g hj hng
    cases hcj : onC j with
    | false =>
      refine ⟨j, fun h => ?_, by rw [hoff j hcj, hj]⟩
      rcases (hmemU j).mp h with h | ⟨-, h, -⟩
      · exact hju h
      · rw [hcj] at h; cases h
    | true =>
      have hcs := hC.σ_mem j hcj
      have hps := hC.πσ j hcj
      refine ⟨σ j, fun h => ?_, ?_⟩
      · rcases (hmemU (σ j)).mp h with h | ⟨-, -, h⟩
        · exact (hC.mem _ hcs).2 h
        · rw [hps] at h; exact hjf h
      · rw [hon_need (σ j) hcs (by rw [hps]; exact hjf), hps, hj]
  obtain ⟨w, hw⟩ := hC.ne
  exact ⟨transfer hS hle hna, hle, w, (hC.mem w hw).1, hlt w hw⟩

end DE
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE.total_lt
#print axioms EFX.DE.completeDE_completion
#print axioms EFX.DE.soundness
#print axioms EFX.DE.na_of_util
#print axioms EFX.DE.transfer
#print axioms EFX.DE.exchange_scores
#print axioms EFX.DE.exchange
