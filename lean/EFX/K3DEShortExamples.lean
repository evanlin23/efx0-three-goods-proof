import EFX.K3DEShort
import EFX.K3DEExamples

/-!
# Draft and Exchange: the worked example, and the instances of Proposition short

The worked example of `paper/k3-simple/long.tex` §7 (`sec:example`) and the two instances that attain the bounds
of Proposition short (Appendix A, `prop:short`), with the remark after its proof. Every fact about a concrete state is
proved by kernel evaluation (`decide`) of decidable formulations, proved equivalent to (or sound for) the
propositions of `EFX/K3DE.lean`, `EFX/K3DEImprove.lean` and `EFX/K3DEShort.lean`.

**Decision procedures** (any finite instance).
- Instances: `Free` (via `freeB`), `Exposed` (via `expB`), needs `NA` (via `naB`), `PropP`, `InBase`, `Dominates`,
  `EFX0L`; `Valid` and `Cycle` over `Fin n` agents and `Fin m` goods (`valid_iff`, `cycle_iff`: the structures as
  conjunctions of their fields).
- `not_shortMove_of_depth_one`: if no need arc ends where another starts, (P) holds, and no agent exposed for a free
  agent `o` has a need arc to `o`, then no short move applies (a walk of need arcs is then a single arc).
- `no_free_absorber`: under (P), no free agent absorbs iff every free agent `o` has `|H_o| ≥ |F|` (Lemma forced,
  `EFX.DE.absorber_iff`).
- `canonY`, `canonUp`, `canon_of_valid`: a valid state is determined by its utilities (`4` pair, `3` `a`, `2` `b`,
  `1` `c`, `0` nothing): `valid_ext`. This reduces "every valid state that dominates `Y`" to finitely many utility
  vectors.

**The worked example** (§7; agents `x₁, x₁', x₂, x₂', o₁, o₂` are `0, …, 5`, goods `g₀, …, g₉` are `0, …, 9`,
rankings `Pw`, values `4, 3, 2`: `vw`, the instance `EFX.DE.Examples.worked`). The draft state `Yw`
(`w_draft`: the draft of Lemma draft in index order) has `NA = {g₀, g₁, g₂, g₃}`, is valid, `J = {g₆, g₇, g₈, g₉}`,
`F = {o₁, o₂}`, the need arcs `x₁ → o₂`, `x₁' → o₂`, `x₂ → o₁`, `x₂' → o₁` (so `D` has no cycle), (P) holds,
`H_{o₁} = {g₆, g₇}`, `H_{o₂} = {g₈, g₉}`, no free agent absorbs, and no short move applies (`w_facts`). Exactly four
valid states Pareto-dominate `Yw` (`w_exactly_four`): the exchanges along the four cycles `o₁ → x → o₂ → x' → o₁` of
`D⁺` (`w_exchanges`), and no other (`w_dominators`, with `valid_ext`); each gives pairs to exactly two agents. All ten
candidate completions (absorber `o₁` or `o₂`, with `H = ∅` or one leftover good, which goes to the other free agent)
fail EFX₀ (`w_completions`, `w_completions_model`).

**Attainment** (Proposition short, "both bounds `n = 6` and `m = 8` are attained"): `w_attains` (`n = 6`, `m = 10`)
and `s8_attains` (`n = 6`, `m = 8`: rankings `P8`, state `Y8`, values `4, 3, 2` in `short8`) satisfy every hypothesis
of `EFX.DE.prop_short`, with `|F| = 2`.

**The remark after the proof** (`s8_remark`): in the `m = 8` instance the four cycles `o₂ → x → o₁ → x' → o₂` of
`D⁺` (`x ∈ {x₁, x₁'}`, `x' ∈ {x₂, x₂'}`) use two exposure arcs; exactly two have distinct labels, and the exchanges
along them (`exchY`, `exchUp`) are valid states that Pareto-dominate `Y8`; along each of the other two, the shared
label (`g₂` or `g₃`, a junk good) would go to two agents, and the result is not a valid state.

**Choices where the prose leaves room.**
1. The rankings are given explicitly (`Pw`, `P8`); they are the rankings that DE computes from the values
   (`w_rankings`, `s8_rankings`) and consistent with them (`Profile.Consistent`).
2. "Exactly four valid states dominate `Y`" is stated for states as in `EFX/K3DE.lean` (a pick map and a list of pair
   holders, all agents being listed here): every valid dominating state has one of the four utility vectors of the
   exchanges, and a valid state is determined by its utility vector (its picks, and which agents hold their pair).
   The enumeration is over utility vectors, not over the `5⁶` holdings: domination forces utility `3` or `4` on each
   `x` and `1` to `4` on each `o`, so `w_check` decides validity of the `2⁴ · 4² = 256` coded states.
3. The candidate completions are `EFX.DE.completeDE` with absorber `o ∈ {o₁, o₂}` and `H ∈ {∅, {g₆}, …, {g₉}}`; with
   `H = {h}` the good `h` goes to the other free agent (`w_completion_H`). EFX₀ fails for the values `4, 3, 2`, both
   over lists (`EFX0L`) and in the model (`Inst.EFX0` of `EFX.DE.Examples.worked`).
4. The `Decidable` instances of `Valid` and `Cycle` are found with `synthInstance.maxSize` raised to `1024` (their
   conjunctions are large); this is an elaboration limit, not a change to what is checked.
-/

set_option autoImplicit false

namespace EFX
namespace DE

open LB Profile

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Decision procedures -/

instance (P : Profile A G) (agents up : List A) (Y : A → Option G) (k : A) :
    Decidable (Free P agents up Y k) :=
  decidable_of_iff _ freeB_iff

instance (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (o x : A) :
    Decidable (Exposed P agents up Y goods o x) :=
  decidable_of_iff _ expB_iff

instance (P : Profile A G) (agents up : List A) (Y : A → Option G) (g : G) :
    Decidable (P.NA agents (· ∈ up) Y g) :=
  decidable_of_iff _ naB_iff

instance (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) :
    Decidable (PropP P agents up Y goods) :=
  inferInstanceAs (Decidable (∀ x ∈ agents, _))

instance (P : Profile A G) (up : List A) (Y : A → Option G) (w : A) (g : G) : Decidable (InBase P up Y w g) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance (P : Profile A G) (agents : List A) (Y' : A → Option G) (up' : List A) (Y : A → Option G) (up : List A) :
    Decidable (Dominates P agents Y' up' Y up) :=
  inferInstanceAs (Decidable ((∀ i ∈ agents, _) ∧ ∃ i ∈ agents, _))

instance (v : A → G → Nat) (agents : List A) (goods : List G) (X : G → A) : Decidable (EFX0L v agents goods X) :=
  inferInstanceAs (Decidable (∀ i ∈ agents, _))

omit [DecidableEq A] in
/-- `EFX.LB.Valid`, as a conjunction of its fields. -/
theorem valid_iff {P : Profile A G} {agents : List A} {goods : List G} {Y : A → Option G} {up : List A} :
    Valid P agents goods Y up ↔
      (∀ k y, Y k = some y → k ∈ agents ∧ y ∈ goods ∧ P.rank k y < 3) ∧
      (∀ k k' y, Y k = some y → Y k' = some y → k = k') ∧
      (∀ u ∈ up, u ∈ agents) ∧ (∀ u ∈ up, Y u = some (P.b u)) ∧
      (∀ u ∈ up, P.c u ∈ goods ∧ ∀ k, Y k ≠ some (P.c u)) ∧
      (∀ u ∈ up, ∀ u' ∈ up, P.c u = P.c u' → u = u') ∧
      (∀ g ∈ goods, (∀ k, Y k ≠ some g) → (∀ u ∈ up, P.c u ≠ g) → ¬ P.NA agents (· ∈ up) Y g) ∧
      (∀ u ∈ up, ¬ P.NA agents (· ∈ up) Y (P.b u) ∧ ¬ P.NA agents (· ∈ up) Y (P.c u)) :=
  ⟨fun h => ⟨h.pick, h.pick_inj, h.up_mem, h.up_b, h.up_c, h.up_c_inj, h.v1, h.v2⟩,
    fun ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

set_option synthInstance.maxSize 1024 in
instance {n m : Nat} (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (goods : List (Fin m))
    (Y : Fin n → Option (Fin m)) (up : List (Fin n)) : Decidable (Valid P agents goods Y up) :=
  decidable_of_iff _ valid_iff.symm

omit [DecidableEq A] in
/-- `EFX.DE.Cycle`, as a conjunction of its fields. -/
theorem cycle_iff {P : Profile A G} {agents : List A} {goods : List G} {Y : A → Option G} {up : List A}
    {onC : A → Bool} {σ π : A → A} :
    Cycle P agents goods Y up onC σ π ↔
      (∀ w, onC w = true → w ∈ agents ∧ w ∉ up) ∧ (∃ w, onC w = true) ∧
      (∀ z, onC z = true → onC (σ z) = true) ∧ (∀ w, onC w = true → onC (π w) = true) ∧
      (∀ w, onC w = true → σ (π w) = w) ∧ (∀ z, onC z = true → π (σ z) = z) ∧
      (∀ z, onC z = true → ¬ Free P agents up Y z → ∃ y, Y z = some y ∧ P.Prefers Y (σ z) y) ∧
      (∀ z, onC z = true → Free P agents up Y z →
        (P.b (σ z) ∈ junkList P agents up Y goods ∨ Y z = some (P.b (σ z))) ∧
        (P.c (σ z) ∈ junkList P agents up Y goods ∨ Y z = some (P.c (σ z)))) ∧
      (∀ z z', onC z = true → onC z' = true → Free P agents up Y z → Free P agents up Y z' → σ z ≠ σ z' →
        ∀ g ∈ junkList P agents up Y goods, (g = P.b (σ z) ∨ g = P.c (σ z)) →
          (g = P.b (σ z') ∨ g = P.c (σ z')) → False) :=
  ⟨fun h => ⟨h.mem, h.ne, h.σ_mem, h.π_mem, h.σπ, h.πσ, h.need, h.free, h.disj⟩,
    fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩

set_option synthInstance.maxSize 1024 in
instance {n m : Nat} (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (goods : List (Fin m))
    (Y : Fin n → Option (Fin m)) (up : List (Fin n)) (onC : Fin n → Bool) (σ π : Fin n → Fin n) :
    Decidable (Cycle P agents goods Y up onC σ π) :=
  decidable_of_iff _ cycle_iff.symm

variable {P : Profile A G} {agents : List A} {goods : List G} {Y : A → Option G} {up : List A}

omit [DecidableEq A] [DecidableEq G] in
/-- If no arc of `R` ends where another starts, every walk of `R` is a single arc. -/
theorem transGen_of_no_two {R : A → A → Prop} (h : ∀ a b c, R a b → ¬ R b c) {x y : A}
    (hxy : Relation.TransGen R x y) : R x y := by
  induction hxy with
  | single h1 => exact h1
  | tail _ h2 ih => exact absurd h2 (h _ _ _ ih)

/-- **No short move, when `D` has depth one**: if no need arc ends where another starts, (P) holds, and no agent
exposed for a free agent `o` that holds a good has a need arc to `o`, then no short move applies. -/
theorem not_shortMove_of_depth_one (h2 : ∀ a b c, NeedArc P agents up Y a b → ¬ NeedArc P agents up Y b c)
    (hPP : PropP P agents up Y goods)
    (h1 : ∀ o x, Free P agents up Y o → Exposed P agents up Y goods o x → ¬ NeedArc P agents up Y x o) :
    ¬ ShortMove P agents goods Y up := by
  rintro (⟨j, hj⟩ | hpc | ⟨o, x, ho, -, hx, hxo⟩)
  · exact needArc_irrefl (transGen_of_no_two h2 hj)
  · exact pairChain_iff.mp hpc hPP
  · exact h1 o x ho hx (transGen_of_no_two h2 hxo)

/-- **No free absorber** (Lemma forced): under (P), no free agent is a valid absorber iff every free agent `o` has
`|H_o| ≥ |F|`. -/
theorem no_free_absorber (hWF : WF P agents goods) (hag : agents.Nodup) (hPP : PropP P agents up Y goods) :
    (¬ ∃ o H, Free P agents up Y o ∧ Absorber P agents goods Y up o H) ↔
      ∀ o, Free P agents up Y o → nFree P agents up Y ≤ (Hset P agents up Y goods o).length := by
  constructor
  · intro hno o ho
    refine Classical.byContradiction fun hlt => hno ?_
    obtain ⟨H, hA⟩ := (absorber_iff hWF hag hPP ho).mpr (by unfold nFree at hlt; omega)
    exact ⟨o, H, ho, hA⟩
  · rintro h ⟨o, H, ho, hA⟩
    have := (absorber_iff hWF hag hPP ho).mp ⟨H, hA⟩
    have := h o ho
    unfold nFree at this
    omega

/-! ## A valid state is determined by its utilities -/

/-- The holding coded by a utility: `4` the pair (`b` as the pick, `c` through `up`), `3`, `2`, `1` the good `a`,
`b`, `c` alone, `0` nothing. -/
def canonY (P : Profile A G) (u : A → Nat) (i : A) : Option G :=
  if u i = 4 then some (P.b i) else if u i = 3 then some (P.a i) else if u i = 2 then some (P.b i)
  else if u i = 1 then some (P.c i) else none

/-- The pair holders coded by a utility vector. -/
def canonUp (agents : List A) (u : A → Nat) : List A :=
  agents.filter (fun i => u i == 4)

/-- **A valid state is coded by its utilities**: the pick of every agent is `canonY` of the utilities, and an agent
is a pair holder iff its utility is `4`. -/
theorem canon_of_valid (hV : Valid P agents goods Y up) (i : A) :
    Y i = canonY P (util P up Y) i ∧ (i ∈ up ↔ util P up Y i = 4) := by
  by_cases hiu : i ∈ up
  · have hu : util P up Y i = 4 := by simp [util, hiu]
    refine ⟨?_, by simp [hiu, hu]⟩
    rw [hV.up_b i hiu]
    simp [canonY, hu]
  · have hpr := pickRank_le (P := P) Y i
    have hu : util P up Y i = 3 - P.pickRank Y i := by simp [util, hiu]
    refine ⟨?_, ⟨fun h => absurd h hiu, fun h => by omega⟩⟩
    cases hY : Y i with
    | none =>
      have h3 : P.pickRank Y i = 3 := by simp [Profile.pickRank, hY]
      simp [canonY, hu, h3]
    | some y =>
      have hr := (hV.pick i y hY).2.2
      have hpr' : P.pickRank Y i = P.rank i y := by simp [Profile.pickRank, hY]
      rw [hpr'] at hu
      unfold Profile.rank at hr hu
      by_cases ha : y = P.a i
      · subst ha; simp [canonY, hu]
      · by_cases hb : y = P.b i
        · subst hb; simp [canonY, hu, ha]
        · by_cases hc : y = P.c i
          · subst hc; simp [canonY, hu, ha, hb]
          · simp [ha, hb, hc] at hr

/-- **Valid states with the same utilities are the same state** (on the listed agents: the same picks, and the same
pair holders). -/
theorem valid_ext {Y' : A → Option G} {up' : List A} (hV : Valid P agents goods Y up)
    (hV' : Valid P agents goods Y' up') (h : ∀ i ∈ agents, util P up Y i = util P up' Y' i) :
    ∀ i ∈ agents, Y i = Y' i ∧ (i ∈ up ↔ i ∈ up') := by
  intro i hi
  obtain ⟨h1, h2⟩ := canon_of_valid hV i
  obtain ⟨h1', h2'⟩ := canon_of_valid hV' i
  refine ⟨?_, by rw [h2, h2', h i hi]⟩
  rw [h1, h1']
  unfold canonY
  rw [h i hi]

omit [DecidableEq A] in
/-- Validity depends on the pair holders only through membership. -/
theorem valid_congr_up {up' : List A} (h : ∀ k, k ∈ up ↔ k ∈ up') (hV : Valid P agents goods Y up) :
    Valid P agents goods Y up' := by
  have e : (fun k => k ∈ up) = (fun k => k ∈ up') := funext fun k => propext (h k)
  refine ⟨hV.pick, hV.pick_inj, fun u hu => hV.up_mem u ((h u).mpr hu), fun u hu => hV.up_b u ((h u).mpr hu),
    fun u hu => hV.up_c u ((h u).mpr hu),
    fun u hu u' hu' => hV.up_c_inj u ((h u).mpr hu) u' ((h u').mpr hu'), fun g hg hp hu => ?_, fun u hu => ?_⟩
  · have := hV.v1 g hg hp (fun u hu' => hu u ((h u).mp hu'))
    rwa [e] at this
  · have := hV.v2 u ((h u).mpr hu)
    rwa [e] at this

/-! ## Cycles of four agents -/

/-- The agents of the cycle `w₀ → w₁ → w₂ → w₃ → w₀`. -/
def cOn (w0 w1 w2 w3 : A) (w : A) : Bool := w == w0 || w == w1 || w == w2 || w == w3

/-- The successor map of the cycle `w₀ → w₁ → w₂ → w₃ → w₀` (the identity off the cycle). -/
def cSucc (w0 w1 w2 w3 : A) (w : A) : A :=
  if w = w0 then w1 else if w = w1 then w2 else if w = w2 then w3 else if w = w3 then w0 else w

/-- The predecessor map of the cycle `w₀ → w₁ → w₂ → w₃ → w₀` (the identity off the cycle). -/
def cPred (w0 w1 w2 w3 : A) (w : A) : A :=
  if w = w1 then w0 else if w = w2 then w1 else if w = w3 then w2 else if w = w0 then w3 else w

namespace ShortExamples

/-- A vector of six utilities. -/
def vec6 (u0 u1 u2 u3 u4 u5 : Nat) (i : Fin 6) : Nat := [u0, u1, u2, u3, u4, u5].getD i.val 0

/-- A utility vector of six agents is the `vec6` of its values. -/
theorem fin6_eta (u : Fin 6 → Nat) : u = vec6 (u 0) (u 1) (u 2) (u 3) (u 4) (u 5) := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨k + 6, h⟩ => exact absurd h (by omega)

/-! ## The worked example (§7) -/

/-- The agents `x₁, x₁', x₂, x₂', o₁, o₂` (`0` to `5`). -/
def ag : List (Fin 6) := List.finRange 6

/-- The goods `g₀, …, g₉`. -/
def gw : List (Fin 10) := List.finRange 10

/-- The rankings of §7: `x₁` `g₀ ≻ g₄ ≻ g₆`, `x₁'` `g₁ ≻ g₄ ≻ g₇`, `x₂` `g₂ ≻ g₅ ≻ g₈`, `x₂'` `g₃ ≻ g₅ ≻ g₉`,
`o₁` `g₂ ≻ g₃ ≻ g₄`, `o₂` `g₀ ≻ g₁ ≻ g₅`. -/
def Pw : Profile (Fin 6) (Fin 10) where
  a := fun i => ([0, 1, 2, 3, 2, 0] : List (Fin 10)).getD i.val 0
  b := fun i => ([4, 4, 5, 5, 3, 1] : List (Fin 10)).getD i.val 0
  c := fun i => ([6, 7, 8, 9, 4, 5] : List (Fin 10)).getD i.val 0

/-- The draft state: the `x`'s hold their tops, `o₁` holds `g₄`, `o₂` holds `g₅`. -/
def Yw (i : Fin 6) : Option (Fin 10) :=
  ([some 0, some 1, some 2, some 3, some 4, some 5] : List (Option (Fin 10))).getD i.val none

/-- The values `4, 3, 2` (`EFX.DE.Examples.worked`). -/
def vw : Fin 6 → Fin 10 → Nat := Examples.worked.v

/-- The rankings are the ones DE computes from the values, and they are consistent with the values. -/
theorem w_rankings : (∀ i, (K3.profileOf vw gw 0).a i = Pw.a i ∧ (K3.profileOf vw gw 0).b i = Pw.b i ∧
      (K3.profileOf vw gw 0).c i = Pw.c i) ∧ Pw.Consistent ag vw := by
  unfold Profile.Consistent
  decide

/-- Each agent's three goods are distinct goods. -/
theorem w_wf : WF Pw ag gw := by unfold WF; decide

/-- `Yw` is the draft (Lemma draft) in index order. -/
theorem w_draft : phase1 Pw ag gw = Yw := funext (by decide)

/-- The draft state is valid (Lemma draft). -/
theorem w_valid : Valid Pw ag gw Yw [] := w_draft ▸ draft_valid (List.nodup_finRange 6) (List.nodup_finRange 10)

/-- No short move applies to the draft state: every need arc ends at `o₁` or `o₂`, which have none. -/
theorem w_noShort : ¬ ShortMove Pw ag gw Yw [] :=
  not_shortMove_of_depth_one (by decide) (by decide) (by decide)

/-- No free agent absorbs: `|H_{o₁}| = |H_{o₂}| = 2 = |F|` (Lemma forced). -/
theorem w_noAbsorber : ¬ ∃ o H, Free Pw ag [] Yw o ∧ Absorber Pw ag gw Yw [] o H :=
  (no_free_absorber w_wf (List.nodup_finRange 6) (by decide)).mpr (by decide)

/-- **The facts of §7 about the draft state.** `NA = {g₀, g₁, g₂, g₃}`; `J = {g₆, g₇, g₈, g₉}`;
`F = {o₁, o₂}`; the need arcs are `x₁ → o₂`, `x₁' → o₂`, `x₂ → o₁`, `x₂' → o₁`, and `D` has no cycle; (P) holds;
`E_{o₁} = {x₁, x₁'}`, `E_{o₂} = {x₂, x₂'}`, `H_{o₁} = {g₆, g₇}`, `H_{o₂} = {g₈, g₉}`; no free agent absorbs; no short
move applies. -/
theorem w_facts :
    (∀ g, Pw.NA ag (· ∈ ([] : List (Fin 6))) Yw g ↔ g ∈ ([0, 1, 2, 3] : List (Fin 10))) ∧
      junkList Pw ag [] Yw gw = [6, 7, 8, 9] ∧
      (∀ k, Free Pw ag [] Yw k ↔ k ∈ ([4, 5] : List (Fin 6))) ∧
      (∀ j j', NeedArc Pw ag [] Yw j j' ↔ (j, j') ∈ ([(0, 5), (1, 5), (2, 4), (3, 4)] : List (Fin 6 × Fin 6))) ∧
      ¬ HasNeedCycle Pw ag [] Yw ∧ PropP Pw ag [] Yw gw ∧
      Eset Pw ag [] Yw gw 4 = [0, 1] ∧ Eset Pw ag [] Yw gw 5 = [2, 3] ∧
      Hset Pw ag [] Yw gw 4 = [6, 7] ∧ Hset Pw ag [] Yw gw 5 = [8, 9] ∧
      (¬ ∃ o H, Free Pw ag [] Yw o ∧ Absorber Pw ag gw Yw [] o H) ∧ ¬ ShortMove Pw ag gw Yw [] :=
  ⟨by decide, by decide, by decide, by decide, fun h => w_noShort (Or.inl h), by decide, by decide, by decide,
    by decide, by decide, w_noAbsorber, w_noShort⟩

/-- **Attainment, `n = 6`** (`m = 10`): the draft state of §7 satisfies every hypothesis of Proposition short
(`EFX.DE.prop_short`), with `|F| = 2`. -/
theorem w_attains :
    WF Pw ag gw ∧ Valid Pw ag gw Yw [] ∧ ag.Nodup ∧ gw.Nodup ∧
      (¬ ∃ o H, Free Pw ag [] Yw o ∧ Absorber Pw ag gw Yw [] o H) ∧ (∃ i ∈ ag, i ∉ ([] : List (Fin 6))) ∧
      ¬ ShortMove Pw ag gw Yw [] ∧ ag.length = 6 ∧ gw.length = 10 ∧ nFree Pw ag [] Yw = 2 :=
  ⟨w_wf, w_valid, List.nodup_finRange 6, List.nodup_finRange 10, w_noAbsorber, ⟨0, by decide, by simp⟩, w_noShort,
    by decide, by decide, by decide⟩

/-- The utility vectors of the four valid states that dominate the draft state (agents `x₁, x₁', x₂, x₂', o₁, o₂`). -/
def wVecs : List (List Nat) := [[4, 3, 4, 3, 3, 3], [4, 3, 3, 4, 2, 3], [3, 4, 4, 3, 3, 2], [3, 4, 3, 4, 2, 2]]

/-- The four cycles `o₁ → x → o₂ → x' → o₁` of `D⁺` (`x ∈ {x₁, x₁'}`, `x' ∈ {x₂, x₂'}`). -/
def wCycles : List (Fin 6 × Fin 6) := [(0, 2), (0, 3), (1, 2), (1, 3)]

/-- **The four exchanges** (Figure "exchange digraph"): each cycle `o₁ → x → o₂ → x' → o₁` is an exchange cycle
(`EFX.DE.Cycle`: two exposure arcs with distinct labels, two need arcs); the exchanges along them are valid states
that Pareto-dominate the draft state, with the utility vectors `wVecs`, and each gives pairs to exactly two agents
(`x` and `x'`). -/
theorem w_exchanges :
    (∀ p ∈ wCycles, Cycle Pw ag gw Yw [] (cOn 4 p.1 5 p.2) (cSucc 4 p.1 5 p.2) (cPred 4 p.1 5 p.2)) ∧
      (∀ p ∈ wCycles,
        Valid Pw ag gw (exchY Pw ag [] Yw (cOn 4 p.1 5 p.2) (cPred 4 p.1 5 p.2))
          (exchUp Pw ag [] Yw (cOn 4 p.1 5 p.2) (cPred 4 p.1 5 p.2)) ∧
        Dominates Pw ag (exchY Pw ag [] Yw (cOn 4 p.1 5 p.2) (cPred 4 p.1 5 p.2))
          (exchUp Pw ag [] Yw (cOn 4 p.1 5 p.2) (cPred 4 p.1 5 p.2)) Yw [] ∧
        exchUp Pw ag [] Yw (cOn 4 p.1 5 p.2) (cPred 4 p.1 5 p.2) = [p.1, p.2]) ∧
      wCycles.map (fun p => ag.map (util Pw (exchUp Pw ag [] Yw (cOn 4 p.1 5 p.2) (cPred 4 p.1 5 p.2))
        (exchY Pw ag [] Yw (cOn 4 p.1 5 p.2) (cPred 4 p.1 5 p.2)))) = wVecs := by
  have hC : ∀ p ∈ wCycles, Cycle Pw ag gw Yw [] (cOn 4 p.1 5 p.2) (cSucc 4 p.1 5 p.2) (cPred 4 p.1 5 p.2) := by
    decide
  refine ⟨hC, fun p hp => ?_, by decide⟩
  obtain ⟨h1, h2⟩ := exchange w_valid w_wf (hC p hp)
  refine ⟨h1, h2, ?_⟩
  revert p
  decide

/-- The finite check behind `w_dominators`: among the utility vectors that weakly dominate the draft state, the valid
coded states are the draft state and the four exchanges. -/
theorem w_check : ∀ u0 ∈ [3, 4], ∀ u1 ∈ [3, 4], ∀ u2 ∈ [3, 4], ∀ u3 ∈ [3, 4], ∀ u4 ∈ [1, 2, 3, 4],
    ∀ u5 ∈ [1, 2, 3, 4],
    Valid Pw ag gw (canonY Pw (vec6 u0 u1 u2 u3 u4 u5)) (canonUp ag (vec6 u0 u1 u2 u3 u4 u5)) →
      [u0, u1, u2, u3, u4, u5] ∈ wVecs ∨ [u0, u1, u2, u3, u4, u5] = [3, 3, 3, 3, 1, 1] := by
  decide

/-- **Exactly four valid states dominate the draft state** (§7, "exhaustive listing"): every valid state that
Pareto-dominates `Yw` has the utility vector of one of the four exchanges (`w_exchanges`), so by `valid_ext` it is one
of them; each gives pairs to exactly two agents. -/
theorem w_dominators (Y' : Fin 6 → Option (Fin 10)) (up' : List (Fin 6)) (hV : Valid Pw ag gw Y' up')
    (hD : Dominates Pw ag Y' up' Yw []) :
    [util Pw up' Y' 0, util Pw up' Y' 1, util Pw up' Y' 2, util Pw up' Y' 3, util Pw up' Y' 4, util Pw up' Y' 5] ∈
      wVecs := by
  have hc : ∀ i, Y' i = canonY Pw (util Pw up' Y') i ∧ (i ∈ up' ↔ util Pw up' Y' i = 4) :=
    fun i => canon_of_valid hV i
  have hb : ∀ i, util Pw [] Yw i ≤ util Pw up' Y' i := fun i => hD.1 i (List.mem_finRange i)
  have hle : ∀ i, util Pw up' Y' i ≤ 4 := fun i => util_le i
  obtain ⟨i0, -, hlt⟩ := hD.2
  generalize util Pw up' Y' = u at hc hb hle hlt ⊢
  have hY : Y' = canonY Pw u := funext fun i => (hc i).1
  subst hY
  have hV2 : Valid Pw ag gw (canonY Pw u) (canonUp ag u) :=
    valid_congr_up (fun k => by
      simp only [canonUp, List.mem_filter, beq_iff_eq, (hc k).2]
      exact ⟨fun h => ⟨List.mem_finRange k, h⟩, fun h => h.2⟩) hV
  have hw : ∀ i, util Pw [] Yw i = [3, 3, 3, 3, 1, 1].getD i.val 0 := by decide
  have hb' : ∀ i, [3, 3, 3, 3, 1, 1].getD i.val 0 ≤ u i := fun i => (hw i) ▸ hb i
  rw [fin6_eta u] at hV2 hlt
  have m3 : ∀ i : Fin 6, 3 ≤ u i → u i ∈ [3, 4] := fun i h => by
    have := hle i; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
  have m1 : ∀ i : Fin 6, 1 ≤ u i → u i ∈ [1, 2, 3, 4] := fun i h => by
    have := hle i; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
  rcases w_check _ (m3 0 (hb' 0)) _ (m3 1 (hb' 1)) _ (m3 2 (hb' 2)) _ (m3 3 (hb' 3)) _ (m1 4 (hb' 4)) _
    (m1 5 (hb' 5)) hV2 with h | h
  · exact h
  · exfalso
    simp only [List.cons.injEq, and_true] at h
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := h
    rw [e0, e1, e2, e3, e4, e5, hw] at hlt
    revert hlt i0
    decide

/-- Each utility vector of `wVecs` is that of the exchange along a cycle of `wCycles`. -/
theorem w_vecs_cycles : ∀ l ∈ wVecs, ∃ p ∈ wCycles, ∀ i : Fin 6,
    util Pw (exchUp Pw ag [] Yw (cOn 4 p.1 5 p.2) (cPred 4 p.1 5 p.2))
      (exchY Pw ag [] Yw (cOn 4 p.1 5 p.2) (cPred 4 p.1 5 p.2)) i = l.getD i.val 0 := by
  decide

/-- **Exactly four valid states Pareto-dominate the draft state** (§7): every valid state that dominates `Yw` is
the exchange along one of the four cycles `o₁ → x → o₂ → x' → o₁` (the same picks and the same pair holders), and
these four states are different (their utility vectors differ). Each gives pairs to exactly two agents
(`w_exchanges`). -/
theorem w_exactly_four : wVecs.Nodup ∧
    ∀ (Y' : Fin 6 → Option (Fin 10)) (up' : List (Fin 6)), Valid Pw ag gw Y' up' → Dominates Pw ag Y' up' Yw [] →
      ∃ p ∈ wCycles, ∀ i, Y' i = exchY Pw ag [] Yw (cOn 4 p.1 5 p.2) (cPred 4 p.1 5 p.2) i ∧
        (i ∈ up' ↔ i ∈ exchUp Pw ag [] Yw (cOn 4 p.1 5 p.2) (cPred 4 p.1 5 p.2)) := by
  refine ⟨by decide, fun Y' up' hV hD => ?_⟩
  obtain ⟨p, hp, hu⟩ := w_vecs_cycles _ (w_dominators Y' up' hV hD)
  refine ⟨p, hp, fun i => ?_⟩
  have hU : ∀ j ∈ ag, util Pw (exchUp Pw ag [] Yw (cOn 4 p.1 5 p.2) (cPred 4 p.1 5 p.2))
      (exchY Pw ag [] Yw (cOn 4 p.1 5 p.2) (cPred 4 p.1 5 p.2)) j = util Pw up' Y' j :=
    fun j _ => (hu j).trans (congrFun (fin6_eta (util Pw up' Y')) j).symm
  have h := valid_ext (w_exchanges.2.1 p hp).1 hV hU i (List.mem_finRange i)
  exact ⟨h.1.symm, h.2.symm⟩

/-- **The ten candidate completions fail EFX₀** (§7): with absorber `o₁` or `o₂` and `H = ∅` or one leftover good,
the completion `completeDE` is not EFX₀ for the values `4, 3, 2`. -/
theorem w_completions : ∀ o ∈ ([4, 5] : List (Fin 6)), ∀ H ∈ ([[], [6], [7], [8], [9]] : List (List (Fin 10))),
    ¬ EFX0L vw ag gw (completeDE Pw ag [] Yw o H) := by
  decide

/-- The same, in the model: `Inst.EFX0` of `EFX.DE.Examples.worked`. -/
theorem w_completions_model : ∀ o ∈ ([4, 5] : List (Fin 6)), ∀ H ∈ ([[], [6], [7], [8], [9]] : List (List (Fin 10))),
    ¬ Examples.worked.EFX0 (completeDE Pw ag [] Yw o H) :=
  fun o ho H hH h => w_completions o ho H hH ((Inst.efx0_iff Examples.worked _).mp h)

/-- In these completions the leftover good of `H` goes to the other free agent, and the rest of the junk to the
absorber; e.g. with absorber `o₁` and `H = {g₆}`, `X_{o₁} = {g₄, g₇, g₈, g₉}` (the paper's "concretely"). -/
theorem w_completion_H : (∀ h ∈ ([6, 7, 8, 9] : List (Fin 10)), completeDE Pw ag [] Yw 4 [h] h = 5 ∧
      completeDE Pw ag [] Yw 5 [h] h = 4) ∧
    bundle gw (completeDE Pw ag [] Yw 4 [6]) 4 = [4, 7, 8, 9] := by
  decide


/-! ## The instance with `n = 6` and `m = 8` (Proposition short, attainment) -/

/-- The goods `g₀, …, g₇`. -/
def g8 : List (Fin 8) := List.finRange 8

/-- The rankings of the `m = 8` instance (agents `x₁, x₁', x₂, x₂', o₁, o₂` are `0, …, 5`): `x₁` `g₄ ≻ g₁ ≻ g₂`,
`x₁'` `g₅ ≻ g₃ ≻ g₁`, `x₂` `g₆ ≻ g₀ ≻ g₂`, `x₂'` `g₇ ≻ g₃ ≻ g₀`, `o₁` `g₄ ≻ g₅ ≻ g₀`, `o₂` `g₆ ≻ g₇ ≻ g₁`. -/
def P8 : Profile (Fin 6) (Fin 8) where
  a := fun i => ([4, 5, 6, 7, 4, 6] : List (Fin 8)).getD i.val 0
  b := fun i => ([1, 3, 0, 3, 5, 7] : List (Fin 8)).getD i.val 0
  c := fun i => ([2, 1, 2, 0, 0, 1] : List (Fin 8)).getD i.val 0

/-- The state: `o₁` holds `g₀`, `o₂` holds `g₁`, every `x` holds its top. -/
def Y8 (i : Fin 6) : Option (Fin 8) :=
  ([some 4, some 5, some 6, some 7, some 0, some 1] : List (Option (Fin 8))).getD i.val none

/-- The `m = 8` instance with values `4, 3, 2` for each agent's `a`, `b`, `c`. -/
def short8 : Inst := Examples.mkInst 6 8
  [[0, 3, 2, 0, 4, 0, 0, 0], [0, 2, 0, 3, 0, 4, 0, 0], [3, 0, 2, 0, 0, 0, 4, 0], [2, 0, 0, 3, 0, 0, 0, 4],
   [2, 0, 0, 0, 4, 3, 0, 0], [0, 2, 0, 0, 0, 0, 4, 3]]

/-- The values of `short8`. -/
def v8 : Fin 6 → Fin 8 → Nat := short8.v

/-- The rankings are the ones DE computes from the values, and they are consistent with the values; every agent
values exactly three goods. -/
theorem s8_rankings : (∀ i, (K3.profileOf v8 g8 0).a i = P8.a i ∧ (K3.profileOf v8 g8 0).b i = P8.b i ∧
      (K3.profileOf v8 g8 0).c i = P8.c i) ∧ P8.Consistent ag v8 ∧ ∀ i, numRelevant short8 i = 3 := by
  unfold Profile.Consistent
  decide

/-- Each agent's three goods are distinct goods. -/
theorem s8_wf : WF P8 ag g8 := by unfold WF; decide

/-- `Y8` is the draft (Lemma draft) in index order. -/
theorem s8_draft : phase1 P8 ag g8 = Y8 := funext (by decide)

/-- The state is valid (Lemma draft). -/
theorem s8_valid : Valid P8 ag g8 Y8 [] := s8_draft ▸ draft_valid (List.nodup_finRange 6) (List.nodup_finRange 8)

/-- No short move applies: every need arc ends at `o₁` or `o₂`, which have none. -/
theorem s8_noShort : ¬ ShortMove P8 ag g8 Y8 [] :=
  not_shortMove_of_depth_one (by decide) (by decide) (by decide)

/-- No free agent absorbs: `|H_{o₁}| = |H_{o₂}| = 2 = |F|` (Lemma forced). -/
theorem s8_noAbsorber : ¬ ∃ o H, Free P8 ag [] Y8 o ∧ Absorber P8 ag g8 Y8 [] o H :=
  (no_free_absorber s8_wf (List.nodup_finRange 6) (by decide)).mpr (by decide)

/-- **The facts of the `m = 8` instance.** `NA = {g₄, g₅, g₆, g₇}`; `J = {g₂, g₃}`; `F = {o₁, o₂}`; the need arcs
are `x₁ → o₁`, `x₁' → o₁`, `x₂ → o₂`, `x₂' → o₂`; `E_{o₂} = {x₁, x₁'}` and `E_{o₁} = {x₂, x₂'}`, both with protecting
goods `g₂, g₃`. -/
theorem s8_facts :
    (∀ g, P8.NA ag (· ∈ ([] : List (Fin 6))) Y8 g ↔ g ∈ ([4, 5, 6, 7] : List (Fin 8))) ∧
      junkList P8 ag [] Y8 g8 = [2, 3] ∧
      (∀ k, Free P8 ag [] Y8 k ↔ k ∈ ([4, 5] : List (Fin 6))) ∧
      (∀ j j', NeedArc P8 ag [] Y8 j j' ↔ (j, j') ∈ ([(0, 4), (1, 4), (2, 5), (3, 5)] : List (Fin 6 × Fin 6))) ∧
      Eset P8 ag [] Y8 g8 5 = [0, 1] ∧ Eset P8 ag [] Y8 g8 4 = [2, 3] ∧
      (Eset P8 ag [] Y8 g8 5).map (hOf P8 ag [] Y8 g8) = [2, 3] ∧
      (Eset P8 ag [] Y8 g8 4).map (hOf P8 ag [] Y8 g8) = [2, 3] ∧
      Hset P8 ag [] Y8 g8 5 = [2, 3] ∧ Hset P8 ag [] Y8 g8 4 = [2, 3] := by
  decide

/-- **Attainment, `n = 6` and `m = 8`** (Proposition short): the state `Y8` satisfies every hypothesis of
`EFX.DE.prop_short`, with `|F| = 2`; so both bounds `n ≥ 6` and `m ≥ 8` are attained. -/
theorem s8_attains :
    WF P8 ag g8 ∧ Valid P8 ag g8 Y8 [] ∧ ag.Nodup ∧ g8.Nodup ∧
      (¬ ∃ o H, Free P8 ag [] Y8 o ∧ Absorber P8 ag g8 Y8 [] o H) ∧ (∃ i ∈ ag, i ∉ ([] : List (Fin 6))) ∧
      ¬ ShortMove P8 ag g8 Y8 [] ∧ ag.length = 6 ∧ g8.length = 8 ∧ nFree P8 ag [] Y8 = 2 :=
  ⟨s8_wf, s8_valid, List.nodup_finRange 6, List.nodup_finRange 8, s8_noAbsorber, ⟨0, by decide, by simp⟩,
    s8_noShort, by decide, by decide, by decide⟩

/-- The four cycles `o₂ → x → o₁ → x' → o₂` of `D⁺` (`x ∈ {x₁, x₁'}`, `x' ∈ {x₂, x₂'}`), as pairs `(x, x')`. -/
def s8Cycles : List (Fin 6 × Fin 6) := [(0, 2), (0, 3), (1, 2), (1, 3)]

/-- **The remark after the proof of Proposition short.** In the `m = 8` instance:
1. each `(x, x')` of `s8Cycles` gives a cycle `o₂ → x → o₁ → x' → o₂` of `D⁺` with two exposure arcs (`o₂`, `o₁` are
   free and hold a good, `x` is exposed for `o₂`, `x'` for `o₁`) and two need arcs;
2. its labels `(h_x, h_{x'})` are `(g₂, g₂)`, `(g₂, g₃)`, `(g₃, g₂)`, `(g₃, g₃)`: exactly two cycles have distinct
   labels;
3. the exchanges along those two are valid states that Pareto-dominate `Y8` (they are exchange cycles, and
   `EFX.DE.exchange` applies);
4. along each of the other two, the shared label, a junk good, would go to both `x` and `x'` (it is in both their
   holdings after the exchange), so the result is not a valid state, and the cycle is not an exchange cycle. -/
theorem s8_remark :
    (∀ p ∈ s8Cycles, Free P8 ag [] Y8 5 ∧ Free P8 ag [] Y8 4 ∧ (∃ y, Y8 5 = some y) ∧ (∃ y, Y8 4 = some y) ∧
      Exposed P8 ag [] Y8 g8 5 p.1 ∧ NeedArc P8 ag [] Y8 p.1 4 ∧ Exposed P8 ag [] Y8 g8 4 p.2 ∧
      NeedArc P8 ag [] Y8 p.2 5) ∧
    s8Cycles.map (fun p => (hOf P8 ag [] Y8 g8 p.1, hOf P8 ag [] Y8 g8 p.2)) = [(2, 2), (2, 3), (3, 2), (3, 3)] ∧
    (∀ p ∈ s8Cycles, hOf P8 ag [] Y8 g8 p.1 ≠ hOf P8 ag [] Y8 g8 p.2 ↔ p ∈ ([(0, 3), (1, 2)] : List (Fin 6 × Fin 6))) ∧
    (∀ p ∈ ([(0, 3), (1, 2)] : List (Fin 6 × Fin 6)),
      Valid P8 ag g8 (exchY P8 ag [] Y8 (cOn 5 p.1 4 p.2) (cPred 5 p.1 4 p.2))
        (exchUp P8 ag [] Y8 (cOn 5 p.1 4 p.2) (cPred 5 p.1 4 p.2)) ∧
      Dominates P8 ag (exchY P8 ag [] Y8 (cOn 5 p.1 4 p.2) (cPred 5 p.1 4 p.2))
        (exchUp P8 ag [] Y8 (cOn 5 p.1 4 p.2) (cPred 5 p.1 4 p.2)) Y8 []) ∧
    (∀ p ∈ ([(0, 2), (1, 3)] : List (Fin 6 × Fin 6)),
      hOf P8 ag [] Y8 g8 p.1 ∈ junkList P8 ag [] Y8 g8 ∧
      InBase P8 (exchUp P8 ag [] Y8 (cOn 5 p.1 4 p.2) (cPred 5 p.1 4 p.2))
        (exchY P8 ag [] Y8 (cOn 5 p.1 4 p.2) (cPred 5 p.1 4 p.2)) p.1 (hOf P8 ag [] Y8 g8 p.1) ∧
      InBase P8 (exchUp P8 ag [] Y8 (cOn 5 p.1 4 p.2) (cPred 5 p.1 4 p.2))
        (exchY P8 ag [] Y8 (cOn 5 p.1 4 p.2) (cPred 5 p.1 4 p.2)) p.2 (hOf P8 ag [] Y8 g8 p.1) ∧
      ¬ Valid P8 ag g8 (exchY P8 ag [] Y8 (cOn 5 p.1 4 p.2) (cPred 5 p.1 4 p.2))
        (exchUp P8 ag [] Y8 (cOn 5 p.1 4 p.2) (cPred 5 p.1 4 p.2)) ∧
      ¬ Cycle P8 ag g8 Y8 [] (cOn 5 p.1 4 p.2) (cSucc 5 p.1 4 p.2) (cPred 5 p.1 4 p.2)) := by
  have hC : ∀ p ∈ ([(0, 3), (1, 2)] : List (Fin 6 × Fin 6)),
      Cycle P8 ag g8 Y8 [] (cOn 5 p.1 4 p.2) (cSucc 5 p.1 4 p.2) (cPred 5 p.1 4 p.2) := by
    decide
  exact ⟨by decide, by decide, by decide, fun p hp => exchange s8_valid s8_wf (hC p hp), by decide⟩

end ShortExamples
end DE
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE.valid_iff
#print axioms EFX.DE.cycle_iff
#print axioms EFX.DE.transGen_of_no_two
#print axioms EFX.DE.not_shortMove_of_depth_one
#print axioms EFX.DE.no_free_absorber
#print axioms EFX.DE.canon_of_valid
#print axioms EFX.DE.valid_ext
#print axioms EFX.DE.valid_congr_up
#print axioms EFX.DE.ShortExamples.w_rankings
#print axioms EFX.DE.ShortExamples.w_draft
#print axioms EFX.DE.ShortExamples.w_valid
#print axioms EFX.DE.ShortExamples.w_facts
#print axioms EFX.DE.ShortExamples.w_attains
#print axioms EFX.DE.ShortExamples.w_exchanges
#print axioms EFX.DE.ShortExamples.w_check
#print axioms EFX.DE.ShortExamples.w_dominators
#print axioms EFX.DE.ShortExamples.w_vecs_cycles
#print axioms EFX.DE.ShortExamples.w_exactly_four
#print axioms EFX.DE.ShortExamples.w_completions
#print axioms EFX.DE.ShortExamples.w_completions_model
#print axioms EFX.DE.ShortExamples.w_completion_H
#print axioms EFX.DE.ShortExamples.s8_rankings
#print axioms EFX.DE.ShortExamples.s8_facts
#print axioms EFX.DE.ShortExamples.s8_attains
#print axioms EFX.DE.ShortExamples.s8_remark
