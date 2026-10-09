import EFX.K3DEShortExamples
import EFX.K3DERings

/-!
# Draft and Exchange: two small examples of the paper (ledger K3S.EX.LEAN)

Two statements of `paper/k3-simple/long.tex` about concrete instances, checked by kernel evaluation (`decide`) with the
decision procedures of `EFX/K3DEShortExamples.lean`.

- **Example "EFX, but not EFX₀"** (§1, `ex:efx-vs-efx0`): two agents and goods `a, b, c`; agent 1 values `a, b, c`
  at `3, 2, 0`, agent 2 values only `c`, at `1` (here agents `0`, `1` and goods `0, 1, 2`). The allocation
  `X₁ = {b}`, `X₂ = {a, c}` is EFX (`EFX`: only goods the envier values positively may be removed) but not EFX₀,
  and `X₁ = {a}`, `X₂ = {b, c}` is EFX₀ (`efx_not_efx0`). EFX₀ implies EFX (`efx_of_efx0`).
- **Remark "The protecting goods cannot be dropped"** (a remark of the earlier version of the paper, after Corollary
  `cor:po`; it is no longer in the paper and is kept here): two agents ranking
  `g₀ ≻ g₁ ≻ g₂` and `g₁ ≻ g₀ ≻ g₂`, each holding its top. The state is valid, both agents are free, `J = {g₂}`, and
  each agent is exposed for the other (`pg_facts`); no valid state Pareto-dominates it (`pg_undominated`, through the
  utility code of `EFX.DE.canon_of_valid`); every valid absorber has `H = {g₂}` (`pg_only_g2`), and both agents
  absorb with it (`pg_absorbers`).
- **The worked example's remaining numbers** (§7, with `EFX/K3DEShortExamples.lean`): with `H = {g₆}` and absorber
  `o₁`, `X_{o₁} = {g₄, g₇, g₈, g₉}`, which `x₁'` values at `5` without `g₈`, more than its `4` (`w_detail`); every
  cycle of the exchange digraph `D⁺` of the draft state has four agents and two exposure arcs (`w_cycles`, the
  Figure's caption; cycles as in `EFX.DE.Rings.DCycle`); DE's step moves along `o₁ → x₁ → o₂ → x₂ → o₁` (`w_step`);
  the sum of utilities rises from `14` to `20` (`w_totals`); in the new state nobody needs a good, `J = {g₇, g₉}`, the
  free agents are `x₁', x₂', o₁, o₂`, nobody is exposed for `x₁'`, and DE's next step stops with absorber `x₁'` and
  `H = ∅` (`w_after`).
-/

set_option autoImplicit false

namespace EFX
namespace DE
namespace Remarks

open LB Profile

/-! ## EFX, but not EFX₀ -/

/-- **Ordinary EFX** in the model: as `EFX.Inst.EFX0`, but only goods that the envier values positively may be
removed. -/
def EFX (I : Inst) (X : I.Alloc) : Prop :=
  ∀ i j : Fin I.n, i ≠ j → ∀ g : Fin I.m, X g = j → 0 < I.v i g →
    I.bundleVal X i j (some g) ≤ I.bundleVal X i i none

instance (I : Inst) (X : I.Alloc) : Decidable (EFX I X) := by
  unfold EFX; infer_instance

/-- EFX₀ implies EFX. -/
theorem efx_of_efx0 (I : Inst) (X : I.Alloc) (h : I.EFX0 X) : EFX I X :=
  fun i j hij g hg _ => h i j hij g hg

/-- The instance of the example: agent `0` values goods `0, 1, 2` at `3, 2, 0`; agent `1` values only good `2`, at
`1`. -/
abbrev exI : Inst := ⟨2, 3, fun i g => ([[3, 2, 0], [0, 0, 1]].getD i.val []).getD g.val 0⟩

/-- `X₁ = {b}`, `X₂ = {a, c}`. -/
def exX : exI.Alloc := fun g => if g.val = 1 then 0 else 1

/-- `X₁ = {a}`, `X₂ = {b, c}`. -/
def exX' : exI.Alloc := fun g => if g.val = 0 then 0 else 1

/-- **Example "EFX, but not EFX₀"**: `exX` is EFX and not EFX₀; `exX'` is EFX₀. -/
theorem efx_not_efx0 : EFX exI exX ∧ ¬ exI.EFX0 exX ∧ exI.EFX0 exX' := by
  unfold EFX Inst.EFX0
  decide

/-! ## The protecting goods cannot be dropped -/

/-- The agents `0, 1`. -/
def ag2 : List (Fin 2) := List.finRange 2

/-- The goods `g₀, g₁, g₂`. -/
def gs2 : List (Fin 3) := List.finRange 3

/-- The rankings `g₀ ≻ g₁ ≻ g₂` and `g₁ ≻ g₀ ≻ g₂`. -/
def P2 : Profile (Fin 2) (Fin 3) where
  a := fun i => if i.val = 0 then 0 else 1
  b := fun i => if i.val = 0 then 1 else 0
  c := fun _ => 2

/-- Each agent holds its top. -/
def Y2 (i : Fin 2) : Option (Fin 3) := some (P2.a i)

/-- The state: rankings well formed, valid, both agents free, `J = {g₂}`, each agent exposed for the other. -/
theorem pg_facts : WF P2 ag2 gs2 ∧ Valid P2 ag2 gs2 Y2 [] ∧ Free P2 ag2 [] Y2 0 ∧ Free P2 ag2 [] Y2 1 ∧
    junkList P2 ag2 [] Y2 gs2 = [2] ∧ Exposed P2 ag2 [] Y2 gs2 0 1 ∧ Exposed P2 ag2 [] Y2 gs2 1 0 :=
  ⟨by unfold WF; decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- A utility vector of two agents. -/
def vec2 (u0 u1 : Nat) (i : Fin 2) : Nat := [u0, u1].getD i.val 0

theorem fin2_eta (u : Fin 2 → Nat) : u = vec2 (u 0) (u 1) := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- The states with utilities at least `3, 3` that are valid: only the state itself. -/
theorem pg_check : ∀ u0 ∈ [3, 4], ∀ u1 ∈ [3, 4],
    Valid P2 ag2 gs2 (canonY P2 (vec2 u0 u1)) (canonUp ag2 (vec2 u0 u1)) → u0 = 3 ∧ u1 = 3 := by
  decide

/-- **No valid state Pareto-dominates the state** (each agent's pair contains the other's top). -/
theorem pg_undominated (Y' : Fin 2 → Option (Fin 3)) (up' : List (Fin 2)) (hV : Valid P2 ag2 gs2 Y' up') :
    ¬ Dominates P2 ag2 Y' up' Y2 [] := by
  intro hD
  have hc : ∀ i, Y' i = canonY P2 (util P2 up' Y') i ∧ (i ∈ up' ↔ util P2 up' Y' i = 4) :=
    fun i => canon_of_valid hV i
  have hb : ∀ i, util P2 [] Y2 i ≤ util P2 up' Y' i := fun i => hD.1 i (List.mem_finRange i)
  have hle : ∀ i, util P2 up' Y' i ≤ 4 := fun i => util_le i
  obtain ⟨i0, -, hlt⟩ := hD.2
  generalize util P2 up' Y' = u at hc hb hle hlt
  have hY : Y' = canonY P2 u := funext fun i => (hc i).1
  subst hY
  have hV2 : Valid P2 ag2 gs2 (canonY P2 u) (canonUp ag2 u) :=
    valid_congr_up (fun k => by
      simp only [canonUp, List.mem_filter, beq_iff_eq, (hc k).2]
      exact ⟨fun h => ⟨List.mem_finRange k, h⟩, fun h => h.2⟩) hV
  have hw : ∀ i, util P2 [] Y2 i = 3 := by decide
  have h3 : ∀ i, 3 ≤ u i := fun i => (hw i) ▸ hb i
  rw [fin2_eta u] at hV2
  have m : ∀ i : Fin 2, u i ∈ [3, 4] := fun i => by
    have := hle i
    have := h3 i
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  obtain ⟨e0, e1⟩ := pg_check _ (m 0) _ (m 1) hV2
  rw [hw] at hlt
  have : u i0 = 3 := by
    match i0 with
    | ⟨0, _⟩ => exact e0
    | ⟨1, _⟩ => exact e1
  omega

/-- **The state is completable only with `H = {g₂}`**: every valid absorber `o` with set `H` has `H = [g₂]`. -/
theorem pg_only_g2 (o : Fin 2) (H : List (Fin 3)) (hA : Absorber P2 ag2 gs2 Y2 [] o H) : H = [2] := by
  have key : ∀ x : Fin 2, Exposed P2 ag2 [] Y2 gs2 o x → P2.b x ∉ junkList P2 ag2 [] Y2 gs2 → P2.c x = 2 →
      (2 : Fin 3) ∈ H := by
    intro x hx hb hc
    rcases hA.hit x hx with h | h
    · exact absurd (hA.junk _ h) hb
    · rwa [hc] at h
  have hfit : nFreeExcept P2 ag2 [] Y2 o = 1 := (by decide : ∀ o : Fin 2, nFreeExcept P2 ag2 [] Y2 o = 1) o
  have hother : ∀ o : Fin 2, Exposed P2 ag2 [] Y2 gs2 o (if o.val = 0 then 1 else 0) := by decide
  have hb : ∀ x : Fin 2, P2.b x ∉ junkList P2 ag2 [] Y2 gs2 := by decide
  have hc : ∀ x : Fin 2, P2.c x = 2 := by decide
  have h2 : (2 : Fin 3) ∈ H := key _ (hother o) (hb _) (hc _)
  have hl := hA.fit
  rw [hfit] at hl
  match H, h2, hl with
  | [h], h2, _ => simp at h2; rw [h2]
  | _ :: _ :: _, _, hl => simp at hl

/-- Both agents are valid absorbers with `H = {g₂}` (the other agent receives `g₂`). -/
theorem pg_absorbers : Absorber P2 ag2 gs2 Y2 [] 0 [2] ∧ Absorber P2 ag2 gs2 Y2 [] 1 [2] :=
  ⟨⟨by decide, Or.inr (by decide), by decide, by decide, by decide⟩,
    ⟨by decide, Or.inr (by decide), by decide, by decide, by decide⟩⟩

/-! ## The worked example's remaining numbers -/

open ShortExamples Rings in
/-- **The failing completion of §7**: with absorber `o₁` and `H = {g₆}`, `X_{o₁} = {g₄, g₇, g₈, g₉}`; without `g₈`
it is worth `3 + 2 = 5` to `x₁'`, which holds `g₁`, worth `4`. -/
theorem w_detail : bundle gw (completeDE Pw ag [] Yw 4 [6]) 4 = [4, 7, 8, 9] ∧
    value vw 1 ((bundle gw (completeDE Pw ag [] Yw 4 [6]) 4).erase 8) = 5 ∧
    value vw 1 (bundle gw (completeDE Pw ag [] Yw 4 [6]) 1) = 4 := by
  decide

/-- `D⁺`'s arcs, as a Boolean. -/
def arcB {A G : Type} [DecidableEq A] [DecidableEq G] (P : Profile A G) (agents up : List A) (Y : A → Option G)
    (goods : List G) (u v : A) : Bool :=
  needArcB P agents up Y u v || Rings.expArcB P agents up Y goods u v

theorem arcB_iff {A G : Type} [DecidableEq A] [DecidableEq G] {P : Profile A G} {agents up : List A}
    {Y : A → Option G} {goods : List G} {u v : A} :
    arcB P agents up Y goods u v = true ↔ Rings.Arc P agents up Y goods u v := by
  unfold arcB Rings.Arc
  rw [Bool.or_eq_true, needArcB_iff, Rings.expArcB_iff]
  exact Iff.rfl

/-- The nonempty duplicate-free lists of agents of `Fin n` built by adding one new agent at a time. -/
def nlists (n : Nat) : Nat → List (List (Fin n))
  | 0 => [[]]
  | k + 1 => (nlists n k).flatMap (fun l => ((List.finRange n).filter (fun x => x ∉ l)).map (· :: l))

theorem mem_nlists {n : Nat} : ∀ c : List (Fin n), c.Nodup → c ∈ nlists n c.length
  | [], _ => by simp [nlists]
  | x :: c, h => by
    have hc := List.nodup_cons.mp h
    simp only [List.length_cons, nlists, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
      true_and, decide_eq_true_eq, List.cons.injEq]
    exact ⟨c, mem_nlists c hc.2, x, hc.1, rfl, rfl⟩

open ShortExamples Rings in
/-- The finite check behind `w_cycles`. -/
theorem w_cycles_check : ∀ k ∈ [0, 1, 2, 3, 4, 5, 6], ∀ c ∈ nlists 6 k,
    (c ≠ [] ∧ (cycArcs c).all (fun e => arcB Pw ag [] Yw gw e.1 e.2) = true) →
      c.length = 4 ∧ nExp Pw ag [] Yw gw c = 2 := by
  decide +kernel

open ShortExamples Rings in
/-- **Every cycle of `D⁺` of the draft state has four agents and two exposure arcs** (the caption of the Figure: the
four cycles `o₁ → x → o₂ → x' → o₁`). -/
theorem w_cycles (c : List (Fin 6)) (hc : DCycle Pw ag [] Yw gw c) : c.length = 4 ∧ nExp Pw ag [] Yw gw c = 2 := by
  have hlen : c.length ≤ 6 := by
    have := length_le_of_nodup_of_subset hc.nodup (m := List.finRange 6) (fun x _ => List.mem_finRange x)
    simpa using this
  have hk : c.length ∈ [0, 1, 2, 3, 4, 5, 6] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
  refine w_cycles_check _ hk c (mem_nlists c hc.nodup) ⟨hc.ne, ?_⟩
  rw [List.all_eq_true]
  intro e he
  exact arcB_iff.mpr (hc.arc e he)

open ShortExamples in
/-- The state after DE's exchange: along `o₁ → x₁ → o₂ → x₂ → o₁`. -/
def Y1 : Fin 6 → Option (Fin 10) := exchY Pw ag [] Yw (cOn 4 0 5 2) (cPred 4 0 5 2)

open ShortExamples in
/-- Its pair holders. -/
def up1 : List (Fin 6) := exchUp Pw ag [] Yw (cOn 4 0 5 2) (cPred 4 0 5 2)

/-- The outcome is a move to a state with these picks and pair holders, as a Boolean. -/
def nextB (o : Out (Fin 6) (Fin 10)) (Y' : Fin 6 → Option (Fin 10)) (up' : List (Fin 6)) : Bool :=
  match o with
  | .next Y'' up'' => (List.finRange 6).all (fun i => Y'' i == Y' i && (up''.contains i == up'.contains i))
  | .stop _ _ => false

theorem nextB_spec {o : Out (Fin 6) (Fin 10)} {Y' : Fin 6 → Option (Fin 10)} {up' : List (Fin 6)}
    (h : nextB o Y' up' = true) :
    ∃ Y'' up'', o = .next Y'' up'' ∧ (∀ i, Y'' i = Y' i) ∧ ∀ i, i ∈ up'' ↔ i ∈ up' := by
  cases o with
  | stop _ _ => simp [nextB] at h
  | next Y'' up'' =>
    refine ⟨Y'', up'', rfl, fun i => ?_, fun i => ?_⟩
    · have := List.all_eq_true.mp h i (List.mem_finRange i)
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      exact this.1
    · have := List.all_eq_true.mp h i (List.mem_finRange i)
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      simpa using this.2

/-- The outcome is a stop with this absorber and set, as a Boolean. -/
def stopB (o : Out (Fin 6) (Fin 10)) (a : Fin 6) (H : List (Fin 10)) : Bool :=
  match o with
  | .stop a' H' => a' == a && H' == H
  | .next _ _ => false

theorem stopB_spec {o : Out (Fin 6) (Fin 10)} {a : Fin 6} {H : List (Fin 10)} (h : stopB o a H = true) :
    o = .stop a H := by
  cases o with
  | next _ _ => simp [stopB] at h
  | stop a' H' =>
    simp only [stopB, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, h.2]

open ShortExamples in
/-- **DE's first step** on the draft state is the exchange along `o₁ → x₁ → o₂ → x₂ → o₁`. -/
theorem w_step : ∃ Y' up', step Pw ag gw 0 Yw [] = .next Y' up' ∧ (∀ i, Y' i = Y1 i) ∧ ∀ i, i ∈ up' ↔ i ∈ up1 :=
  nextB_spec (by decide : nextB (step Pw ag gw 0 Yw []) Y1 up1 = true)

open ShortExamples in
/-- **The sum of utilities rises from `14` to `20`.** -/
theorem w_totals : total Pw ag Yw [] = 14 ∧ total Pw ag Y1 up1 = 20 := by
  decide

open ShortExamples in
/-- **The completion paragraph of §7**: in the new state nobody needs a good, `J = {g₇, g₉}`, the free agents are
`x₁', x₂', o₁, o₂`, nobody is exposed for `x₁'`, and DE's next step stops with absorber `x₁'` and `H = ∅`. -/
theorem w_after : (∀ g, ¬ Pw.NA ag (· ∈ up1) Y1 g) ∧ junkList Pw ag up1 Y1 gw = [7, 9] ∧
    ag.filter (freeB Pw ag up1 Y1) = [1, 3, 4, 5] ∧ (∀ x, ¬ Exposed Pw ag up1 Y1 gw 1 x) ∧
    step Pw ag gw 0 Y1 up1 = .stop 1 [] :=
  ⟨by decide, by decide, by decide, by decide, stopB_spec (by decide)⟩

end Remarks
end DE
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE.Remarks.efx_of_efx0
#print axioms EFX.DE.Remarks.efx_not_efx0
#print axioms EFX.DE.Remarks.pg_facts
#print axioms EFX.DE.Remarks.pg_check
#print axioms EFX.DE.Remarks.pg_undominated
#print axioms EFX.DE.Remarks.pg_only_g2
#print axioms EFX.DE.Remarks.pg_absorbers
#print axioms EFX.DE.Remarks.w_detail
#print axioms EFX.DE.Remarks.arcB_iff
#print axioms EFX.DE.Remarks.mem_nlists
#print axioms EFX.DE.Remarks.w_cycles_check
#print axioms EFX.DE.Remarks.w_cycles
#print axioms EFX.DE.Remarks.nextB_spec
#print axioms EFX.DE.Remarks.stopB_spec
#print axioms EFX.DE.Remarks.w_step
#print axioms EFX.DE.Remarks.w_totals
#print axioms EFX.DE.Remarks.w_after
