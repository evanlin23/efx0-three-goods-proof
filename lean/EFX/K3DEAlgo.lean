import EFX.K3DEImprove

/-!
# Draft and Exchange, part 3: the algorithm and its correctness (ledger K3S.PO.LEAN)

Algorithm DE of `paper/k3-simple/long.tex` §6, as a computable function, and Theorem "DE is correct":

1. **Peeling** (`run`): while at least two agents and some goods remain, the first agent to which rule R1 applies
   leaves, with its favourite remaining good or with nothing (`EFX.K3.findR1`, as in `EFX.K3.reduce`); one agent left
   takes everything.
2. **The core** (`deStage`): when R1 applies to nobody, every remaining agent values exactly three goods and is
   strictly balanced (`EFX.not_R1`); its ranking is computed by sorting (`EFX.K3.profileOf`). The draft is
   serial dictatorship in the order of `agents` (`EFX.LB.phase1`, a valid state: `draft_valid`). Then `loop` repeats
   `step`, the loop's three steps (*chain*: a chain if (NC), here (P), fails; *finish*: stop if every agent is a pair
   holder or some free agent passes the count `|H_o| ≤ |F| − 1`; *ring*: a ring, with pair arrows or of want arrows
   only), until it stops with a valid absorber `o` (an agent that can finish) and its set `H`, and the completion
   `completeDE` gives each good of `H` to a different free agent and the rest of the junk to `o`. The names are those
   of `EFX/K3DE.lean`.

**Results.**
- `draft_valid` (**Lemma draft**): the draft is a valid state with no pair holder.
- `loop_spec`: from a valid state, with enough fuel, the loop ends at a valid state with a valid absorber, and the
  number of exchanges is at most the increase of the sum of utilities, which lies in `[0, 4n]`.
- `deStage_sound`: the core stage returns a complete EFX₀ allocation in which every bundle but one has at most two
  goods, after at most `4n` exchanges.
- `run_sound` (**Theorem DE is correct**, lists) and `deSpec_correct` (the model's instances): on every instance in
  which every agent positively values at most three goods, DE returns a complete EFX₀ allocation in which all bundles
  but at most one have at most two goods, after at most `4n` exchanges.

The running time `O(n(n + m))` of the paper is formalized in `EFX/K3DECost*.lean` (ledger K3S.TIME,
`EFX.DE.deC_cost`); this file proves correctness and the count of exchanges.
-/

set_option autoImplicit false

namespace EFX
namespace DE

open LB Profile

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## The loop -/

/-- The outcome of the loop: the absorber, its set, the final state, and the number of exchanges. -/
structure Result (A G : Type) where
  o : A
  H : List G
  Y : A → Option G
  up : List A
  moves : Nat

/-- **The loop of DE**: apply `step` until it stops, counting the exchanges (`fuel` bounds the iterations). -/
def loop (P : Profile A G) (agents : List A) (goods : List G) (d : A) :
    Nat → (A → Option G) → List A → Nat → Result A G
  | 0, Y, up, k => ⟨d, [], Y, up, k⟩
  | fuel + 1, Y, up, k =>
    match step P agents goods d Y up with
    | .stop o H => ⟨o, H, Y, up, k⟩
    | .next Y' up' => loop P agents goods d fuel Y' up' (k + 1)

variable {P : Profile A G} {agents : List A} {goods : List G}

/-- **The loop ends at a valid absorber.** From a valid state whose sum of utilities plus the fuel exceeds `4n`, the
loop returns a valid state with a valid absorber (free unless every agent is a pair holder); every exchange raises the
sum of utilities, so the number of exchanges is at most its increase. -/
theorem loop_spec (hWF : WF P agents goods) (hag : agents.Nodup) (hne : agents ≠ []) (d : A) :
    ∀ (fuel : Nat) (Y : A → Option G) (up : List A) (k : Nat), Valid P agents goods Y up →
      4 * agents.length < total P agents Y up + fuel →
      Valid P agents goods (loop P agents goods d fuel Y up k).Y (loop P agents goods d fuel Y up k).up ∧
      Absorber P agents goods (loop P agents goods d fuel Y up k).Y (loop P agents goods d fuel Y up k).up
        (loop P agents goods d fuel Y up k).o (loop P agents goods d fuel Y up k).H ∧
      (Free P agents (loop P agents goods d fuel Y up k).up (loop P agents goods d fuel Y up k).Y
          (loop P agents goods d fuel Y up k).o ∨ ∀ i ∈ agents, i ∈ (loop P agents goods d fuel Y up k).up) ∧
      (loop P agents goods d fuel Y up k).moves + total P agents Y up ≤
        k + total P agents (loop P agents goods d fuel Y up k).Y (loop P agents goods d fuel Y up k).up
  | 0, Y, up, _, _, hf => by
    have := total_le (P := P) (agents := agents) (Y := Y) (up := up)
    omega
  | fuel + 1, Y, up, k, hV, hf => by
    cases h : step P agents goods d Y up with
    | stop o H =>
      have e : loop P agents goods d (fuel + 1) Y up k = ⟨o, H, Y, up, k⟩ := by simp [loop, h]
      rw [e]
      obtain ⟨hA, hF⟩ := step_stop hWF hag hne h
      exact ⟨hV, hA, hF, Nat.le_refl _⟩
    | next Y' up' =>
      have e : loop P agents goods d (fuel + 1) Y up k = loop P agents goods d fuel Y' up' (k + 1) := by
        simp [loop, h]
      rw [e]
      obtain ⟨hV', hD⟩ := step_next hV hWF hag h
      have hlt := total_lt hD
      obtain ⟨h1, h2, h3, h4⟩ := loop_spec hWF hag hne d fuel Y' up' (k + 1) hV' (by omega)
      exact ⟨h1, h2, h3, by omega⟩

/-- **Lemma draft**: serial dictatorship in the order of `agents` (each agent takes the first of its three goods not
yet taken, or nothing) is a valid state with no pair holder. -/
theorem draft_valid (hag : agents.Nodup) (hgd : goods.Nodup) : Valid P agents goods (phase1 P agents goods) [] := by
  obtain ⟨h1, h2, h3⟩ := phase1_spec P agents goods hag hgd
  refine ⟨h1, h2, by simp, by simp, by simp, by simp, fun g hg hp _ hna => ?_, by simp⟩
  obtain ⟨i, hi, -, hpr⟩ := hna
  obtain ⟨k, hk⟩ := h3 i hi g hg hpr
  exact hp k hk

/-- **The core of DE** with the rankings `P`: the draft, then the loop with `4n + 1` rounds of fuel. -/
def deCore (P : Profile A G) (agents : List A) (goods : List G) (d : A) : Result A G :=
  loop P agents goods d (4 * agents.length + 1) (phase1 P agents goods) [] 0

/-- **DE on the core, with the rankings `P`**: the loop ends at a valid state with a valid absorber, after at most
`4n` exchanges; its completion is a complete allocation, EFX₀ for every valuation consistent with the rankings, with
at most one bundle (the absorber's) of more than two goods. -/
theorem deCore_spec (hWF : WF P agents goods) (hag : agents.Nodup) (hgd : goods.Nodup) (hne : agents ≠ []) (d : A) :
    let r := deCore P agents goods d
    Valid P agents goods r.Y r.up ∧ Absorber P agents goods r.Y r.up r.o r.H ∧ r.moves ≤ 4 * agents.length ∧
      IsAllocation agents goods (completeDE P agents r.up r.Y r.o r.H) ∧
      (∀ v : A → G → Nat, P.Consistent agents v → EFX0L v agents goods (completeDE P agents r.up r.Y r.o r.H)) ∧
      ∀ j ∈ agents, j ≠ r.o → (bundle goods (completeDE P agents r.up r.Y r.o r.H) j).length ≤ 2 := by
  intro r
  obtain ⟨h1, h2, -, h4⟩ := loop_spec hWF hag hne d (4 * agents.length + 1) (phase1 P agents goods) [] 0
    (draft_valid hag hgd) (by omega)
  have hle := total_le (P := P) (agents := agents) (Y := r.Y) (up := r.up)
  obtain ⟨s1, s2, s3⟩ := soundness h1 hag hgd h2
  exact ⟨h1, h2, by simp only [r, deCore] at h4 hle ⊢; omega, s1, s2, s3⟩

/-! ## DE with values: the core stage and peeling -/

/-- **The core stage of DE** with the rankings computed from the values (`EFX.K3.profileOf`): the allocation and the
number of exchanges. -/
def deStage (v : A → G → Nat) (agents : List A) (goods : List G) (g0 : G) (d : A) : (G → A) × Nat :=
  let P := K3.profileOf v goods g0
  let r := deCore P agents goods d
  (completeDE P agents r.up r.Y r.o r.H, r.moves)

/-- **Algorithm DE, over lists**, with `fuel ≥` the number of agents: peel by R1 while it applies to some agent (at
least two agents and some goods left), then the core stage. The agent `d` only receives goods in unreachable cases. -/
def run (v : A → G → Nat) (d : A) : Nat → List A → List G → (G → A) × Nat
  | 0, _, _ => (fun _ => d, 0)
  | fuel + 1, agents, goods =>
    if agents.length ≤ 1 then (fun _ => agents.headD d, 0)
    else
      match goods with
      | [] => (fun _ => d, 0)
      | g0 :: gs =>
        match K3.findR1 v agents (g0 :: gs) with
        | some (i, none) => run v d fuel (agents.erase i) (g0 :: gs)
        | some (i, some p) =>
          let r := run v d fuel (agents.erase i) ((g0 :: gs).erase p)
          (extend i p r.1, r.2)
        | none => deStage v agents (g0 :: gs) g0 d

/-- **The core stage is correct.** If every agent of `agents` has exactly three relevant goods among `goods` and is
balanced, `deStage` is a complete EFX₀ allocation with at most one bundle of more than two goods, after at most
`4n` exchanges. -/
theorem deStage_sound (v : A → G → Nat) {agents : List A} {goods : List G} (g0 : G) (d : A)
    (hag : agents.Nodup) (hgd : goods.Nodup) (hne : agents ≠ [])
    (h3 : ∀ i ∈ agents, (relevant v i goods).length = 3)
    (hbal : ∀ i ∈ agents, ∀ g ∈ goods, 2 * v i g ≤ value v i goods) :
    IsAllocation agents goods (deStage v agents goods g0 d).1 ∧ EFX0L v agents goods (deStage v agents goods g0 d).1 ∧
      (∃ o, ∀ j ∈ agents, j ≠ o → (bundle goods (deStage v agents goods g0 d).1 j).length ≤ 2) ∧
      (deStage v agents goods g0 d).2 ≤ 4 * agents.length := by
  let P := K3.profileOf v goods g0
  let v' : A → G → Nat := fun j g => if g ∈ goods then v j g else 0
  have hWF : WF P agents goods := fun i hi => by
    obtain ⟨h1, h2, h3', h4, h5, h6, -⟩ := K3.sort3_ranking v i g0 hgd (h3 i hi) (hbal i hi)
    exact ⟨h1, h2, h3', h4, h5, h6⟩
  have hcons : P.Consistent agents v' := by
    intro i hi
    obtain ⟨h1, h2, h3', h4, h5, h6, h7, h8, h9, h10, h11⟩ := K3.sort3_ranking v i g0 hgd (h3 i hi) (hbal i hi)
    refine ⟨by simp [v', P, K3.profileOf, h3', h7], by simp [v', P, K3.profileOf, h2, h3', h8],
      by simp [v', P, K3.profileOf, h1, h2, h9], by simp [v', P, K3.profileOf, h1, h2, h3', h10],
      fun g hg => ?_, h4, h5, h6⟩
    obtain ⟨ha, hb, hc⟩ := LB.ne_of_rank_three hg
    by_cases hgg : g ∈ goods
    · simp only [v', hgg, ↓reduceIte]; exact h11 g hgg ha hb hc
    · simp [v', hgg]
  obtain ⟨-, -, hmoves, hX, hE, hlen⟩ := deCore_spec hWF hag hgd hne d
  refine ⟨hX, fun x hx y hy hxy g hg => ?_, ⟨_, hlen⟩, hmoves⟩
  have := hE v' hcons x hx y hy hxy g hg
  change value v' x ((bundle goods (deStage v agents goods g0 d).1 y).erase g) ≤
    value v' x (bundle goods (deStage v agents goods g0 d).1 x) at this
  have hsub : ∀ S : List G, S.Sublist goods → value v' x S = value v x S := fun S hS =>
    LB.value_restrict v goods x (fun g hg => hS.subset hg)
  rwa [hsub ((bundle goods (deStage v agents goods g0 d).1 y).erase g) (List.erase_sublist.trans List.filter_sublist),
    hsub (bundle goods (deStage v agents goods g0 d).1 x) List.filter_sublist] at this

/-- **Theorem DE is correct, over lists.** For every instance in which every agent has at most three relevant goods,
`run` (with fuel at least the number of agents) returns a complete EFX₀ allocation in which all bundles but at most
one have at most two goods, after at most `4n` exchanges. -/
theorem run_sound (v : A → G → Nat) (d : A) : ∀ (fuel : Nat) (agents : List A) (goods : List G),
    agents ≠ [] → agents.Nodup → goods.Nodup → agents.length ≤ fuel →
    (∀ i ∈ agents, (relevant v i goods).length ≤ 3) →
    IsAllocation agents goods (run v d fuel agents goods).1 ∧ EFX0L v agents goods (run v d fuel agents goods).1 ∧
      (∃ o, ∀ j ∈ agents, j ≠ o → (bundle goods (run v d fuel agents goods).1 j).length ≤ 2) ∧
      (run v d fuel agents goods).2 ≤ 4 * agents.length
  | 0, agents, _, hne, _, _, hl, _ => by
    exact absurd (List.length_eq_zero_iff.mp (by omega)) hne
  | fuel + 1, agents, goods, hne, hag, hgd, hl, h3 => by
    unfold run
    by_cases h1 : agents.length ≤ 1
    · simp only [h1, ↓reduceIte]
      obtain ⟨i0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
      have hrest : rest = [] := by
        cases rest with
        | nil => rfl
        | cons _ _ => simp at h1
      subst hrest
      refine ⟨fun _ _ => by simp, fun x hx y hy hxy => ?_, ⟨i0, fun j hj hji => by simp at hj; exact absurd hj hji⟩,
        by simp⟩
      simp at hx hy
      exact absurd (hx.trans hy.symm) hxy
    simp only [h1, ↓reduceIte]
    cases goods with
    | nil =>
      simp only
      exact ⟨fun g hg => by simp at hg, fun _ _ _ _ _ g hg => by simp [bundle] at hg,
        ⟨d, fun j _ _ => by simp [bundle]⟩, by simp⟩
    | cons g0 gs =>
      simp only
      have hrest : ∀ i ∈ agents, agents.erase i ≠ [] := by
        intro i hi h
        have := List.length_erase_of_mem hi
        rw [h] at this; simp at this; omega
      cases hf : K3.findR1 v agents (g0 :: gs) with
      | some q =>
        obtain ⟨i, s⟩ := q
        obtain ⟨hi, hs⟩ := K3.findR1_some hf
        have hil : (agents.erase i).length + 1 = agents.length := by
          rw [List.length_erase_of_mem hi]; have := List.length_pos_of_mem hi; omega
        have hnot : i ∉ agents.erase i := List.Nodup.not_mem_erase hag
        cases s with
        | none =>
          simp only
          obtain ⟨hX', hE', ⟨o, hlen⟩, hc⟩ := run_sound v d fuel (agents.erase i) (g0 :: gs) (hrest i hi)
            (hag.erase i) hgd (by omega) (fun j hj => h3 j (List.mem_of_mem_erase hj))
          obtain ⟨hX, hE⟩ := peelEmpty v hnot hX' hE' (K3.r1Step_none_zero hs)
          refine ⟨fun g hg => (mem_cons_erase hi _).mp (hX g hg), efx0L_congr v (mem_cons_erase hi) hE,
            ⟨o, fun j hj hjo => ?_⟩, by omega⟩
          by_cases hji : j = i
          · subst hji
            have : bundle (g0 :: gs) (run v d fuel (agents.erase j) (g0 :: gs)).1 j = [] := by
              apply List.eq_nil_iff_forall_not_mem.mpr
              intro g hg
              obtain ⟨hgg, hXg⟩ := mem_bundle.mp hg
              have := hX' g hgg
              rw [hXg] at this
              exact hnot this
            rw [this]; simp
          · exact hlen j ((List.Nodup.mem_erase_iff hag).mpr ⟨hji, hj⟩) hjo
        | some p =>
          simp only
          obtain ⟨hp, htop⟩ := K3.r1Step_some hs
          obtain ⟨hX', hE', ⟨o, hlen⟩, hc⟩ := run_sound v d fuel (agents.erase i) ((g0 :: gs).erase p) (hrest i hi)
            (hag.erase i) (hgd.erase p) (by omega)
            (fun j hj => Nat.le_trans (relevant_sublist v List.erase_sublist) (h3 j (List.mem_of_mem_erase hj)))
          obtain ⟨hX, hE⟩ := peel v hnot hp hgd hX' hE' htop
          refine ⟨fun g hg => (mem_cons_erase hi _).mp (hX g hg), efx0L_congr v (mem_cons_erase hi) hE,
            ⟨o, fun j hj hjo => ?_⟩, by omega⟩
          by_cases hji : j = i
          · subst hji
            refine Nat.le_trans (LB.length_le_one (nodup_bundle hgd _ j) (y := p) fun g hg => ?_) (by omega)
            obtain ⟨hgg, hXg⟩ := mem_bundle.mp hg
            refine Classical.byContradiction fun hgp => ?_
            have hX'g := hX' g ((List.mem_erase_of_ne hgp).mpr hgg)
            have : extend j p (run v d fuel (agents.erase j) ((g0 :: gs).erase p)).1 g =
                (run v d fuel (agents.erase j) ((g0 :: gs).erase p)).1 g := by simp [extend, hgp]
            rw [this] at hXg
            rw [hXg] at hX'g
            exact hnot hX'g
          · rw [bundle_extend_of_ne hgd hji]
            exact hlen j ((List.Nodup.mem_erase_iff hag).mpr ⟨hji, hj⟩) hjo
      | none =>
        simp only
        have hnone := K3.findR1_none hf
        have hb : ∀ i ∈ agents, 3 ≤ (relevant v i (g0 :: gs)).length ∧
            ∀ g ∈ g0 :: gs, 2 * v i g < value v i (g0 :: gs) :=
          fun i hi => not_R1 v (by simp) (K3.r1Step_eq_none (hnone i hi))
        exact deStage_sound v g0 d hag hgd hne (fun i hi => Nat.le_antisymm (h3 i hi) (hb i hi).1)
          (fun i hi g hg => Nat.le_of_lt ((hb i hi).2 g hg))

/-! ## The model's instances -/

/-- **Algorithm DE** for an instance of the model with `n ≥ 1` agents: `run` on all agents and all goods (in index
order), with agent `0` as the default. -/
def deSpec (I : Inst) (hn : 0 < I.n) : I.Alloc :=
  (run I.v ⟨0, hn⟩ I.n (List.finRange I.n) (List.finRange I.m)).1

/-- The number of exchanges (need cycles, pair chains and exchange cycles) that DE applies. -/
def deMoves (I : Inst) (hn : 0 < I.n) : Nat :=
  (run I.v ⟨0, hn⟩ I.n (List.finRange I.n) (List.finRange I.m)).2

/-- **Theorem DE is correct** (`paper/k3-simple/long.tex`, Theorems existence, one large bundle and algorithm). On
every instance in which every agent positively values at most three goods, DE returns an EFX₀ allocation in which all
bundles but at most one have at most two goods, and it applies at most `4n` exchanges. -/
theorem deSpec_correct (I : Inst) (hn : 0 < I.n) (h : ∀ i, numRelevant I i ≤ 3) :
    I.EFX0 (deSpec I hn) ∧
      (∃ o, ∀ j, j ≠ o → finSum I.m (fun g => if deSpec I hn g = j then 1 else 0) ≤ 2) ∧
      deMoves I hn ≤ 4 * I.n := by
  obtain ⟨-, hE, ⟨o, hlen⟩, hc⟩ := run_sound I.v ⟨0, hn⟩ I.n (List.finRange I.n) (List.finRange I.m)
    (List.ne_nil_of_mem (List.mem_finRange ⟨0, hn⟩)) (List.nodup_finRange _) (List.nodup_finRange _)
    (by simp) (fun i _ => (numRelevant_eq I i) ▸ h i)
  refine ⟨(Inst.efx0_iff I _).mpr hE, ⟨o, fun j hj => ?_⟩, by simpa [deMoves] using hc⟩
  rw [finSum_bundle_eq]
  exact hlen j (List.mem_finRange j) hj

end DE
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE.loop_spec
#print axioms EFX.DE.draft_valid
#print axioms EFX.DE.deCore_spec
#print axioms EFX.DE.deStage_sound
#print axioms EFX.DE.run_sound
#print axioms EFX.DE.deSpec_correct
