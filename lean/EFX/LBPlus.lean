import EFX.Rotation

/-!
# Construction LB⁺ and Theorem C (`proofs/lb_last_step.md` §6)

`EFX.LB.lbPlus` is construction LB⁺, with Phase 1's processing order as an argument:
1. Phase 1 in `order` (`phase1`); LB's upgrades (`lbUp`).
2. If the junk fits the slots (`ω ≤ 0`), the completion without owner.
3. Otherwise let `r` be the last agent not upgraded (`lastOut`). If `r` is a valid owner (Lemma 1's
   condition holds for some `H`; by `validOwner_iff` exactly when `H = hitSet` fits), the completion with
   owner `r` and `H = hitSet`.
4. Otherwise the bad case holds (Theorem A, `theoremA_invalid`): rotate along the need chain from `k*` to `r`
   (`rotPicks`, `k*` upgraded), and return the completion of the rotated pre-allocation without owner if its
   junk fits its slots, and with owner `k*` and `H = hitSet` otherwise (Theorem B).

LB⁺ has no failure case: it always returns an allocation (`G → A`).

LB⁺ over all its choices (`LBPlusRun`, `LBPlusOut`): Phase 1 in any order with R1 priority, the upgrades in
any order (`UpFinal`), any need chain from `k*` to `r` (`NeedChain`), and any completions satisfying (OC)
(`Completion`).

- `lbPlusRun_sound`: **Theorem C, over all choices**: every output is a complete allocation, EFX₀ for every
  additive valuation consistent with the rankings (ties allowed), with at most one bundle of more than two
  goods. `lbPlusOut_exists`: LB⁺ never meets an undefined case (for every order and every end state of the
  upgrades, an output exists); `lbPlusOut_exists_chain`: in the rotation branch, every need chain from `k*` to
  `r` gives an output. `lbPlus_run`: the computable `lbPlus` is one of the outputs.
- `lbPlus_sound`: **Theorem C** for `lbPlus`; `lbPlus_sound_model`: the same in the model's terms
  (`EFX.Inst.EFX0`).

The agent `d` is a default that only unreachable branches use (LB⁺ with no agent not upgraded).
-/

set_option autoImplicit false

namespace EFX
namespace LB

variable {A G : Type} [DecidableEq A] [DecidableEq G]

open Profile

/-- **Construction LB⁺** (`proofs/lb_last_step.md` §6), with Phase 1 run in `order`. -/
def lbPlus (P : Profile A G) (agents : List A) (goods : List G) (order : List A) (d : A) : G → A :=
  let Y := phase1 P order goods
  let up := lbUp P agents goods Y
  let J := junkList P agents up Y goods
  if J.length ≤ slotSum P agents up Y then complete P agents up Y goods none [] d
  else
    match lastOut up order with
    | none => complete P agents up Y goods none [] d
    | some r =>
      let H := hitSet P J (exposedL P agents up Y goods r)
      -- `r` is a valid owner exactly when `H` fits (`validOwner_iff`)
      if H.length ≤ (agents.map (slotsExcept (cap P agents up Y) (some r))).sum then
        complete P agents up Y goods (some r) H d
      else
        match kstar P agents up Y goods (blkAux P order goods 0) r with
        | none => complete P agents up Y goods (some r) H d
        | some k =>
          -- the bad case: rotate along the need chain from `k` to `r`
          let Y' := rotPicks P Y k (chainFrom P agents up Y k (after order k))
          let J' := junkList P agents (k :: up) Y' goods
          if J'.length ≤ slotSum P agents (k :: up) Y' then complete P agents (k :: up) Y' goods none [] d
          else complete P agents (k :: up) Y' goods (some k)
            (hitSet P J' (exposedL P agents (k :: up) Y' goods k)) d

/-! ## LB⁺ over all its choices -/

/-- A need chain `k :: ch` from `k` to `r`, of listed agents, in the pre-allocation `(Y, up)`. -/
def NeedChain (P : Profile A G) (agents up : List A) (Y : A → Option G) (k r : A) (ch : List A) : Prop :=
  IsChain P agents up Y k ch ∧ (∀ j ∈ ch, j ∈ agents) ∧ ch.getLastD k = r

/-- The outputs of LB⁺ (`proofs/lb_last_step.md` §6) for Phase 1 in `order` and the upgraded agents `up`,
over every remaining choice. With `Y` Phase 1's picks:
- if the junk fits the slots, any completion without owner;
- otherwise, with `r` the last agent not upgraded: if `r` is a valid owner (`ValidOwner`: Lemma 1's
  condition holds for some `H`), any completion with owner `r` satisfying the owner constraint;
- otherwise, for any need chain from `k*` to `r` (`k*` the agent exposed for `r` in `r`'s block), the
  rotation along it, and then any completion of the rotated pre-allocation: without owner if its junk fits
  its slots, with owner `k*` otherwise. -/
def LBPlusOut (P : Profile A G) (agents : List A) (goods : List G) (order up : List A) (X : G → A) : Prop :=
  let Y := phase1 P order goods
  ((junkList P agents up Y goods).length ≤ slotSum P agents up Y ∧ Completion P agents goods Y up none X) ∨
  (slotSum P agents up Y < (junkList P agents up Y goods).length ∧ ∃ r, lastOut up order = some r ∧
    ((ValidOwner P agents up Y goods r ∧ Completion P agents goods Y up (some r) X) ∨
     (¬ ValidOwner P agents up Y goods r ∧ ∃ k ch, kstar P agents up Y goods (blkAux P order goods 0) r = some k ∧
       NeedChain P agents up Y k r ch ∧
       (((junkList P agents (k :: up) (rotPicks P Y k ch) goods).length ≤
            slotSum P agents (k :: up) (rotPicks P Y k ch) ∧
          Completion P agents goods (rotPicks P Y k ch) (k :: up) none X) ∨
        (slotSum P agents (k :: up) (rotPicks P Y k ch) <
            (junkList P agents (k :: up) (rotPicks P Y k ch) goods).length ∧
          Completion P agents goods (rotPicks P Y k ch) (k :: up) (some k) X)))))

/-- The outputs of LB⁺ for Phase 1 in `order`, with the upgrades in any order. -/
def LBPlusRun (P : Profile A G) (agents : List A) (goods : List G) (order : List A) (X : G → A) : Prop :=
  ∃ up, UpFinal P agents (phase1 P order goods) goods up ∧ LBPlusOut P agents goods order up X

section
variable {P : Profile A G} {agents : List A} {goods : List G} {Y : A → Option G} {up : List A}

/-- Lemma 1 from `OwnerOK`. -/
theorem OwnerOK.completion (hV : Valid P agents goods Y up) (hag : agents.Nodup) (hgd : goods.Nodup)
    {w : A} {H : List G} (h : OwnerOK P agents up Y goods w H) (d : A) :
    Completion P agents goods Y up (some w) (complete P agents up Y goods (some w) H d) :=
  complete_some hV hag hgd h.mem h.term h.sub h.fit
    (fun x hx hxw hxu hxa hb hc => h.hit x hx ⟨hxw, hxu, hxa, hb, hc⟩)

/-- Theorem 1′, in the form Theorem C returns it. -/
theorem conclude {o : Option A} {X : G → A} (hV : Valid P agents goods Y up)
    (hC : Completion P agents goods Y up o X) (hgd : goods.Nodup) (d : A) :
    IsAllocation agents goods X ∧ (∀ v : A → G → Nat, P.Consistent agents v → EFX0L v agents goods X) ∧
      ∃ w, ∀ j ∈ agents, j ≠ w → (bundle goods X j).length ≤ 2 := by
  obtain ⟨h1, h2⟩ := hV.sound hC hgd
  refine ⟨hC.alloc, h1, o.getD d, fun j hj hjw => h2 j hj (fun e => hjw ?_)⟩
  rw [e]; rfl

end

section theoremC
variable {P : Profile A G} {agents : List A} {goods : List G} {order : List A}

/-- The state after Phase 1 in an order with R1 priority and any end state of the upgrades. -/
theorem state_of_final (hag : agents.Nodup) (hgd : goods.Nodup) (hWF : WF P agents goods)
    (hord : order.Nodup) (hperm : ∀ i, i ∈ order ↔ i ∈ agents) (hR : R1Prio P order goods) {up : List A}
    (hup : UpFinal P agents (phase1 P order goods) goods up) :
    State P agents goods order (phase1 P order goods) (blkAux P order goods 0)
      (fun x => leadB P order goods x = true) up := by
  have hrun := phase1_run hWF hgd hord hperm hR
  obtain ⟨hV, hUT⟩ := upFinal_valid hrun hWF hgd hup
  exact ⟨hrun, hV, hUT, hWF, hag, hgd⟩

/-- The chain LB⁺ uses is a need chain from `k*` to `r` in the bad case. -/
theorem needChain_chainFrom {Y : A → Option G} {blk : A → Nat} {lead : A → Prop} {up : List A}
    (hS : State P agents goods order Y blk lead up) {r k : A} (hr : lastOut up order = some r)
    (hk : kstar P agents up Y goods blk r = some k)
    (hall : ∀ ch, IsChain P agents up Y k ch → (∀ j ∈ ch, j ∈ agents) →
      frozenB P agents up Y (ch.getLastD k) = false → ch.getLastD k = r) :
    NeedChain P agents up Y k r (chainFrom P agents up Y k (after order k)) := by
  obtain ⟨hkE, -, -⟩ := kstar_spec hS hr hk
  obtain ⟨hka, ⟨-, hku, -⟩, -⟩ := exposed_r hS hr hkE
  have hmem := chainFrom_mem (up := up) hS.run k (after order k) (after_mem hS.run)
  refine ⟨chainFrom_isChain k _, fun j hj => (hmem j hj).1, hall _ (chainFrom_isChain k _)
    (fun j hj => (hmem j hj).1) (chainEnd_spec hS.run hka hku).1.2.2⟩

/-- **Theorem C, over all choices.** Every output of LB⁺, for Phase 1 in any order with R1 priority, the
upgrades in any order, any need chain and any completions, is a complete allocation that is EFX₀ for every
additive valuation consistent with the rankings, with at most one bundle of more than two goods. -/
theorem lbPlusRun_sound (d : A) (hag : agents.Nodup) (hgd : goods.Nodup) (hWF : WF P agents goods)
    (hord : order.Nodup) (hperm : ∀ i, i ∈ order ↔ i ∈ agents) (hR : R1Prio P order goods) {X : G → A}
    (h : LBPlusRun P agents goods order X) :
    IsAllocation agents goods X ∧ (∀ v : A → G → Nat, P.Consistent agents v → EFX0L v agents goods X) ∧
      ∃ o, ∀ j ∈ agents, j ≠ o → (bundle goods X j).length ≤ 2 := by
  obtain ⟨up, hup, hout⟩ := h
  have hS := state_of_final hag hgd hWF hord hperm hR hup
  rcases hout with ⟨-, hC⟩ | ⟨-, r, hr, ⟨-, hC⟩ | ⟨hinv, k, ch, hk, ⟨hch, hcha, hend⟩, hrot⟩⟩
  · exact conclude hS.valid hC hgd d
  · exact conclude hS.valid hC hgd d
  · obtain ⟨k', hk', -, hm, -⟩ := theoremA_invalid hS hr hinv
    rw [hk] at hk'
    cases hk'
    obtain ⟨hV', -⟩ := theoremB (⟨hS, hr, hk, hm, hch, hcha, hend⟩ :
      BadCase P agents goods order (phase1 P order goods) (blkAux P order goods 0)
        (fun x => leadB P order goods x = true) up r k ch)
    rcases hrot with ⟨-, hC⟩ | ⟨-, hC⟩
    · exact conclude hV' hC hgd d
    · exact conclude hV' hC hgd d

/-- **LB⁺ never meets an undefined case.** For Phase 1 in any order with R1 priority and every end state of
the upgrades (in any order), LB⁺ has an output: when `r` is not a valid owner, the bad case holds, a need
chain from `k*` to `r` exists, and after the rotation `k*` is a valid owner. -/
theorem lbPlusOut_exists (d : A) (hag : agents.Nodup) (hgd : goods.Nodup) (hne : agents ≠ [])
    (hWF : WF P agents goods) (hord : order.Nodup) (hperm : ∀ i, i ∈ order ↔ i ∈ agents)
    (hR : R1Prio P order goods) {up : List A} (hup : UpFinal P agents (phase1 P order goods) goods up) :
    ∃ X, LBPlusOut P agents goods order up X := by
  have hS := state_of_final hag hgd hWF hord hperm hR hup
  by_cases hfit : (junkList P agents up (phase1 P order goods) goods).length ≤
      slotSum P agents up (phase1 P order goods)
  · exact ⟨_, Or.inl ⟨hfit, complete_none (d := d) hS.valid hag hgd hfit⟩⟩
  obtain ⟨r, hr⟩ := lastOut_exists hS hne
  by_cases hval : ValidOwner P agents up (phase1 P order goods) goods r
  · obtain ⟨H, hH⟩ := hval
    exact ⟨_, Or.inr ⟨by omega, r, hr, Or.inl ⟨⟨H, hH⟩, hH.completion hS.valid hag hgd d⟩⟩⟩
  obtain ⟨k, hk, -, hm, hall⟩ := theoremA_invalid hS hr hval
  have hch := needChain_chainFrom hS hr hk hall
  have hB : BadCase P agents goods order (phase1 P order goods) (blkAux P order goods 0)
      (fun x => leadB P order goods x = true) up r k (chainFrom P agents up (phase1 P order goods) k
        (after order k)) := ⟨hS, hr, hk, hm, hch.1, hch.2.1, hch.2.2⟩
  obtain ⟨hV', hO'⟩ := theoremB hB
  by_cases hfit' : (junkList P agents (k :: up) (rotPicks P (phase1 P order goods) k
      (chainFrom P agents up (phase1 P order goods) k (after order k))) goods).length ≤
      slotSum P agents (k :: up) (rotPicks P (phase1 P order goods) k
        (chainFrom P agents up (phase1 P order goods) k (after order k)))
  · exact ⟨_, Or.inr ⟨by omega, r, hr, Or.inr ⟨hval, k, _, hk, hch,
      Or.inl ⟨hfit', complete_none (d := d) hV' hag hgd hfit'⟩⟩⟩⟩
  · exact ⟨_, Or.inr ⟨by omega, r, hr, Or.inr ⟨hval, k, _, hk, hch,
      Or.inr ⟨by omega, hO'.completion hV' hag hgd d⟩⟩⟩⟩

/-- **Every need chain works.** If the junk overflows the slots and `r` is not a valid owner, then for *every*
need chain `ch` from `k*` to `r` the rotation along `ch` has a completion, without owner if the rotated junk
fits the rotated slots and with owner `k*` otherwise, and it is an output of LB⁺. -/
theorem lbPlusOut_exists_chain (d : A) (hag : agents.Nodup) (hgd : goods.Nodup)
    (hWF : WF P agents goods) (hord : order.Nodup) (hperm : ∀ i, i ∈ order ↔ i ∈ agents)
    (hR : R1Prio P order goods) {up : List A} (hup : UpFinal P agents (phase1 P order goods) goods up)
    (hfit : slotSum P agents up (phase1 P order goods) <
      (junkList P agents up (phase1 P order goods) goods).length)
    {r k : A} {ch : List A} (hr : lastOut up order = some r)
    (hinv : ¬ ValidOwner P agents up (phase1 P order goods) goods r)
    (hk : kstar P agents up (phase1 P order goods) goods (blkAux P order goods 0) r = some k)
    (hch : NeedChain P agents up (phase1 P order goods) k r ch) :
    ∃ X, (((junkList P agents (k :: up) (rotPicks P (phase1 P order goods) k ch) goods).length ≤
            slotSum P agents (k :: up) (rotPicks P (phase1 P order goods) k ch) ∧
          Completion P agents goods (rotPicks P (phase1 P order goods) k ch) (k :: up) none X) ∨
        (slotSum P agents (k :: up) (rotPicks P (phase1 P order goods) k ch) <
            (junkList P agents (k :: up) (rotPicks P (phase1 P order goods) k ch) goods).length ∧
          Completion P agents goods (rotPicks P (phase1 P order goods) k ch) (k :: up) (some k) X)) ∧
      LBPlusOut P agents goods order up X := by
  have hS := state_of_final hag hgd hWF hord hperm hR hup
  obtain ⟨-, -, -, hm, -⟩ := theoremA_invalid hS hr hinv
  obtain ⟨hV', hO'⟩ := theoremB (⟨hS, hr, hk, hm, hch.1, hch.2.1, hch.2.2⟩ :
    BadCase P agents goods order (phase1 P order goods) (blkAux P order goods 0)
      (fun x => leadB P order goods x = true) up r k ch)
  by_cases hfit' : (junkList P agents (k :: up) (rotPicks P (phase1 P order goods) k ch) goods).length ≤
      slotSum P agents (k :: up) (rotPicks P (phase1 P order goods) k ch)
  · have hC := complete_none (d := d) hV' hag hgd hfit'
    exact ⟨_, Or.inl ⟨hfit', hC⟩, Or.inr ⟨hfit, r, hr, Or.inr ⟨hinv, k, ch, hk, hch, Or.inl ⟨hfit', hC⟩⟩⟩⟩
  · have hC := hO'.completion hV' hag hgd d
    exact ⟨_, Or.inr ⟨by omega, hC⟩,
      Or.inr ⟨hfit, r, hr, Or.inr ⟨hinv, k, ch, hk, hch, Or.inr ⟨by omega, hC⟩⟩⟩⟩

/-- The computable LB⁺ (`lbPlus`) is one of LB⁺'s runs: LB's upgrade order, the chain `chainFrom`, and the
completions `complete`. -/
theorem lbPlus_run (d : A) (hag : agents.Nodup) (hgd : goods.Nodup) (hne : agents ≠ [])
    (hWF : WF P agents goods) (hord : order.Nodup) (hperm : ∀ i, i ∈ order ↔ i ∈ agents)
    (hR : R1Prio P order goods) :
    LBPlusRun P agents goods order (lbPlus P agents goods order d) := by
  have hup := lbUp_final P agents (phase1 P order goods) goods
  have hS := state_of_final hag hgd hWF hord hperm hR hup
  refine ⟨_, hup, ?_⟩
  unfold lbPlus LBPlusOut
  simp only
  split
  · rename_i hfit
    exact Or.inl ⟨hfit, complete_none hS.valid hag hgd hfit⟩
  rename_i hfit
  split
  · rename_i hnone
    obtain ⟨r, hr⟩ := lastOut_exists hS hne
    rw [hnone] at hr; cases hr
  rename_i r hr
  split
  · rename_i hfitr
    exact Or.inr ⟨by omega, r, hr, Or.inl ⟨(validOwner_iff hS hr).mpr hfitr,
      (ownerOK_of_fits hS hr hfitr).completion hS.valid hag hgd d⟩⟩
  rename_i hfitr
  have hval : ¬ ValidOwner P agents (lbUp P agents goods (phase1 P order goods)) (phase1 P order goods)
      goods r := fun h => hfitr ((validOwner_iff hS hr).mp h)
  obtain ⟨k0, hk0, -, hm, hall⟩ := theoremA_invalid hS hr hval
  split
  · rename_i hk; rw [hk] at hk0; cases hk0
  rename_i k hk
  have e : k0 = k := by rw [hk] at hk0; exact (Option.some.inj hk0).symm
  rw [e] at hall
  have hch := needChain_chainFrom hS hr hk hall
  obtain ⟨hV', hO'⟩ := theoremB (⟨hS, hr, hk, hm, hch.1, hch.2.1, hch.2.2⟩ :
    BadCase P agents goods order (phase1 P order goods) (blkAux P order goods 0)
      (fun x => leadB P order goods x = true) (lbUp P agents goods (phase1 P order goods)) r k _)
  refine Or.inr ⟨by omega, r, hr, Or.inr ⟨hval, k, _, hk, hch, ?_⟩⟩
  split
  · rename_i hfit'
    exact Or.inl ⟨hfit', complete_none hV' hag hgd hfit'⟩
  · rename_i hfit'
    exact Or.inr ⟨by omega, hO'.completion hV' hag hgd d⟩

/-- **Theorem C (LB⁺ never fails).** For every processing order of Phase 1 with R1 priority (any choice at
every R1 step and every insertion step), LB⁺ returns a complete allocation that is EFX₀ for every additive
valuation consistent with the rankings (each agent values exactly its three goods, `a ≥ b ≥ c > 0`,
`a ≤ b + c`), and in which at most one bundle has more than two goods. -/
theorem lbPlus_sound (d : A) (hag : agents.Nodup) (hgd : goods.Nodup) (hne : agents ≠ [])
    (hWF : WF P agents goods) (hord : order.Nodup) (hperm : ∀ i, i ∈ order ↔ i ∈ agents)
    (hR : R1Prio P order goods) :
    IsAllocation agents goods (lbPlus P agents goods order d) ∧
    (∀ v : A → G → Nat, P.Consistent agents v → EFX0L v agents goods (lbPlus P agents goods order d)) ∧
    ∃ o, ∀ j ∈ agents, j ≠ o → (bundle goods (lbPlus P agents goods order d) j).length ≤ 2 :=
  lbPlusRun_sound d hag hgd hWF hord hperm hR (lbPlus_run d hag hgd hne hWF hord hperm hR)

end theoremC

/-- **Theorem C, in the model's terms.** Agents `Fin n` (`n ≥ 1`), goods `Fin m`, a ranking profile `P` in
which each agent ranks three distinct goods, and a processing order of all agents with R1 priority. LB⁺'s
allocation is EFX₀ for every additive valuation consistent with `P`, and all its bundles but one have at
most two goods. -/
theorem lbPlus_sound_model {n m : Nat} (P : Profile (Fin n) (Fin m)) (hn : 0 < n)
    (hdist : ∀ i, P.a i ≠ P.b i ∧ P.a i ≠ P.c i ∧ P.b i ≠ P.c i)
    (order : List (Fin n)) (hord : order.Nodup) (hperm : ∀ i, i ∈ order)
    (hR : R1Prio P order (List.finRange m)) :
    (∀ v : Fin n → Fin m → Nat, P.Consistent (List.finRange n) v →
      (Inst.mk n m v).EFX0 (lbPlus P (List.finRange n) (List.finRange m) order ⟨0, hn⟩)) ∧
    ∃ o, ∀ j, j ≠ o →
      finSum m (fun g => if lbPlus P (List.finRange n) (List.finRange m) order ⟨0, hn⟩ g = j then 1 else 0)
        ≤ 2 := by
  obtain ⟨-, h1, o, h2⟩ := lbPlus_sound (P := P) ⟨0, hn⟩ (List.nodup_finRange n)
    (List.nodup_finRange m) (List.ne_nil_of_mem (List.mem_finRange ⟨0, hn⟩))
    (fun i _ => ⟨List.mem_finRange _, List.mem_finRange _, List.mem_finRange _, hdist i⟩) hord
    (fun i => ⟨fun _ => List.mem_finRange i, fun _ => hperm i⟩) hR
  refine ⟨fun v hv => (Inst.efx0_iff (Inst.mk n m v) _).mpr (h1 v hv), o, fun j hj => ?_⟩
  rw [finSum_bundle_eq]
  exact h2 j (List.mem_finRange j) hj

/-! ## Examples (checked by `decide`) -/

/-- A connected core with `n = 3`, `m = 5`: rankings `(0, 2, 3)`, `(2, 1, 4)`, `(0, 2, 1)`. -/
def exampleP3 : Profile Nat Nat :=
  ⟨fun i => [0, 2, 0].getD i 0, fun i => [2, 1, 2].getD i 0, fun i => [3, 4, 1].getD i 0⟩

/-- Phase 1 in the order `1, 0, 2` has R1 priority: agent 1 is inserted (takes good 2), then agents 0 and 2
are R1 steps (goods 0 and 1). -/
example : R1Prio exampleP3 [1, 0, 2] [0, 1, 2, 3, 4] := by decide

/-- On this run LB fails: no agent is a valid owner of the overflow bundle. -/
example : lb exampleP3 [0, 1, 2] [0, 1, 2, 3, 4] [1, 0, 2] 0 = none := by decide

/-- LB⁺ reaches the bad case (`r = 2`, `k* = 1`, need chain `1 → 2`) and rotates: agent 2 takes good 2,
agent 1 is upgraded to `{1, 4}`, and the junk good 3 fits agent 2's slot. The result is
`{0}, {1, 4}, {2, 3}`. -/
example : [0, 1, 2, 3, 4].map (lbPlus exampleP3 [0, 1, 2] [0, 1, 2, 3, 4] [1, 0, 2] 0) = [0, 1, 2, 2, 1] := by
  decide

/-- The need chain LB⁺ rotates along in the run above: `1 → 2`. -/
example :
    let Y := phase1 exampleP3 [1, 0, 2] [0, 1, 2, 3, 4]
    chainFrom exampleP3 [0, 1, 2] (lbUp exampleP3 [0, 1, 2] [0, 1, 2, 3, 4] Y) Y 1 (after [1, 0, 2] 1) = [2] := by
  decide

/-- A connected core with `n = 5`, `m = 8`: rankings `(0, 2, 5)`, `(4, 1, 6)`, `(4, 3, 7)`, `(0, 1, 4)`,
`(4, 2, 3)`. -/
def exampleP5 : Profile Nat Nat :=
  ⟨fun i => [0, 4, 4, 0, 4].getD i 0, fun i => [2, 1, 3, 1, 2].getD i 0, fun i => [5, 6, 7, 4, 3].getD i 0⟩

example : R1Prio exampleP5 [1, 3, 0, 2, 4] [0, 1, 2, 3, 4, 5, 6, 7] := by decide

/-- With Phase 1 in the order `1, 3, 0, 2, 4`, LB⁺ rotates along the need chain `1 → 2 → 4`, and
`k* = 1`, now upgraded, owns the large bundle `{1, 6, 7}` (the same allocation as `src/lbplus.py` on
`proof/lb-last-step`). -/
example : [0, 1, 2, 3, 4, 5, 6, 7].map
    (lbPlus exampleP5 [0, 1, 2, 3, 4] [0, 1, 2, 3, 4, 5, 6, 7] [1, 3, 0, 2, 4] 0) = [3, 1, 0, 4, 2, 4, 1, 1] := by
  decide

/-- A core with `n = 5`, `m = 8`: rankings `(5, 0, 2)`, `(1, 2, 6)`, `(3, 4, 7)`, `(3, 4, 0)`, `(1, 3, 4)`. -/
def exampleQ5 : Profile Nat Nat :=
  ⟨fun i => [5, 1, 3, 3, 1].getD i 0, fun i => [0, 2, 4, 4, 3].getD i 0, fun i => [2, 6, 7, 0, 4].getD i 0⟩

/-- With Phase 1 in the order `0, 1, 4, 3, 2` (agents 0 and 1 inserted), `r = 2`, and agents 0 and 1 are
exposed for `r` with junk parts `{0, 2}` and `{2, 6}`: one good per exposed pair would need two slots, but
only one is free. `r` is still a valid owner, through the shared good 2 (`hitSet = [2]`), and LB⁺ gives it the
large bundle `{0, 6, 7}` without rotating. -/
example : R1Prio exampleQ5 [0, 1, 4, 3, 2] [0, 1, 2, 3, 4, 5, 6, 7] := by decide

example :
    let Y := phase1 exampleQ5 [0, 1, 4, 3, 2] [0, 1, 2, 3, 4, 5, 6, 7]
    let up := lbUp exampleQ5 [0, 1, 2, 3, 4] [0, 1, 2, 3, 4, 5, 6, 7] Y
    lastOut up [0, 1, 4, 3, 2] = some 2 ∧
    exposedL exampleQ5 [0, 1, 2, 3, 4] up Y [0, 1, 2, 3, 4, 5, 6, 7] 2 = [0, 1] ∧
    hitSet exampleQ5 (junkList exampleQ5 [0, 1, 2, 3, 4] up Y [0, 1, 2, 3, 4, 5, 6, 7])
      (exposedL exampleQ5 [0, 1, 2, 3, 4] up Y [0, 1, 2, 3, 4, 5, 6, 7] 2) = [2] ∧
    ([0, 1, 2, 3, 4].map (slotsExcept (cap exampleQ5 [0, 1, 2, 3, 4] up Y) (some 2))).sum = 1 := by
  decide

example : [0, 1, 2, 3, 4, 5, 6, 7].map
    (lbPlus exampleQ5 [0, 1, 2, 3, 4] [0, 1, 2, 3, 4, 5, 6, 7] [0, 1, 4, 3, 2] 0) = [2, 1, 0, 4, 3, 0, 2, 2] := by
  decide

/-- The need chain of that run: `1 → 2 → 4`. -/
example :
    let Y := phase1 exampleP5 [1, 3, 0, 2, 4] [0, 1, 2, 3, 4, 5, 6, 7]
    chainFrom exampleP5 [0, 1, 2, 3, 4] (lbUp exampleP5 [0, 1, 2, 3, 4] [0, 1, 2, 3, 4, 5, 6, 7] Y) Y 1
      (after [1, 3, 0, 2, 4] 1) = [2, 4] := by
  decide

end LB
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB.lbPlusRun_sound
#print axioms EFX.LB.lbPlusOut_exists
#print axioms EFX.LB.lbPlusOut_exists_chain
#print axioms EFX.LB.state_of_final
#print axioms EFX.LB.lbPlus_run
#print axioms EFX.LB.lbPlus_sound
#print axioms EFX.LB.lbPlus_sound_model
