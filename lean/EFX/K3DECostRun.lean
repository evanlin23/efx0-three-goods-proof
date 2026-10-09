import EFX.K3DECostStep

/-!
# The running time of Draft and Exchange, part 3: the counted program `deC` computes `deSpec`

Algorithm DE (`paper/k3-simple/long.tex` §6, Algorithm `alg:de`) as a counted program over the model's instances,
built from the parts of `EFX.K3DECost` and `EFX.K3DECostStep`; units as in `EFX.K3DECost`.

- **Reading the input** (`deC`): the lists of agents and goods, and for each agent its relevant goods among all
  goods (`rel`, one value read and one comparison per pair: `O(nm)`), and an array marking the remaining goods.
- **Peeling** (`peelC`, as `EFX.DE.run`): each round tests rule R1 from the relevant goods of each agent
  (`EFX.DE.findR1F`), removes the agent (and its good) from the lists, unmarks its good, and writes the good's
  owner into the allocation returned by the rest (`wr`, the value of `EFX.extend`).
- **The core** (`coreC`, as `EFX.DE.deStage`): the rankings by sorting each agent's (three) relevant remaining goods
  (`profC`), the draft (`draftC`, Phase 1 with an array of available goods), the loop (`loopC`, `4n + 1` rounds of
  `EFX.DE.stepC` at most, as `EFX.DE.loop`), and the completion (`completeC`, as `EFX.DE.completeDE`: the tables of
  the final state and the slots filled by one pass over the agents, `fillC`).

**Results.** **`de_eq_spec`**: `(deC I hn).val = deSpec I hn`, on every instance (no hypothesis). The algorithm is
`de I hn := (deC I hn).val`, and `deC_correct` restates Theorem "DE is correct" (`deSpec_correct`) for it. The value
lemmas of the parts: `draftC_val`, `loopC_val`, `fillC_val`, `completeC_val`, `profC_val`, `coreC_val`, `peelC_val`.
The cost bound is `EFX.DE.deC_cost` (`EFX.K3DECostBound`).

**Choices.**
1. The relevant goods of each agent are computed once among all goods; those that remain are found by reading the
   array of remaining goods (`relevant_filter`: the remaining goods stay a sublist of all goods, in index order).
2. The allocation of the peeled goods is written into the array that the rest returns (`EFX.extend` is one write);
   the base cases return a new array (`m` units).
3. The loop counts the exchanges as `EFX.DE.loop` does (the field `moves` of the result), one addition per round.
-/

set_option autoImplicit false

namespace EFX
namespace DE

open Timed LB Profile

section fin
variable {n m : Nat}

/-! ## The draft -/

/-- `fav P pool i` from an array of the available goods: three profile reads, three array reads. -/
def favT (P : Profile (Fin n) (Fin m)) (avail : Fin m → Bool) (i : Fin n) : Timed (Option (Fin m)) := do
  let a ← rd P.a i
  let b ← rd P.b i
  let c ← rd P.c i
  let xa ← rd avail a
  let xb ← rd avail b
  let xc ← rd avail c
  pure (bif xa then some a else bif xb then some b else bif xc then some c else none)

/-- Unmark the pick (if any) in the array of available goods. -/
def removeT (avail : Fin m → Bool) : Option (Fin m) → Timed (Fin m → Bool)
  | none => pure avail
  | some y => wr avail y false

/-- **The draft** (`EFX.LB.phase1`): serial dictatorship in the order of the list, with an array of the available
goods; each agent's pick is written into a new array. -/
def draftC (P : Profile (Fin n) (Fin m)) : List (Fin n) → (Fin m → Bool) → Timed (Fin n → Option (Fin m))
  | [], _ => constT n none
  | i :: order, avail => do
    tick 1
    let f ← favT P avail i
    let avail' ← removeT avail f
    let Y ← draftC P order avail'
    wr Y i f

theorem favT_val (P : Profile (Fin n) (Fin m)) {pool : List (Fin m)} {avail : Fin m → Bool}
    (h : ∀ g, avail g = decide (g ∈ pool)) (i : Fin n) : (favT P avail i).val = fav P pool i := by
  simp only [favT, bind_val, rd_val, pure_val, h, fav]
  by_cases ha : P.a i ∈ pool
  · simp [ha]
  · by_cases hb : P.b i ∈ pool
    · simp [ha, hb]
    · by_cases hc : P.c i ∈ pool <;> simp [ha, hb, hc]

theorem removeT_val {pool : List (Fin m)} (hp : pool.Nodup) {avail : Fin m → Bool}
    (h : ∀ g, avail g = decide (g ∈ pool)) (f : Option (Fin m)) :
    ∀ g, (removeT avail f).val g = decide (g ∈ removePick pool f) := by
  intro g
  cases f with
  | none => exact h g
  | some y =>
    simp only [removeT, wr_val, removePick]
    rw [h g]
    by_cases e : g = y
    · subst e; simp [List.Nodup.mem_erase_iff hp]
    · simp [e, List.Nodup.mem_erase_iff hp]

theorem draftC_val (P : Profile (Fin n) (Fin m)) : ∀ (order : List (Fin n)) (pool : List (Fin m))
    (avail : Fin m → Bool), pool.Nodup → (∀ g, avail g = decide (g ∈ pool)) →
    (draftC P order avail).val = phase1 P order pool
  | [], _, _, _, _ => by funext k; simp [draftC, phase1]
  | i :: order, pool, avail, hp, h => by
    simp only [draftC, bind_val, wr_val]
    rw [draftC_val P order (removePick pool (fav P pool i)) _ (nodup_removePick hp _)
      (by rw [favT_val P h i]; exact removeT_val hp h _)]
    funext k
    rw [favT_val P h i]
    rfl

/-! ## The loop -/

/-- **The loop of DE** (`EFX.DE.loop`): `stepC` until it stops, at most `fuel` rounds. -/
def loopC (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (inA : Fin n → Bool) (inG : Fin m → Bool)
    (d : Fin n) (l : Nat) :
    Nat → (Fin n → Option (Fin m)) → List (Fin n) → Nat → Timed (Result (Fin n) (Fin m))
  | 0, Y, up, k => pure ⟨d, [], Y, up, k⟩
  | fuel + 1, Y, up, k => do
    let o ← stepC P agents inA inG d l Y up
    match o with
    | .stop o H => pure ⟨o, H, Y, up, k⟩
    | .next Y' up' => do
      tick 1
      loopC P agents inA inG d l fuel Y' up' (k + 1)

theorem loopC_val (P : Profile (Fin n) (Fin m)) {agents : List (Fin n)} {inA : Fin n → Bool} {inG : Fin m → Bool}
    {goods : List (Fin m)} (d : Fin n) (hA : ∀ k, inA k = agents.contains k)
    (hG : ∀ g, inG g = decide (g ∈ goods)) :
    ∀ (fuel : Nat) (Y : Fin n → Option (Fin m)) (up : List (Fin n)) (k : Nat),
      (loopC P agents inA inG d agents.length fuel Y up k).val = loop P agents goods d fuel Y up k
  | 0, _, _, _ => rfl
  | fuel + 1, Y, up, k => by
    simp only [loopC, loop, bind_val, stepC_val P d Y up hA hG]
    cases step P agents goods d Y up with
    | stop o H => rfl
    | next Y' up' => exact loopC_val P d hA hG fuel Y' up' (k + 1)

/-! ## The completion -/

/-- **The slots** (`EFX.LB.fill` with `slot1`): one pass over the agents, each free agent other than `o` taking the
next good of `H` (written into `T` unless the good has an agent already: `fill` gives the first). -/
def fillC (free : Fin n → Bool) (o : Fin n) : List (Fin n) → List (Fin m) → (Fin m → Option (Fin n)) →
    Timed (Fin m → Option (Fin n))
  | [], _, T => pure T
  | _ :: _, [], T => pure T
  | k :: ks, h :: hs, T => do
    tick 2
    let f ← rd free k
    bif (k != o) && f then do
      let t ← rd T h
      let T' ← wr T h (t.or (some k))
      fillC free o ks hs T'
    else fillC free o ks (h :: hs) T

theorem fill_nil_rest {A G : Type} [DecidableEq G] (s : A → Nat) : ∀ (ks : List A) (g : G),
    fill s ks [] g = none
  | [], _ => rfl
  | k :: ks, g => by simp [fill, fill_nil_rest s ks g]

theorem fillC_val (P : Profile (Fin n) (Fin m)) (agents up : List (Fin n)) (Y : Fin n → Option (Fin m)) (o : Fin n) :
    ∀ (ks : List (Fin n)) (rest : List (Fin m)) (T : Fin m → Option (Fin n)),
    (fillC (freeB P agents up Y) o ks rest T).val = fun g => (T g).or (fill (slot1 P agents up Y o) ks rest g)
  | [], _, T => by funext g; simp [fillC, fill]
  | k :: ks, [], T => by funext g; simp [fillC, fill_nil_rest]
  | k :: ks, h :: hs, T => by
    funext g
    simp only [fillC, bind_val, rd_val]
    by_cases hs1 : k ≠ o ∧ freeB P agents up Y k = true
    · have hb : ((k != o) && freeB P agents up Y k) = true := by simp [hs1.1, hs1.2]
      have h1 : slot1 P agents up Y o k = 1 := by simp [slot1, hs1]
      simp only [hb, Bool.cond_true, bind_val, rd_val, wr_val]
      rw [fillC_val P agents up Y o ks hs]
      simp only [fill, h1, List.take_succ_cons, List.take_zero, List.mem_singleton, List.drop_succ_cons,
        List.drop_zero]
      by_cases e : g = h
      · subst e; cases T g <;> simp
      · simp [e]
    · have hb : ((k != o) && freeB P agents up Y k) = false := by
        cases hk : freeB P agents up Y k
        · simp
        · have : k = o := Classical.byContradiction fun hne => hs1 ⟨hne, hk⟩
          subst this
          simp
      have h0 : slot1 P agents up Y o k = 0 := by simp [slot1, hs1]
      simp only [hb, Bool.cond_false]
      rw [fillC_val P agents up Y o ks (h :: hs)]
      simp [fill, h0]

/-- The agent of `g` in the completion: its holder, else the pair holder whose `c` it is, else its slot, else `o`. -/
def compEntryC (holder upc fl : Fin m → Option (Fin n)) (o : Fin n) (g : Fin m) : Timed (Fin n) := do
  let h ← rd holder g
  match h with
  | some k => pure k
  | none => do
    let u ← rd upc g
    match u with
    | some u => pure u
    | none => do
      let f ← rd fl g
      pure (f.getD o)

/-- **The completion** (`EFX.DE.completeDE`): the tables of the final state, the slots, and one table over the
goods. -/
def completeC (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (inA : Fin n → Bool) (inG : Fin m → Bool)
    (r : Result (Fin n) (Fin m)) : Timed (Fin m → Fin n) := do
  let tb ← tabsC P agents inA inG r.Y r.up
  let T0 ← constT m none
  let fl ← fillC tb.free r.o agents r.H T0
  mkTable m (compEntryC tb.holder tb.upc fl r.o)

theorem completeC_val (P : Profile (Fin n) (Fin m)) {agents : List (Fin n)} {inA : Fin n → Bool}
    {inG : Fin m → Bool} {goods : List (Fin m)} (hA : ∀ k, inA k = agents.contains k)
    (hG : ∀ g, inG g = decide (g ∈ goods)) (r : Result (Fin n) (Fin m)) :
    (completeC P agents inA inG r).val = completeDE P agents r.up r.Y r.o r.H := by
  funext g
  simp only [completeC, bind_val, tabsC_val P r.Y r.up hA hG, constT_val, mkTable_val, compEntryC, specTabs]
  rw [fillC_val]
  unfold completeDE
  simp only [rd_val]
  cases picker agents r.Y g with
  | some k => rfl
  | none =>
    simp only [bind_val, rd_val]
    cases upOf P r.up g with
    | some u => rfl
    | none => simp

/-! ## The core stage -/

/-- Agent `i`'s ranking: its relevant remaining goods, sorted. -/
def profEntryC (v : Fin n → Fin m → Nat) (rel : Fin n → List (Fin m)) (inG : Fin m → Bool) (g0 : Fin m)
    (i : Fin n) :
    Timed (Fin m × Fin m × Fin m) := do
  let R ← rd rel i
  let R' ← filterC (rd inG) R
  K3.sort3C (v i) g0 R'

/-- **The rankings** (`EFX.K3.profileOf`): each agent's relevant remaining goods, sorted (`EFX.K3.sort3C`). -/
def profC (v : Fin n → Fin m → Nat) (rel : Fin n → List (Fin m)) (inG : Fin m → Bool) (g0 : Fin m) :
    Timed (Profile (Fin n) (Fin m)) := do
  let t ← mkTable n (profEntryC v rel inG g0)
  pure ⟨fun i => (t i).1, fun i => (t i).2.1, fun i => (t i).2.2⟩

theorem profC_val (v : Fin n → Fin m → Nat) {rel : Fin n → List (Fin m)} {inG : Fin m → Bool}
    {goods : List (Fin m)} (g0 : Fin m) (hrel : ∀ i, rel i = relevant v i (List.finRange m))
    (hinG : ∀ g, inG g = decide (g ∈ goods)) (hsub : goods.Sublist (List.finRange m)) :
    (profC v rel inG g0).val = K3.profileOf v goods g0 := by
  have hR : ∀ i, (rel i).filter (fun g => inG g) = relevant v i goods := fun i => by
    rw [hrel i, ← relevant_filter v i hsub]
    exact List.filter_congr fun g _ => hinG g
  simp only [profC, profEntryC, bind_val, mkTable_val, rd_val, filterC_val, K3.sort3C, pure_val, hR,
    K3.profileOf]

/-- **The core stage of DE** (`EFX.DE.deStage`): rankings, draft, loop (`4n + 1` rounds at most), completion. -/
def coreC (v : Fin n → Fin m → Nat) (rel : Fin n → List (Fin m)) (inG : Fin m → Bool) (agents : List (Fin n))
    (g0 : Fin m) (d : Fin n) : Timed (Fin m → Fin n) := do
  let P ← profC v rel inG g0
  let A0 ← constT n false
  let inA ← setAllC true agents A0
  let av ← mkTable m (rd inG)
  let Y0 ← draftC P agents av
  let l ← lengthC agents
  tick 2
  let r ← loopC P agents inA inG d l (4 * l + 1) Y0 [] 0
  completeC P agents inA inG r

theorem coreC_val (v : Fin n → Fin m → Nat) {rel : Fin n → List (Fin m)} {inG : Fin m → Bool}
    (agents : List (Fin n)) {goods : List (Fin m)} (g0 : Fin m) (d : Fin n)
    (hrel : ∀ i, rel i = relevant v i (List.finRange m)) (hinG : ∀ g, inG g = decide (g ∈ goods))
    (hsub : goods.Sublist (List.finRange m)) (hgd : goods.Nodup) :
    (coreC v rel inG agents g0 d).val = (deStage v agents goods g0 d).1 := by
  have hA : ∀ k, (setAllC true agents (fun _ : Fin n => false)).val k = agents.contains k := by
    intro k; rw [setAllC_val]; by_cases h : k ∈ agents <;> simp [h]
  have hav : ∀ g, (mkTable m (rd inG)).val g = decide (g ∈ goods) := by
    intro g; simp [hinG g]
  simp only [coreC, bind_val, profC_val v g0 hrel hinG hsub, constT_val, lengthC_val]
  rw [draftC_val _ agents goods _ hgd hav, loopC_val _ d hA hinG, completeC_val _ hA hinG]
  rfl

/-! ## Peeling, and the whole algorithm -/

/-- **Algorithm DE, over lists, as a counted program** (`EFX.DE.run`): peel by R1 from the relevant goods while it
applies (at least two agents and some goods left), then the core stage. `inG` marks the remaining goods. -/
def peelC (v : Fin n → Fin m → Nat) (rel : Fin n → List (Fin m)) (d : Fin n) :
    Nat → List (Fin n) → List (Fin m) → (Fin m → Bool) → Timed (Fin m → Fin n)
  | 0, _, _, _ => constT m d
  | fuel + 1, agents, goods, inG => do
    let l ← lengthC agents
    tick 1
    if l ≤ 1 then constT m (agents.headD d)
    else
      match goods with
      | [] => constT m d
      | g0 :: gs => do
        let f ← findR1F v rel inG agents
        match f with
        | some (i, none) => do
          let agents' ← eraseC i agents
          peelC v rel d fuel agents' (g0 :: gs) inG
        | some (i, some p) => do
          let agents' ← eraseC i agents
          let goods' ← eraseC p (g0 :: gs)
          let inG' ← wr inG p false
          let X ← peelC v rel d fuel agents' goods' inG'
          wr X p i
        | none => coreC v rel inG agents g0 d

theorem peelC_val (v : Fin n → Fin m → Nat) {rel : Fin n → List (Fin m)} (d : Fin n)
    (hrel : ∀ i, rel i = relevant v i (List.finRange m)) : ∀ (fuel : Nat) (agents : List (Fin n))
    (goods : List (Fin m)) (inG : Fin m → Bool), (∀ g, inG g = decide (g ∈ goods)) →
    goods.Sublist (List.finRange m) → goods.Nodup →
    (peelC v rel d fuel agents goods inG).val = (run v d fuel agents goods).1
  | 0, _, _, _, _, _, _ => by simp [peelC, run]
  | fuel + 1, agents, goods, inG, hinG, hsub, hgd => by
    unfold peelC run
    simp only [bind_val, lengthC_val]
    split
    · simp
    cases goods with
    | nil => simp
    | cons g0 gs =>
      simp only [bind_val, findR1F_val v agents hrel hinG hsub]
      cases K3.findR1 v agents (g0 :: gs) with
      | some q =>
        obtain ⟨i, s⟩ := q
        cases s with
        | none =>
          simp only [bind_val, eraseC_val]
          exact peelC_val v d hrel fuel _ _ inG hinG hsub hgd
        | some p =>
          simp only [bind_val, eraseC_val, wr_val]
          rw [peelC_val v d hrel fuel _ ((g0 :: gs).erase p) _ (fun g => by
              simp only [hinG g]
              by_cases e : g = p
              · subst e; simp [List.Nodup.mem_erase_iff hgd]
              · simp [e, List.Nodup.mem_erase_iff hgd])
            (List.erase_sublist.trans hsub) (hgd.erase p)]
          rfl
      | none =>
        simp only
        exact coreC_val v agents g0 d hrel hinG hsub hgd

/-- `0 < v i g`: one value read and one comparison. -/
def posC (v : Fin n → Fin m → Nat) (i : Fin n) (g : Fin m) : Timed Bool := do
  tick 2
  pure (decide (0 < v i g))

/-- Agent `i`'s relevant goods among `goods`. -/
def relEntryC (v : Fin n → Fin m → Nat) (goods : List (Fin m)) (i : Fin n) : Timed (List (Fin m)) :=
  filterC (posC v i) goods

/-- **Algorithm DE as a counted program** on an instance with `n ≥ 1` agents: read the input (the lists of agents
and goods, each agent's relevant goods), then peel and run the core (`peelC`). -/
def deC (I : Inst) (hn : 0 < I.n) : Timed I.Alloc := do
  let agents ← K3.finRangeC I.n
  let goods ← K3.finRangeC I.m
  let rel ← mkTable I.n (relEntryC I.v goods)
  let inG ← constT I.m true
  peelC I.v rel ⟨0, hn⟩ I.n agents goods inG

/-- **Algorithm DE** (`paper/k3-simple/long.tex`, Algorithm `alg:de`): the allocation `deC` computes. -/
def de (I : Inst) (hn : 0 < I.n) : I.Alloc := (deC I hn).val

/-- **`deC` computes the specification** `EFX.DE.deSpec`, on every instance. -/
theorem de_eq_spec (I : Inst) (hn : 0 < I.n) : (deC I hn).val = deSpec I hn := by
  simp only [deC, bind_val, K3.finRangeC, pure_val, constT_val, deSpec]
  apply peelC_val I.v ⟨0, hn⟩
  · intro i
    simp [relEntryC, posC, relevant]
  · intro g; simp
  · exact List.Sublist.refl _
  · exact List.nodup_finRange _

/-- **Theorem DE is correct**, for the counted algorithm: on every instance in which every agent positively values at
most three goods, `de I hn` is EFX₀ and all bundles but at most one have at most two goods. -/
theorem deC_correct (I : Inst) (hn : 0 < I.n) (h : ∀ i, numRelevant I i ≤ 3) :
    I.EFX0 (de I hn) ∧ ∃ o, ∀ j, j ≠ o → finSum I.m (fun g => if de I hn g = j then 1 else 0) ≤ 2 := by
  obtain ⟨h1, h2, -⟩ := deSpec_correct I hn h
  simp only [de, de_eq_spec]
  exact ⟨h1, h2⟩

end fin

end DE
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE.draftC_val
#print axioms EFX.DE.loopC_val
#print axioms EFX.DE.fillC_val
#print axioms EFX.DE.completeC_val
#print axioms EFX.DE.coreC_val
#print axioms EFX.DE.peelC_val
#print axioms EFX.DE.de_eq_spec
#print axioms EFX.DE.deC_correct
