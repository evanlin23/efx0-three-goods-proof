import EFX.K3CostLB

/-!
# The algorithm `EFX.K3.algo` as a counted program (`proofs/k3_algorithm.md` §6)

`algoC I hn : Timed I.Alloc` is algorithm K3ALG written in the cost monad `EFX.Timed`, with the functions that
the specification `EFX.K3.algoSpec` recomputes (the profile, Phase 1's picks, the blocks, the slots, the rotated
picks) stored in arrays (`EFX.Timed.mkTable`), and the output tabulated over the goods.

- `algo I hn := (algoC I hn).val`: **the algorithm**.
- `algo_eq_spec`: it computes `algoSpec`, the composition of proven constructions of `EFX.K3Algo`.
- `algo_efx0`: **correctness**: if every agent positively values at most three goods, `algo I hn` is EFX₀.
- The running-time theorem `algoC_cost` is in `EFX.K3CostBound`.

What one counted unit stands for is listed in `EFX.K3CostLB`. In addition: building `List.finRange k` costs `k`;
reading the input `v i g` costs one; the tables filled here are arrays filled once, at the cost of their
entries' evaluations plus one per entry.
-/

set_option autoImplicit false

namespace EFX
namespace K3

open Timed LB

/-! ## Rule R1 as a counted program (generic) -/

section generic
variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- `favorite f S` with `f` a counted function (a value read): one comparison per good. -/
def favoriteC (f : G → Timed Nat) : List G → Timed (Option G)
  | [] => pure none
  | g :: S => do
    let r ← favoriteC f S
    match r with
    | none => do tick 1; pure (some g)
    | some h => do
      let fh ← f h
      let fg ← f g
      tick 1
      pure (if fh ≤ fg then some g else some h)

/-- `value v i S`: one value read per good (and one addition, counted by `sumMapC`). -/
def valueC (v : A → G → Nat) (i : A) (S : List G) : Timed Nat :=
  sumMapC (fun g => do tick 1; pure (v i g)) S

/-- `r1Step v goods i`: the favourite, two value reads and a comparison with `0`, the other goods' value, and a
comparison. -/
def r1StepC (v : A → G → Nat) (goods : List G) (i : A) : Timed (Option (Option G)) := do
  let fp ← favoriteC (fun g => do tick 1; pure (v i g)) goods
  match fp with
  | none => pure (some none)
  | some p => do
    tick 2
    if v i p = 0 then pure (some none) else do
      let rest ← eraseC p goods
      let s ← valueC v i rest
      tick 2
      pure (if s ≤ v i p then some (some p) else none)

/-- `findR1 v agents goods`. -/
def findR1C (v : A → G → Nat) (agents : List A) (goods : List G) : Timed (Option (A × Option G)) :=
  findSomeC (fun i => do
    let s ← r1StepC v goods i
    pure (s.map (fun s => (i, s)))) agents

omit [DecidableEq G] in
@[simp] theorem favoriteC_val (f : G → Timed Nat) : ∀ S : List G,
    (favoriteC f S).val = favorite (fun g => (f g).val) S
  | [] => rfl
  | g :: S => by
    unfold favoriteC favorite
    simp only [bind_val, favoriteC_val f S]
    cases favorite (fun g => (f g).val) S with
    | none => rfl
    | some h => simp only [bind_val, pure_val]

omit [DecidableEq A] [DecidableEq G] in
@[simp] theorem valueC_val (v : A → G → Nat) (i : A) (S : List G) : (valueC v i S).val = value v i S := by
  simp [valueC, value]

omit [DecidableEq A] in
@[simp] theorem r1StepC_val (v : A → G → Nat) (goods : List G) (i : A) : (r1StepC v goods i).val = r1Step v goods i := by
  unfold r1StepC r1Step
  simp only [bind_val, favoriteC_val]
  cases favorite (v i) goods with
  | none => rfl
  | some p =>
    by_cases h0 : v i p = 0
    · simp [h0]
    · simp [h0]

omit [DecidableEq A] in
@[simp] theorem findR1C_val (v : A → G → Nat) (agents : List A) (goods : List G) :
    (findR1C v agents goods).val = findR1 v agents goods := by
  simp [findR1C, findR1]

end generic

/-! ## The algorithm on the model's instances -/

section fin
variable {n m : Nat}

/-- `sort3` of a list: at most four list cells inspected, three value reads, three comparisons. -/
def sort3C (f : Fin m → Nat) (g0 : Fin m) (l : List (Fin m)) : Timed (Fin m × Fin m × Fin m) := do
  tick 10
  pure (sort3 f g0 l)

/-- The profile `profileOf v goods g0`, stored in an array: each agent's relevant goods (one value read and one
comparison per good), sorted. -/
def profTabC (v : Fin n → Fin m → Nat) (goods : List (Fin m)) (g0 : Fin m) : Timed (Profile (Fin n) (Fin m)) := do
  let t ← mkTable n (fun i => do
    let rel ← filterC (fun g => do tick 2; pure (decide (0 < v i g))) goods
    sort3C (v i) g0 rel)
  pure ⟨fun i => (t i).1, fun i => (t i).2.1, fun i => (t i).2.2⟩

/-- `complete P agents up Y goods o H d`, tabulated over the goods, from the slot table `capT` and the junk `J`. -/
def completeTabC (P : Profile (Fin n) (Fin m)) (agents up : List (Fin n)) (Y : Fin n → Option (Fin m))
    (capT : Fin n → Nat) (J : List (Fin m)) (o : Option (Fin n)) (H : List (Fin m)) (d : Fin n) :
    Timed (Fin m → Fin n) := do
  let L ← placeListC H J
  mkTable m (fun g => completeOneC P agents up Y o d (slotsExcept capT o) L g)

/-- **LB⁺** (`EFX.LB.lbPlus`) as a counted program: Phase 1's picks, the slots, the blocks and the rotated picks
are tables. -/
def lbPlusC (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (goods : List (Fin m)) (order : List (Fin n))
    (d : Fin n) : Timed (Fin m → Fin n) := do
  let Y ← mkTable n (fun k => phase1C P order goods k)
  let up ← lbUpC P agents goods Y
  let J ← junkListC P agents up Y goods
  let capT ← mkTable n (capC P agents up Y)
  let S ← sumTabC capT agents
  let lJ ← lengthC J
  tick 1
  if lJ ≤ S then completeTabC P agents up Y capT J none [] d
  else do
    let lo ← lastOutC up order
    match lo with
    | none => completeTabC P agents up Y capT J none [] d
    | some r => do
      let E ← exposedLC P agents up Y J r
      let H ← hitSetC P J E
      let lH ← lengthC H
      let Sr ← sumExceptC capT (some r) agents
      tick 1
      if lH ≤ Sr then completeTabC P agents up Y capT J (some r) H d
      else do
        let blk ← mkTable n (fun k => blkAuxC P order goods 0 k)
        let ks ← kstarC blk E r
        match ks with
        | none => completeTabC P agents up Y capT J (some r) H d
        | some k => do
          let af ← afterC order k
          let ch ← chainFromC P agents up Y k af
          let Y' ← mkTable n (fun x => rotPicksC P Y k ch x)
          let J' ← junkListC P agents (k :: up) Y' goods
          let capT' ← mkTable n (capC P agents (k :: up) Y')
          let S' ← sumTabC capT' agents
          let lJ' ← lengthC J'
          tick 1
          if lJ' ≤ S' then completeTabC P agents (k :: up) Y' capT' J' none [] d
          else do
            let E' ← exposedLC P agents (k :: up) Y' J' k
            let H' ← hitSetC P J' E'
            completeTabC P agents (k :: up) Y' capT' J' (some k) H' d

/-- **The algorithm's peeling loop** (`EFX.K3.reduce`) as a counted program. It returns the goods peeled with
their agents, and the allocation of the rest (a constant or an LB⁺ table). -/
def reduceC (v : Fin n → Fin m → Nat) (d : Fin n) :
    Nat → List (Fin n) → List (Fin m) → Timed (List (Fin n × Fin m) × (Fin m → Fin n))
  | 0, _, _ => pure ([], fun _ => d)
  | fuel + 1, agents, goods => do
    let l ← lengthC agents
    tick 1
    if l ≤ 1 then pure ([], fun _ => agents.headD d)
    else
      match goods with
      | [] => pure ([], fun _ => d)
      | g0 :: gs => do
        let f ← findR1C v agents (g0 :: gs)
        match f with
        | some (i, none) => do
          let agents' ← eraseC i agents
          reduceC v d fuel agents' (g0 :: gs)
        | some (i, some p) => do
          let agents' ← eraseC i agents
          let goods' ← eraseC p (g0 :: gs)
          let r ← reduceC v d fuel agents' goods'
          pure ((i, p) :: r.1, r.2)
        | none => do
          let P ← profTabC v (g0 :: gs) g0
          let l' ← lengthC agents
          let order ← r1OrderC P l' agents (g0 :: gs)
          let X ← lbPlusC P agents (g0 :: gs) order d
          pure ([], X)

/-- `List.finRange k`, one unit per element. -/
def finRangeC (k : Nat) : Timed (List (Fin k)) := do
  tick k
  pure (List.finRange k)

end fin

/-- **Algorithm K3ALG as a counted program.** Peel by R1, run LB⁺ on the rest, and tabulate the allocation: for
each good, look it up among the peeled goods (one comparison per peeled good), else read the rest's table. -/
def algoC (I : Inst) (hn : 0 < I.n) : Timed I.Alloc := do
  let agents ← finRangeC I.n
  let goods ← finRangeC I.m
  let r ← reduceC I.v ⟨0, hn⟩ I.n agents goods
  mkTable I.m (fun g => do
    let q ← findC (fun q => do tick 1; pure (q.2 == g)) r.1
    tick 1
    pure ((q.map Prod.fst).getD (r.2 g)))

/-- **Algorithm K3ALG** (`proofs/k3_algorithm.md`): the allocation `algoC` computes. -/
def algo (I : Inst) (hn : 0 < I.n) : I.Alloc := (algoC I hn).val

/-! ## `algo` computes the specification -/

section fin
variable {n m : Nat}

theorem profTabC_val (v : Fin n → Fin m → Nat) (goods : List (Fin m)) (g0 : Fin m) :
    (profTabC v goods g0).val = profileOf v goods g0 := by
  simp [profTabC, sort3C, profileOf, relevant]

theorem completeTabC_val (P : Profile (Fin n) (Fin m)) (agents up : List (Fin n)) (Y : Fin n → Option (Fin m))
    (goods : List (Fin m)) (o : Option (Fin n)) (H : List (Fin m)) (d : Fin n) :
    (completeTabC P agents up Y (cap P agents up Y) (junkList P agents up Y goods) o H d).val =
      complete P agents up Y goods o H d := by
  funext g
  simp only [completeTabC, bind_val, mkTable_val, placeListC_val]
  exact completeOneC_val P agents up Y goods o H d g

theorem lbPlusC_val (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (goods : List (Fin m))
    (order : List (Fin n)) (d : Fin n) : (lbPlusC P agents goods order d).val = lbPlus P agents goods order d := by
  have ecap : ∀ (up : List (Fin n)) (Y : Fin n → Option (Fin m)),
      (fun k => (capC P agents up Y k).val) = cap P agents up Y := fun up Y => by funext k; simp
  have eY : (fun k => (phase1C P order goods k).val) = phase1 P order goods := by funext k; simp
  have eblk : (fun k => (blkAuxC P order goods 0 k).val) = blkAux P order goods 0 := by funext k; simp
  have erot : ∀ (Y : Fin n → Option (Fin m)) (k : Fin n) (ch : List (Fin n)),
      (fun x => (rotPicksC P Y k ch x).val) = rotPicks P Y k ch := fun Y k ch => by funext x; simp
  unfold lbPlusC lbPlus
  simp only [bind_val, mkTable_val, eY, lbUpC_val, junkListC_val, ecap, sumTabC_val, lengthC_val]
  simp only [slotSum]
  split
  · rename_i h1
    simp only [h1, ↓reduceIte]
    exact completeTabC_val P agents _ _ goods none [] d
  rename_i h1
  simp only [h1, ↓reduceIte, bind_val, lastOutC_val]
  cases lastOut (lbUp P agents goods (phase1 P order goods)) order with
  | none => exact completeTabC_val P agents _ _ goods none [] d
  | some r =>
    simp only [bind_val, exposedLC_val, hitSetC_val, lengthC_val, sumExceptC_val]
    split
    · exact completeTabC_val P agents _ _ goods (some r) _ d
    simp only [bind_val, mkTable_val, eblk, kstarC_val]
    cases kstar P agents (lbUp P agents goods (phase1 P order goods)) (phase1 P order goods) goods
        (blkAux P order goods 0) r with
    | none => exact completeTabC_val P agents _ _ goods (some r) _ d
    | some k =>
      simp only [bind_val, afterC_val, chainFromC_val, mkTable_val, erot, junkListC_val, ecap, sumTabC_val,
        lengthC_val]
      split
      · rename_i h3
        simp only [h3, ↓reduceIte]
        exact completeTabC_val P agents _ _ goods none [] d
      rename_i h3
      simp only [h3, ↓reduceIte, bind_val, exposedLC_val, hitSetC_val]
      exact completeTabC_val P agents _ _ goods (some k) _ d

/-- `reduceC` computes `reduce`: the allocation of `reduce` is the peeled goods' agents, and the rest's
allocation elsewhere. -/
theorem reduceC_val (v : Fin n → Fin m → Nat) (d : Fin n) : ∀ (fuel : Nat) (agents : List (Fin n))
    (goods : List (Fin m)) (g : Fin m),
    reduce v d fuel agents goods g =
      ((((reduceC v d fuel agents goods).val.1.find? (fun q => q.2 == g)).map Prod.fst).getD
        ((reduceC v d fuel agents goods).val.2 g))
  | 0, _, _, _ => rfl
  | fuel + 1, agents, goods, g => by
    unfold reduce reduceC
    simp only [bind_val, lengthC_val]
    split
    · simp
    cases goods with
    | nil => simp
    | cons g0 gs =>
      simp only [bind_val, findR1C_val]
      cases findR1 v agents (g0 :: gs) with
      | some q =>
        obtain ⟨i, s⟩ := q
        cases s with
        | none =>
          simp only [bind_val, eraseC_val]
          exact reduceC_val v d fuel _ _ g
        | some p =>
          simp only [bind_val, eraseC_val, pure_val, extend, List.find?_cons]
          by_cases hg : g = p
          · subst hg; simp
          · have : (p == g) = false := by simp [Ne.symm hg]
            simp only [hg, ↓reduceIte, this]
            exact reduceC_val v d fuel _ _ g
      | none =>
        simp only [bind_val, profTabC_val, lengthC_val, r1OrderC_val, lbPlusC_val, pure_val, List.find?_nil,
          Option.map_none, Option.getD_none]
        rfl

end fin

/-- **`algo` computes the specification** `algoSpec`. -/
theorem algo_eq_spec (I : Inst) (hn : 0 < I.n) : algo I hn = algoSpec I hn := by
  funext g
  simp only [algo, algoC, algoSpec, bind_val, finRangeC, pure_val, mkTable_val, findC_val]
  rw [reduceC_val]

/-- **Correctness of algorithm K3ALG.** For every instance with `n ≥ 1` agents in which every agent positively
values at most three goods, `algo I hn` is an EFX₀ allocation. -/
theorem algo_efx0 (I : Inst) (hn : 0 < I.n) (h : ∀ i, numRelevant I i ≤ 3) : I.EFX0 (algo I hn) := by
  rw [algo_eq_spec]
  exact algoSpec_efx0 I hn h

end K3
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.K3.lbPlusC_val
#print axioms EFX.K3.reduceC_val
#print axioms EFX.K3.algo_eq_spec
#print axioms EFX.K3.algo_efx0
