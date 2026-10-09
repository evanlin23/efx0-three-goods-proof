import EFX.Timed
import EFX.K3Algo

/-!
# LB⁺'s steps as counted programs (`proofs/k3_algorithm.md` §6)

Each definition `fooC` here is `EFX.LB.foo` (or a step of `EFX.K3.reduce`) written in the cost monad
`EFX.Timed`; its value lemma `fooC_val` says that it computes exactly `foo`. The cost lemmas bound the number of
counted operations in terms of an upper bound `N ≥ 1` on the lengths of the lists involved.

**What one unit counts** (the cost model; see also `EFX.Timed`):
- one step of a list traversal (one cell visited by `map`, `filter`, `any`, `find?`, `findSome?`, a sum, `length`,
  `++`, `take`, `drop`, membership, `erase`, or by the recursions below), and one comparison of two agents or two
  goods (membership and `erase` count one unit per cell for the comparison and the step together);
- one read of a *table*: the profile's `a i`, `b i`, `c i`, the picks `Y k`, the blocks `blk k`, the slots `s k`;
  in `EFX.K3Cost` these functions are arrays filled once by `EFX.Timed.mkTable`, whose filling is counted there;
- one read of an input value `v i g`, one comparison or addition of two natural numbers (values or counters),
  arbitrary-size natural numbers counting as one unit.
Straight-line code with a bounded number of these operations is charged by a single `tick k` with `k` at least
that number; each such `tick` is annotated below.

Nothing is charged for building a pair, an `Option` or a list cell that a counted step produces, or for pattern
matching on it. The program's shape is that of the definitions it computes (`fooC_val`), so every loop of
`EFX.LB.lbPlus` is a loop here and is counted.
-/

set_option autoImplicit false

namespace EFX
namespace K3

open Timed LB

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Rankings -/

/-- `P.rank i g`: three table reads (`a i`, `b i`, `c i`) and at most three comparisons. -/
def rankC (P : Profile A G) (i : A) (g : G) : Timed Nat := do
  tick 6
  pure (P.rank i g)

/-- `P.pickRank Y i`: one table read (`Y i`) and a rank. -/
def pickRankC (P : Profile A G) (Y : A → Option G) (i : A) : Timed Nat := do
  tick 1
  match Y i with
  | none => pure 3
  | some y => rankC P i y

/-- `P.Prefers Y i g`: two ranks and one comparison. -/
def prefersC (P : Profile A G) (Y : A → Option G) (i : A) (g : G) : Timed Bool := do
  let r ← rankC P i g
  let q ← pickRankC P Y i
  tick 1
  pure (decide (r < q))

omit [DecidableEq A] in
@[simp] theorem rankC_val (P : Profile A G) (i : A) (g : G) : (rankC P i g).val = P.rank i g := rfl

omit [DecidableEq A] in
@[simp] theorem pickRankC_val (P : Profile A G) (Y : A → Option G) (i : A) :
    (pickRankC P Y i).val = P.pickRank Y i := by
  unfold pickRankC Profile.pickRank
  cases Y i <;> rfl

omit [DecidableEq A] in
@[simp] theorem prefersC_val (P : Profile A G) (Y : A → Option G) (i : A) (g : G) :
    (prefersC P Y i g).val = decide (P.Prefers Y i g) := by
  simp only [prefersC, bind_val, rankC_val, pickRankC_val, pure_val]
  rfl

/-! ## Phase 1 -/

/-- `fav P pool i`: three table reads and up to three membership tests. -/
def favC (P : Profile A G) (pool : List G) (i : A) : Timed (Option G) := do
  tick 3
  let ha ← memC (P.a i) pool
  if ha then pure (some (P.a i)) else do
    let hb ← memC (P.b i) pool
    if hb then pure (some (P.b i)) else do
      let hc ← memC (P.c i) pool
      pure (if hc then some (P.c i) else none)

/-- `removePick pool p`. -/
def removePickC (pool : List G) : Option G → Timed (List G)
  | none => pure pool
  | some g => eraseC g pool

/-- `full P pool i`: three table reads and three membership tests. -/
def fullC (P : Profile A G) (pool : List G) (i : A) : Timed Bool := do
  tick 3
  let x ← memC (P.a i) pool
  let y ← memC (P.b i) pool
  let z ← memC (P.c i) pool
  pure (x && y && z)

/-- `r1Order P fuel rem pool`. -/
def r1OrderC (P : Profile A G) : Nat → List A → List G → Timed (List A)
  | 0, _, _ => pure []
  | fuel + 1, rem, pool => do
    let f ← findC (fun j => do let b ← fullC P pool j; pure (!b)) rem
    match f with
    | some i => do
      let rem' ← eraseC i rem
      let y ← favC P pool i
      let pool' ← removePickC pool y
      let rest ← r1OrderC P fuel rem' pool'
      pure (i :: rest)
    | none =>
      match rem with
      | [] => pure []
      | i :: rest => do
        let y ← favC P pool i
        let pool' ← removePickC pool y
        let rest' ← r1OrderC P fuel rest pool'
        pure (i :: rest')

/-- `phase1 P order pool k`: `k`'s pick, by running Phase 1 up to `k`'s turn (one comparison per turn). -/
def phase1C (P : Profile A G) : List A → List G → A → Timed (Option G)
  | [], _, _ => pure none
  | i :: order, pool, k => do
    tick 1
    if k = i then favC P pool i else do
      let y ← favC P pool i
      let pool' ← removePickC pool y
      phase1C P order pool' k

/-- `blkAux P order pool cnt k`: one comparison and one addition per turn. -/
def blkAuxC (P : Profile A G) : List A → List G → Nat → A → Timed Nat
  | [], _, _, _ => pure 0
  | i :: order, pool, cnt, k => do
    tick 2
    let f ← fullC P pool i
    if k = i then pure (if f then cnt + 1 else cnt) else do
      let y ← favC P pool i
      let pool' ← removePickC pool y
      blkAuxC P order pool' (if f then cnt + 1 else cnt) k

omit [DecidableEq A] in
@[simp] theorem favC_val (P : Profile A G) (pool : List G) (i : A) : (favC P pool i).val = fav P pool i := by
  unfold favC fav
  by_cases ha : P.a i ∈ pool <;> by_cases hb : P.b i ∈ pool <;> by_cases hc : P.c i ∈ pool <;>
    simp [ha, hb, hc]

@[simp] theorem removePickC_val (pool : List G) (p : Option G) : (removePickC pool p).val = removePick pool p := by
  cases p <;> simp [removePickC, removePick]

omit [DecidableEq A] in
@[simp] theorem fullC_val (P : Profile A G) (pool : List G) (i : A) : (fullC P pool i).val = full P pool i := by
  simp [fullC, full, Bool.and_assoc]

@[simp] theorem r1OrderC_val (P : Profile A G) : ∀ (fuel : Nat) (rem : List A) (pool : List G),
    (r1OrderC P fuel rem pool).val = r1Order P fuel rem pool
  | 0, _, _ => rfl
  | fuel + 1, rem, pool => by
    unfold r1OrderC r1Order
    simp only [bind_val, findC_val, fullC_val, pure_val]
    cases rem.find? (fun j => !full P pool j) with
    | some i => simp [r1OrderC_val P fuel]
    | none =>
      cases rem with
      | nil => rfl
      | cons i rest => simp [r1OrderC_val P fuel]

@[simp] theorem phase1C_val (P : Profile A G) : ∀ (order : List A) (pool : List G) (k : A),
    (phase1C P order pool k).val = phase1 P order pool k
  | [], _, _ => rfl
  | i :: order, pool, k => by
    unfold phase1C
    by_cases h : k = i
    · simp [h, phase1]
    · simp [h, phase1, phase1C_val P order]

@[simp] theorem blkAuxC_val (P : Profile A G) : ∀ (order : List A) (pool : List G) (cnt : Nat) (k : A),
    (blkAuxC P order pool cnt k).val = blkAux P order pool cnt k
  | [], _, _, _ => rfl
  | i :: order, pool, cnt, k => by
    unfold blkAuxC
    by_cases h : k = i
    · simp [h, blkAux]
    · simp [h, blkAux, blkAuxC_val P order]

/-! ## Phase 2: NA, frozen agents, slots, upgrades -/

/-- `naB P agents up Y g`. -/
def naBC (P : Profile A G) (agents up : List A) (Y : A → Option G) (g : G) : Timed Bool :=
  anyC (fun i => do
    let u ← memC i up
    let p ← prefersC P Y i g
    pure (!u && p)) agents

/-- `frozenB P agents up Y k`: one table read (`Y k`) and `naB`. -/
def frozenBC (P : Profile A G) (agents up : List A) (Y : A → Option G) (k : A) : Timed Bool := do
  tick 1
  match Y k with
  | none => pure false
  | some y => naBC P agents up Y y

/-- `cap P agents up Y k`: frozen, membership in `up`, one table read (`Y k`) and one comparison. -/
def capC (P : Profile A G) (agents up : List A) (Y : A → Option G) (k : A) : Timed Nat := do
  let f ← frozenBC P agents up Y k
  let u ← memC k up
  tick 2
  pure (if f || u then 0 else if Y k = none then 2 else 1)

/-- `canUp P agents up Y J k`: two memberships, a pick rank, `naB`, one table read (`c k`... `b k`: two) and
one comparison. -/
def canUpC (P : Profile A G) (agents up : List A) (Y : A → Option G) (J : List G) (k : A) : Timed Bool := do
  tick 3
  let u ← memC k up
  let r ← pickRankC P Y k
  let cj ← memC (P.c k) J
  let na ← naBC P agents up Y (P.b k)
  pure (!u && r == 1 && cj && !na)

/-- `upgrades P agents Y fuel up J`: each round finds the first agent that can be upgraded. -/
def upgradesC (P : Profile A G) (agents : List A) (Y : A → Option G) :
    Nat → List A → List G → Timed (List A × List G)
  | 0, up, J => pure (up, J)
  | fuel + 1, up, J => do
    let f ← findC (canUpC P agents up Y J) agents
    match f with
    | none => pure (up, J)
    | some k => do
      tick 1
      let J' ← eraseC (P.c k) J
      upgradesC P agents Y fuel (k :: up) J'

/-- `picker agents Y g`: one table read and one comparison per agent. -/
def pickerC (agents : List A) (Y : A → Option G) (g : G) : Timed (Option A) :=
  findC (fun k => do tick 2; pure (Y k == some g)) agents

/-- `upOf P up g`: one table read and one comparison per agent. -/
def upOfC (P : Profile A G) (up : List A) (g : G) : Timed (Option A) :=
  findC (fun k => do tick 2; pure (P.c k == g)) up

/-- `junk0 agents Y goods`. -/
def junk0C (agents : List A) (Y : A → Option G) (goods : List G) : Timed (List G) :=
  filterC (fun g => do let p ← pickerC agents Y g; pure p.isNone) goods

/-- `lbUp P agents goods Y`. -/
def lbUpC (P : Profile A G) (agents : List A) (goods : List G) (Y : A → Option G) : Timed (List A) := do
  let J0 ← junk0C agents Y goods
  let l ← lengthC agents
  let r ← upgradesC P agents Y l [] J0
  pure r.1

/-- `junkList P agents up Y goods`. -/
def junkListC (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) : Timed (List G) :=
  filterC (fun g => do
    let p ← pickerC agents Y g
    let u ← upOfC P up g
    tick 1
    pure (p.isNone && u.isNone)) goods

/-- The sum of a table over `agents`: one read per agent (and one addition, counted by `sumMapC`). -/
def sumTabC (s : A → Nat) (agents : List A) : Timed Nat :=
  sumMapC (fun k => do tick 1; pure (s k)) agents

/-- `(agents.map (slotsExcept s o)).sum`: one read and one comparison per agent. -/
def sumExceptC (s : A → Nat) (o : Option A) (agents : List A) : Timed Nat :=
  sumMapC (fun k => do tick 2; pure (slotsExcept s o k)) agents

/-- `lastOut up order`: one step per cell of `order`, and a membership test until `r` is found. -/
def lastOutC (up : List A) : List A → Timed (Option A)
  | [] => pure none
  | i :: order => do
    tick 1
    let r ← lastOutC up order
    match r with
    | some r => pure (some r)
    | none => do
      let b ← memC i up
      pure (if b then none else some i)

@[simp] theorem naBC_val (P : Profile A G) (agents up : List A) (Y : A → Option G) (g : G) :
    (naBC P agents up Y g).val = naB P agents up Y g := by
  simp [naBC, naB]

@[simp] theorem frozenBC_val (P : Profile A G) (agents up : List A) (Y : A → Option G) (k : A) :
    (frozenBC P agents up Y k).val = frozenB P agents up Y k := by
  unfold frozenBC frozenB
  cases Y k <;> simp

@[simp] theorem capC_val (P : Profile A G) (agents up : List A) (Y : A → Option G) (k : A) :
    (capC P agents up Y k).val = cap P agents up Y k := by
  simp [capC, cap]

@[simp] theorem canUpC_val (P : Profile A G) (agents up : List A) (Y : A → Option G) (J : List G) (k : A) :
    (canUpC P agents up Y J k).val = canUp P agents up Y J k := by
  simp [canUpC, canUp]

@[simp] theorem upgradesC_val (P : Profile A G) (agents : List A) (Y : A → Option G) :
    ∀ (fuel : Nat) (up : List A) (J : List G), (upgradesC P agents Y fuel up J).val = upgrades P agents Y fuel up J
  | 0, _, _ => rfl
  | fuel + 1, up, J => by
    unfold upgradesC upgrades
    have e : (fun k => (canUpC P agents up Y J k).val) = canUp P agents up Y J := by
      funext k; exact canUpC_val P agents up Y J k
    simp only [bind_val, findC_val, e]
    cases agents.find? (canUp P agents up Y J) with
    | none => rfl
    | some k => simp [upgradesC_val P agents Y fuel]

omit [DecidableEq A] in
@[simp] theorem pickerC_val (agents : List A) (Y : A → Option G) (g : G) :
    (pickerC agents Y g).val = picker agents Y g := by
  simp [pickerC, picker]

omit [DecidableEq A] in
@[simp] theorem upOfC_val (P : Profile A G) (up : List A) (g : G) : (upOfC P up g).val = upOf P up g := by
  simp [upOfC, upOf]

omit [DecidableEq A] in
@[simp] theorem junk0C_val (agents : List A) (Y : A → Option G) (goods : List G) :
    (junk0C agents Y goods).val = junk0 agents Y goods := by
  simp [junk0C, junk0]

@[simp] theorem lbUpC_val (P : Profile A G) (agents : List A) (goods : List G) (Y : A → Option G) :
    (lbUpC P agents goods Y).val = lbUp P agents goods Y := by
  simp [lbUpC, lbUp]

omit [DecidableEq A] in
@[simp] theorem junkListC_val (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) :
    (junkListC P agents up Y goods).val = junkList P agents up Y goods := by
  simp [junkListC, junkList]

omit [DecidableEq A] in
@[simp] theorem sumTabC_val (s : A → Nat) (agents : List A) : (sumTabC s agents).val = (agents.map s).sum := by
  simp [sumTabC]

@[simp] theorem sumExceptC_val (s : A → Nat) (o : Option A) (agents : List A) :
    (sumExceptC s o agents).val = (agents.map (slotsExcept s o)).sum := by
  simp [sumExceptC]

@[simp] theorem lastOutC_val (up : List A) : ∀ order : List A, (lastOutC up order).val = lastOut up order
  | [] => rfl
  | i :: order => by
    unfold lastOutC lastOut
    simp only [bind_val, lastOutC_val up order]
    cases lastOut up order with
    | some r => rfl
    | none => simp

/-! ## The owner test: exposed agents and the hitting set -/

/-- `InBase P up Y w g`: one table read (`Y w`), membership, one table read (`c w`), two comparisons. -/
def inBaseC (P : Profile A G) (up : List A) (Y : A → Option G) (w : A) (g : G) : Timed Bool := do
  tick 4
  let u ← memC w up
  pure (Y w == some g || (u && P.c w == g))

/-- `Exposed P agents up Y goods w x`, with the junk `J` computed once: one comparison, three table reads, one
comparison of picks, memberships and bases. -/
def exposedC (P : Profile A G) (up : List A) (Y : A → Option G) (J : List G) (w x : A) : Timed Bool := do
  tick 6
  let u ← memC x up
  let jb ← memC (P.b x) J
  let bb ← inBaseC P up Y w (P.b x)
  let jc ← memC (P.c x) J
  let cb ← inBaseC P up Y w (P.c x)
  pure (decide (x ≠ w) && !u && (Y x == some (P.a x)) && (jb || bb) && (jc || cb))

/-- `exposedL P agents up Y goods w`, with `J = junkList P agents up Y goods` computed once. -/
def exposedLC (P : Profile A G) (agents up : List A) (Y : A → Option G) (J : List G) (w : A) :
    Timed (List A) :=
  filterC (exposedC P up Y J w) agents

/-- `pickOne P J x`: membership, two table reads. -/
def pickOneC (P : Profile A G) (J : List G) (x : A) : Timed G := do
  tick 2
  let hb ← memC (P.b x) J
  pure (if hb then P.b x else P.c x)

/-- `meet P J E`: for each pair of agents of `E`, one comparison, two table reads, and for each of the two goods
a membership test, two table reads and two comparisons. -/
def meetC (P : Profile A G) (J : List G) (E : List A) : Timed (Option (A × A × G)) :=
  findSomeC (fun x => findSomeC (fun y => do
    tick 3
    if x = y then pure none else do
      let r ← findC (fun g => do
        let mj ← memC g J
        tick 4
        pure (decide (mj = true ∧ (g = P.b y ∨ g = P.c y)))) [P.b x, P.c x]
      pure (r.map (fun g => (x, y, g)))) E) E

/-- `hitSet P J E`. -/
def hitSetC (P : Profile A G) (J : List G) (E : List A) : Timed (List G) := do
  let mt ← meetC P J E
  match mt with
  | some (x, y, g) => do
    let E' ← filterC (fun z => do tick 2; pure (decide (z ≠ x ∧ z ≠ y))) E
    let l ← mapC (pickOneC P J) E'
    pure (g :: l)
  | none => mapC (pickOneC P J) E

/-- `kstar P agents up Y goods blk r`, from `E = exposedL P agents up Y goods r`: two table reads and one
comparison per agent. -/
def kstarC (blk : A → Nat) (E : List A) (r : A) : Timed (Option A) :=
  findC (fun x => do tick 3; pure (blk x == blk r)) E

@[simp] theorem inBaseC_val (P : Profile A G) (up : List A) (Y : A → Option G) (w : A) (g : G) :
    (inBaseC P up Y w g).val = decide (InBase P up Y w g) := by
  simp only [inBaseC, bind_val, memC_val, pure_val]
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp [InBase]

@[simp] theorem exposedC_val (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G)
    (w x : A) : (exposedC P up Y (junkList P agents up Y goods) w x).val = decide (Exposed P agents up Y goods w x) := by
  simp only [exposedC, bind_val, memC_val, inBaseC_val, pure_val]
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp [Exposed, and_assoc]

@[simp] theorem exposedLC_val (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G)
    (w : A) : (exposedLC P agents up Y (junkList P agents up Y goods) w).val = exposedL P agents up Y goods w := by
  simp [exposedLC, exposedL]

omit [DecidableEq A] in
@[simp] theorem pickOneC_val (P : Profile A G) (J : List G) (x : A) : (pickOneC P J x).val = pickOne P J x := by
  simp [pickOneC, pickOne]

@[simp] theorem meetC_val (P : Profile A G) (J : List G) (E : List A) : (meetC P J E).val = meet P J E := by
  unfold meetC meet
  simp only [findSomeC_val, bind_val]
  congr 1; funext x; congr 1; funext y
  by_cases h : x = y
  · simp [h]
  · simp [h]

@[simp] theorem hitSetC_val (P : Profile A G) (J : List G) (E : List A) : (hitSetC P J E).val = hitSet P J E := by
  unfold hitSetC hitSet
  simp only [bind_val, meetC_val]
  cases meet P J E with
  | none => simp
  | some q =>
    obtain ⟨x, y, g⟩ := q
    simp

@[simp] theorem kstarC_val (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G)
    (blk : A → Nat) (r : A) : (kstarC blk (exposedL P agents up Y goods r) r).val = kstar P agents up Y goods blk r := by
  simp [kstarC, kstar]

/-! ## The rotation -/

/-- `after order x`: one comparison per step. -/
def afterC : List A → A → Timed (List A)
  | [], _ => pure []
  | i :: order, x => do
    tick 1
    if x = i then pure order else afterC order x

/-- `isNext P agents up Y cur j`: frozen, membership, one table read (`Y cur`), and a comparison of ranks. -/
def isNextC (P : Profile A G) (agents up : List A) (Y : A → Option G) (cur j : A) : Timed Bool := do
  let f ← frozenBC P agents up Y cur
  let u ← memC j up
  tick 1
  let p ← match Y cur with
    | some y => prefersC P Y j y
    | none => pure false
  pure (f && !u && p)

/-- `chainFrom P agents up Y cur rest`. -/
def chainFromC (P : Profile A G) (agents up : List A) (Y : A → Option G) : A → List A → Timed (List A)
  | _, [] => pure []
  | cur, j :: rest => do
    tick 1
    let b ← isNextC P agents up Y cur j
    if b then do
      let l ← chainFromC P agents up Y j rest
      pure (j :: l)
    else chainFromC P agents up Y cur rest

/-- `rotY Y cur l x`: one comparison per step, one table read at the end. -/
def rotYC (Y : A → Option G) : A → List A → A → Timed (Option G)
  | _, [], x => do tick 1; pure (Y x)
  | cur, j :: l, x => do
    tick 2
    if x = j then pure (Y cur) else rotYC Y j l x

/-- `rotPicks P Y k c x`: one comparison, one table read. -/
def rotPicksC (P : Profile A G) (Y : A → Option G) (k : A) (c : List A) (x : A) : Timed (Option G) := do
  tick 2
  if x = k then pure (some (P.b k)) else rotYC Y k c x

@[simp] theorem afterC_val : ∀ (order : List A) (x : A), (afterC order x).val = after order x
  | [], _ => rfl
  | i :: order, x => by
    unfold afterC after
    by_cases h : x = i
    · simp [h]
    · simp [h, afterC_val order x]

@[simp] theorem isNextC_val (P : Profile A G) (agents up : List A) (Y : A → Option G) (cur j : A) :
    (isNextC P agents up Y cur j).val = isNext P agents up Y cur j := by
  unfold isNextC isNext
  cases Y cur <;> simp

@[simp] theorem chainFromC_val (P : Profile A G) (agents up : List A) (Y : A → Option G) :
    ∀ (cur : A) (rest : List A), (chainFromC P agents up Y cur rest).val = chainFrom P agents up Y cur rest
  | _, [] => rfl
  | cur, j :: rest => by
    unfold chainFromC chainFrom
    simp only [bind_val, isNextC_val]
    cases isNext P agents up Y cur j <;> simp [chainFromC_val P agents up Y _ rest]

omit [DecidableEq G] in
@[simp] theorem rotYC_val (Y : A → Option G) : ∀ (cur : A) (l : List A) (x : A), (rotYC Y cur l x).val = rotY Y cur l x
  | _, [], _ => rfl
  | cur, j :: l, x => by
    unfold rotYC rotY
    by_cases h : x = j
    · simp [h]
    · simp [h, rotYC_val Y j l x]

omit [DecidableEq G] in
@[simp] theorem rotPicksC_val (P : Profile A G) (Y : A → Option G) (k : A) (c : List A) (x : A) :
    (rotPicksC P Y k c x).val = rotPicks P Y k c x := by
  unfold rotPicksC rotPicks
  by_cases h : x = k <;> simp [h]

/-! ## The completion -/

/-- `fill s ks rest g`: one table read (`s k`) and one comparison per agent, the `take`, the membership and the
`drop`. -/
def fillC (s : A → Nat) (g : G) : List A → List G → Timed (Option A)
  | [], _ => pure none
  | k :: ks, rest => do
    tick 2
    let t ← takeC (s k) rest
    let b ← memC g t
    if b then pure (some k) else do
      let r ← dropC (s k) rest
      fillC s g ks r

/-- `complete P agents up Y goods o H d g`, with the slots `s` and the list `L` of junk goods in placement order
computed once. -/
def completeOneC (P : Profile A G) (agents up : List A) (Y : A → Option G) (o : Option A) (d : A)
    (s : A → Nat) (L : List G) (g : G) : Timed A := do
  let p ← pickerC agents Y g
  match p with
  | some k => pure k
  | none => do
    let u ← upOfC P up g
    match u with
    | some u => pure u
    | none => do
      let f ← fillC s g agents L
      tick 1
      pure (f.getD (o.getD d))

/-- The list `L = H ++ (J minus H)` of `complete`: the junk goods in placement order. -/
def placeListC (H J : List G) : Timed (List G) := do
  let J' ← filterC (fun g => do let b ← memC g H; pure (!b)) J
  appendC H J'

omit [DecidableEq A] in
@[simp] theorem fillC_val (s : A → Nat) (g : G) : ∀ (ks : List A) (rest : List G),
    (fillC s g ks rest).val = fill s ks rest g
  | [], _ => rfl
  | k :: ks, rest => by
    unfold fillC fill
    by_cases h : g ∈ rest.take (s k)
    · simp [h]
    · simp [h, fillC_val s g ks]

@[simp] theorem placeListC_val (H J : List G) : (placeListC H J).val = H ++ J.filter (fun g => decide (g ∉ H)) := by
  simp [placeListC]

theorem completeOneC_val (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G)
    (o : Option A) (H : List G) (d : A) (g : G) :
    (completeOneC P agents up Y o d (slotsExcept (cap P agents up Y) o)
      (H ++ (junkList P agents up Y goods).filter (fun g => decide (g ∉ H))) g).val =
      complete P agents up Y goods o H d g := by
  unfold completeOneC complete
  simp only [bind_val, pickerC_val]
  cases picker agents Y g with
  | some k => rfl
  | none =>
    simp only [bind_val, upOfC_val]
    cases upOf P up g with
    | some u => rfl
    | none => simp

end K3
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.K3.r1OrderC_val
#print axioms EFX.K3.upgradesC_val
#print axioms EFX.K3.hitSetC_val
#print axioms EFX.K3.completeOneC_val
