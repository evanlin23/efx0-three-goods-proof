import EFX.K3DECost

/-!
# The running time of Draft and Exchange, part 2: one step of the loop in `O(n + m)`

`stepC` is `EFX.DE.step` (one iteration of the loop of Algorithm DE, `paper/k3-simple/long.tex` §6: chain, finish,
ring) as a counted program over `Fin n` and `Fin m`, and `stepC_val` proves that it computes `step`. Units as in
`EFX.K3DECost`.

**The tables of a state** (`tabsC`, `tabsC_val`), each built in `O(n + m)` from new arrays and one pass over a list:
`inUp` (membership in `up`), `holder` (`EFX.LB.picker`: for each good, the first agent holding it), `upc`
(`EFX.LB.upOf`: the first pair holder whose `c` it is), `out` (for each good, the first agent outside `up` that
needs it: the out-neighbour `outNb` of its holder, and `naB` is `out g ≠ none`), `junk` (`junkB`) and `free`
(`freeB`). The needs of an agent are among its three goods, so `out` is a scatter of at most three keys per agent.

**The exposed agents** (the paper's remark that "all sets `E_o` and `H_o` are found by one pass over the agents").
Under (P), an agent `x` that holds only its top is exposed for a free agent `o` exactly when `o`'s good is one of
`b x`, `c x` and the other is junk (or `b x = c x` is `o`'s good): `x` determines one good `gxS x`, and the agents
exposed for a free `o` with good `g` are those with `gxS x = g`, other than `o` (`filter_expB`). `xsC` lists them for
every good in one pass; for each free agent, `freeLoopC` reads its list, computes `H_o` (`EFX.DE.dd` with a mark
array, cleared afterwards) and its length.

**Representatives, `σ`, the cycle.** `repsC` is `EFX.DE.reps` with a mark array of used goods; `sigLoopC` finds each
free agent's image by scanning its exposed agents; `sigExC`, `sigPairC` tabulate `σ`. `cycleC` is `cycleStep`:
`σⁿ(s)` by `n` reads, the period by walking until the first return (`searchC`, as `period`), the orbit marked in a
new array (`onLoopC`), the predecessor `σ^(per−1)` on the orbit by writing `pred (σ w) := w` along the orbit
(`predLoopC`; the orbit's points are distinct, `period_facts`, so `pred_orbit`), and the new state by one table and
one filter (`cycleC_val`).

**Results.** `stepC_val`: `stepC` computes `step` on every state (valid or not), given arrays marking the agents and
the goods. Also `tabsC_val`, `expB_eq`/`filter_expB`/`Hset_eq` (exposure under (P)), `cycleC_val`, `repsC_val`,
`freeLoopC_free`. The cost of a step is bounded in `EFX.K3DECostBound` (`stepC_cost`).

**Choices.**
1. Every table reproduces the specification's function exactly, on all agents and goods: a key receives the
   *first* element of the list that lists it (`scatterC`, as `List.find?` in `picker`, `upOf`, `outNb`), the
   representatives' table keeps the first representative (`repOf`), and the slots of the completion keep the first
   agent (`fill`). So no invariant of the loop is needed for the value, only for the cost.
2. The specification evaluates `H_o` only after the test for (P), so the exposed agents are computed under (P)
   (`expL`, from the lists `xsS`), where each agent holding only its top is a candidate for at most one good.
3. `EFX.DE.dd` keeps the first occurrence of each good (so `H_o` lists the goods in the order of their first exposed
   agents, `EFX.DE.find?_Hset`); `ddC` walks the list from its start with a mark array.
4. The period is the first return to `p` within `n` steps, else `1` (as `period`); with `per = 1` and no return,
   the predecessor of `p` is `p` itself (`σ⁰`), which `pred p := σ^(per−1)(p)` covers.
-/

set_option autoImplicit false

namespace EFX
namespace DE

open Timed LB Profile

/-! ## Facts about the specification -/

section spec
variable {A G : Type} [DecidableEq A] [DecidableEq G]

omit [DecidableEq A] [DecidableEq G] in
theorem isSome_find {α : Type} (p : α → Bool) : ∀ l : List α, (l.find? p).isSome = l.any p
  | [] => rfl
  | x :: l => by
    rw [List.find?_cons, List.any_cons]
    cases p x
    · simp [isSome_find p l]
    · rfl

/-- The good that determines for which free agent `x` is exposed (under (P)): `x` outside `up` holds its top, and
either one of `b x`, `c x` is junk (then the other one), or neither is and `b x = c x`. -/
def gxS (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (x : A) : Option G :=
  if !(up.contains x) && (Y x == some (P.a x)) then
    (if junkB P agents up Y goods (P.b x) && junkB P agents up Y goods (P.c x) then none
      else if junkB P agents up Y goods (P.b x) then some (P.c x)
      else if junkB P agents up Y goods (P.c x) then some (P.b x)
      else if P.b x = P.c x then some (P.b x) else none)
  else none

/-- The agents of `agents` determined by the good `g`. -/
def xsS (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (g : G) : List A :=
  agents.filter (fun x => gxS P agents up Y goods x == some g)

/-- The agents exposed for `o`, from the lists `xsS`. -/
def expL (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (o : A) : List A :=
  match Y o with
  | none => []
  | some g => (xsS P agents up Y goods g).filter (fun x => x != o)

variable {P : Profile A G} {agents : List A} {goods : List G} {Y : A → Option G} {up : List A}

omit [DecidableEq A] in
theorem beq_symm' (a b : G) : (a == b) = (b == a) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact eq_comm

/-- **Exposure under (P)**: for a free agent `o` and a listed agent `x`, `x` is exposed for `o` iff `o` holds the
good `gxS x` and `x ≠ o`. -/
theorem expB_eq (hP : agents.find? (pairB P agents up Y goods) = none) {o x : A}
    (ho : freeB P agents up Y o = true) (hx : x ∈ agents) :
    expB P agents up Y goods o x =
      match Y o with
      | none => false
      | some g => (gxS P agents up Y goods x == some g) && (x != o) := by
  have hpx : ¬ pairB P agents up Y goods x = true := List.find?_eq_none.mp hP x hx
  have hou : up.contains o = false := by simp [(freeB_iff.mp ho).2.1]
  have hxa : agents.contains x = true := by simpa using hx
  unfold pairB at hpx
  unfold expB gxS inBaseB
  rw [hxa, hou]
  generalize junkB P agents up Y goods (P.b x) = jb at hpx ⊢
  generalize junkB P agents up Y goods (P.c x) = jc at hpx ⊢
  generalize hu : up.contains x = u at hpx ⊢
  generalize ht : (Y x == some (P.a x)) = t at hpx ⊢
  cases hY : Y o with
  | none =>
    cases u <;> cases t <;> cases jb <;> cases jc <;> simp at hpx ⊢
  | some g =>
    cases u
    · cases t
      · simp
      · cases jb <;> cases jc
        · simp only [Bool.false_or, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          by_cases hb : P.b x = P.c x
          · simp only [hb, ↓reduceIte]
            by_cases hg : g = P.c x
            · subst hg; simp [Bool.and_comm]
            · simp [beq_symm' g, Bool.and_comm]
          · simp only [hb, ↓reduceIte]
            by_cases hg : g = P.c x
            · subst hg; simp [Ne.symm hb]
            · simp [hg]
        · simp [beq_symm' g, Bool.and_comm]
        · simp [beq_symm' g, Bool.and_comm]
        · simp at hpx
    · simp

/-- **The agents exposed for a free agent** under (P) are `expL`. -/
theorem filter_expB (hP : agents.find? (pairB P agents up Y goods) = none) {o : A}
    (ho : freeB P agents up Y o = true) :
    agents.filter (expB P agents up Y goods o) = expL P agents up Y goods o := by
  unfold expL xsS
  cases hY : Y o with
  | none =>
    simp only
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    rw [expB_eq hP ho hx, hY]
    simp
  | some g =>
    simp only
    rw [List.filter_filter]
    refine List.filter_congr fun x hx => ?_
    rw [expB_eq hP ho hx, hY]
    exact Bool.and_comm _ _

/-- `H_o` under (P), from `expL`. -/
theorem Hset_eq (hP : agents.find? (pairB P agents up Y goods) = none) {o : A}
    (ho : freeB P agents up Y o = true) :
    Hset P agents up Y goods o = dd ((expL P agents up Y goods o).map (hOf P agents up Y goods)) := by
  unfold Hset
  rw [filter_expB hP ho]

/-- The image of a free agent under `σ` (the ring step), from `expL`. -/
theorem find_expB (hP : agents.find? (pairB P agents up Y goods) = none) {o : A}
    (ho : freeB P agents up Y o = true) (q : G) :
    agents.find? (fun x => expB P agents up Y goods o x && hOf P agents up Y goods x == q) =
      (expL P agents up Y goods o).find? (fun x => hOf P agents up Y goods x == q) := by
  rw [← filter_expB hP ho, List.find?_filter]
  congr 1
  funext x
  rw [Bool.eq_iff_iff]
  simp

end spec

/-! ## The tables of a state -/

section fin
variable {n m : Nat}

/-- The tables of a state `(Y, up)`. -/
structure Tabs (n m : Nat) where
  inUp : Fin n → Bool
  holder : Fin m → Option (Fin n)
  upc : Fin m → Option (Fin n)
  out : Fin m → Option (Fin n)
  junk : Fin m → Bool
  free : Fin n → Bool

/-- What the tables hold. -/
def specTabs (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (goods : List (Fin m))
    (Y : Fin n → Option (Fin m)) (up : List (Fin n)) : Tabs n m where
  inUp := fun k => up.contains k
  holder := picker agents Y
  upc := upOf P up
  out := fun g => agents.find? (fun j => !(up.contains j) && decide (P.Prefers Y j g))
  junk := junkB P agents up Y goods
  free := freeB P agents up Y

/-- The goods `j` needs (those it ranks above its pick, if it is not a pair holder): at most three. -/
def needKeysC (P : Profile (Fin n) (Fin m)) (Y : Fin n → Option (Fin m)) (inUp : Fin n → Bool) (j : Fin n) :
    Timed (List (Fin m)) := do
  let u ← rd inUp j
  if u then pure [] else do
    let a ← rd P.a j
    let b ← rd P.b j
    let c ← rd P.c j
    filterC (K3.prefersC P Y j) [a, b, c]

/-- The holding of `k`, as a list of keys (at most one). -/
def holdKeysC (Y : Fin n → Option (Fin m)) (k : Fin n) : Timed (List (Fin m)) := do
  let y ← rd Y k
  pure y.toList

/-- The `c` of `u`, as a list of keys. -/
def cKeysC (P : Profile (Fin n) (Fin m)) (u : Fin n) : Timed (List (Fin m)) := do
  let c ← rd P.c u
  pure [c]

/-- `g` is junk: remaining, held by nobody, and not the `c` of a pair holder. -/
def junkEntryC (inG : Fin m → Bool) (holder upc : Fin m → Option (Fin n)) (g : Fin m) : Timed Bool := do
  let x ← rd inG g
  let h ← rd holder g
  let u ← rd upc g
  tick 1
  pure (x && (h.isNone && u.isNone))

/-- `k` is free: listed, not a pair holder, and its pick (if any) is needed by nobody. -/
def freeEntryC (inA inUp : Fin n → Bool) (Y : Fin n → Option (Fin m)) (out : Fin m → Option (Fin n)) (k : Fin n) :
    Timed Bool := do
  let a ← rd inA k
  let u ← rd inUp k
  let y ← rd Y k
  let fz ← match y with
    | none => pure false
    | some g => do
      let o ← rd out g
      pure o.isSome
  pure (a && !u && !fz)

/-- **The tables of a state**: new arrays, filled by passes over `up` and `agents` and over the goods. -/
def tabsC (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (inA : Fin n → Bool) (inG : Fin m → Bool)
    (Y : Fin n → Option (Fin m)) (up : List (Fin n)) : Timed (Tabs n m) := do
  let U0 ← constT n false
  let inUp ← setAllC true up U0
  let H0 ← constT m none
  let holder ← scatterC (holdKeysC Y) agents H0
  let C0 ← constT m none
  let upc ← scatterC (cKeysC P) up C0
  let O0 ← constT m none
  let out ← scatterC (needKeysC P Y inUp) agents O0
  let junk ← mkTable m (junkEntryC inG holder upc)
  let free ← mkTable n (freeEntryC inA inUp Y out)
  pure ⟨inUp, holder, upc, out, junk, free⟩

theorem needKeysC_mem (P : Profile (Fin n) (Fin m)) (Y : Fin n → Option (Fin m)) (up : List (Fin n)) (j : Fin n)
    (g : Fin m) :
    decide (g ∈ (needKeysC P Y (fun k => up.contains k) j).val) = (!(up.contains j) && decide (P.Prefers Y j g)) := by
  simp only [needKeysC, bind_val, rd_val]
  by_cases hu : up.contains j = true
  · have hu2 : j ∈ up := by simpa using hu
    simp [hu2]
  · have hu' : up.contains j = false := by simpa using hu
    simp only [hu', Bool.false_eq_true, ↓reduceIte, bind_val, rd_val, filterC_val, K3.prefersC_val, Bool.not_false,
      Bool.true_and]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h
      refine ⟨?_, h⟩
      have h3 := pickRank_le (P := P) Y j
      unfold Profile.Prefers at h
      exact mem_of_rank_lt (by omega)

theorem tabsC_val (P : Profile (Fin n) (Fin m)) {agents : List (Fin n)} {inA : Fin n → Bool} {inG : Fin m → Bool}
    {goods : List (Fin m)} (Y : Fin n → Option (Fin m)) (up : List (Fin n))
    (hA : ∀ k, inA k = agents.contains k) (hG : ∀ g, inG g = decide (g ∈ goods)) :
    (tabsC P agents inA inG Y up).val = specTabs P agents goods Y up := by
  have hU : (setAllC true up (fun _ : Fin n => false)).val = fun k => up.contains k := by
    rw [setAllC_val]; funext k; by_cases h : k ∈ up <;> simp [h]
  have hH : (scatterC (holdKeysC Y) agents (fun _ => none)).val = picker agents Y := by
    rw [scatterC_val]; funext g
    simp only [Option.none_or, holdKeysC, bind_val, rd_val, pure_val, picker]
    congr 1; funext k
    have e : ∀ y : Option (Fin m), decide (g ∈ y.toList) = (y == some g) := fun y => by
      cases y with
      | none => simp
      | some y =>
        rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, Option.mem_toList, Option.some.injEq]
    exact e (Y k)
  have hC : (scatterC (cKeysC P) up (fun _ => none)).val = upOf P up := by
    rw [scatterC_val]; funext g
    simp only [Option.none_or, cKeysC, bind_val, rd_val, pure_val, upOf]
    congr 1; funext k
    show decide (g ∈ [P.c k]) = (P.c k == g)
    by_cases h : P.c k = g
    · subst h; simp
    · simp [h, Ne.symm h]
  have hO : (scatterC (needKeysC P Y (fun k => up.contains k)) agents (fun _ => none)).val =
      fun g => agents.find? (fun j => !(up.contains j) && decide (P.Prefers Y j g)) := by
    rw [scatterC_val]; funext g
    simp only [Option.none_or]
    congr 1; funext j
    exact needKeysC_mem P Y up j g
  simp only [tabsC, bind_val, constT_val, hU, hH, hC, hO, mkTable_val, junkEntryC, freeEntryC, rd_val, pure_val,
    specTabs]
  congr 1
  · funext g
    rw [hG g]
    unfold junkB junkList
    cases h1 : picker agents Y g <;> cases h2 : upOf P up g <;> simp [List.mem_filter, h1, h2]
  · funext k
    rw [hA k]
    unfold freeB frozenB naB
    cases Y k with
    | none => simp
    | some y => simp only [bind_val, rd_val, pure_val, isSome_find]


/-! ## The cycle of `σ`: walks over the orbit -/

/-- `σᵏ(w)`: `k` reads. -/
def iterC (σ : Fin n → Fin n) : Nat → Fin n → Timed (Fin n)
  | 0, w => pure w
  | k + 1, w => do
    let w' ← iterC σ k w
    tick 1
    rd σ w'

theorem iterC_val (σ : Fin n → Fin n) : ∀ (k : Nat) (w : Fin n), (iterC σ k w).val = iter σ k w
  | 0, _ => rfl
  | k + 1, w => by simp only [iterC, bind_val, rd_val, iterC_val σ k w]; rfl

theorem iterC_cost (σ : Fin n → Fin n) : ∀ (k : Nat) (w : Fin n), (iterC σ k w).cost = 2 * k
  | 0, _ => rfl
  | k + 1, w => by simp only [iterC, bind_cost, tick_cost, rd_cost, iterC_cost σ k w]; omega

/-- The search for the period: `q = σ^(k+1)(p)`; stop at the first return to `p` (a comparison, an increment of the
counter and a read per step). -/
def searchC (σ : Fin n → Fin n) (p : Fin n) : Nat → Nat → Fin n → Timed (Option Nat)
  | 0, _, _ => pure none
  | fuel + 1, k, q => do
    tick 2
    if q = p then pure (some k) else do
      let q' ← rd σ q
      searchC σ p fuel (k + 1) q'

theorem searchC_val (σ : Fin n → Fin n) (p : Fin n) : ∀ (fuel k : Nat),
    (searchC σ p fuel k (iter σ (k + 1) p)).val = (List.range' k fuel).find? (fun j => iter σ (j + 1) p == p)
  | 0, _ => rfl
  | fuel + 1, k => by
    rw [List.range'_succ, List.find?_cons]
    simp only [searchC, bind_val]
    by_cases h : iter σ (k + 1) p = p
    · simp [h]
    · have hb : (iter σ (k + 1) p == p) = false := by simp [h]
      simp only [h, ↓reduceIte, bind_val, rd_val, hb]
      have e : σ (iter σ (k + 1) p) = iter σ (k + 1 + 1) p := rfl
      rw [e, searchC_val σ p fuel (k + 1)]

theorem searchC_cost (σ : Fin n → Fin n) (p : Fin n) : ∀ (fuel k : Nat) (q : Fin n),
    (searchC σ p fuel k q).cost ≤ 3 * fuel
  | 0, _, _ => by simp [searchC]
  | fuel + 1, k, q => by
    have ih := searchC_cost σ p fuel (k + 1) (σ q)
    simp only [searchC, bind_cost, tick_cost]
    split
    · simp only [pure_cost]; omega
    · simp only [bind_cost, rd_cost, rd_val]; omega

/-- **The period** of `p` (`EFX.DE.period`): the first return to `p` within `l` steps, else `1`. -/
def periodC (σ : Fin n → Fin n) (l : Nat) (p : Fin n) : Timed Nat := do
  let q ← rd σ p
  let r ← searchC σ p l 0 q
  tick 1
  pure ((r.map (· + 1)).getD 1)

theorem periodC_val (σ : Fin n → Fin n) (l : Nat) (p : Fin n) : (periodC σ l p).val = period σ l p := by
  simp only [periodC, bind_val, rd_val, pure_val, period, List.range_eq_range']
  have e : σ p = iter σ (0 + 1) p := rfl
  rw [e, searchC_val]

theorem periodC_cost (σ : Fin n → Fin n) (l : Nat) (p : Fin n) : (periodC σ l p).cost ≤ 3 * l + 2 := by
  have := searchC_cost σ p l 0 (σ p)
  simp only [periodC, bind_cost, rd_cost, rd_val, tick_cost, pure_cost]
  omega

/-- Mark `w, σ w, …, σ^(k−1) w` in `T`. -/
def onLoopC (σ : Fin n → Fin n) : Nat → Fin n → (Fin n → Bool) → Timed (Fin n → Bool)
  | 0, _, T => pure T
  | k + 1, w, T => do
    tick 1
    let T' ← wr T w true
    let w' ← rd σ w
    onLoopC σ k w' T'

theorem onLoopC_val (σ : Fin n → Fin n) (p : Fin n) : ∀ (k j0 : Nat) (T : Fin n → Bool),
    (onLoopC σ k (iter σ j0 p) T).val = fun x => T x || (List.range' j0 k).any (fun j => iter σ j p == x)
  | 0, _, T => by simp [onLoopC]
  | k + 1, j0, T => by
    simp only [onLoopC, bind_val, wr_val, rd_val]
    have e : σ (iter σ j0 p) = iter σ (j0 + 1) p := rfl
    rw [e, onLoopC_val σ p k (j0 + 1)]
    funext x
    rw [List.range'_succ, List.any_cons]
    by_cases h : x = iter σ j0 p
    · subst h; simp
    · have : (iter σ j0 p == x) = false := by simp [Ne.symm h]
      simp [h, this]

theorem onLoopC_cost (σ : Fin n → Fin n) : ∀ (k : Nat) (w : Fin n) (T : Fin n → Bool),
    (onLoopC σ k w T).cost = 3 * k
  | 0, _, _ => rfl
  | k + 1, w, T => by
    simp only [onLoopC, bind_cost, tick_cost, wr_cost, rd_cost, wr_val, rd_val, onLoopC_cost σ k]
    omega

/-- Write `pred (σ w) := w` along `w, σ w, …, σ^(k−1) w`; return the array and `σᵏ w`. -/
def predLoopC (σ : Fin n → Fin n) : Nat → Fin n → (Fin n → Fin n) → Timed ((Fin n → Fin n) × Fin n)
  | 0, w, T => pure (T, w)
  | k + 1, w, T => do
    tick 1
    let w' ← rd σ w
    let T' ← wr T w' w
    predLoopC σ k w' T'

theorem predLoopC_cost (σ : Fin n → Fin n) : ∀ (k : Nat) (w : Fin n) (T : Fin n → Fin n),
    (predLoopC σ k w T).cost = 3 * k
  | 0, _, _ => rfl
  | k + 1, w, T => by
    simp only [predLoopC, bind_cost, tick_cost, wr_cost, rd_cost, wr_val, rd_val, predLoopC_cost σ k]
    omega

theorem predLoopC_spec (σ : Fin n → Fin n) (p : Fin n) : ∀ (k j0 : Nat) (T : Fin n → Fin n),
    (∀ a b, j0 + 1 ≤ a → a < b → b ≤ j0 + k → iter σ a p ≠ iter σ b p) →
    (predLoopC σ k (iter σ j0 p) T).val.2 = iter σ (j0 + k) p ∧
    (∀ j, j0 ≤ j → j < j0 + k → (predLoopC σ k (iter σ j0 p) T).val.1 (iter σ (j + 1) p) = iter σ j p) ∧
    (∀ x, (∀ j, j0 ≤ j → j < j0 + k → iter σ (j + 1) p ≠ x) →
      (predLoopC σ k (iter σ j0 p) T).val.1 x = T x)
  | 0, j0, T, _ => by
    refine ⟨rfl, fun j h1 h2 => by omega, fun x _ => rfl⟩
  | k + 1, j0, T, hD => by
    have e : (predLoopC σ (k + 1) (iter σ j0 p) T).val =
        (predLoopC σ k (iter σ (j0 + 1) p)
          (fun x => if x = iter σ (j0 + 1) p then iter σ j0 p else T x)).val := rfl
    rw [e]
    obtain ⟨ih1, ih2, ih3⟩ := predLoopC_spec σ p k (j0 + 1)
      (fun x => if x = iter σ (j0 + 1) p then iter σ j0 p else T x)
      (fun a b h1 h2 h3 => hD a b (by omega) h2 (by omega))
    refine ⟨by rw [ih1]; congr 1; omega, fun j h1 h2 => ?_, fun x hx => ?_⟩
    · by_cases hj : j = j0
      · subst hj
        rw [ih3 _ (fun j' h1' h2' heq => hD (j + 1) (j' + 1) (by omega) (by omega) (by omega) heq.symm)]
        simp
      · exact ih2 j (by omega) (by omega)
    · rw [ih3 x (fun j h1 h2 => hx j (by omega) (by omega))]
      have : x ≠ iter σ (j0 + 1) p := fun h => hx j0 (Nat.le_refl _) (by omega) h.symm
      simp [this]

end fin

section orbit
variable {A : Type} [DecidableEq A]

omit [DecidableEq A] in
theorem find_range'_some (q : Nat → Bool) : ∀ (k s j : Nat), (List.range' s k).find? q = some j →
    s ≤ j ∧ j < s + k ∧ q j = true ∧ ∀ i, s ≤ i → i < j → q i = false
  | 0, s, j, h => by simp at h
  | k + 1, s, j, h => by
    rw [List.range'_succ, List.find?_cons] at h
    cases hq : q s with
    | true =>
      rw [hq] at h
      cases h
      exact ⟨Nat.le_refl _, by omega, hq, fun i h1 h2 => by omega⟩
    | false =>
      rw [hq] at h
      obtain ⟨h1, h2, h3, h4⟩ := find_range'_some q k (s + 1) j h
      refine ⟨by omega, by omega, h3, fun i hi1 hi2 => ?_⟩
      by_cases his : i = s
      · subst his; exact hq
      · exact h4 i (by omega) hi2

/-- **The period** is positive, the orbit's points `σⁱ p`, `i < per`, are distinct, and if `per > 1` then
`σ^per p = p`. -/
theorem period_facts (σ : A → A) (l : Nat) (p : A) :
    0 < period σ l p ∧ (∀ a b, a < b → b < period σ l p → iter σ a p ≠ iter σ b p) ∧
      (period σ l p = 1 ∨ iter σ (period σ l p) p = p) := by
  unfold period
  cases h : (List.range l).find? (fun k => iter σ (k + 1) p == p) with
  | none => exact ⟨by simp, fun a b h1 h2 => by simp at h2; omega, Or.inl rfl⟩
  | some k =>
    rw [List.range_eq_range'] at h
    obtain ⟨-, -, hk, hlt⟩ := find_range'_some _ l 0 k h
    simp only [beq_iff_eq] at hk
    simp only [Option.map_some, Option.getD_some]
    refine ⟨by omega, fun a b hab hb heq => ?_, Or.inr hk⟩
    have h1 : iter σ (k + 1 - b) (iter σ a p) = iter σ (k + 1 - b) (iter σ b p) := by rw [heq]
    rw [← iter_add, ← iter_add] at h1
    have e2 : k + 1 - b + b = k + 1 := by omega
    rw [e2, hk] at h1
    have := hlt (k - b + a) (by omega) (by omega)
    have e3 : k - b + a + 1 = k + 1 - b + a := by omega
    rw [e3, h1] at this
    simp at this

end orbit

section fin
variable {n m : Nat}

/-- The predecessor on the orbit, from `predLoopC`: `σ^(per−1)`. -/
theorem pred_orbit (σ : Fin n → Fin n) (l : Nat) (p : Fin n) (T : Fin n → Fin n) {w : Fin n}
    (hw : onOrbit σ (period σ l p) p w = true) :
    (if w = p then (predLoopC σ (period σ l p - 1) p T).val.2 else (predLoopC σ (period σ l p - 1) p T).val.1 w) =
      iter σ (period σ l p - 1) w := by
  obtain ⟨hpos, hdist, hret⟩ := period_facts σ l p
  obtain ⟨i, hi, rfl⟩ := onOrbit_iff.mp hw
  have hD : ∀ a b, 0 + 1 ≤ a → a < b → b ≤ 0 + (period σ l p - 1) → iter σ a p ≠ iter σ b p :=
    fun a b h1 h2 h3 => hdist a b h2 (by omega)
  obtain ⟨h1, h2, -⟩ := predLoopC_spec σ p (period σ l p - 1) 0 T hD
  have h1' : (predLoopC σ (period σ l p - 1) p T).val.2 = iter σ (period σ l p - 1) p := by
    have := h1
    rw [Nat.zero_add] at this
    exact this
  have h2' : ∀ j, j < period σ l p - 1 →
      (predLoopC σ (period σ l p - 1) p T).val.1 (iter σ (j + 1) p) = iter σ j p :=
    fun j hj => h2 j (Nat.zero_le _) (by omega)
  by_cases hi0 : i = 0
  · subst hi0
    have e0 : iter σ 0 p = p := rfl
    simp [e0, h1']
  · have hne : iter σ i p ≠ p := fun h => hdist 0 i (by omega) hi h.symm
    simp only [hne, ↓reduceIte]
    have e : iter σ i p = iter σ (i - 1 + 1) p := by congr 1; omega
    rw [e, h2' (i - 1) (by omega)]
    have hp : iter σ (period σ l p) p = p := hret.resolve_left (by omega)
    rw [← iter_add]
    have e2 : period σ l p - 1 + (i - 1 + 1) = i - 1 + period σ l p := by omega
    rw [e2, iter_add, hp]


/-- The new holding of `w` (`exchY`): its pair if its predecessor on the cycle is free, else the predecessor's good;
unchanged off the cycle. -/
def exchEntryC (free : Fin n → Bool) (P : Profile (Fin n) (Fin m)) (Y : Fin n → Option (Fin m))
    (onC : Fin n → Bool) (pred : Fin n → Fin n) (w : Fin n) : Timed (Option (Fin m)) := do
  let on ← rd onC w
  bif on then do
    let pw ← rd pred w
    let f ← rd free pw
    bif f then do
      let b ← rd P.b w
      pure (some b)
    else rd Y pw
  else rd Y w

/-- `w` becomes a pair holder (`exchUp`): on the cycle, with a free predecessor. -/
def newPairC (free : Fin n → Bool) (onC : Fin n → Bool) (pred : Fin n → Fin n) (w : Fin n) : Timed Bool := do
  let on ← rd onC w
  bif on then do
    let pw ← rd pred w
    rd free pw
  else pure false

/-- **The move along the cycle of `σ` through `σˡ(s)`** (`cycleStep`), from the tables. -/
def cycleC (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (Y : Fin n → Option (Fin m))
    (up : List (Fin n)) (σ : Fin n → Fin n) (s : Fin n) (l : Nat) :
    Timed ((Fin n → Option (Fin m)) × List (Fin n)) := do
  let p ← iterC σ l s
  let per ← periodC σ l p
  let O0 ← constT n false
  let onC ← onLoopC σ per p O0
  let Q0 ← constT n p
  tick 1
  let r ← predLoopC σ (per - 1) p Q0
  let pred ← wr r.1 p r.2
  let Y' ← mkTable n (exchEntryC tb.free P Y onC pred)
  let np ← filterC (newPairC tb.free onC pred) agents
  let up' ← appendC up np
  pure (Y', up')

theorem cycleC_val (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (agents : List (Fin n))
    (Y : Fin n → Option (Fin m)) (up : List (Fin n)) (σ : Fin n → Fin n) (s : Fin n)
    (hf : tb.free = freeB P agents up Y) :
    (cycleC tb P agents Y up σ s agents.length).val = cycleStep P agents up Y σ s := by
  have hon : ∀ (p : Fin n) (k : Nat), (onLoopC σ k p (fun _ => false)).val = onOrbit σ k p := by
    intro p k
    refine (onLoopC_val σ p k 0 (fun _ => false)).trans ?_
    funext x
    simp only [onOrbit, List.range_eq_range', Bool.false_or]
  simp only [cycleC, bind_val, iterC_val, periodC_val, constT_val, hon, wr_val, mkTable_val, exchEntryC, newPairC,
    rd_val, filterC_val, appendC_val, pure_val, cycleStep, hf]
  generalize iter σ agents.length s = p
  have hpred := fun w (hw : onOrbit σ (period σ agents.length p) p w = true) =>
    pred_orbit σ agents.length p (fun _ => p) hw
  congr 1
  · funext w
    unfold exchY
    by_cases hw : onOrbit σ (period σ agents.length p) p w = true
    · simp only [hw, Bool.cond_true, ↓reduceIte, bind_val, rd_val]
      rw [hpred w hw]
      cases freeB P agents up Y (iter σ (period σ agents.length p - 1) w) <;> simp
    · have hw' : onOrbit σ (period σ agents.length p) p w = false := by simpa using hw
      simp [hw']
  · unfold exchUp
    congr 1
    refine List.filter_congr fun w _ => ?_
    by_cases hw : onOrbit σ (period σ agents.length p) p w = true
    · simp only [hw, Bool.cond_true, bind_val, rd_val, Bool.true_and]
      rw [hpred w hw]
    · have hw' : onOrbit σ (period σ agents.length p) p w = false := by simpa using hw
      simp [hw']

/-! ## The exposed agents, `H_o`, the representatives and `σ` -/

/-- `gxS x` from the tables: seven reads and two comparisons. -/
def gxC (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (Y : Fin n → Option (Fin m)) (x : Fin n) :
    Timed (Option (Fin m)) := do
  let u ← rd tb.inUp x
  let y ← rd Y x
  let a ← rd P.a x
  let b ← rd P.b x
  let c ← rd P.c x
  let jb ← rd tb.junk b
  let jc ← rd tb.junk c
  tick 2
  pure (if !u && (y == some a) then
    (if jb && jc then none else if jb then some c else if jc then some b else if b = c then some b else none)
    else none)

theorem gxC_val (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (goods : List (Fin m))
    (Y : Fin n → Option (Fin m)) (up : List (Fin n)) (x : Fin n) :
    (gxC (specTabs P agents goods Y up) P Y x).val = gxS P agents up Y goods x := rfl

/-- **The lists `xsS g` for all goods** in one pass over `l` (from its end): `x` is added to the list of `gx x`. -/
def xsC (gx : Fin n → Timed (Option (Fin m))) : List (Fin n) → (Fin m → List (Fin n)) →
    Timed (Fin m → List (Fin n))
  | [], T => pure T
  | x :: l, T => do
    let T' ← xsC gx l T
    tick 1
    let k ← gx x
    match k with
    | none => pure T'
    | some g => do
      let cur ← rd T' g
      wr T' g (x :: cur)

theorem xsC_val (gx : Fin n → Timed (Option (Fin m))) : ∀ (l : List (Fin n)) (T : Fin m → List (Fin n)),
    (xsC gx l T).val = fun g => l.filter (fun x => (gx x).val == some g) ++ T g
  | [], T => by simp [xsC]
  | x :: l, T => by
    funext g
    simp only [xsC, bind_val]
    rw [xsC_val gx l T]
    cases hk : (gx x).val with
    | none => simp [hk]
    | some g' =>
      simp only [bind_val, rd_val, wr_val]
      by_cases hg : g = g'
      · subst hg; simp [hk]
      · have : (some g' == some g) = false := by simp [Ne.symm hg]
        simp [hk, hg, this]

/-- `hOf x` from the tables. -/
def hOfC (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (x : Fin n) : Timed (Fin m) := do
  let b ← rd P.b x
  let jb ← rd tb.junk b
  bif jb then pure b else rd P.c x

theorem hOfC_val (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (goods : List (Fin m))
    (Y : Fin n → Option (Fin m)) (up : List (Fin n)) (x : Fin n) :
    (hOfC (specTabs P agents goods Y up) P x).val = hOf P agents up Y goods x := by
  simp only [hOfC, bind_val, rd_val, specTabs, hOf]
  cases h : junkB P agents up Y goods (P.b x) <;> simp

/-- `x ≠ o`: one comparison. -/
def neC (o x : Fin n) : Timed Bool := do
  tick 1
  pure (x != o)

/-- `expL o` from the lists: `o`'s good, its list, without `o`. -/
def ELC (Xs : Fin m → List (Fin n)) (Y : Fin n → Option (Fin m)) (o : Fin n) : Timed (List (Fin n)) := do
  let y ← rd Y o
  match y with
  | none => pure []
  | some g => do
    let L ← rd Xs g
    filterC (neC o) L

theorem ELC_val (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (goods : List (Fin m))
    (Y : Fin n → Option (Fin m)) (up : List (Fin n)) (o : Fin n) :
    (ELC (xsS P agents up Y goods) Y o).val = expL P agents up Y goods o := by
  simp only [ELC, bind_val, rd_val, expL]
  cases Y o <;> simp [neC]

/-- **For each free agent**: its exposed agents, `H_o` (with the mark array, cleared afterwards) and `|H_o|`. -/
def freeLoopC (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (Y : Fin n → Option (Fin m))
    (Xs : Fin m → List (Fin n)) :
    List (Fin n) → (Fin m → Bool) → (Fin n → List (Fin n)) → (Fin n → List (Fin m) × Nat) →
      Timed ((Fin n → List (Fin n)) × (Fin n → List (Fin m) × Nat) × (Fin m → Bool))
  | [], M, EL, HS => pure (EL, HS, M)
  | o :: os, M, EL, HS => do
    tick 1
    let E ← ELC Xs Y o
    let hs ← mapC (hOfC tb P) E
    let r ← ddC hs M
    let M' ← setAllC false r.1 r.2
    let len ← lengthC r.1
    let EL' ← wr EL o E
    let HS' ← wr HS o (r.1, len)
    freeLoopC tb P Y Xs os M' EL' HS'

theorem freeLoopC_val (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (Y : Fin n → Option (Fin m))
    (Xs : Fin m → List (Fin n)) :
    ∀ (os : List (Fin n)) (EL : Fin n → List (Fin n)) (HS : Fin n → List (Fin m) × Nat),
    (freeLoopC tb P Y Xs os (fun _ => false) EL HS).val =
      (fun x => if x ∈ os then (ELC Xs Y x).val else EL x,
       fun x => if x ∈ os then (dd (((ELC Xs Y x).val).map (fun y => (hOfC tb P y).val)),
          (dd (((ELC Xs Y x).val).map (fun y => (hOfC tb P y).val))).length) else HS x,
       fun _ => false)
  | [], EL, HS => by simp [freeLoopC]
  | o :: os, EL, HS => by
    simp only [freeLoopC, bind_val, mapC_val, ddC_val, clear_dd, lengthC_val, wr_val]
    rw [freeLoopC_val tb P Y Xs os]
    simp only [Prod.mk.injEq, and_true]
    constructor
    · funext x
      by_cases h1 : x ∈ os
      · simp [h1]
      · by_cases h2 : x = o
        · subst h2; simp [h1]
        · simp [h1, h2]
    · funext x
      by_cases h1 : x ∈ os
      · simp [h1]
      · by_cases h2 : x = o
        · subst h2; simp [h1]
        · simp [h1, h2]

/-- `h` is not used yet. -/
def unusedC (U : Fin m → Bool) (h : Fin m) : Timed Bool := do
  let u ← rd U h
  pure !u

/-- **Greedy distinct representatives** (`EFX.DE.reps`), with a mark array of the used goods; the representative of
each agent is written into `R` (if it has none yet: `EFX.DE.repOf` takes the first). -/
def repsC (HS : Fin n → List (Fin m) × Nat) : List (Fin n) → (Fin m → Bool) → (Fin n → Option (Fin m)) →
    Timed (Fin n → Option (Fin m))
  | [], _, R => pure R
  | o :: os, U, R => do
    tick 1
    let H ← rd HS o
    let q ← findC (unusedC U) H.1
    match q with
    | none => repsC HS os U R
    | some q => do
      let U' ← wr U q true
      let r ← rd R o
      let R' ← wr R o (r.or (some q))
      repsC HS os U' R'

theorem repsC_val (HS : Fin n → List (Fin m) × Nat) (Hs : Fin n → List (Fin m)) :
    ∀ (os : List (Fin n)) (used : List (Fin m)) (U : Fin m → Bool) (R : Fin n → Option (Fin m)),
    (∀ o ∈ os, (HS o).1 = Hs o) → (∀ h, U h = used.contains h) →
    (repsC HS os U R).val = fun o => (R o).or (repOf (reps Hs os used) o)
  | [], _, _, R, _, _ => by simp [repsC, reps, repOf]
  | o :: os, used, U, R, hH, hU => by
    have hU' : (fun h => !U h) = fun h => !(used.contains h) := by funext h; rw [hU h]
    have hf : (findC (unusedC U) (HS o).1).val = (Hs o).find? (fun h => !(used.contains h)) := by
      simp only [findC_val, unusedC, bind_val, rd_val, pure_val, hH o (by simp)]
      rw [hU']
    simp only [repsC, bind_val, rd_val, hf]
    unfold reps
    cases hq : (Hs o).find? (fun h => !(used.contains h)) with
    | none =>
      exact repsC_val HS Hs os used U R (fun o' ho' => hH o' (by simp [ho'])) hU
    | some q =>
      have hU2 : ∀ h, (if h = q then true else U h) = (q :: used).contains h := by
        intro h; rw [hU h]; by_cases e : h = q <;> simp [e]
      simp only [bind_val, wr_val, rd_val]
      rw [repsC_val HS Hs os (q :: used) _ _ (fun o' ho' => hH o' (by simp [ho'])) hU2]
      funext o'
      by_cases e : o' = o
      · subst e; cases R o' <;> simp [repOf]
      · simp [repOf, e]

/-- The protecting good of `x` is `q`. -/
def hEqC (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (q : Fin m) (x : Fin n) : Timed Bool := do
  let h ← hOfC tb P x
  tick 1
  pure (h == q)

/-- The image of a free agent `o` under `σ` (the ring step): the first agent exposed for `o` whose protecting good is `o`'s
representative (or `o`). -/
def sigOneC (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (EL : Fin n → List (Fin n)) (R : Fin n → Option (Fin m))
    (o : Fin n) : Timed (Fin n) := do
  let r ← rd R o
  match r with
  | none => pure o
  | some q => do
    let E ← rd EL o
    let f ← findC (hEqC tb P q) E
    pure (f.getD o)

/-- **`σ` on the free agents** (the ring step), written into `S`. -/
def sigLoopC (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (EL : Fin n → List (Fin n))
    (R : Fin n → Option (Fin m)) :
    List (Fin n) → (Fin n → Fin n) → Timed (Fin n → Fin n)
  | [], S => pure S
  | o :: os, S => do
    tick 1
    let x ← sigOneC tb P EL R o
    let S' ← wr S o x
    sigLoopC tb P EL R os S'

/-- The image of a free agent `o` under `σ` (the ring step). -/
def sigFree (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (EL : Fin n → List (Fin n)) (R : Fin n → Option (Fin m))
    (o : Fin n) : Fin n :=
  match R o with
  | none => o
  | some q => ((EL o).find? (fun x => (hOfC tb P x).val == q)).getD o

theorem sigOneC_val (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (EL : Fin n → List (Fin n))
    (R : Fin n → Option (Fin m)) (o : Fin n) : (sigOneC tb P EL R o).val = sigFree tb P EL R o := by
  unfold sigOneC sigFree
  simp only [bind_val, rd_val]
  cases R o with
  | none => rfl
  | some q => simp [hEqC]

theorem sigLoopC_val (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (EL : Fin n → List (Fin n))
    (R : Fin n → Option (Fin m)) : ∀ (os : List (Fin n)) (S : Fin n → Fin n),
    (sigLoopC tb P EL R os S).val = fun x => if x ∈ os then sigFree tb P EL R x else S x
  | [], S => by simp [sigLoopC]
  | o :: os, S => by
    simp only [sigLoopC, bind_val, sigOneC_val, wr_val]
    rw [sigLoopC_val tb P EL R os]
    funext x
    by_cases h1 : x ∈ os
    · simp [h1]
    · by_cases h2 : x = o
      · subst h2; simp [h1]
      · simp [h1, h2]

/-- The out-neighbour of `j` in the need digraph (or `j`), from the tables. -/
def outNbC (tb : Tabs n m) (Y : Fin n → Option (Fin m)) (j : Fin n) : Timed (Fin n) := do
  let y ← rd Y j
  match y with
  | none => pure j
  | some g => do
    let o ← rd tb.out g
    pure (o.getD j)

/-- `σ j` in the ring step: a free agent by `S`, any other agent to its out-neighbour (or itself). -/
def sigExEntryC (tb : Tabs n m) (Y : Fin n → Option (Fin m)) (S : Fin n → Fin n) (j : Fin n) : Timed (Fin n) := do
  let f ← rd tb.free j
  bif f then rd S j else outNbC tb Y j

/-- `σ j` in the chain step: a free agent to `x`, any other agent to its out-neighbour (or itself). -/
def sigPairEntryC (tb : Tabs n m) (Y : Fin n → Option (Fin m)) (x j : Fin n) : Timed (Fin n) := do
  let f ← rd tb.free j
  bif f then pure x else outNbC tb Y j

/-- **The table of `σ`** (the ring step). -/
def sigExC (tb : Tabs n m) (Y : Fin n → Option (Fin m)) (S : Fin n → Fin n) : Timed (Fin n → Fin n) :=
  mkTable n (sigExEntryC tb Y S)

/-- **The table of `σ`** in the chain step: every free agent to `x`. -/
def sigPairC (tb : Tabs n m) (Y : Fin n → Option (Fin m)) (x : Fin n) : Timed (Fin n → Fin n) :=
  mkTable n (sigPairEntryC tb Y x)

theorem outNbC_val (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (goods : List (Fin m))
    (Y : Fin n → Option (Fin m)) (up : List (Fin n)) (j : Fin n) :
    (outNbC (specTabs P agents goods Y up) Y j).val = (outNb P agents up Y j).getD j := by
  unfold outNbC outNb
  simp only [bind_val, rd_val, specTabs]
  cases Y j <;> simp

theorem sigExC_val (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (goods : List (Fin m))
    (Y : Fin n → Option (Fin m)) (up : List (Fin n)) (S : Fin n → Fin n) :
    (sigExC (specTabs P agents goods Y up) Y S).val =
      fun j => if freeB P agents up Y j then S j else (outNb P agents up Y j).getD j := by
  funext j
  simp only [sigExC, mkTable_val, sigExEntryC, bind_val, rd_val]
  by_cases hf : freeB P agents up Y j = true
  · simp [hf, specTabs]
  · have hf' : freeB P agents up Y j = false := by simpa using hf
    have : (specTabs P agents goods Y up).free j = false := hf'
    simp only [this, hf', Bool.cond_false, Bool.false_eq_true, ↓reduceIte, outNbC_val]

theorem sigPairC_val (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (goods : List (Fin m))
    (Y : Fin n → Option (Fin m)) (up : List (Fin n)) (x : Fin n) :
    (sigPairC (specTabs P agents goods Y up) Y x).val = sigmaMap P agents up Y goods (some x) [] := by
  funext j
  simp only [sigPairC, mkTable_val, sigPairEntryC, bind_val, rd_val, sigmaMap]
  by_cases hf : freeB P agents up Y j = true
  · simp [hf, specTabs]
  · have hf' : freeB P agents up Y j = false := by simpa using hf
    have : (specTabs P agents goods Y up).free j = false := hf'
    simp only [this, hf', Bool.cond_false, Bool.false_eq_true, ↓reduceIte, outNbC_val]

/-! ## One step -/

/-- (P) fails at `x` (`pairB`), from the tables. -/
def pairTestC (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (Y : Fin n → Option (Fin m)) (x : Fin n) :
    Timed Bool := do
  let u ← rd tb.inUp x
  let y ← rd Y x
  let a ← rd P.a x
  let b ← rd P.b x
  let c ← rd P.c x
  let jb ← rd tb.junk b
  let jc ← rd tb.junk c
  tick 1
  pure (!u && (y == some a) && jb && jc)

/-- `k` is not a pair holder. -/
def notUpC (tb : Tabs n m) (k : Fin n) : Timed Bool := do
  let u ← rd tb.inUp k
  pure !u

/-- `o` is free and `|H_o| + 1 ≤ |F|` (Lemma forced), from the table of `(H_o, |H_o|)`. -/
def forcedC (tb : Tabs n m) (HS : Fin n → List (Fin m) × Nat) (lF : Nat) (o : Fin n) : Timed Bool := do
  let f ← rd tb.free o
  bif f then do
    let h ← rd HS o
    tick 2
    pure (decide (h.2 + 1 ≤ lF))
  else pure false

/-- A new array holding each index (`n` units). -/
def idTabC (k : Nat) : Timed (Fin k → Fin k) := mkTable k (fun j => pure j)

@[simp] theorem idTabC_val (k : Nat) : (idTabC k).val = fun j => j := by simp [idTabC]

/-- **One step of DE** (`EFX.DE.step`) as a counted program. `l` is the number of agents. -/
def stepC (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (inA : Fin n → Bool) (inG : Fin m → Bool)
    (d : Fin n) (l : Nat) (Y : Fin n → Option (Fin m)) (up : List (Fin n)) : Timed (Out (Fin n) (Fin m)) := do
  let tb ← tabsC P agents inA inG Y up
  let px ← findC (pairTestC tb P Y) agents
  match px with
  | some x => do
    let σ ← sigPairC tb Y x
    let r ← cycleC tb P agents Y up σ x l
    pure (.next r.1 r.2)
  | none => do
    let s ← findC (notUpC tb) agents
    match s with
    | none => pure (.stop (agents.headD d) [])
    | some s => do
      let F ← filterC (rd tb.free) agents
      let lF ← lengthC F
      let X0 ← constT m []
      let Xs ← xsC (gxC tb P Y) agents X0
      let M0 ← constT m false
      let EL0 ← constT n []
      let HS0 ← constT n ([], 0)
      let fr ← freeLoopC tb P Y Xs F M0 EL0 HS0
      let fo ← findC (forcedC tb fr.2.1 lF) agents
      match fo with
      | some o => do
        let h ← rd fr.2.1 o
        pure (.stop o h.1)
      | none => do
        let U0 ← constT m false
        let R0 ← constT n none
        let R ← repsC fr.2.1 F U0 R0
        let S0 ← idTabC n
        let S ← sigLoopC tb P fr.1 R F S0
        let σ ← sigExC tb Y S
        let r ← cycleC tb P agents Y up σ s l
        pure (.next r.1 r.2)

/-! ## `stepC` computes `step` -/

theorem xsC_spec (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (goods : List (Fin m))
    (Y : Fin n → Option (Fin m)) (up : List (Fin n)) :
    (xsC (gxC (specTabs P agents goods Y up) P Y) agents (fun _ => [])).val = xsS P agents up Y goods := by
  rw [xsC_val]
  funext g
  simp only [gxC_val, List.append_nil, xsS]

theorem freeLoopC_spec (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (goods : List (Fin m))
    (Y : Fin n → Option (Fin m)) (up : List (Fin n)) (F : List (Fin n)) :
    (freeLoopC (specTabs P agents goods Y up) P Y (xsS P agents up Y goods) F (fun _ => false) (fun _ => [])
      (fun _ => ([], 0))).val =
      (fun x => if x ∈ F then expL P agents up Y goods x else [],
       fun x => if x ∈ F then (dd ((expL P agents up Y goods x).map (hOf P agents up Y goods)),
          (dd ((expL P agents up Y goods x).map (hOf P agents up Y goods))).length) else ([], 0),
       fun _ => false) := by
  rw [freeLoopC_val]
  simp only [ELC_val, hOfC_val]

@[simp] theorem specTabs_free (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (goods : List (Fin m))
    (Y : Fin n → Option (Fin m)) (up : List (Fin n)) :
    (specTabs P agents goods Y up).free = freeB P agents up Y := rfl

theorem mem_filter_free {P : Profile (Fin n) (Fin m)} {agents : List (Fin n)} {Y : Fin n → Option (Fin m)}
    {up : List (Fin n)} (x : Fin n) : x ∈ agents.filter (freeB P agents up Y) ↔ freeB P agents up Y x = true := by
  rw [List.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨(freeB_iff.mp h).1, h⟩

/-- The free-agent loop, under (P): the exposed agents and `(H_o, |H_o|)` of each free agent. -/
theorem freeLoopC_free (P : Profile (Fin n) (Fin m)) {agents : List (Fin n)} {goods : List (Fin m)}
    {Y : Fin n → Option (Fin m)} {up : List (Fin n)} (hx : agents.find? (pairB P agents up Y goods) = none) :
    (freeLoopC (specTabs P agents goods Y up) P Y (xsS P agents up Y goods) (agents.filter (freeB P agents up Y))
      (fun _ => false) (fun _ => []) (fun _ => ([], 0))).val =
      (fun x => if freeB P agents up Y x then expL P agents up Y goods x else [],
       fun x => if freeB P agents up Y x then (Hset P agents up Y goods x, (Hset P agents up Y goods x).length)
         else ([], 0),
       fun _ => false) := by
  rw [freeLoopC_spec]
  simp only [Prod.mk.injEq, and_true]
  constructor
  · funext x
    by_cases h : freeB P agents up Y x = true
    · simp [(mem_filter_free x).mpr h, h]
    · have h' : freeB P agents up Y x = false := by simpa using h
      have : x ∉ agents.filter (freeB P agents up Y) := fun hm => h ((mem_filter_free x).mp hm)
      simp [this, h']
  · funext x
    by_cases h : freeB P agents up Y x = true
    · simp [(mem_filter_free x).mpr h, h, Hset_eq hx h]
    · have h' : freeB P agents up Y x = false := by simpa using h
      have : x ∉ agents.filter (freeB P agents up Y) := fun hm => h ((mem_filter_free x).mp hm)
      simp [this, h']

theorem and_if_len {G : Type} (b : Bool) (H : List G) (k : Nat) :
    (b && decide ((if b = true then (H, H.length) else (([] : List G), 0)).2 + 1 ≤ k)) =
      (b && decide (H.length + 1 ≤ k)) := by
  cases b <;> simp

theorem forcedC_val (tb : Tabs n m) (HS : Fin n → List (Fin m) × Nat) (lF : Nat) (o : Fin n) :
    (forcedC tb HS lF o).val = (tb.free o && decide ((HS o).2 + 1 ≤ lF)) := by
  simp only [forcedC, bind_val, rd_val]
  cases tb.free o <;> rfl

/-- **`stepC` computes `step`.** -/
theorem stepC_val (P : Profile (Fin n) (Fin m)) {agents : List (Fin n)} {inA : Fin n → Bool} {inG : Fin m → Bool}
    {goods : List (Fin m)} (d : Fin n) (Y : Fin n → Option (Fin m)) (up : List (Fin n))
    (hA : ∀ k, inA k = agents.contains k) (hG : ∀ g, inG g = decide (g ∈ goods)) :
    (stepC P agents inA inG d agents.length Y up).val = step P agents goods d Y up := by
  have hpair : ∀ x, (pairTestC (specTabs P agents goods Y up) P Y x).val = pairB P agents up Y goods x :=
    fun _ => rfl
  have hnu : ∀ k, (notUpC (specTabs P agents goods Y up) k).val = !(up.contains k) := fun _ => rfl
  unfold stepC step
  simp only [bind_val, tabsC_val P Y up hA hG, findC_val, hpair]
  cases hx : agents.find? (pairB P agents up Y goods) with
  | some x =>
    simp only [bind_val, sigPairC_val, cycleC_val (specTabs P agents goods Y up) P agents Y up _ x rfl, pure_val]
  | none =>
    simp only [bind_val, findC_val, hnu]
    cases hs : agents.find? (fun k => !(up.contains k)) with
    | none => rfl
    | some s =>
      simp only [bind_val, filterC_val, rd_val, lengthC_val, constT_val, xsC_spec, specTabs_free]
      rw [freeLoopC_free P hx]
      simp only [findC_val, forcedC_val, specTabs_free, and_if_len]
      cases hfo : List.find? (fun o => freeB P agents up Y o &&
          decide ((Hset P agents up Y goods o).length + 1 ≤ (List.filter (freeB P agents up Y) agents).length))
          agents with
      | some o =>
        have hfree : freeB P agents up Y o = true := by
          have := List.find?_some hfo
          simp only [Bool.and_eq_true] at this
          exact this.1
        simp [hfree]
      | none =>
        simp only [bind_val, constT_val, idTabC_val, pure_val]
        rw [repsC_val _ (Hset P agents up Y goods) (agents.filter (freeB P agents up Y)) [] (fun _ => false)
          (fun _ => none) (fun o ho => by simp [(mem_filter_free o).mp ho]) (fun h => rfl)]
        rw [sigLoopC_val, sigExC_val, cycleC_val (specTabs P agents goods Y up) P agents Y up _ s rfl]
        congr 3 <;> funext j
        all_goals
          by_cases hf : freeB P agents up Y j = true
          · have hj : j ∈ List.filter (fun x => freeB P agents up Y x) agents := (mem_filter_free j).mpr hf
            simp only [hf, ↓reduceIte, hj, sigFree, sigmaMap, Option.none_or]
            cases hr : repOf (reps (Hset P agents up Y goods) (List.filter (freeB P agents up Y) agents) []) j with
            | none => rfl
            | some q =>
              simp only [hOfC_val]
              rw [find_expB hx hf q]
          · have hf' : freeB P agents up Y j = false := by simpa using hf
            simp [hf', sigmaMap]

end fin

end DE
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE.expB_eq
#print axioms EFX.DE.filter_expB
#print axioms EFX.DE.tabsC_val
#print axioms EFX.DE.period_facts
#print axioms EFX.DE.pred_orbit
#print axioms EFX.DE.cycleC_val
#print axioms EFX.DE.repsC_val
#print axioms EFX.DE.freeLoopC_free
#print axioms EFX.DE.stepC_val
