import EFX.K3DEAlgo
import EFX.K3Cost

/-!
# The running time of Draft and Exchange, part 1: arrays with writes, and peeling

`paper/k3-simple/long.tex` §6, paragraph "Running time": DE runs in `O(n(n + m))` steps. This file and
`EFX.K3DECostStep`, `EFX.K3DECostRun`, `EFX.K3DECostBound` formalize that count: a counted program `EFX.DE.deC`
(in the cost monad `EFX.Timed`) whose value is `EFX.DE.deSpec` (`EFX.DE.de_eq_spec`), and a bound
`O((n + 1)(n + m + 1))` on its counted operations (`EFX.DE.deC_cost`).

**The cost model.** The units of `EFX.Timed` and `EFX.K3CostLB`: one step of a loop (a list cell visited, or one
round of a walk such as `σ ↦ σ(w)`), one comparison of two agents, goods or numbers, one addition (values or
counters), one read of a table or of an input value `v i g`; `EFX.Timed.mkTable` fills an array of `k` entries at
the cost of its entries plus `k`, and `K3.finRangeC k` costs `k`. As there, building a pair, an `Option` or a list
cell, pattern matching, and Boolean connectives are free, and straight-line code is charged by one `tick`. One new
kind of unit is introduced here:
- **an array write** (`wr`): an array is represented by its read function `α → β` (with `α = Fin k` in the
  programs); writing one entry costs one unit, as in the RAM model. A read (`rd`) costs one unit, as before. An
  entry may hold a list (a pointer): prepending to it is one write.
  The programs use every array single-threaded: once an entry is overwritten, the old version of the array is
  never read again (a fresh array, `constT` or `mkTable`, is made whenever an old version is still needed: the
  draft copies the array of remaining goods, the exchange writes the new holdings into a new table), so a RAM
  implementation updates the array in place. The value lemmas do not depend on this; the cost model does.

**Contents.**
- `rd`, `wr`, `constT` (a new array with one value, `k` units), and loops over lists that write into arrays:
  `setAllC` (set the entries of a list), `putC`/`scatterC` (each key receives the first element of a list that
  lists it: the holder of a good, the first pair holder of a `c`, the first agent that needs a good), `ddC`
  (`EFX.DE.dd` with a mark array, followed by `setAllC false` to clear the marks), with value and cost lemmas.
- Peeling: `r1Rel` (rule R1 computed from the relevant goods only, `r1Step_eq_rel`), `r1C`, `findR1F`
  (`EFX.K3.findR1` from each agent's relevant goods and a membership array of the remaining goods:
  `findR1F_val`); with at most three relevant goods per agent a test costs `27` units, so a round of peeling
  costs `O(n)` besides the list updates.
-/

set_option autoImplicit false

namespace EFX
namespace DE

open Timed LB

/-! ## Arrays: reads, writes, new arrays -/

section arrays
variable {α β κ : Type}

/-- Read entry `a` of the array `f`: one unit. -/
def rd (f : α → β) (a : α) : Timed β := ⟨f a, 1⟩

/-- Write `b` into entry `a` of the array `f`: one unit (the RAM model; see the module doc). -/
def wr [DecidableEq α] (f : α → β) (a : α) (b : β) : Timed (α → β) :=
  ⟨fun x => if x = a then b else f x, 1⟩

@[simp] theorem rd_val (f : α → β) (a : α) : (rd f a).val = f a := rfl
@[simp] theorem rd_cost (f : α → β) (a : α) : (rd f a).cost = 1 := rfl
@[simp] theorem wr_val [DecidableEq α] (f : α → β) (a : α) (b : β) :
    (wr f a b).val = fun x => if x = a then b else f x := rfl
@[simp] theorem wr_cost [DecidableEq α] (f : α → β) (a : α) (b : β) : (wr f a b).cost = 1 := rfl

/-- A new array of `k` entries, all `b`: `k` units. -/
def constT (k : Nat) (b : β) : Timed (Fin k → β) := mkTable k (fun _ => pure b)

@[simp] theorem constT_val (k : Nat) (b : β) : (constT k b).val = fun _ => b := by
  simp [constT]

theorem constT_cost (k : Nat) (b : β) : (constT k b).cost ≤ k := by
  have := mkTable_cost k (fun _ => (pure b : Timed β)) 0 (fun _ => by simp)
  simpa [constT] using this

/-! ## Loops that write into arrays -/

/-- Write `b` into the entries of `l`, in order: two units per element. -/
def setAllC [DecidableEq α] (b : β) : List α → (α → β) → Timed (α → β)
  | [], T => pure T
  | x :: l, T => do
    tick 1
    let T' ← wr T x b
    setAllC b l T'

theorem setAllC_val [DecidableEq α] (b : β) : ∀ (l : List α) (T : α → β),
    (setAllC b l T).val = fun y => if y ∈ l then b else T y
  | [], T => by simp [setAllC]
  | x :: l, T => by
    simp only [setAllC, bind_val, wr_val]
    rw [setAllC_val b l]
    funext y
    by_cases h1 : y ∈ l
    · simp [h1]
    · by_cases h2 : y = x
      · simp [h2]
      · simp [h1, h2]

theorem setAllC_cost [DecidableEq α] (b : β) : ∀ (l : List α) (T : α → β), (setAllC b l T).cost = 2 * l.length
  | [], T => by simp [setAllC]
  | x :: l, T => by
    simp only [setAllC, bind_cost, tick_cost, wr_cost, setAllC_cost b l, List.length_cons]
    omega

/-- `x` takes every key of `ks` that has no element yet (a step, a read and possibly a write per key). -/
def putC [DecidableEq κ] (x : α) : List κ → (κ → Option α) → Timed (κ → Option α)
  | [], T => pure T
  | k :: ks, T => do
    tick 1
    let t ← rd T k
    match t with
    | some _ => putC x ks T
    | none => do
      let T' ← wr T k (some x)
      putC x ks T'

theorem putC_val [DecidableEq κ] (x : α) : ∀ (ks : List κ) (T : κ → Option α),
    (putC x ks T).val = fun k => (T k).or (if k ∈ ks then some x else none)
  | [], T => by simp [putC]
  | k :: ks, T => by
    funext k'
    cases hT : T k with
    | some y =>
      simp only [putC, bind_val, rd_val, hT]
      rw [putC_val x ks T]
      by_cases hk : k' = k
      · subst hk; simp [hT]
      · simp [hk]
    | none =>
      simp only [putC, bind_val, rd_val, hT, wr_val]
      rw [putC_val x ks]
      by_cases hk : k' = k
      · subst hk; simp [hT]
      · simp [hk]

theorem putC_cost [DecidableEq κ] (x : α) :
    ∀ (ks : List κ) (T : κ → Option α), (putC x ks T).cost ≤ 3 * ks.length
  | [], T => by simp [putC]
  | k :: ks, T => by
    have h1 := putC_cost x ks T
    cases hT : T k with
    | some y =>
      simp only [putC, bind_cost, tick_cost, rd_cost, rd_val, hT, List.length_cons]
      omega
    | none =>
      have h2 := putC_cost x ks (fun z => if z = k then some x else T z)
      simp only [putC, bind_cost, tick_cost, rd_cost, rd_val, hT, wr_cost, wr_val, List.length_cons]
      omega

/-- **First-wins scatter.** Each element `x` of `l`, in order, takes the keys `keys x` that have no element yet:
afterwards a key holds the first element of `l` that lists it. -/
def scatterC [DecidableEq κ] (keys : α → Timed (List κ)) :
    List α → (κ → Option α) → Timed (κ → Option α)
  | [], T => pure T
  | x :: l, T => do
    tick 1
    let ks ← keys x
    let T' ← putC x ks T
    scatterC keys l T'

theorem scatterC_val [DecidableEq κ] (keys : α → Timed (List κ)) : ∀ (l : List α) (T : κ → Option α),
    (scatterC keys l T).val = fun k => (T k).or (l.find? (fun x => decide (k ∈ (keys x).val)))
  | [], T => by simp [scatterC]
  | x :: l, T => by
    simp only [scatterC, bind_val, putC_val]
    rw [scatterC_val keys l]
    funext k
    rw [Option.or_assoc, List.find?_cons]
    by_cases h : k ∈ (keys x).val <;> simp [h]

theorem scatterC_cost [DecidableEq κ] (keys : α → Timed (List κ)) (B : Nat) :
    ∀ (l : List α) (T : κ → Option α),
    (∀ x ∈ l, (keys x).cost + 3 * (keys x).val.length ≤ B) → (scatterC keys l T).cost ≤ l.length * (B + 1)
  | [], T, _ => by simp [scatterC]
  | x :: l, T, h => by
    have hx := h x (by simp)
    have ih := scatterC_cost keys B l ((putC x (keys x).val T).val) (fun y hy => h y (by simp [hy]))
    have hp := putC_cost x (keys x).val T
    simp only [scatterC, bind_cost, tick_cost, List.length_cons, Nat.succ_mul]
    omega

/-- **`dd` with a mark array**: walks the list from its start, keeping each element not marked yet and marking it;
from an array without marks this is `dd l` (each element at its first occurrence), with the marks of the elements of
`l` (`ddC_val`). `setAllC false (dd l)` clears the marks afterwards. -/
def ddC [DecidableEq α] : List α → (α → Bool) → Timed (List α × (α → Bool))
  | [], M => pure ([], M)
  | x :: l, M => do
    tick 1
    let seen ← rd M x
    if seen then ddC l M else do
      let M' ← wr M x true
      let r ← ddC l M'
      pure (x :: r.1, r.2)

/-- `ddC` from any marks: the unmarked elements of `dd l`, and the marks with those of `l` added. -/
theorem ddC_val_marks [DecidableEq α] : ∀ (l : List α) (M : α → Bool),
    (ddC l M).val = ((dd l).filter (fun y => !M y), fun y => M y || decide (y ∈ l))
  | [], M => by simp [ddC, dd]
  | x :: l, M => by
    simp only [ddC, bind_val]
    split
    · rename_i hx
      rw [rd_val] at hx
      simp only [ddC_val_marks l M, dd, List.filter_cons, hx, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        List.filter_filter, Prod.mk.injEq]
      constructor
      · refine List.filter_congr fun y _ => ?_
        by_cases h : y = x
        · subst h; simp [hx]
        · simp [h]
      · funext y
        by_cases h : y = x
        · subst h; simp [hx]
        · simp [h]
    · rename_i hx
      have hx' : M x = false := by simpa using hx
      simp only [bind_val, wr_val, pure_val, ddC_val_marks l, dd, List.filter_cons, hx', Bool.not_false,
        ↓reduceIte, List.filter_filter, Prod.mk.injEq]
      constructor
      · congr 1
        refine List.filter_congr fun y _ => ?_
        by_cases h : y = x
        · subst h; simp
        · simp [h]
      · funext y
        by_cases h : y = x
        · subst h; simp
        · simp [h]

theorem ddC_val [DecidableEq α] (l : List α) :
    (ddC l (fun _ => false)).val = (dd l, fun y => decide (y ∈ l)) := by
  rw [ddC_val_marks]
  simp

theorem ddC_cost [DecidableEq α] : ∀ (l : List α) (M : α → Bool), (ddC l M).cost ≤ 3 * l.length
  | [], M => by simp [ddC]
  | x :: l, M => by
    simp only [ddC, bind_cost, tick_cost, rd_cost, List.length_cons]
    split
    · have := ddC_cost l M; omega
    · have := ddC_cost l (wr M x true).val
      simp only [bind_cost, wr_cost, pure_cost]; omega

theorem length_dd [DecidableEq α] : ∀ l : List α, (dd l).length ≤ l.length
  | [] => by simp [dd]
  | x :: l => by
    have := length_dd l
    have := List.length_filter_le (· != x) (dd l)
    simp only [dd, List.length_cons]
    omega

/-- Marking the result of `ddC` and clearing it leaves an array without marks. -/
theorem clear_dd [DecidableEq α] (l : List α) :
    (setAllC false (dd l) (fun y => decide (y ∈ l))).val = fun _ => false := by
  rw [setAllC_val]
  funext y
  by_cases h : y ∈ l
  · simp [mem_dd.mpr h]
  · simp [h]

end arrays

/-! ## Peeling: rule R1 from the relevant goods -/

section peel
variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- Rule R1 for agent `i`, computed from `R`, its relevant goods among the remaining goods. -/
def r1Rel (v : A → G → Nat) (i : A) (R : List G) : Option (Option G) :=
  match favorite (v i) R with
  | none => some none
  | some p => if value v i (R.erase p) ≤ v i p then some (some p) else none

omit [DecidableEq G] in
/-- The favourite among the goods of positive value is the favourite, if its value is positive. -/
theorem favorite_filter_pos (f : G → Nat) : ∀ l : List G,
    favorite f (l.filter (fun g => 0 < f g)) = (favorite f l).bind (fun p => if f p = 0 then none else some p)
  | [] => by simp [favorite]
  | g :: S => by
    have ih := favorite_filter_pos f S
    by_cases hg : 0 < f g
    · have hg' : f g ≠ 0 := by omega
      rw [List.filter_cons_of_pos (by simpa using hg)]
      simp only [favorite, ih]
      cases hS : favorite f S with
      | none => simp [hg']
      | some p =>
        by_cases hp : f p = 0
        · simp [hp, hg']
        · by_cases hpg : f p ≤ f g
          · simp [hp, hpg, hg']
          · simp [hp, hpg]
    · have hg0 : f g = 0 := by omega
      rw [List.filter_cons_of_neg (by simpa using hg)]
      simp only [favorite, ih]
      cases hS : favorite f S with
      | none => simp [hg0]
      | some p =>
        by_cases hp : f p = 0
        · simp [hp, hg0]
        · have : ¬ f p ≤ f g := by omega
          simp [hp, this]

omit [DecidableEq A] [DecidableEq G] in
theorem value_filter_pos (v : A → G → Nat) (i : A) : ∀ l : List G,
    value v i (l.filter (fun g => 0 < v i g)) = value v i l
  | [] => rfl
  | g :: S => by
    have ih := value_filter_pos v i S
    by_cases hg : 0 < v i g
    · rw [List.filter_cons_of_pos (by simpa using hg)]
      simp [ih]
    · rw [List.filter_cons_of_neg (by simpa using hg)]
      simp only [value_cons, ih]
      omega

omit [DecidableEq A] in
/-- **Rule R1 needs only the relevant goods**: `r1Step` is `r1Rel` on the relevant remaining goods. -/
theorem r1Step_eq_rel (v : A → G → Nat) (goods : List G) (i : A) :
    K3.r1Step v goods i = r1Rel v i (relevant v i goods) := by
  unfold K3.r1Step r1Rel relevant
  rw [favorite_filter_pos]
  cases hf : favorite (v i) goods with
  | none => simp
  | some p =>
    by_cases h0 : v i p = 0
    · simp [h0]
    · simp only [Option.bind_some, h0, ↓reduceIte]
      have hp := (favorite_spec _ hf).1
      have hpf : p ∈ goods.filter (fun g => 0 < v i g) := List.mem_filter.mpr ⟨hp, by simp; omega⟩
      have e1 := value_erase v (i := i) hp
      have e2 := value_erase v (i := i) hpf
      have e3 := value_filter_pos v i goods
      have : value v i (goods.erase p) = value v i ((goods.filter (fun g => 0 < v i g)).erase p) := by omega
      rw [this]

end peel

/-! ## Peeling over `Fin n`, `Fin m` -/

section fin
variable {n m : Nat}

/-- Filtering a duplicate-free list by membership in one of its sublists gives the sublist. -/
theorem filter_mem_of_sublist {α : Type} [DecidableEq α] {L l : List α} (hL : L.Nodup) (h : l.Sublist L) :
    L.filter (fun x => decide (x ∈ l)) = l := by
  induction h with
  | slnil => rfl
  | cons a h ih =>
    have ha : a ∉ _ := (List.nodup_cons.mp hL).1
    rw [List.filter_cons_of_neg (by simpa using fun h' => ha (h.subset h')), ih (List.nodup_cons.mp hL).2]
  | cons_cons a h ih =>
    have ha := (List.nodup_cons.mp hL).1
    rw [List.filter_cons_of_pos (by simp)]
    congr 1
    refine (List.filter_congr fun x hx => ?_).trans (ih (List.nodup_cons.mp hL).2)
    have : x ≠ a := fun e => ha (e ▸ hx)
    simp [this]

/-- The relevant goods among the remaining goods, from the relevant goods among all goods. -/
theorem relevant_filter (v : Fin n → Fin m → Nat) (i : Fin n) {goods : List (Fin m)}
    (hsub : goods.Sublist (List.finRange m)) :
    (relevant v i (List.finRange m)).filter (fun g => decide (g ∈ goods)) = relevant v i goods := by
  unfold relevant
  rw [List.filter_filter]
  conv => rhs; rw [← filter_mem_of_sublist (List.nodup_finRange m) hsub]
  rw [List.filter_filter]
  exact List.filter_congr fun x _ => Bool.and_comm _ _

/-- Rule R1 for agent `i`: its relevant goods (an array read), those still present (one read each), the favourite
(one value read and one comparison each), and the value of the others. -/
def r1C (v : Fin n → Fin m → Nat) (rel : Fin n → List (Fin m)) (inG : Fin m → Bool) (i : Fin n) :
    Timed (Option (Option (Fin m))) := do
  let R ← rd rel i
  let R' ← filterC (fun g => rd inG g) R
  let fp ← K3.favoriteC (fun g => rd (v i) g) R'
  match fp with
  | none => pure (some none)
  | some p => do
    let rest ← eraseC p R'
    let s ← K3.valueC v i rest
    let vp ← rd (v i) p
    tick 1
    pure (if s ≤ vp then some (some p) else none)

theorem r1C_val (v : Fin n → Fin m → Nat) (rel : Fin n → List (Fin m)) (inG : Fin m → Bool) (i : Fin n) :
    (r1C v rel inG i).val = r1Rel v i ((rel i).filter inG) := by
  simp only [r1C, bind_val, rd_val, filterC_val, K3.favoriteC_val]
  unfold r1Rel
  cases favorite (v i) ((rel i).filter inG) with
  | none => rfl
  | some p => simp <;> rfl

/-- `EFX.K3.findR1` from the relevant goods: the first agent to which rule R1 applies. -/
def findR1F (v : Fin n → Fin m → Nat) (rel : Fin n → List (Fin m)) (inG : Fin m → Bool)
    (agents : List (Fin n)) :
    Timed (Option (Fin n × Option (Fin m))) :=
  findSomeC (fun i => do
    let s ← r1C v rel inG i
    pure (s.map (fun s => (i, s)))) agents

theorem findR1F_val (v : Fin n → Fin m → Nat) {rel : Fin n → List (Fin m)} {inG : Fin m → Bool}
    (agents : List (Fin n)) {goods : List (Fin m)} (hrel : ∀ i, rel i = relevant v i (List.finRange m))
    (hinG : ∀ g, inG g = decide (g ∈ goods)) (hsub : goods.Sublist (List.finRange m)) :
    (findR1F v rel inG agents).val = K3.findR1 v agents goods := by
  have hR : ∀ i, (rel i).filter inG = relevant v i goods := fun i => by
    rw [hrel i, ← relevant_filter v i hsub]
    exact List.filter_congr fun g _ => hinG g
  simp only [findR1F, findSomeC_val, bind_val, r1C_val, pure_val, K3.findR1, hR, r1Step_eq_rel]

/-! ### Costs -/

theorem favoriteC_rd_cost (f : Fin m → Nat) : ∀ S : List (Fin m),
    (K3.favoriteC (fun g => rd f g) S).cost ≤ 3 * S.length
  | [] => by simp [K3.favoriteC]
  | g :: S => by
    have ih := favoriteC_rd_cost f S
    simp only [K3.favoriteC, bind_cost, List.length_cons]
    split
    · simp only [bind_cost, tick_cost, pure_cost]; omega
    · simp only [bind_cost, rd_cost, tick_cost, pure_cost]; omega

theorem valueC_cost (v : Fin n → Fin m → Nat) (i : Fin n) (S : List (Fin m)) :
    (K3.valueC v i S).cost ≤ 2 * S.length := by
  have := sumMapC_cost (fun g => do tick 1; pure (v i g)) 1 S (fun _ _ => by simp)
  simp only [K3.valueC]
  omega

theorem r1C_cost (v : Fin n → Fin m → Nat) (rel : Fin n → List (Fin m)) (inG : Fin m → Bool) (i : Fin n) :
    (r1C v rel inG i).cost ≤ 3 + 8 * (rel i).length := by
  have hf := filterC_cost (fun g => rd inG g) 1 (rel i) (fun _ _ => by simp)
  have hl : ((filterC (fun g => rd inG g) (rel i)).val).length ≤ (rel i).length := by
    simp only [filterC_val, rd_val]; exact List.length_filter_le _ _
  have hfav := favoriteC_rd_cost (v i) (filterC (fun g => rd inG g) (rel i)).val
  simp only [r1C, bind_cost, rd_cost, rd_val]
  split
  · simp only [pure_cost]; omega
  · rename_i p _
    have he := eraseC_cost p (filterC (fun g => rd inG g) (rel i)).val
    have hel := List.length_erase_le (a := p) (l := (filterC (fun g => rd inG g) (rel i)).val)
    have hv := valueC_cost v i ((eraseC p (filterC (fun g => rd inG g) (rel i)).val).val)
    simp only [eraseC_val] at hv
    simp only [bind_cost, rd_cost, tick_cost, pure_cost, eraseC_val]
    omega

theorem findR1F_cost (v : Fin n → Fin m → Nat) {rel : Fin n → List (Fin m)} (inG : Fin m → Bool)
    (agents : List (Fin n)) (h3 : ∀ i, (rel i).length ≤ 3) :
    (findR1F v rel inG agents).cost ≤ 28 * agents.length := by
  have := findSomeC_cost (fun i => do
    let s ← r1C v rel inG i
    pure (s.map (fun s => (i, s)))) 27 agents (fun i _ => by
      have := r1C_cost v rel inG i
      have := h3 i
      simp only [bind_cost, pure_cost]
      omega)
  simp only [findR1F]
  omega

end fin

end DE
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE.setAllC_val
#print axioms EFX.DE.scatterC_val
#print axioms EFX.DE.ddC_val_marks
#print axioms EFX.DE.ddC_val
#print axioms EFX.DE.r1Step_eq_rel
#print axioms EFX.DE.findR1F_val
#print axioms EFX.DE.findR1F_cost
