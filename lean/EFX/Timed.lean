/-!
# A cost model: computations that count their elementary operations

`Timed α` is a value of type `α` together with a natural number, the number of elementary operations spent to
compute it. Programs are written in `Timed`'s monad; `tick k` spends `k` operations; `bind` adds the costs. So a
program's `cost` is the sum of the ticks along the path its evaluation takes, and its `val` is what it computes.
A program's `cost` therefore counts exactly what its ticks count; `proofs/k3_algorithm.md` §6 and the module doc
of `EFX.K3Cost` list what one unit stands for.

This file defines the monad and the list operations used by the algorithm (`EFX.K3Cost`), each with:
- a *value lemma*: its `val` is the corresponding function of Lean's core library (`List.map`, `List.filter`,
  `List.any`, `List.find?`, `List.findSome?`, membership, `List.erase`, `List.take`, `List.drop`, `++`, `length`,
  sums), with the element function's `val` in place of the element function;
- a *cost lemma*: one unit per list cell visited, plus the cost of the element function at each visited cell.

`mkTable n f` evaluates `f` once at each index of `Fin n` and stores the results in an array (`Array.ofFn`); the
table it returns reads that array. Its cost is the cost of the `n` evaluations plus `n`. Reading a table is an
array read, one unit, charged by the program that reads it.

-/

set_option autoImplicit false

namespace EFX

/-- A value together with the number of elementary operations spent to compute it. -/
structure Timed (α : Type) where
  val : α
  cost : Nat

namespace Timed

instance : Monad Timed where
  pure a := ⟨a, 0⟩
  bind x f := ⟨(f x.val).val, x.cost + (f x.val).cost⟩

variable {α β : Type}

@[simp] theorem pure_val (a : α) : (pure a : Timed α).val = a := rfl
@[simp] theorem pure_cost (a : α) : (pure a : Timed α).cost = 0 := rfl
@[simp] theorem bind_val (x : Timed α) (f : α → Timed β) : (x >>= f).val = (f x.val).val := rfl
@[simp] theorem bind_cost (x : Timed α) (f : α → Timed β) : (x >>= f).cost = x.cost + (f x.val).cost := rfl

end Timed

/-- Spend `k` elementary operations. -/
def tick (k : Nat) : Timed Unit := ⟨(), k⟩

@[simp] theorem tick_val (k : Nat) : (tick k).val = () := rfl
@[simp] theorem tick_cost (k : Nat) : (tick k).cost = k := rfl

namespace Timed

variable {α β : Type}

/-! ## List operations -/

/-- `List.map`: one unit per element, plus the element's cost. -/
def mapC (f : α → Timed β) : List α → Timed (List β)
  | [] => pure []
  | x :: xs => do
    tick 1
    let y ← f x
    let ys ← mapC f xs
    pure (y :: ys)

/-- `List.filter`. -/
def filterC (p : α → Timed Bool) : List α → Timed (List α)
  | [] => pure []
  | x :: xs => do
    tick 1
    let b ← p x
    let ys ← filterC p xs
    pure (if b then x :: ys else ys)

/-- `List.any`, stopping at the first element that passes. -/
def anyC (p : α → Timed Bool) : List α → Timed Bool
  | [] => pure false
  | x :: xs => do
    tick 1
    let b ← p x
    if b then pure true else anyC p xs

/-- `List.find?`, stopping at the first element that passes. -/
def findC (p : α → Timed Bool) : List α → Timed (Option α)
  | [] => pure none
  | x :: xs => do
    tick 1
    let b ← p x
    if b then pure (some x) else findC p xs

/-- `List.findSome?`, stopping at the first element with a result. -/
def findSomeC (f : α → Timed (Option β)) : List α → Timed (Option β)
  | [] => pure none
  | x :: xs => do
    tick 1
    let r ← f x
    match r with
    | some y => pure (some y)
    | none => findSomeC f xs

/-- The sum of `f` over a list: one unit per element (the addition), plus the element's cost. -/
def sumMapC (f : α → Timed Nat) : List α → Timed Nat
  | [] => pure 0
  | x :: xs => do
    tick 1
    let y ← f x
    let s ← sumMapC f xs
    pure (y + s)

/-- The length of a list. -/
def lengthC : List α → Timed Nat
  | [] => pure 0
  | _ :: xs => do
    tick 1
    let k ← lengthC xs
    pure (k + 1)

/-- `l ++ l'`: one unit per element of `l`. -/
def appendC : List α → List α → Timed (List α)
  | [], l' => pure l'
  | x :: xs, l' => do
    tick 1
    let ys ← appendC xs l'
    pure (x :: ys)

/-- `List.take k`. -/
def takeC : Nat → List α → Timed (List α)
  | 0, _ => pure []
  | _ + 1, [] => pure []
  | k + 1, x :: xs => do
    tick 1
    let ys ← takeC k xs
    pure (x :: ys)

/-- `List.drop k`. -/
def dropC : Nat → List α → Timed (List α)
  | 0, l => pure l
  | _ + 1, [] => pure []
  | k + 1, _ :: xs => do
    tick 1
    dropC k xs

section deq
variable [DecidableEq α]

/-- Membership: one unit per comparison. -/
def memC (a : α) : List α → Timed Bool
  | [] => pure false
  | x :: xs => do
    tick 1
    if a = x then pure true else memC a xs

/-- `List.erase`: one unit per comparison. -/
def eraseC (a : α) : List α → Timed (List α)
  | [] => pure []
  | x :: xs => do
    tick 1
    if x = a then pure xs else do
      let ys ← eraseC a xs
      pure (x :: ys)

end deq

/-! ## Value lemmas -/

@[simp] theorem mapC_val (f : α → Timed β) : ∀ l : List α, (mapC f l).val = l.map (fun x => (f x).val)
  | [] => rfl
  | x :: xs => by simp [mapC, mapC_val f xs]

@[simp] theorem filterC_val (p : α → Timed Bool) : ∀ l : List α,
    (filterC p l).val = l.filter (fun x => (p x).val)
  | [] => rfl
  | x :: xs => by
    simp only [filterC, bind_val, pure_val, filterC_val p xs, List.filter_cons]

@[simp] theorem anyC_val (p : α → Timed Bool) : ∀ l : List α, (anyC p l).val = l.any (fun x => (p x).val)
  | [] => rfl
  | x :: xs => by
    simp only [anyC, bind_val, List.any_cons]
    cases (p x).val <;> simp [anyC_val p xs]

@[simp] theorem findC_val (p : α → Timed Bool) : ∀ l : List α, (findC p l).val = l.find? (fun x => (p x).val)
  | [] => rfl
  | x :: xs => by
    simp only [findC, bind_val, List.find?_cons]
    cases (p x).val <;> simp [findC_val p xs]

@[simp] theorem findSomeC_val (f : α → Timed (Option β)) : ∀ l : List α,
    (findSomeC f l).val = l.findSome? (fun x => (f x).val)
  | [] => rfl
  | x :: xs => by
    simp only [findSomeC, bind_val, List.findSome?_cons]
    cases (f x).val <;> simp [findSomeC_val f xs]

@[simp] theorem sumMapC_val (f : α → Timed Nat) : ∀ l : List α,
    (sumMapC f l).val = (l.map (fun x => (f x).val)).sum
  | [] => rfl
  | x :: xs => by simp [sumMapC, sumMapC_val f xs]

@[simp] theorem lengthC_val : ∀ l : List α, (lengthC l).val = l.length
  | [] => rfl
  | _ :: xs => by simp [lengthC, lengthC_val xs]

@[simp] theorem appendC_val : ∀ l l' : List α, (appendC l l').val = l ++ l'
  | [], _ => rfl
  | x :: xs, l' => by simp [appendC, appendC_val xs l']

@[simp] theorem takeC_val : ∀ (k : Nat) (l : List α), (takeC k l).val = l.take k
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: xs => by simp [takeC, takeC_val k xs]

@[simp] theorem dropC_val : ∀ (k : Nat) (l : List α), (dropC k l).val = l.drop k
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, _ :: xs => by simp [dropC, dropC_val k xs]

section deq
variable [DecidableEq α]

@[simp] theorem memC_val (a : α) : ∀ l : List α, (memC a l).val = decide (a ∈ l)
  | [] => rfl
  | x :: xs => by
    simp only [memC, bind_val]
    by_cases h : a = x
    · simp [h]
    · simp [h, memC_val a xs]

@[simp] theorem eraseC_val (a : α) : ∀ l : List α, (eraseC a l).val = l.erase a
  | [] => rfl
  | x :: xs => by
    simp only [eraseC, bind_val]
    by_cases h : x = a
    · subst h; simp
    · have : (x == a) = false := by simp [h]
      simp [h, this, eraseC_val a xs]

end deq

/-! ## Cost lemmas -/

theorem mapC_cost (f : α → Timed β) (B : Nat) : ∀ l : List α, (∀ x ∈ l, (f x).cost ≤ B) →
    (mapC f l).cost ≤ l.length * (B + 1)
  | [], _ => by simp [mapC]
  | x :: xs, h => by
    have := mapC_cost f B xs (fun y hy => h y (by simp [hy]))
    have := h x (by simp)
    simp only [mapC, bind_cost, tick_cost, pure_cost, List.length_cons, Nat.succ_mul]
    omega

theorem filterC_cost (p : α → Timed Bool) (B : Nat) : ∀ l : List α, (∀ x ∈ l, (p x).cost ≤ B) →
    (filterC p l).cost ≤ l.length * (B + 1)
  | [], _ => by simp [filterC]
  | x :: xs, h => by
    have := filterC_cost p B xs (fun y hy => h y (by simp [hy]))
    have := h x (by simp)
    simp only [filterC, bind_cost, tick_cost, pure_cost, List.length_cons, Nat.succ_mul]
    omega

theorem anyC_cost (p : α → Timed Bool) (B : Nat) : ∀ l : List α, (∀ x ∈ l, (p x).cost ≤ B) →
    (anyC p l).cost ≤ l.length * (B + 1)
  | [], _ => by simp [anyC]
  | x :: xs, h => by
    have ih := anyC_cost p B xs (fun y hy => h y (by simp [hy]))
    have := h x (by simp)
    simp only [anyC, bind_cost, tick_cost, List.length_cons, Nat.succ_mul]
    split <;> (try simp only [pure_cost]) <;> omega

theorem findC_cost (p : α → Timed Bool) (B : Nat) : ∀ l : List α, (∀ x ∈ l, (p x).cost ≤ B) →
    (findC p l).cost ≤ l.length * (B + 1)
  | [], _ => by simp [findC]
  | x :: xs, h => by
    have ih := findC_cost p B xs (fun y hy => h y (by simp [hy]))
    have := h x (by simp)
    simp only [findC, bind_cost, tick_cost, List.length_cons, Nat.succ_mul]
    split <;> (try simp only [pure_cost]) <;> omega

theorem findSomeC_cost (f : α → Timed (Option β)) (B : Nat) : ∀ l : List α, (∀ x ∈ l, (f x).cost ≤ B) →
    (findSomeC f l).cost ≤ l.length * (B + 1)
  | [], _ => by simp [findSomeC]
  | x :: xs, h => by
    have ih := findSomeC_cost f B xs (fun y hy => h y (by simp [hy]))
    have := h x (by simp)
    simp only [findSomeC, bind_cost, tick_cost, List.length_cons, Nat.succ_mul]
    split <;> (try simp only [pure_cost]) <;> omega

theorem sumMapC_cost (f : α → Timed Nat) (B : Nat) : ∀ l : List α, (∀ x ∈ l, (f x).cost ≤ B) →
    (sumMapC f l).cost ≤ l.length * (B + 1)
  | [], _ => by simp [sumMapC]
  | x :: xs, h => by
    have := sumMapC_cost f B xs (fun y hy => h y (by simp [hy]))
    have := h x (by simp)
    simp only [sumMapC, bind_cost, tick_cost, pure_cost, List.length_cons, Nat.succ_mul]
    omega

theorem lengthC_cost : ∀ l : List α, (lengthC l).cost = l.length
  | [] => rfl
  | _ :: xs => by simp [lengthC, lengthC_cost xs]; omega

theorem appendC_cost : ∀ l l' : List α, (appendC l l').cost = l.length
  | [], _ => rfl
  | _ :: xs, l' => by simp [appendC, appendC_cost xs l']; omega

theorem takeC_cost : ∀ (k : Nat) (l : List α), (takeC k l).cost ≤ k
  | 0, _ => by simp [takeC]
  | _ + 1, [] => by simp [takeC]
  | k + 1, _ :: xs => by have := takeC_cost k xs; simp [takeC]; omega

theorem dropC_cost : ∀ (k : Nat) (l : List α), (dropC k l).cost ≤ k
  | 0, _ => by simp [dropC]
  | _ + 1, [] => by simp [dropC]
  | k + 1, _ :: xs => by have := dropC_cost k xs; simp [dropC]; omega

section deq
variable [DecidableEq α]

theorem memC_cost (a : α) : ∀ l : List α, (memC a l).cost ≤ l.length
  | [] => by simp [memC]
  | x :: xs => by
    have := memC_cost a xs
    simp only [memC, bind_cost, tick_cost, List.length_cons]
    split <;> (try simp only [pure_cost]) <;> omega

theorem eraseC_cost (a : α) : ∀ l : List α, (eraseC a l).cost ≤ l.length
  | [] => by simp [eraseC]
  | x :: xs => by
    have := eraseC_cost a xs
    simp only [eraseC, bind_cost, tick_cost, List.length_cons]
    split <;> (try simp only [pure_cost, bind_cost]) <;> omega

end deq

/-! ## Tables -/

/-- Evaluate `f` at every index of `Fin n` once and store the results in an array; the table reads the array.
Cost: the `n` evaluations plus one unit per entry. Irreducible, so that proofs about costs do not unfold the
array (its value and cost are given by `mkTable_val` and `mkTable_cost`). -/
@[irreducible] def mkTable (n : Nat) (f : Fin n → Timed β) : Timed (Fin n → β) :=
  let arr := Array.ofFn f
  ⟨fun i => (arr[i.val]'(by simp [arr])).val, (arr.toList.map Timed.cost).sum + n⟩

@[simp] theorem mkTable_val (n : Nat) (f : Fin n → Timed β) : (mkTable n f).val = fun i => (f i).val := by
  funext i
  simp [mkTable]

theorem sum_le_mul {l : List Nat} {B : Nat} (h : ∀ x ∈ l, x ≤ B) : l.sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have := ih (fun y hy => h y (by simp [hy]))
    have := h x (by simp)
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem mkTable_cost (n : Nat) (f : Fin n → Timed β) (B : Nat) (h : ∀ i, (f i).cost ≤ B) :
    (mkTable n f).cost ≤ n * (B + 1) := by
  simp only [mkTable, Array.toList_ofFn]
  have : (List.map Timed.cost (List.ofFn f)).sum ≤ (List.map Timed.cost (List.ofFn f)).length * B :=
    sum_le_mul (fun x hx => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
      exact h i)
  simp only [List.length_map, List.length_ofFn] at this
  rw [Nat.mul_succ]
  omega

end Timed
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.Timed.mapC_val
#print axioms EFX.Timed.filterC_val
#print axioms EFX.Timed.findSomeC_val
#print axioms EFX.Timed.mkTable_val
#print axioms EFX.Timed.mkTable_cost
