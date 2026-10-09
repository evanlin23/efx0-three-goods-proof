import EFX.K3DECostRun
import EFX.K3CostBound

/-!
# The running time of Draft and Exchange, part 4: `O(n(n + m))` operations

`paper/k3-simple/long.tex` §6, paragraph "Running time": "an iteration takes `O(n + m)` steps, and so does a
round of peeling once the relevant goods of each agent are known … So DE runs in `O(n(n + m))` steps, reading the
input included. This count is machine-checked in Lean". This file proves it for the counted program
`EFX.DE.deC` (`EFX.K3DECostRun`, whose value is `deSpec`: `EFX.DE.de_eq_spec`). The units are those of
`EFX.K3DECost` (list cells, comparisons, arithmetic, table and input reads, and array writes, one unit each; a new
array of `k` entries costs `k`).

**Results.**
- `deC_cost` (**the running-time theorem**): on every instance with `n ≥ 1` agents and `m` goods in which every
  agent positively values at most three goods, `(deC I hn).cost ≤ 750 (n + 1)(n + m + 1)`; more precisely
  (`deC_cost_poly`) at most `730 n² + 48 nm + 326 n + 29 m + 10`, **reading the input included** (the `O(nm)` term
  is the computation of each agent's relevant goods, one value read and one comparison per pair).
- `stepC_cost`: one iteration of the loop costs at most `175 n + 11 m + 7` when the picks are distinct and at most
  `n` agents hold pairs; `loopC_cost`: the loop's `4n + 1` rounds at most, `175 n + 11 m + 8` each (one unit for the
  exchange counter); `coreC_cost`: the core stage;
  `peelC_cost`: each round of peeling costs at most `30 n + m + 3`.

**Where the terms come from** (`a = |agents| ≤ n`, `u = |up| ≤ n`).
- The tables of a state (`tabsC_cost`, `6n + 8m + 64a + 7u`): new arrays over the agents and the goods, filled by
  one pass over `up` and over `agents` (an agent needs at most its three goods, so the first agent that needs each
  good is a scatter of at most three keys per agent).
- The free agents (`freeLoopC_cost`, `repsC_cost`, `sigLoopC_cost`): `O(1)` per free agent plus `O(1)` per agent of
  its list of candidates `xsS (Y o)`. The lists of distinct goods are disjoint (each agent determines one good,
  `gxS`), and the picks are distinct in a valid state (`EFX.LB.Valid.pick_inj`), so the candidates of all free agents
  together are at most `a` (`sum_key_le`): the paper's "one pass over the agents".
- The cycle (`cycleC_cost`): `σⁿ(s)`, the period (at most `n + 1`), the orbit and the predecessors, `O(n)`.
- The invariants that the bound uses (distinct picks, distinct pair holders, `up ⊆ agents`) hold along the loop:
  validity by the soundness of the steps (`EFX.DE.draft_valid`, `EFX.DE.step_next`), the distinct pair holders by
  `step_inv` (an exchange makes pair holders of agents outside `up` only). They need the rankings to be well formed,
  which holds when every agent has at most three relevant goods (`wf_of_findR1_none`, as in `deStage_sound`);
  hence the hypothesis of the running-time theorem. (Without it, `deC` still computes `deSpec`.)

**Arithmetic.** The costs of a program are sums of many terms, added by `bind_cost`; `omega` is slow on long
right-nested sums, so they are first re-associated (`← Nat.add_assoc`). The final bound expands the products by hand
(`expand1` … `expand4`).
-/

set_option autoImplicit false

namespace EFX
namespace DE

open Timed LB Profile

/-! ## Sums over lists -/

section sums
variable {α κ : Type}

theorem length_filter_or (p q : α → Bool) : ∀ l : List α, (∀ x ∈ l, ¬ (p x = true ∧ q x = true)) →
    (l.filter (fun x => p x || q x)).length = (l.filter p).length + (l.filter q).length
  | [], _ => rfl
  | x :: l, h => by
    have ih := length_filter_or p q l (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    simp only [List.filter_cons]
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

/-- **Each element is counted once**: if every element of `l` is related to at most one key, the elements related
to `k`, summed over distinct keys `k`, are at most all of `l`. -/
theorem sum_filter_rel (r : α → κ → Bool) (l : List α)
    (hr : ∀ x k k', r x k = true → r x k' = true → k = k') :
    ∀ L : List κ, L.Nodup → (L.map (fun k => (l.filter (fun x => r x k)).length)).sum ≤ l.length := by
  have hsplit : ∀ L : List κ, L.Nodup →
      (L.map (fun k => (l.filter (fun x => r x k)).length)).sum = (l.filter (fun x => L.any (r x))).length := by
    intro L hL
    induction L with
    | nil =>
      simp only [List.map_nil, List.sum_nil, List.any_nil]
      rw [List.filter_eq_nil_iff.mpr (fun _ _ => Bool.false_ne_true)]
      rfl
    | cons k L ih =>
      have hk : k ∉ L := (List.nodup_cons.mp hL).1
      rw [List.map_cons, List.sum_cons, ih (List.nodup_cons.mp hL).2, ← length_filter_or]
      · simp [List.any_cons]
      · intro x _ ⟨h1, h2⟩
        obtain ⟨k', hk', hrk'⟩ := List.any_eq_true.mp h2
        exact hk ((hr x k k' h1 hrk') ▸ hk')
  intro L hL
  rw [hsplit L hL]
  exact List.length_filter_le _ _

/-- A sum over the elements with a value of `f`, as a sum over the values (`filterMap`). -/
theorem sum_filterMap {β : Type} (f : β → Option κ) (w : κ → Nat) : ∀ F : List β,
    (F.map (fun o => ((f o).map w).getD 0)).sum = ((F.filterMap f).map w).sum
  | [] => rfl
  | o :: F => by
    rw [List.map_cons, List.sum_cons, sum_filterMap f w F, List.filterMap_cons]
    cases f o <;> simp

theorem nodup_filterMap {β : Type} (f : β → Option κ) (hf : ∀ a b k, f a = some k → f b = some k → a = b) :
    ∀ F : List β, F.Nodup → (F.filterMap f).Nodup
  | [], _ => by simp
  | o :: F, hF => by
    have ih := nodup_filterMap f hf F (List.nodup_cons.mp hF).2
    rw [List.filterMap_cons]
    cases ho : f o with
    | none => exact ih
    | some k =>
      refine List.nodup_cons.mpr ⟨fun hk => ?_, ih⟩
      obtain ⟨b, hb, hbk⟩ := List.mem_filterMap.mp hk
      have := hf b o k hbk ho
      subst this
      exact (List.nodup_cons.mp hF).1 hb

/-- **The free agents' lists are disjoint**: if `f` is injective (where defined), `F` has no repetitions and every
element of `l` is related to at most one key, the sum over `o ∈ F` of the number of elements related to `f o` is at
most `|l|`. -/
theorem sum_key_le {β : Type} (r : α → κ → Bool) (l : List α)
    (hr : ∀ x k k', r x k = true → r x k' = true → k = k')
    (f : β → Option κ) (F : List β) (hF : F.Nodup) (hf : ∀ a b k, f a = some k → f b = some k → a = b) :
    (F.map (fun o => ((f o).map (fun k => (l.filter (fun x => r x k)).length)).getD 0)).sum ≤ l.length := by
  rw [sum_filterMap]
  exact sum_filter_rel r l hr _ (nodup_filterMap f hf F hF)

theorem sum_map_le (f g : α → Nat) : ∀ l : List α, (∀ x ∈ l, f x ≤ g x) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | x :: l, h => by
    have := sum_map_le f g l (fun y hy => h y (by simp [hy]))
    have := h x (by simp)
    simp only [List.map_cons, List.sum_cons]
    omega

end sums


/-! ## Costs of the parts -/

section fin
variable {n m : Nat}

theorem holdKeysC_cost (Y : Fin n → Option (Fin m)) (k : Fin n) :
    (holdKeysC Y k).cost + 3 * (holdKeysC Y k).val.length ≤ 4 := by
  simp only [holdKeysC, bind_cost, bind_val, rd_cost, rd_val, pure_cost, pure_val]
  cases Y k <;> simp

theorem cKeysC_cost (P : Profile (Fin n) (Fin m)) (u : Fin n) :
    (cKeysC P u).cost + 3 * (cKeysC P u).val.length ≤ 4 := by
  simp [cKeysC]

theorem needKeysC_cost (P : Profile (Fin n) (Fin m)) (Y : Fin n → Option (Fin m)) (inUp : Fin n → Bool)
    (j : Fin n) :
    (needKeysC P Y inUp j).cost + 3 * (needKeysC P Y inUp j).val.length ≤ 58 := by
  unfold needKeysC
  simp only [bind_cost, bind_val, rd_cost, rd_val]
  by_cases hu : inUp j = true
  · simp [hu]
  · have hu' : inUp j = false := by simpa using hu
    simp only [hu', Bool.false_eq_true, ↓reduceIte]
    have hf := filterC_cost (K3.prefersC P Y j) 14 [P.a j, P.b j, P.c j] (fun g _ => K3.prefersC_cost P Y j g)
    have hl : ((filterC (K3.prefersC P Y j) [P.a j, P.b j, P.c j]).val).length ≤ 3 := by
      simp only [filterC_val]
      exact Nat.le_trans (List.length_filter_le _ _) (by simp)
    simp only [List.length_cons, List.length_nil] at hf
    simp only [bind_cost, bind_val, rd_cost, rd_val]
    omega

theorem freeEntryC_cost (inA inUp : Fin n → Bool) (Y : Fin n → Option (Fin m)) (out : Fin m → Option (Fin n))
    (k : Fin n) : (freeEntryC inA inUp Y out k).cost ≤ 4 := by
  unfold freeEntryC
  simp only [bind_cost, rd_cost, rd_val]
  cases Y k <;> simp

/-- **The tables of a state** cost `O(n + m)`. -/
theorem tabsC_cost (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (inA : Fin n → Bool) (inG : Fin m → Bool)
    (Y : Fin n → Option (Fin m)) (up : List (Fin n)) :
    (tabsC P agents inA inG Y up).cost ≤ 6 * n + 8 * m + 64 * agents.length + 7 * up.length := by
  unfold tabsC
  simp only [bind_cost, pure_cost]
  generalize (constT n false).val = U0
  generalize (constT m (none : Option (Fin n))).val = T0
  have h1 := constT_cost n false
  have h2 := setAllC_cost true up U0
  have h3 := constT_cost m (none : Option (Fin n))
  have h4 := scatterC_cost (holdKeysC Y) 4 agents T0 (fun k _ => holdKeysC_cost Y k)
  have h5 := scatterC_cost (cKeysC P) 4 up T0 (fun u _ => cKeysC_cost P u)
  have h6 := scatterC_cost (needKeysC P Y (setAllC true up U0).val) 58 agents T0
    (fun j _ => needKeysC_cost P Y _ j)
  have h7 := mkTable_cost m (junkEntryC inG (scatterC (holdKeysC Y) agents T0).val (scatterC (cKeysC P) up T0).val) 4
    (fun g => by simp [junkEntryC])
  have h8 := mkTable_cost n (freeEntryC inA (setAllC true up U0).val Y
    (scatterC (needKeysC P Y (setAllC true up U0).val) agents T0).val) 4 (fun k => freeEntryC_cost _ _ _ _ k)
  omega

theorem pairTestC_cost (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (Y : Fin n → Option (Fin m)) (x : Fin n) :
    (pairTestC tb P Y x).cost = 8 := rfl

theorem gxC_cost (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (Y : Fin n → Option (Fin m)) (x : Fin n) :
    (gxC tb P Y x).cost = 9 := rfl

theorem hOfC_cost (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (x : Fin n) : (hOfC tb P x).cost ≤ 3 := by
  unfold hOfC
  simp only [bind_cost, rd_cost, rd_val]
  cases tb.junk (P.b x) <;> simp

theorem forcedC_cost (tb : Tabs n m) (HS : Fin n → List (Fin m) × Nat) (lF : Nat) (o : Fin n) :
    (forcedC tb HS lF o).cost ≤ 4 := by
  unfold forcedC
  simp only [bind_cost, rd_cost, rd_val]
  cases tb.free o <;> simp

theorem hEqC_cost (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (q : Fin m) (x : Fin n) :
    (hEqC tb P q x).cost ≤ 4 := by
  have := hOfC_cost tb P x
  simp only [hEqC, bind_cost, tick_cost, pure_cost]
  omega

theorem exchEntryC_cost (free : Fin n → Bool) (P : Profile (Fin n) (Fin m)) (Y : Fin n → Option (Fin m))
    (onC : Fin n → Bool) (pred : Fin n → Fin n) (w : Fin n) : (exchEntryC free P Y onC pred w).cost ≤ 4 := by
  unfold exchEntryC
  simp only [bind_cost, rd_cost, rd_val]
  cases onC w
  · simp
  · simp only [Bool.cond_true, bind_cost, rd_cost, rd_val]
    cases free (pred w) <;> simp

theorem newPairC_cost (free : Fin n → Bool) (onC : Fin n → Bool) (pred : Fin n → Fin n) (w : Fin n) :
    (newPairC free onC pred w).cost ≤ 3 := by
  unfold newPairC
  simp only [bind_cost, rd_cost, rd_val]
  cases onC w <;> simp

theorem outNbC_cost (tb : Tabs n m) (Y : Fin n → Option (Fin m)) (j : Fin n) : (outNbC tb Y j).cost ≤ 2 := by
  unfold outNbC
  simp only [bind_cost, rd_cost, rd_val]
  cases Y j <;> simp

theorem sigExC_cost (tb : Tabs n m) (Y : Fin n → Option (Fin m)) (S : Fin n → Fin n) :
    (sigExC tb Y S).cost ≤ 4 * n := by
  have := mkTable_cost n (sigExEntryC tb Y S) 3 (fun j => by
    unfold sigExEntryC
    simp only [bind_cost, rd_cost, rd_val]
    have := outNbC_cost tb Y j
    cases tb.free j <;> simp <;> omega)
  simp only [sigExC]
  omega

theorem sigPairC_cost (tb : Tabs n m) (Y : Fin n → Option (Fin m)) (x : Fin n) :
    (sigPairC tb Y x).cost ≤ 4 * n := by
  have := mkTable_cost n (sigPairEntryC tb Y x) 3 (fun j => by
    unfold sigPairEntryC
    simp only [bind_cost, rd_cost, rd_val]
    have := outNbC_cost tb Y j
    cases tb.free j <;> simp <;> omega)
  simp only [sigPairC]
  omega

theorem idTabC_cost (k : Nat) : (idTabC k).cost ≤ k := by
  have := mkTable_cost k (fun j => (pure j : Timed (Fin k))) 0 (fun _ => by simp)
  simp only [idTabC]
  omega

/-! ### The cycle -/

theorem period_le (σ : Fin n → Fin n) (l : Nat) (p : Fin n) : period σ l p ≤ l + 1 := by
  unfold period
  cases h : (List.range l).find? (fun k => iter σ (k + 1) p == p) with
  | none => simp
  | some k =>
    have := List.mem_range.mp (List.mem_of_find?_eq_some h)
    simp only [Option.map_some, Option.getD_some]
    omega

/-- **The move along the cycle** costs `O(n)`. -/
theorem cycleC_cost (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (Y : Fin n → Option (Fin m))
    (up : List (Fin n)) (σ : Fin n → Fin n) (s : Fin n) (l : Nat) :
    (cycleC tb P agents Y up σ s l).cost ≤ 7 * n + 11 * l + 4 * agents.length + up.length + 7 := by
  unfold cycleC
  simp only [bind_cost, tick_cost, pure_cost]
  generalize (iterC σ l s).val = p
  have hper : (periodC σ l p).val ≤ l + 1 := by rw [periodC_val]; exact period_le σ l p
  generalize (periodC σ l p).val = per at hper
  generalize (constT n false).val = O0
  generalize (constT n p).val = Q0
  generalize (onLoopC σ per p O0).val = onC
  generalize (predLoopC σ (per - 1) p Q0).val = r
  generalize (wr r.1 p r.2).val = pred
  have h1 := iterC_cost σ l s
  have h2 := periodC_cost σ l p
  have h3 := constT_cost n false
  have h4 := onLoopC_cost σ per p O0
  have h5 := constT_cost n p
  have h6 := predLoopC_cost σ (per - 1) p Q0
  have h7 := mkTable_cost n (exchEntryC tb.free P Y onC pred) 4 (fun w => exchEntryC_cost _ _ _ _ _ w)
  have h8 := filterC_cost (newPairC tb.free onC pred) 3 agents (fun w _ => newPairC_cost _ _ _ w)
  have h9 := appendC_cost up (filterC (newPairC tb.free onC pred) agents).val
  simp only [wr_cost]
  omega

/-! ### The exposed agents and the loops over the free agents -/

/-- The length of `o`'s list of candidates (`0` if `o` holds nothing). -/
def lenL (Xs : Fin m → List (Fin n)) (Y : Fin n → Option (Fin m)) (o : Fin n) : Nat :=
  ((Y o).map (fun g => (Xs g).length)).getD 0

theorem xsC_cost (gx : Fin n → Timed (Option (Fin m))) (B : Nat) (hB : ∀ x, (gx x).cost ≤ B) :
    ∀ (l : List (Fin n)) (T : Fin m → List (Fin n)), (xsC gx l T).cost ≤ l.length * (B + 3)
  | [], T => by simp [xsC]
  | x :: l, T => by
    have ih := xsC_cost gx B hB l T
    have hx := hB x
    simp only [xsC, bind_cost, tick_cost, List.length_cons, Nat.succ_mul]
    split
    · simp only [pure_cost]; omega
    · simp only [bind_cost, rd_cost, wr_cost]; omega

theorem ELC_cost (Xs : Fin m → List (Fin n)) (Y : Fin n → Option (Fin m)) (o : Fin n) :
    (ELC Xs Y o).cost ≤ 2 + 2 * lenL Xs Y o ∧ (ELC Xs Y o).val.length ≤ lenL Xs Y o := by
  unfold ELC lenL
  simp only [bind_cost, bind_val, rd_cost, rd_val]
  cases Y o with
  | none => simp
  | some g =>
    simp only [Option.map_some, Option.getD_some]
    have h1 := filterC_cost (neC o) 1 (Xs g) (fun _ _ => by simp [neC])
    simp only [bind_cost, bind_val, rd_cost, rd_val, filterC_val]
    exact ⟨by omega, List.length_filter_le _ _⟩

theorem ddC_length {α : Type} [DecidableEq α] (l : List α) (M : α → Bool) :
    ((ddC l M).val.1).length ≤ l.length := by
  rw [ddC_val_marks]
  exact Nat.le_trans (List.length_filter_le _ _) (length_dd l)

/-- The loop over the free agents costs `5` per agent plus `11` per candidate. -/
theorem freeLoopC_cost (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (Y : Fin n → Option (Fin m))
    (Xs : Fin m → List (Fin n)) : ∀ (os : List (Fin n)) (M : Fin m → Bool) (EL : Fin n → List (Fin n))
    (HS : Fin n → List (Fin m) × Nat),
    (freeLoopC tb P Y Xs os M EL HS).cost ≤ 5 * os.length + 12 * (os.map (lenL Xs Y)).sum
  | [], _, _, _ => by simp [freeLoopC]
  | o :: os, M, EL, HS => by
    simp only [freeLoopC, bind_cost, tick_cost, List.length_cons, List.map_cons, List.sum_cons]
    obtain ⟨hE1, hE2⟩ := ELC_cost Xs Y o
    generalize (ELC Xs Y o).val = E at hE2
    have hm := mapC_cost (hOfC tb P) 3 E (fun x _ => hOfC_cost tb P x)
    have hml : ((mapC (hOfC tb P) E).val).length = E.length := by simp
    generalize (mapC (hOfC tb P) E).val = hs at hml
    have hd := ddC_cost hs M
    have hdl := ddC_length hs M
    generalize (ddC hs M).val = r at hdl
    have hs2 := setAllC_cost false r.1 r.2
    have hl := lengthC_cost r.1
    have ih := freeLoopC_cost tb P Y Xs os (setAllC false r.1 r.2).val
      (wr EL o E).val (wr HS o (r.1, (lengthC r.1).val)).val
    simp only [wr_cost, wr_val] at ih ⊢
    omega

/-- Greedy representatives cost `5` per agent plus `2` per good of its set. -/
theorem repsC_cost (HS : Fin n → List (Fin m) × Nat) : ∀ (os : List (Fin n)) (U : Fin m → Bool)
    (R : Fin n → Option (Fin m)),
    (repsC HS os U R).cost ≤ 5 * os.length + 2 * (os.map (fun o => (HS o).1.length)).sum
  | [], _, _ => by simp [repsC]
  | o :: os, U, R => by
    have hf := findC_cost (unusedC U) 1 (HS o).1 (fun _ _ => by simp [unusedC])
    simp only [repsC, bind_cost, tick_cost, rd_cost, rd_val, List.length_cons, List.map_cons, List.sum_cons]
    split
    · have ih := repsC_cost HS os U R
      omega
    · rename_i q _
      have ih := repsC_cost HS os (wr U q true).val (wr R o ((R o).or (some q))).val
      simp only [bind_cost, wr_cost, rd_cost, wr_val, rd_val] at ih ⊢
      omega

/-- `σ` on the free agents costs `4` per agent plus `5` per exposed agent. -/
theorem sigLoopC_cost (tb : Tabs n m) (P : Profile (Fin n) (Fin m)) (EL : Fin n → List (Fin n))
    (R : Fin n → Option (Fin m)) : ∀ (os : List (Fin n)) (S : Fin n → Fin n),
    (sigLoopC tb P EL R os S).cost ≤ 4 * os.length + 5 * (os.map (fun o => (EL o).length)).sum
  | [], _ => by simp [sigLoopC]
  | o :: os, S => by
    have h1 : (sigOneC tb P EL R o).cost ≤ 2 + 5 * (EL o).length := by
      unfold sigOneC
      simp only [bind_cost, rd_cost, rd_val]
      cases R o with
      | none => simp only [pure_cost]; omega
      | some q =>
        have := findC_cost (hEqC tb P q) 4 (EL o) (fun x _ => hEqC_cost tb P q x)
        simp only [bind_cost, rd_cost, rd_val, pure_cost]
        omega
    have ih := sigLoopC_cost tb P EL R os (wr S o (sigOneC tb P EL R o).val).val
    simp only [sigLoopC, bind_cost, tick_cost, wr_cost, List.length_cons, List.map_cons, List.sum_cons]
    omega

end fin


/-! ## One step costs `O(n + m)` -/

section fin
variable {n m : Nat}

/-- The candidates of a free agent bound its exposed agents and its set `H_o`. -/
theorem expL_length_le (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (goods : List (Fin m))
    (Y : Fin n → Option (Fin m)) (up : List (Fin n)) (o : Fin n) :
    (expL P agents up Y goods o).length ≤ lenL (xsS P agents up Y goods) Y o := by
  unfold expL lenL
  cases Y o with
  | none => simp
  | some g => exact List.length_filter_le _ _

/-- **One step costs `O(n + m)`** when the picks are distinct and `|agents|, |up| ≤ n`. -/
theorem stepC_cost (P : Profile (Fin n) (Fin m)) {agents : List (Fin n)} {inA : Fin n → Bool} {inG : Fin m → Bool}
    {goods : List (Fin m)} (d : Fin n) (Y : Fin n → Option (Fin m)) (up : List (Fin n))
    (hA : ∀ k, inA k = agents.contains k) (hG : ∀ g, inG g = decide (g ∈ goods)) (hnd : agents.Nodup)
    (hinj : ∀ k k' y, Y k = some y → Y k' = some y → k = k') (ha : agents.length ≤ n) (hu : up.length ≤ n) :
    (stepC P agents inA inG d agents.length Y up).cost ≤ 175 * n + 11 * m + 7 := by
  unfold stepC
  simp only [bind_cost]
  have htab := tabsC_cost P agents inA inG Y up
  have htv := tabsC_val P Y up hA hG
  generalize (tabsC P agents inA inG Y up).val = tb at htv
  have hpf := findC_cost (pairTestC tb P Y) 8 agents (fun x _ => Nat.le_of_eq (pairTestC_cost tb P Y x))
  split
  · rename_i x _
    have h1 := sigPairC_cost tb Y x
    have h2 := cycleC_cost tb P agents Y up (sigPairC tb Y x).val x agents.length
    simp only [bind_cost, pure_cost]
    omega
  · rename_i hx
    have hP : agents.find? (pairB P agents up Y goods) = none := by
      subst htv
      rw [findC_val] at hx
      exact hx
    have hnu := findC_cost (notUpC tb) 1 agents (fun _ _ => by simp [notUpC])
    simp only [bind_cost]
    split
    · simp only [pure_cost]; omega
    · rename_i s _
      simp only [bind_cost]
      have hFc := filterC_cost (rd tb.free) 1 agents (fun _ _ => by simp)
      have hFv : (filterC (rd tb.free) agents).val = agents.filter (freeB P agents up Y) := by
        subst htv; simp [specTabs]
      generalize (filterC (rd tb.free) agents).val = F at hFv
      have hFl : F.length ≤ agents.length := by rw [hFv]; exact List.length_filter_le _ _
      have hFnd : F.Nodup := by rw [hFv]; exact hnd.filter _
      have hlF := lengthC_cost F
      have hc1 := constT_cost m ([] : List (Fin n))
      have hxs := xsC_cost (gxC tb P Y) 9 (fun x => Nat.le_of_eq (gxC_cost tb P Y x)) agents (constT m []).val
      have hXv : (xsC (gxC tb P Y) agents (constT m []).val).val = xsS P agents up Y goods := by
        subst htv; rw [constT_val]; exact xsC_spec P agents goods Y up
      generalize (xsC (gxC tb P Y) agents (constT m []).val).val = Xs at hXv
      have hc2 := constT_cost m false
      have hc3 := constT_cost n ([] : List (Fin n))
      have hc4 := constT_cost n (([] : List (Fin m)), 0)
      have hfl := freeLoopC_cost tb P Y Xs F (constT m false).val (constT n []).val (constT n ([], 0)).val
      generalize (freeLoopC tb P Y Xs F (constT m false).val (constT n []).val (constT n ([], 0)).val).cost = cfl
        at hfl
      have hfrv : (freeLoopC tb P Y Xs F (constT m false).val (constT n []).val (constT n ([], 0)).val).val =
          (fun x => if freeB P agents up Y x then expL P agents up Y goods x else [],
           fun x => if freeB P agents up Y x then (Hset P agents up Y goods x, (Hset P agents up Y goods x).length)
             else ([], 0),
           fun _ => false) := by
        subst htv hXv hFv
        simp only [constT_val]
        exact freeLoopC_free P hP
      generalize (freeLoopC tb P Y Xs F (constT m false).val (constT n []).val (constT n ([], 0)).val).val = fr
        at hfrv
      -- the sums over the free agents
      have hW : (F.map (lenL Xs Y)).sum ≤ agents.length := by
        subst hXv
        show (F.map (fun o => ((Y o).map (fun k =>
          (agents.filter (fun x => gxS P agents up Y goods x == some k)).length)).getD 0)).sum ≤ agents.length
        refine sum_key_le (fun x k => gxS P agents up Y goods x == some k) agents (fun x k k' h1 h2 => ?_) Y F hFnd
          hinj
        simp only [beq_iff_eq] at h1 h2
        rw [h1] at h2
        exact Option.some.inj h2
      have hfree : ∀ o ∈ F, freeB P agents up Y o = true := by
        intro o ho; rw [hFv] at ho; exact (List.mem_filter.mp ho).2
      have hR : (F.map (fun o => (fr.2.1 o).1.length)).sum ≤ (F.map (lenL Xs Y)).sum := by
        apply sum_map_le
        intro o ho
        rw [hfrv]
        simp only [hfree o ho, ↓reduceIte]
        rw [Hset_eq hP (hfree o ho)]
        refine Nat.le_trans (length_dd _) ?_
        rw [List.length_map, hXv]
        exact expL_length_le P agents goods Y up o
      have hE : (F.map (fun o => (fr.1 o).length)).sum ≤ (F.map (lenL Xs Y)).sum := by
        apply sum_map_le
        intro o ho
        rw [hfrv]
        simp only [hfree o ho, ↓reduceIte]
        rw [hXv]
        exact expL_length_le P agents goods Y up o
      have hfo := findC_cost (forcedC tb fr.2.1 (lengthC F).val) 4 agents (fun o _ => forcedC_cost _ _ _ o)
      split
      · simp only [bind_cost, rd_cost, pure_cost, ← Nat.add_assoc, Nat.add_zero]; omega
      · simp only [bind_cost, pure_cost]
        have hc5 := constT_cost m false
        have hc6 := constT_cost n (none : Option (Fin m))
        generalize (constT m false).val = U0
        generalize (constT n (none : Option (Fin m))).val = R0
        have hr := repsC_cost fr.2.1 F U0 R0
        generalize (repsC fr.2.1 F U0 R0).val = R
        have hid := idTabC_cost n
        generalize (idTabC n).val = S0
        have hsl := sigLoopC_cost tb P fr.1 R F S0
        generalize (sigLoopC tb P fr.1 R F S0).val = S
        have hse := sigExC_cost tb Y S
        generalize (sigExC tb Y S).val = σ
        have hcy := cycleC_cost tb P agents Y up σ s agents.length
        simp only [← Nat.add_assoc, Nat.add_zero]
        omega

end fin


/-! ## The loop: at most `4n + 1` steps -/

section loop
variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- **The invariant of the loop**: a valid state whose pair holders are distinct (an exchange makes pair holders
of agents outside `up` only). -/
theorem step_inv {P : Profile A G} {agents : List A} {goods : List G} (hWF : WF P agents goods) (hag : agents.Nodup)
    {d : A} {Y : A → Option G} {up : List A} (hV : Valid P agents goods Y up) (hup : up.Nodup)
    {Y' : A → Option G} {up' : List A} (h : step P agents goods d Y up = .next Y' up') :
    Valid P agents goods Y' up' ∧ up'.Nodup := by
  refine ⟨(step_next hV hWF hag h).1, ?_⟩
  obtain ⟨onC, σ, π, hC, -, rfl⟩ := step_next_cycle hWF hag h
  unfold exchUp
  refine List.nodup_append.mpr ⟨hup, hag.filter _, fun x hx y hy hxy => ?_⟩
  subst hxy
  have := (List.mem_filter.mp hy).2
  simp only [Bool.and_eq_true] at this
  exact (hC.mem x this.1).2 hx

theorem loop_inv {P : Profile A G} {agents : List A} {goods : List G} (hWF : WF P agents goods) (hag : agents.Nodup)
    (d : A) : ∀ (fuel : Nat) (Y : A → Option G) (up : List A) (k : Nat), Valid P agents goods Y up → up.Nodup →
      Valid P agents goods (loop P agents goods d fuel Y up k).Y (loop P agents goods d fuel Y up k).up ∧
        (loop P agents goods d fuel Y up k).up.Nodup
  | 0, _, _, _, hV, hup => ⟨hV, hup⟩
  | fuel + 1, Y, up, k, hV, hup => by
    cases h : step P agents goods d Y up with
    | stop o H =>
      have e : loop P agents goods d (fuel + 1) Y up k = ⟨o, H, Y, up, k⟩ := by simp [loop, h]
      rw [e]
      exact ⟨hV, hup⟩
    | next Y' up' =>
      have e : loop P agents goods d (fuel + 1) Y up k = loop P agents goods d fuel Y' up' (k + 1) := by
        simp [loop, h]
      rw [e]
      obtain ⟨hV', hup'⟩ := step_inv hWF hag hV hup h
      exact loop_inv hWF hag d fuel Y' up' (k + 1) hV' hup'

end loop

section fin
variable {n m : Nat}

/-- **The loop costs `O(n + m)` per round.** -/
theorem loopC_cost (P : Profile (Fin n) (Fin m)) {agents : List (Fin n)} {inA : Fin n → Bool} {inG : Fin m → Bool}
    {goods : List (Fin m)} (d : Fin n) (hA : ∀ k, inA k = agents.contains k)
    (hG : ∀ g, inG g = decide (g ∈ goods)) (hWF : WF P agents goods) (hag : agents.Nodup)
    (ha : agents.length ≤ n) :
    ∀ (fuel : Nat) (Y : Fin n → Option (Fin m)) (up : List (Fin n)) (k : Nat), Valid P agents goods Y up →
      up.Nodup → (loopC P agents inA inG d agents.length fuel Y up k).cost ≤ fuel * (175 * n + 11 * m + 8)
  | 0, _, _, _, _, _ => by simp [loopC]
  | fuel + 1, Y, up, k, hV, hup => by
    have hu : up.length ≤ n :=
      Nat.le_trans (List.Nodup.length_le_of_subset hup (fun u hu => hV.up_mem u hu)) ha
    have hs := stepC_cost P d Y up hA hG hag hV.pick_inj ha hu
    have hv := stepC_val P d Y up hA hG
    simp only [loopC, bind_cost]
    split
    · simp only [pure_cost]; rw [Nat.succ_mul fuel (175 * n + 11 * m + 8)]; omega
    · rename_i Y' up' h
      rw [hv] at h
      obtain ⟨hV', hup'⟩ := step_inv hWF hag hV hup h
      have ih := loopC_cost P d hA hG hWF hag ha fuel Y' up' (k + 1) hV' hup'
      simp only [bind_cost, tick_cost]
      rw [Nat.succ_mul fuel (175 * n + 11 * m + 8)]
      omega

/-! ## The draft, the completion, the rankings -/

theorem draftC_cost (P : Profile (Fin n) (Fin m)) : ∀ (order : List (Fin n)) (avail : Fin m → Bool),
    (draftC P order avail).cost ≤ 9 * order.length + n
  | [], _ => by
    simp only [draftC, List.length_nil, Nat.mul_zero, Nat.zero_add]
    exact constT_cost n none
  | i :: order, avail => by
    have hr : ∀ f, (removeT avail f).cost ≤ 1 := fun f => by cases f <;> simp [removeT]
    have h1 := hr (favT P avail i).val
    have ih := draftC_cost P order (removeT avail (favT P avail i).val).val
    have hf : (favT P avail i).cost = 6 := rfl
    simp only [draftC, bind_cost, tick_cost, wr_cost, List.length_cons]
    omega

theorem fillC_cost (free : Fin n → Bool) (o : Fin n) : ∀ (ks : List (Fin n)) (rest : List (Fin m))
    (T : Fin m → Option (Fin n)), (fillC free o ks rest T).cost ≤ 5 * ks.length
  | [], _, _ => by simp [fillC]
  | _ :: _, [], _ => by simp [fillC]
  | k :: ks, h :: hs, T => by
    simp only [fillC, bind_cost, tick_cost, rd_cost, rd_val, List.length_cons]
    cases ((k != o) && free k)
    · have := fillC_cost free o ks (h :: hs) T
      simp only [Bool.cond_false]; omega
    · have := fillC_cost free o ks hs (fun x => if x = h then (T h).or (some k) else T x)
      simp only [Bool.cond_true, bind_cost, rd_cost, wr_cost, rd_val, wr_val]; omega

theorem compEntryC_cost (holder upc fl : Fin m → Option (Fin n)) (o : Fin n) (g : Fin m) :
    (compEntryC holder upc fl o g).cost ≤ 3 := by
  unfold compEntryC
  simp only [bind_cost, rd_cost, rd_val]
  cases holder g with
  | some k => simp
  | none =>
    simp only [bind_cost, rd_cost, rd_val]
    cases upc g <;> simp

/-- **The completion costs `O(n + m)`.** -/
theorem completeC_cost (P : Profile (Fin n) (Fin m)) (agents : List (Fin n)) (inA : Fin n → Bool)
    (inG : Fin m → Bool) (r : Result (Fin n) (Fin m)) :
    (completeC P agents inA inG r).cost ≤ 6 * n + 13 * m + 69 * agents.length + 7 * r.up.length := by
  unfold completeC
  simp only [bind_cost]
  have h1 := tabsC_cost P agents inA inG r.Y r.up
  generalize (tabsC P agents inA inG r.Y r.up).val = tb
  have h2 := constT_cost m (none : Option (Fin n))
  generalize (constT m (none : Option (Fin n))).val = T0
  have h3 := fillC_cost tb.free r.o agents r.H T0
  have h4 := mkTable_cost m (compEntryC tb.holder tb.upc (fillC tb.free r.o agents r.H T0).val r.o) 3
    (fun g => compEntryC_cost _ _ _ _ g)
  omega

theorem profC_cost (v : Fin n → Fin m → Nat) (rel : Fin n → List (Fin m)) (inG : Fin m → Bool) (g0 : Fin m)
    (h3 : ∀ i, (rel i).length ≤ 3) : (profC v rel inG g0).cost ≤ 18 * n := by
  have := mkTable_cost n (profEntryC v rel inG g0) 17 (fun i => by
    have hf := filterC_cost (rd inG) 1 (rel i) (fun _ _ => by simp)
    have := h3 i
    simp only [profEntryC, bind_cost, rd_cost, rd_val, K3.sort3C, tick_cost, pure_cost]
    omega)
  simp only [profC, bind_cost, pure_cost]
  omega

/-! ## The core stage -/

/-- When rule R1 applies to nobody and every agent has at most three relevant goods, the rankings are well formed
(as in `EFX.DE.deStage_sound`). -/
theorem wf_of_findR1_none (v : Fin n → Fin m → Nat) {agents : List (Fin n)} {goods : List (Fin m)} (g0 : Fin m)
    (hgd : goods.Nodup) (hne : goods ≠ []) (h3 : ∀ i ∈ agents, (relevant v i goods).length ≤ 3)
    (hf : K3.findR1 v agents goods = none) : WF (K3.profileOf v goods g0) agents goods := by
  have hnone := K3.findR1_none hf
  intro i hi
  have hb := not_R1 v hne (K3.r1Step_eq_none (hnone i hi))
  obtain ⟨h1, h2, h3', h4, h5, h6, -⟩ := K3.sort3_ranking v i g0 hgd (Nat.le_antisymm (h3 i hi) hb.1)
    (fun g hg => Nat.le_of_lt (hb.2 g hg))
  exact ⟨h1, h2, h3', h4, h5, h6⟩

/-- **The core stage costs `O(n(n + m))`**: at most `4n + 1` rounds of the loop. -/
theorem coreC_cost (v : Fin n → Fin m → Nat) {rel : Fin n → List (Fin m)} {inG : Fin m → Bool}
    {agents : List (Fin n)} {goods : List (Fin m)} (g0 : Fin m) (d : Fin n)
    (hrel : ∀ i, rel i = relevant v i (List.finRange m)) (hinG : ∀ g, inG g = decide (g ∈ goods))
    (hsub : goods.Sublist (List.finRange m)) (hgd : goods.Nodup) (hne : goods ≠ [])
    (hag : agents.Sublist (List.finRange n)) (h3 : ∀ i, (rel i).length ≤ 3) (hf : K3.findR1 v agents goods = none) :
    (coreC v rel inG agents g0 d).cost ≤ (4 * n + 1) * (175 * n + 11 * m + 8) + 114 * n + 15 * m + 2 := by
  have hagnd : agents.Nodup := hag.nodup (List.nodup_finRange n)
  have ha : agents.length ≤ n := by simpa using hag.length_le
  have hrel3 : ∀ i ∈ agents, (relevant v i goods).length ≤ 3 := fun i _ =>
    Nat.le_trans (relevant_sublist v hsub) (by rw [← hrel i]; exact h3 i)
  have hWF := wf_of_findR1_none v g0 hgd hne hrel3 hf
  unfold coreC
  simp only [bind_cost, tick_cost]
  have hP := profC_cost v rel inG g0 h3
  rw [profC_val v g0 hrel hinG hsub]
  generalize hPdef : K3.profileOf v goods g0 = P at hWF
  have hc1 := constT_cost n false
  have hA : ∀ k, (setAllC true agents (constT n false).val).val k = agents.contains k := by
    intro k; rw [constT_val, setAllC_val]; by_cases h : k ∈ agents <;> simp [h]
  have hs1 := setAllC_cost true agents (constT n false).val
  generalize (setAllC true agents (constT n false).val).val = inA at hA
  have hav := mkTable_cost m (rd inG) 1 (fun _ => by simp)
  have havv : ∀ g, (mkTable m (rd inG)).val g = decide (g ∈ goods) := by intro g; simp [hinG g]
  generalize (mkTable m (rd inG)).val = av at havv
  have hd := draftC_cost P agents av
  have hdv := draftC_val P agents goods av hgd havv
  generalize (draftC P agents av).val = Y0 at hdv
  have hl := lengthC_cost agents
  rw [lengthC_val]
  have hV0 : Valid P agents goods Y0 [] := by rw [hdv]; exact draft_valid hagnd hgd
  have hlo := loopC_cost P d hA hinG hWF hagnd ha (4 * agents.length + 1) Y0 [] 0 hV0 List.nodup_nil
  have hlv := loopC_val P d hA hinG (4 * agents.length + 1) Y0 [] 0
  obtain ⟨hVr, hupr⟩ := loop_inv hWF hagnd d (4 * agents.length + 1) Y0 [] 0 hV0 List.nodup_nil
  rw [← hlv] at hVr hupr
  have hur : (loopC P agents inA inG d agents.length (4 * agents.length + 1) Y0 [] 0).val.up.length ≤ n :=
    Nat.le_trans (List.Nodup.length_le_of_subset hupr (fun u hu => hVr.up_mem u hu)) ha
  have hco := completeC_cost P agents inA inG
    (loopC P agents inA inG d agents.length (4 * agents.length + 1) Y0 [] 0).val
  have hmul : (4 * agents.length + 1) * (175 * n + 11 * m + 8) ≤ (4 * n + 1) * (175 * n + 11 * m + 8) :=
    Nat.mul_le_mul_right _ (by omega)
  generalize (4 * n + 1) * (175 * n + 11 * m + 8) = K at hmul ⊢
  generalize (4 * agents.length + 1) * (175 * n + 11 * m + 8) = K' at hlo hmul
  simp only [← Nat.add_assoc]
  omega

/-! ## Peeling, and the whole algorithm -/

/-- **Peeling costs `O(n + m)` per round** (each agent's test reads at most three relevant goods), plus the core. -/
theorem peelC_cost (v : Fin n → Fin m → Nat) {rel : Fin n → List (Fin m)} (d : Fin n)
    (hrel : ∀ i, rel i = relevant v i (List.finRange m)) (h3 : ∀ i, (rel i).length ≤ 3) :
    ∀ (fuel : Nat) (agents : List (Fin n)) (goods : List (Fin m)) (inG : Fin m → Bool),
    (∀ g, inG g = decide (g ∈ goods)) → goods.Sublist (List.finRange m) → goods.Nodup →
    agents.Sublist (List.finRange n) →
    (peelC v rel d fuel agents goods inG).cost ≤
      fuel * (30 * n + m + 3) + m + ((4 * n + 1) * (175 * n + 11 * m + 8) + 114 * n + 15 * m + 2)
  | 0, _, _, _, _, _, _, _ => by
    simp only [peelC]; have := constT_cost m d; omega
  | fuel + 1, agents, goods, inG, hinG, hsub, hgd, hag => by
    have ha : agents.length ≤ n := by simpa using hag.length_le
    have hgl : goods.length ≤ m := by simpa using hsub.length_le
    unfold peelC
    simp only [bind_cost, tick_cost, lengthC_cost, lengthC_val]
    rw [Nat.succ_mul fuel (30 * n + m + 3)]
    split
    · have := constT_cost m (agents.headD d); omega
    · cases goods with
      | nil => simp only; have := constT_cost m d; omega
      | cons g0 gs =>
        simp only [bind_cost]
        have hfc := findR1F_cost v inG agents h3
        have hfv := findR1F_val v agents hrel hinG hsub
        split
        · rename_i i hf
          have he := eraseC_cost i agents
          have ih := peelC_cost v d hrel h3 fuel (agents.erase i) (g0 :: gs) inG hinG hsub hgd
            (List.erase_sublist.trans hag)
          simp only [bind_cost, eraseC_val]
          omega
        · rename_i i p hf
          have he := eraseC_cost i agents
          have he2 := eraseC_cost p (g0 :: gs)
          have hinG' : ∀ g, (wr inG p false).val g = decide (g ∈ (g0 :: gs).erase p) := by
            intro g
            simp only [wr_val, hinG g]
            by_cases e : g = p
            · subst e; simp [List.Nodup.mem_erase_iff hgd]
            · simp [e, List.Nodup.mem_erase_iff hgd]
          have ih := peelC_cost v d hrel h3 fuel (agents.erase i) ((g0 :: gs).erase p) (wr inG p false).val
            hinG' (List.erase_sublist.trans hsub) (hgd.erase p) (List.erase_sublist.trans hag)
          simp only [bind_cost, eraseC_val, wr_cost]
          omega
        · rename_i hf
          rw [hfv] at hf
          have hc := coreC_cost v g0 d hrel hinG hsub hgd (List.cons_ne_nil g0 gs) hag h3 hf
          omega

theorem expand1 (n m : Nat) : n * (m * 3 + 1) = 3 * (n * m) + n := by
  rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm (n * m) 3]

theorem expand2 (n m : Nat) : n * (30 * n + m + 3) = 30 * (n * n) + n * m + 3 * n := by
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm n 3]

theorem expand3 (n m : Nat) :
    (4 * n + 1) * (175 * n + 11 * m + 8) = 700 * (n * n) + 44 * (n * m) + 207 * n + 11 * m + 8 := by
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm n 175 n,
    ← Nat.mul_assoc 4 175, Nat.mul_assoc 4 n (11 * m), Nat.mul_left_comm n 11 m, ← Nat.mul_assoc 4 11,
    Nat.mul_assoc 4 n 8, Nat.mul_comm n 8, ← Nat.mul_assoc 4 8]
  omega

theorem expand4 (n m : Nat) :
    750 * (n + 1) * (n + m + 1) = 750 * (n * n) + 750 * (n * m) + 1500 * n + 750 * m + 750 := by
  have h : (n + 1) * (n + m + 1) = n * n + n * m + 2 * n + m + 1 := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega
  rw [Nat.mul_assoc, h]; omega

/-- **The running time of DE** (`paper/k3-simple/long.tex` §6, "Running time"): on every instance with `n ≥ 1`
agents and `m` goods in which every agent positively values at most three goods, the counted program `deC` (whose
value is `deSpec`, `de_eq_spec`) performs at most `730 n² + 48 nm + 326 n + 29 m + 10` operations, reading the
input included. -/
theorem deC_cost_poly (I : Inst) (hn : 0 < I.n) (h : ∀ i, numRelevant I i ≤ 3) :
    (deC I hn).cost ≤ 730 * (I.n * I.n) + 48 * (I.n * I.m) + 326 * I.n + 29 * I.m + 10 := by
  have hrel : ∀ i, (mkTable I.n (relEntryC I.v (List.finRange I.m))).val i = relevant I.v i (List.finRange I.m) := by
    intro i; simp [relEntryC, posC, relevant]
  have h3 : ∀ i, ((mkTable I.n (relEntryC I.v (List.finRange I.m))).val i).length ≤ 3 := by
    intro i; rw [hrel i, ← numRelevant_eq]; exact h i
  have hr := mkTable_cost I.n (relEntryC I.v (List.finRange I.m)) (I.m * 3) (fun i => by
    have := filterC_cost (posC I.v i) 2 (List.finRange I.m) (fun _ _ => by simp [posC])
    simp only [relEntryC, List.length_finRange] at this ⊢
    omega)
  have hp := peelC_cost I.v ⟨0, hn⟩ hrel h3 I.n (List.finRange I.n) (List.finRange I.m) (constT I.m true).val
    (fun g => by simp) (List.Sublist.refl _) (List.nodup_finRange _) (List.Sublist.refl _)
  have hc := constT_cost I.m true
  have hfn : (K3.finRangeC I.n).cost = I.n := rfl
  have hfm : (K3.finRangeC I.m).cost = I.m := rfl
  simp only [deC, bind_cost]
  have hv1 : (K3.finRangeC I.n).val = List.finRange I.n := rfl
  have hv2 : (K3.finRangeC I.m).val = List.finRange I.m := rfl
  rw [hv1, hv2]
  rw [expand1] at hr
  rw [expand2, expand3] at hp
  omega

/-- **The running time of DE**, in the form `O(n(n + m))`: at most `750 (n + 1)(n + m + 1)` counted operations, on
every instance in which every agent positively values at most three goods (reading the input included). -/
theorem deC_cost (I : Inst) (hn : 0 < I.n) (h : ∀ i, numRelevant I i ≤ 3) :
    (deC I hn).cost ≤ 750 * (I.n + 1) * (I.n + I.m + 1) := by
  have := deC_cost_poly I hn h
  rw [expand4]
  omega

end fin

end DE
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE.sum_key_le
#print axioms EFX.DE.tabsC_cost
#print axioms EFX.DE.cycleC_cost
#print axioms EFX.DE.freeLoopC_cost
#print axioms EFX.DE.stepC_cost
#print axioms EFX.DE.step_inv
#print axioms EFX.DE.loopC_cost
#print axioms EFX.DE.completeC_cost
#print axioms EFX.DE.coreC_cost
#print axioms EFX.DE.peelC_cost
#print axioms EFX.DE.deC_cost_poly
#print axioms EFX.DE.deC_cost
