import EFX.K3Cost

/-!
# The running time of algorithm K3ALG (`proofs/k3_algorithm.md` §6)

Cost bounds for the counted programs of `EFX.K3CostLB` and `EFX.K3Cost`, in terms of a number `N ≥ 1` that bounds
the lengths of the lists involved; at the top, `N = n + m + 1`.

- `algoC_cost`: **the running-time theorem**. `(algoC I hn).cost ≤ 2000 · (n + m + 1)⁴` for every instance with
  `n ≥ 1` agents and `m` goods (every instance, not only those with at most three relevant goods per agent).

The largest term is LB's upgrade loop: at most `n` rounds, each testing every agent, and each test computes `NA`
for one good by scanning the agents (`O(n)`) and the upgraded agents (`O(n)`), so `O(n⁴)` in all.
-/

set_option autoImplicit false

namespace EFX
namespace K3

open Timed LB

/-! ## Arithmetic -/

section arith
variable {N : Nat}

theorem pw_mono (hN : 1 ≤ N) {d e : Nat} (h : d ≤ e) : N ^ d ≤ N ^ e := Nat.pow_le_pow_right hN h

theorem pw_facts (hN : 1 ≤ N) : 1 ≤ N ∧ N ≤ N ^ 2 ∧ N ^ 2 ≤ N ^ 3 ∧ N ^ 3 ≤ N ^ 4 := by
  refine ⟨hN, ?_, pw_mono hN (by omega), pw_mono hN (by omega)⟩
  have := pw_mono hN (d := 1) (e := 2) (by omega)
  simpa using this

/-- A loop over at most `N` elements, each costing at most `K · N^d` plus one step. -/
theorem loop_le (hN : 1 ≤ N) {a B K d : Nat} (ha : a ≤ N) (hB : B ≤ K * N ^ d) :
    a * (B + 1) ≤ (K + 1) * N ^ (d + 1) := by
  have h1 : a * (B + 1) ≤ N * (K * N ^ d + 1) := Nat.mul_le_mul ha (by omega)
  have h2 : N ≤ N ^ (d + 1) := by
    have := pw_mono hN (d := 1) (e := d + 1) (by omega)
    simpa using this
  have h3 : N * (K * N ^ d + 1) = K * N ^ (d + 1) + N := by
    rw [Nat.pow_succ, Nat.mul_add, Nat.mul_one, Nat.mul_comm N (K * N ^ d), Nat.mul_assoc]
  rw [h3] at h1
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem loop1 (hN : 1 ≤ N) {a B K : Nat} (ha : a ≤ N) (hB : B ≤ K) : a * (B + 1) ≤ (K + 1) * N := by
  have := loop_le hN ha (K := K) (d := 0) (by simpa using hB)
  simpa using this

theorem loop2 (hN : 1 ≤ N) {a B K : Nat} (ha : a ≤ N) (hB : B ≤ K * N) : a * (B + 1) ≤ (K + 1) * N ^ 2 :=
  loop_le hN ha (d := 1) (by simpa using hB)

theorem loop3 (hN : 1 ≤ N) {a B K : Nat} (ha : a ≤ N) (hB : B ≤ K * N ^ 2) : a * (B + 1) ≤ (K + 1) * N ^ 3 :=
  loop_le hN ha hB

theorem loop4 (hN : 1 ≤ N) {a B K : Nat} (ha : a ≤ N) (hB : B ≤ K * N ^ 3) : a * (B + 1) ≤ (K + 1) * N ^ 4 :=
  loop_le hN ha hB

/-- Lift a bound of degree `d ≤ 4` to degree 4. -/
theorem up4 (hN : 1 ≤ N) {x K d : Nat} (hd : d ≤ 4) (h : x ≤ K * N ^ d) : x ≤ K * N ^ 4 :=
  Nat.le_trans h (Nat.mul_le_mul_left K (pw_mono hN hd))

theorem up4_len (hN : 1 ≤ N) {x : Nat} (h : x ≤ N) : x ≤ 1 * N ^ 4 :=
  up4 hN (d := 1) (by omega) (by simpa using h)

/-- Two bounds in the same power of `N` add up. -/
theorem sum_le {a b K L X : Nat} (ha : a ≤ K * X) (hb : b ≤ L * X) : a + b ≤ (K + L) * X := by
  rw [Nat.add_mul]; exact Nat.add_le_add ha hb

end arith

/-- Bound a sum `c₀ + (c₁ + …)` by `K · X`: bound each summand by a hypothesis `cᵢ ≤ Kᵢ · X`, add the bounds
(`sum_le`), and check `Σ Kᵢ ≤ K` by `decide`. (Faster than `omega` on these many-term sums.) -/
theorem le_of_sum {s X K K' : Nat} (h : s ≤ K' * X) (hk : K' ≤ K) : s ≤ K * X :=
  Nat.le_trans h (Nat.mul_le_mul_right X hk)

macro "cost_sum" : tactic =>
  `(tactic| (apply le_of_sum
             (repeat (first | with_reducible assumption | with_reducible apply sum_le))
             decide))

/-! ## Phase 1 -/

section generic
variable {A G : Type} [DecidableEq A] [DecidableEq G] {N : Nat}

omit [DecidableEq A] in
theorem rankC_cost (P : Profile A G) (i : A) (g : G) : (rankC P i g).cost = 6 := rfl

omit [DecidableEq A] in
theorem pickRankC_cost (P : Profile A G) (Y : A → Option G) (i : A) : (pickRankC P Y i).cost ≤ 7 := by
  unfold pickRankC; cases Y i <;> simp [rankC]

omit [DecidableEq A] in
theorem prefersC_cost (P : Profile A G) (Y : A → Option G) (i : A) (g : G) : (prefersC P Y i g).cost ≤ 14 := by
  have := pickRankC_cost P Y i
  simp only [prefersC, bind_cost, rankC_cost, tick_cost, pure_cost]
  omega

omit [DecidableEq A] in
theorem favC_cost (P : Profile A G) (pool : List G) (i : A) : (favC P pool i).cost ≤ 3 + 3 * pool.length := by
  have h1 := memC_cost (P.a i) pool
  have h2 := memC_cost (P.b i) pool
  have h3 := memC_cost (P.c i) pool
  unfold favC
  simp only [bind_cost, tick_cost]
  split
  · simp only [pure_cost]; omega
  · simp only [bind_cost]
    split
    · simp only [pure_cost]; omega
    · simp only [bind_cost, pure_cost]; omega

omit [DecidableEq A] in
theorem fullC_cost (P : Profile A G) (pool : List G) (i : A) : (fullC P pool i).cost ≤ 3 + 3 * pool.length := by
  have h1 := memC_cost (P.a i) pool
  have h2 := memC_cost (P.b i) pool
  have h3 := memC_cost (P.c i) pool
  simp only [fullC, bind_cost, tick_cost, pure_cost]
  omega

theorem removePickC_cost (pool : List G) (p : Option G) : (removePickC pool p).cost ≤ pool.length := by
  cases p with
  | none => simp [removePickC]
  | some g => exact eraseC_cost g pool

theorem length_removePick (pool : List G) (p : Option G) : (removePick pool p).length ≤ pool.length := by
  cases p with
  | none => simp [removePick]
  | some g => simp only [removePick]; exact List.length_erase_le

theorem phase1C_cost (P : Profile A G) (hN : 1 ≤ N) : ∀ (order : List A) (pool : List G) (k : A),
    pool.length ≤ N → (phase1C P order pool k).cost ≤ (order.length + 1) * (8 * N)
  | [], _, _, _ => by simp [phase1C]
  | i :: order, pool, k, hp => by
    have hf := favC_cost P pool i
    have hr := removePickC_cost pool (fav P pool i)
    unfold phase1C
    simp only [bind_cost, tick_cost]
    split
    · rw [List.length_cons, Nat.add_mul, Nat.add_mul]; omega
    · have ih := phase1C_cost P hN order (removePick pool (fav P pool i)) k
        (Nat.le_trans (length_removePick pool _) hp)
      simp only [bind_cost, favC_val, removePickC_val]
      rw [List.length_cons, Nat.add_mul (order.length + 1) 1]
      omega

theorem blkAuxC_cost (P : Profile A G) (hN : 1 ≤ N) : ∀ (order : List A) (pool : List G) (cnt : Nat) (k : A),
    pool.length ≤ N → (blkAuxC P order pool cnt k).cost ≤ (order.length + 1) * (15 * N)
  | [], _, _, _, _ => by simp [blkAuxC]
  | i :: order, pool, cnt, k, hp => by
    have hfu := fullC_cost P pool i
    have hf := favC_cost P pool i
    have hr := removePickC_cost pool (fav P pool i)
    unfold blkAuxC
    simp only [bind_cost, tick_cost]
    split
    · simp only [pure_cost]; rw [List.length_cons, Nat.add_mul, Nat.add_mul]; omega
    · have ih := blkAuxC_cost P hN order (removePick pool (fav P pool i))
        (if (fullC P pool i).val = true then cnt + 1 else cnt) k (Nat.le_trans (length_removePick pool _) hp)
      simp only [bind_cost, favC_val, removePickC_val]
      rw [List.length_cons, Nat.add_mul (order.length + 1) 1]
      omega

theorem r1OrderC_cost (P : Profile A G) (hN : 1 ≤ N) : ∀ (fuel : Nat) (rem : List A) (pool : List G),
    rem.length ≤ N → pool.length ≤ N → (r1OrderC P fuel rem pool).cost ≤ fuel * (15 * N ^ 2)
  | 0, _, _, _, _ => by simp [r1OrderC]
  | fuel + 1, rem, pool, hr, hp => by
    have hfind : (findC (fun j => do let b ← fullC P pool j; pure (!b)) rem).cost ≤ 7 * N ^ 2 := by
      have h1 := findC_cost (fun j => do let b ← fullC P pool j; pure (!b)) (6 * N) rem (fun j _ => by
        have := fullC_cost P pool j; simp only [bind_cost, pure_cost]; omega)
      have h2 := loop2 hN hr (K := 6) (B := 6 * N) (Nat.le_refl _)
      omega
    have hsq := pw_facts hN
    unfold r1OrderC
    simp only [bind_cost]
    split
    · rename_i i hi
      have he := eraseC_cost i rem
      have hf := favC_cost P pool i
      have hrp := removePickC_cost pool (fav P pool i)
      have ih := r1OrderC_cost P hN fuel (rem.erase i) (removePick pool (fav P pool i))
        (Nat.le_trans List.length_erase_le hr) (Nat.le_trans (length_removePick pool _) hp)
      simp only [bind_cost, eraseC_val, favC_val, removePickC_val, pure_cost]
      rw [Nat.add_mul]
      omega
    · cases rem with
      | nil => simp [findC]
      | cons i rest =>
        have hf := favC_cost P pool i
        have hrp := removePickC_cost pool (fav P pool i)
        have ih := r1OrderC_cost P hN fuel rest (removePick pool (fav P pool i))
          (by simp at hr; omega) (Nat.le_trans (length_removePick pool _) hp)
        simp only [bind_cost, favC_val, removePickC_val, pure_cost]
        rw [Nat.add_mul]
        omega


/-! ## Phase 2 -/

omit [DecidableEq A] [DecidableEq G] in
theorem mul_pw {N a K d : Nat} (ha : a ≤ N) : a * (K * N ^ d) ≤ K * N ^ (d + 1) := by
  have := Nat.mul_le_mul_right (K * N ^ d) ha
  rw [Nat.pow_succ]
  calc a * (K * N ^ d) ≤ N * (K * N ^ d) := this
    _ = K * (N ^ d * N) := by rw [Nat.mul_comm N, Nat.mul_assoc]

theorem naBC_cost (P : Profile A G) (hN : 1 ≤ N) {agents up : List A} (Y : A → Option G) (g : G)
    (ha : agents.length ≤ N) (hu : up.length ≤ N) : (naBC P agents up Y g).cost ≤ 16 * N ^ 2 := by
  have h1 := anyC_cost (fun i => do
    let u ← memC i up
    let p ← prefersC P Y i g
    pure (!u && p)) (15 * N) agents (fun i _ => by
      have := memC_cost i up
      have := prefersC_cost P Y i g
      simp only [bind_cost, pure_cost]
      omega)
  have h2 := loop2 hN ha (K := 15) (B := 15 * N) (Nat.le_refl _)
  unfold naBC
  omega

theorem frozenBC_cost (P : Profile A G) (hN : 1 ≤ N) {agents up : List A} (Y : A → Option G) (k : A)
    (ha : agents.length ≤ N) (hu : up.length ≤ N) : (frozenBC P agents up Y k).cost ≤ 17 * N ^ 2 := by
  have hf := pw_facts hN
  unfold frozenBC
  cases hy : Y k with
  | none => simp; omega
  | some y =>
    have := naBC_cost P hN Y y ha hu
    simp only [bind_cost, tick_cost]
    omega

theorem capC_cost (P : Profile A G) (hN : 1 ≤ N) {agents up : List A} (Y : A → Option G) (k : A)
    (ha : agents.length ≤ N) (hu : up.length ≤ N) : (capC P agents up Y k).cost ≤ 20 * N ^ 2 := by
  have hf := pw_facts hN
  have h1 := frozenBC_cost P hN Y k ha hu
  have h2 := memC_cost k up
  simp only [capC, bind_cost, tick_cost, pure_cost]
  omega

theorem canUpC_cost (P : Profile A G) (hN : 1 ≤ N) {agents up : List A} (Y : A → Option G) {J : List G}
    (k : A) (ha : agents.length ≤ N) (hu : up.length ≤ N) (hJ : J.length ≤ N) :
    (canUpC P agents up Y J k).cost ≤ 28 * N ^ 2 := by
  have hf := pw_facts hN
  have h1 := memC_cost k up
  have h2 := pickRankC_cost P Y k
  have h3 := memC_cost (P.c k) J
  have h4 := naBC_cost P hN Y (P.b k) ha hu
  simp only [canUpC, bind_cost, tick_cost, pure_cost]
  omega

theorem length_upgrades (P : Profile A G) (agents : List A) (Y : A → Option G) :
    ∀ (fuel : Nat) (up : List A) (J : List G),
      (upgrades P agents Y fuel up J).1.length ≤ up.length + fuel ∧ (upgrades P agents Y fuel up J).2.length ≤ J.length
  | 0, _, _ => by simp [upgrades]
  | fuel + 1, up, J => by
    unfold upgrades
    split
    · simp
    · rename_i k _
      have h1 := length_upgrades P agents Y fuel (k :: up) (J.erase (P.c k))
      have h2 := List.length_erase_le (a := P.c k) (l := J)
      simp only [List.length_cons] at h1
      omega

theorem upgradesC_cost (P : Profile A G) (hN : 1 ≤ N) {agents : List A} (Y : A → Option G)
    (ha : agents.length ≤ N) : ∀ (fuel : Nat) (up : List A) (J : List G),
      up.length + fuel ≤ N → J.length ≤ N → (upgradesC P agents Y fuel up J).cost ≤ fuel * (31 * N ^ 3)
  | 0, _, _, _, _ => by simp [upgradesC]
  | fuel + 1, up, J, hu, hJ => by
    have hf := pw_facts hN
    have h1 := findC_cost (canUpC P agents up Y J) (28 * N ^ 2) agents
      (fun k _ => canUpC_cost P hN Y k ha (by omega) hJ)
    have h2 := loop3 hN ha (K := 28) (Nat.le_refl (28 * N ^ 2))
    unfold upgradesC
    simp only [bind_cost]
    split
    · simp only [pure_cost]; rw [Nat.add_mul]; omega
    · rename_i k _
      have he := eraseC_cost (P.c k) J
      have ih := upgradesC_cost P hN Y ha fuel (k :: up) (J.erase (P.c k)) (by simp; omega)
        (Nat.le_trans List.length_erase_le hJ)
      simp only [bind_cost, tick_cost, eraseC_val]
      rw [Nat.add_mul]
      omega

omit [DecidableEq A] in
theorem pickerC_cost {agents : List A} (Y : A → Option G) (g : G) (ha : agents.length ≤ N) :
    (pickerC agents Y g).cost ≤ 3 * N := by
  have := findC_cost (fun k => do tick 2; pure (Y k == some g)) 2 agents (fun _ _ => by simp)
  have := Nat.mul_le_mul_right 3 ha
  unfold pickerC; omega

omit [DecidableEq A] in
theorem upOfC_cost (P : Profile A G) {up : List A} (g : G) (hu : up.length ≤ N) :
    (upOfC P up g).cost ≤ 3 * N := by
  have := findC_cost (fun k => do tick 2; pure (P.c k == g)) 2 up (fun _ _ => by simp)
  have := Nat.mul_le_mul_right 3 hu
  unfold upOfC; omega

omit [DecidableEq A] in
theorem junk0C_cost (hN : 1 ≤ N) {agents : List A} (Y : A → Option G) {goods : List G}
    (ha : agents.length ≤ N) (hg : goods.length ≤ N) : (junk0C agents Y goods).cost ≤ 4 * N ^ 2 := by
  have h1 := filterC_cost (fun g => do let p ← pickerC agents Y g; pure p.isNone) (3 * N) goods
    (fun g _ => by have := pickerC_cost Y g ha; simp only [bind_cost, pure_cost]; omega)
  have h2 := loop2 hN hg (K := 3) (Nat.le_refl (3 * N))
  unfold junk0C; omega

theorem lbUpC_cost (P : Profile A G) (hN : 1 ≤ N) {agents : List A} {goods : List G} (Y : A → Option G)
    (ha : agents.length ≤ N) (hg : goods.length ≤ N) : (lbUpC P agents goods Y).cost ≤ 36 * N ^ 4 := by
  have hf := pw_facts hN
  have h1 := junk0C_cost hN Y ha hg
  have h2 := lengthC_cost agents
  have h3 := upgradesC_cost P hN Y ha agents.length [] (junk0 agents Y goods) (by simpa using ha)
    (Nat.le_trans (List.length_filter_le _ _) hg)
  have h4 : agents.length * (31 * N ^ 3) ≤ 31 * N ^ 4 := mul_pw ha
  simp only [lbUpC, bind_cost, junk0C_val, lengthC_val, pure_cost]
  omega

omit [DecidableEq A] in
theorem junkListC_cost (P : Profile A G) (hN : 1 ≤ N) {agents up : List A} (Y : A → Option G) {goods : List G}
    (ha : agents.length ≤ N) (hu : up.length ≤ N) (hg : goods.length ≤ N) :
    (junkListC P agents up Y goods).cost ≤ 8 * N ^ 2 := by
  have h1 := filterC_cost (fun g => do
    let p ← pickerC agents Y g
    let u ← upOfC P up g
    tick 1
    pure (p.isNone && u.isNone)) (7 * N) goods (fun g _ => by
      have := pickerC_cost Y g ha
      have := upOfC_cost P g hu
      simp only [bind_cost, tick_cost, pure_cost]
      omega)
  have h2 := loop2 hN hg (K := 7) (Nat.le_refl (7 * N))
  unfold junkListC; omega

omit [DecidableEq A] [DecidableEq G] in
theorem sumTabC_cost (s : A → Nat) {agents : List A} (ha : agents.length ≤ N) : (sumTabC s agents).cost ≤ 2 * N := by
  have := sumMapC_cost (fun k => do tick 1; pure (s k)) 1 agents (fun _ _ => by simp)
  unfold sumTabC; omega

omit [DecidableEq G] in
theorem sumExceptC_cost (s : A → Nat) (o : Option A) {agents : List A} (ha : agents.length ≤ N) :
    (sumExceptC s o agents).cost ≤ 3 * N := by
  have := sumMapC_cost (fun k => do tick 2; pure (slotsExcept s o k)) 2 agents (fun _ _ => by simp)
  have := Nat.mul_le_mul_right 3 ha
  unfold sumExceptC; omega

omit [DecidableEq G] in
theorem lastOutC_cost (up : List A) (hu : up.length ≤ N) : ∀ order : List A,
    (lastOutC up order).cost ≤ order.length * (N + 1)
  | [] => by simp [lastOutC]
  | i :: order => by
    have ih := lastOutC_cost up hu order
    have := memC_cost i up
    have e : (order.length + 1) * (N + 1) = order.length * (N + 1) + (N + 1) := Nat.succ_mul _ _
    unfold lastOutC
    simp only [bind_cost, tick_cost, List.length_cons, e]
    split
    · simp only [pure_cost]; omega
    · simp only [bind_cost, pure_cost]; omega

/-! ## The owner test -/

theorem inBaseC_cost (P : Profile A G) {up : List A} (Y : A → Option G) (w : A) (g : G) (hu : up.length ≤ N) :
    (inBaseC P up Y w g).cost ≤ N + 4 := by
  have := memC_cost w up
  simp only [inBaseC, bind_cost, tick_cost, pure_cost]
  omega

theorem exposedLC_cost (P : Profile A G) (hN : 1 ≤ N) {agents up : List A} (Y : A → Option G) {J : List G}
    (w : A) (ha : agents.length ≤ N) (hu : up.length ≤ N) (hJ : J.length ≤ N) :
    (exposedLC P agents up Y J w).cost ≤ 20 * N ^ 2 := by
  have h1 := filterC_cost (exposedC P up Y J w) (19 * N) agents (fun x _ => by
    have := memC_cost x up
    have := memC_cost (P.b x) J
    have := memC_cost (P.c x) J
    have := inBaseC_cost P Y w (P.b x) hu
    have := inBaseC_cost P Y w (P.c x) hu
    simp only [exposedC, bind_cost, tick_cost, pure_cost]
    omega)
  have h2 := loop2 hN ha (K := 19) (Nat.le_refl (19 * N))
  unfold exposedLC; omega

omit [DecidableEq A] in
theorem pickOneC_cost (P : Profile A G) (hN : 1 ≤ N) {J : List G} (x : A) (hJ : J.length ≤ N) :
    (pickOneC P J x).cost ≤ 3 * N := by
  have := memC_cost (P.b x) J
  simp only [pickOneC, bind_cost, tick_cost, pure_cost]
  omega

theorem meetC_cost (P : Profile A G) (hN : 1 ≤ N) {J : List G} {E : List A} (hJ : J.length ≤ N)
    (hE : E.length ≤ N) : (meetC P J E).cost ≤ 17 * N ^ 3 := by
  have hin : ∀ x y : A, (do
      tick 3
      if x = y then pure none else do
        let r ← findC (fun g => do
          let mj ← memC g J
          tick 4
          pure (decide (mj = true ∧ (g = P.b y ∨ g = P.c y)))) [P.b x, P.c x]
        pure (r.map (fun g => (x, y, g))) : Timed (Option (A × A × G))).cost ≤ 15 * N := by
    intro x y
    have := findC_cost (fun g => do
          let mj ← memC g J
          tick 4
          pure (decide (mj = true ∧ (g = P.b y ∨ g = P.c y)))) (N + 4) [P.b x, P.c x]
      (fun g _ => by have := memC_cost g J; simp only [bind_cost, tick_cost, pure_cost]; omega)
    simp only [bind_cost, tick_cost]
    split
    · simp only [pure_cost]; omega
    · simp only [bind_cost, pure_cost, List.length_cons, List.length_nil] at this ⊢; omega
  have hinner : ∀ x : A, (findSomeC (fun y => (do
      tick 3
      if x = y then pure none else do
        let r ← findC (fun g => do
          let mj ← memC g J
          tick 4
          pure (decide (mj = true ∧ (g = P.b y ∨ g = P.c y)))) [P.b x, P.c x]
        pure (r.map (fun g => (x, y, g))) : Timed (Option (A × A × G)))) E).cost ≤ 16 * N ^ 2 := by
    intro x
    have := findSomeC_cost _ (15 * N) E (fun y _ => hin x y)
    have := loop2 hN hE (K := 15) (Nat.le_refl (15 * N))
    omega
  have := findSomeC_cost _ (16 * N ^ 2) E (fun x _ => hinner x)
  have := loop3 hN hE (K := 16) (Nat.le_refl (16 * N ^ 2))
  unfold meetC; omega

theorem hitSetC_cost (P : Profile A G) (hN : 1 ≤ N) {J : List G} {E : List A} (hJ : J.length ≤ N)
    (hE : E.length ≤ N) : (hitSetC P J E).cost ≤ 24 * N ^ 3 := by
  have hf := pw_facts hN
  have h1 := meetC_cost P hN hJ hE
  have hmap : ∀ E' : List A, E'.length ≤ N → (mapC (pickOneC P J) E').cost ≤ 4 * N ^ 2 := fun E' hE' => by
    have := mapC_cost (pickOneC P J) (3 * N) E' (fun x _ => pickOneC_cost P hN x hJ)
    have := loop2 hN hE' (K := 3) (Nat.le_refl (3 * N))
    omega
  unfold hitSetC
  simp only [bind_cost]
  split
  · rename_i x y g _
    have h2 := filterC_cost (fun z => do tick 2; pure (decide (z ≠ x ∧ z ≠ y))) 2 E (fun _ _ => by simp)
    have h3 := hmap (E.filter (fun z => (do tick 2; pure (decide (z ≠ x ∧ z ≠ y)) : Timed Bool).val))
      (Nat.le_trans (List.length_filter_le _ _) hE)
    have h4 := Nat.mul_le_mul_right 3 hE
    simp only [bind_cost, filterC_val, pure_cost]
    omega
  · have := hmap E hE
    omega

omit [DecidableEq A] [DecidableEq G] in
theorem kstarC_cost (blk : A → Nat) {E : List A} (r : A) (hE : E.length ≤ N) : (kstarC blk E r).cost ≤ 4 * N := by
  have := findC_cost (fun x => do tick 3; pure (blk x == blk r)) 3 E (fun _ _ => by simp)
  have := Nat.mul_le_mul_right 4 hE
  unfold kstarC; omega

/-! ## The rotation -/

omit [DecidableEq G] in
theorem afterC_cost : ∀ (order : List A) (x : A), (afterC order x).cost ≤ order.length
  | [], _ => by simp [afterC]
  | i :: order, x => by
    have := afterC_cost order x
    unfold afterC
    simp only [bind_cost, tick_cost, List.length_cons]
    split
    · simp only [pure_cost]; omega
    · omega

theorem isNextC_cost (P : Profile A G) (hN : 1 ≤ N) {agents up : List A} (Y : A → Option G) (cur j : A)
    (ha : agents.length ≤ N) (hu : up.length ≤ N) : (isNextC P agents up Y cur j).cost ≤ 33 * N ^ 2 := by
  have hf := pw_facts hN
  have h1 := frozenBC_cost P hN Y cur ha hu
  have h2 := memC_cost j up
  unfold isNextC
  cases hy : Y cur with
  | none => simp only [bind_cost, tick_cost, pure_cost]; omega
  | some y =>
    have := prefersC_cost P Y j y
    simp only [bind_cost, tick_cost, pure_cost]; omega

theorem chainFromC_cost (P : Profile A G) (hN : 1 ≤ N) {agents up : List A} (Y : A → Option G)
    (ha : agents.length ≤ N) (hu : up.length ≤ N) : ∀ (cur : A) (rest : List A),
      (chainFromC P agents up Y cur rest).cost ≤ rest.length * (33 * N ^ 2 + 1)
  | _, [] => by simp [chainFromC]
  | cur, j :: rest => by
    have h1 := isNextC_cost P hN Y cur j ha hu
    have e : (rest.length + 1) * (33 * N ^ 2 + 1) = rest.length * (33 * N ^ 2 + 1) + (33 * N ^ 2 + 1) :=
      Nat.succ_mul _ _
    unfold chainFromC
    simp only [bind_cost, tick_cost, List.length_cons, e]
    split
    · have := chainFromC_cost P hN Y ha hu j rest
      simp only [bind_cost, pure_cost]; omega
    · have := chainFromC_cost P hN Y ha hu cur rest
      omega

omit [DecidableEq G] in
theorem rotYC_cost (Y : A → Option G) : ∀ (cur : A) (l : List A) (x : A), (rotYC Y cur l x).cost ≤ 2 * l.length + 1
  | _, [], _ => by simp [rotYC]
  | cur, j :: l, x => by
    have := rotYC_cost Y j l x
    unfold rotYC
    simp only [bind_cost, tick_cost, List.length_cons]
    split
    · simp only [pure_cost]; omega
    · omega

omit [DecidableEq G] in
theorem rotPicksC_cost (P : Profile A G) (hN : 1 ≤ N) (Y : A → Option G) (k : A) {c : List A} (x : A)
    (hc : c.length ≤ N) : (rotPicksC P Y k c x).cost ≤ 5 * N := by
  have := rotYC_cost Y k c x
  unfold rotPicksC
  simp only [bind_cost, tick_cost]
  split
  · simp only [pure_cost]; omega
  · omega

/-! ## The completion -/

omit [DecidableEq A] in
theorem fillC_cost (s : A → Nat) (hs : ∀ k, s k ≤ 2) (g : G) : ∀ (ks : List A) (rest : List G),
    (fillC s g ks rest).cost ≤ 8 * ks.length
  | [], _ => by simp [fillC]
  | k :: ks, rest => by
    have ht := takeC_cost (s k) rest
    have hm := memC_cost g ((takeC (s k) rest).val)
    have hl : ((takeC (s k) rest).val).length ≤ s k := by rw [takeC_val]; exact List.length_take_le _ _
    have hd := dropC_cost (s k) rest
    have hsk := hs k
    unfold fillC
    simp only [bind_cost, tick_cost, List.length_cons]
    split
    · simp only [pure_cost]; omega
    · have := fillC_cost s hs g ks ((dropC (s k) rest).val)
      simp only [bind_cost]; omega

omit [DecidableEq A] in
theorem completeOneC_cost (P : Profile A G) (hN : 1 ≤ N) {agents up : List A} (Y : A → Option G)
    (o : Option A) (d : A) (s : A → Nat) (hs : ∀ k, s k ≤ 2) (L : List G) (g : G)
    (ha : agents.length ≤ N) (hu : up.length ≤ N) : (completeOneC P agents up Y o d s L g).cost ≤ 15 * N := by
  have h1 := pickerC_cost Y g ha
  have h2 := upOfC_cost P g hu
  have h3 := fillC_cost s hs g agents L
  unfold completeOneC
  simp only [bind_cost]
  split
  · simp only [pure_cost]; omega
  · simp only [bind_cost]
    split
    · simp only [pure_cost]; omega
    · simp only [bind_cost, tick_cost, pure_cost]; omega

omit [DecidableEq A] in
theorem placeListC_cost (hN : 1 ≤ N) {H J : List G} (hH : H.length ≤ N) (hJ : J.length ≤ N) :
    (placeListC H J).cost ≤ 3 * N ^ 2 := by
  have hf := pw_facts hN
  have h1 := filterC_cost (fun g => do let b ← memC g H; pure (!b)) N J
    (fun g _ => by have := memC_cost g H; simp only [bind_cost, pure_cost]; omega)
  have h2 := loop2 hN hJ (K := 1) (B := N) (by omega)
  have h3 := appendC_cost H (J.filter (fun g => (do let b ← memC g H; pure (!b) : Timed Bool).val))
  simp only [placeListC, bind_cost, filterC_val]
  omega

theorem cap_le_two (P : Profile A G) (agents up : List A) (Y : A → Option G) (k : A) : cap P agents up Y k ≤ 2 := by
  unfold cap; split
  · omega
  · split <;> omega

omit [DecidableEq G] in
theorem slotsExcept_le (s : A → Nat) (hs : ∀ k, s k ≤ 2) (o : Option A) (k : A) : slotsExcept s o k ≤ 2 := by
  unfold slotsExcept; split
  · omega
  · exact hs k


/-! ## Lengths -/

theorem length_r1Order (P : Profile A G) : ∀ (fuel : Nat) (rem : List A) (pool : List G),
    (r1Order P fuel rem pool).length ≤ fuel
  | 0, _, _ => by simp [r1Order]
  | fuel + 1, rem, pool => by
    unfold r1Order
    split
    · rename_i i _
      have := length_r1Order P fuel (rem.erase i) (removePick pool (fav P pool i)); simp; omega
    · split
      · simp
      · rename_i i rest _
        have := length_r1Order P fuel rest (removePick pool (fav P pool i)); simp; omega

omit [DecidableEq G] in
theorem length_after : ∀ (order : List A) (x : A), (after order x).length ≤ order.length
  | [], _ => by simp [after]
  | i :: order, x => by
    have := length_after order x
    unfold after
    split <;> simp <;> omega

/-! ## Rule R1 -/

omit [DecidableEq A] [DecidableEq G] in
theorem favoriteC_cost (f : G → Timed Nat) (hf : ∀ g, (f g).cost ≤ 1) : ∀ S : List G,
    (favoriteC f S).cost ≤ 3 * S.length
  | [] => by simp [favoriteC]
  | g :: S => by
    have ih := favoriteC_cost f hf S
    have h1 := hf g
    unfold favoriteC
    simp only [bind_cost, List.length_cons]
    split
    · simp only [bind_cost, tick_cost, pure_cost]; omega
    · rename_i h _
      have h2 := hf h
      simp only [bind_cost, tick_cost, pure_cost]; omega

omit [DecidableEq A] [DecidableEq G] in
theorem valueC_cost (v : A → G → Nat) (i : A) (S : List G) : (valueC v i S).cost ≤ 2 * S.length := by
  have := sumMapC_cost (fun g => do tick 1; pure (v i g)) 1 S (fun _ _ => by simp)
  unfold valueC; omega

omit [DecidableEq A] in
theorem r1StepC_cost (v : A → G → Nat) (hN : 1 ≤ N) {goods : List G} (i : A) (hg : goods.length ≤ N) :
    (r1StepC v goods i).cost ≤ 10 * N := by
  have h1 := favoriteC_cost (fun g => do tick 1; pure (v i g)) (fun _ => by simp) goods
  unfold r1StepC
  simp only [bind_cost]
  split
  · simp only [pure_cost]; omega
  · rename_i p _
    simp only [bind_cost, tick_cost]
    split
    · simp only [pure_cost]; omega
    · have h2 := eraseC_cost p goods
      have h3 := valueC_cost v i (goods.erase p)
      have h4 := List.length_erase_le (a := p) (l := goods)
      simp only [bind_cost, eraseC_val, tick_cost, pure_cost]; omega

omit [DecidableEq A] in
theorem findR1C_cost (v : A → G → Nat) (hN : 1 ≤ N) {agents : List A} {goods : List G}
    (ha : agents.length ≤ N) (hg : goods.length ≤ N) : (findR1C v agents goods).cost ≤ 11 * N ^ 2 := by
  have h1 := findSomeC_cost (fun i => do
    let s ← r1StepC v goods i
    pure (s.map (fun s => (i, s)))) (10 * N) agents
    (fun i _ => by have := r1StepC_cost v hN i hg; simp only [bind_cost, pure_cost]; omega)
  have h2 := loop2 hN ha (K := 10) (Nat.le_refl (10 * N))
  unfold findR1C; omega

end generic


/-! ## The algorithm -/

section fin
variable {n m N : Nat}

theorem profTabC_cost (v : Fin n → Fin m → Nat) (hN : 1 ≤ N) {goods : List (Fin m)} (g0 : Fin m)
    (hn : n ≤ N) (hg : goods.length ≤ N) : (profTabC v goods g0).cost ≤ 14 * N ^ 2 := by
  have h1 := mkTable_cost n (fun i => do
    let rel ← filterC (fun g => do tick 2; pure (decide (0 < v i g))) goods
    sort3C (v i) g0 rel) (13 * N) (fun i => by
      have := filterC_cost (fun g => do tick 2; pure (decide (0 < v i g))) 2 goods (fun _ _ => by simp)
      have := Nat.mul_le_mul_right 3 hg
      simp only [bind_cost, sort3C, tick_cost, pure_cost]
      omega)
  have h2 := loop2 hN hn (K := 13) (Nat.le_refl (13 * N))
  simp only [profTabC, bind_cost, pure_cost]
  omega

theorem completeTabC_cost (P : Profile (Fin n) (Fin m)) (hN : 1 ≤ N) {agents up : List (Fin n)}
    (Y : Fin n → Option (Fin m)) (capT : Fin n → Nat) (hc : ∀ k, capT k ≤ 2) {J : List (Fin m)}
    (o : Option (Fin n)) {H : List (Fin m)} (d : Fin n) (hm : m ≤ N) (ha : agents.length ≤ N)
    (hu : up.length ≤ N) (hJ : J.length ≤ N) (hH : H.length ≤ N) :
    (completeTabC P agents up Y capT J o H d).cost ≤ 19 * N ^ 2 := by
  have h1 := placeListC_cost hN hH hJ
  have h2 := mkTable_cost m (fun g => completeOneC P agents up Y o d (slotsExcept capT o)
    (placeListC H J).val g) (15 * N)
    (fun g => completeOneC_cost P hN Y o d _ (slotsExcept_le capT hc o) _ g ha hu)
  have h3 := loop2 hN hm (K := 15) (Nat.le_refl (15 * N))
  simp only [completeTabC, bind_cost]
  omega

-- The counted programs are opaque to the arithmetic below: `omega` compares its atoms up to definitional
-- unfolding, which is slow on these definitions.
attribute [local irreducible] phase1C blkAuxC lbUpC junkListC capC sumTabC lengthC lastOutC exposedLC hitSetC
  sumExceptC kstarC afterC chainFromC rotPicksC completeTabC in
theorem lbPlusC_cost (P : Profile (Fin n) (Fin m)) (hN : 1 ≤ N) {agents : List (Fin n)} {goods : List (Fin m)}
    {order : List (Fin n)} (d : Fin n) (hn : n ≤ N) (hm : m ≤ N) (ha : agents.length + 1 ≤ N)
    (hg : goods.length ≤ N) (ho : order.length ≤ N) : (lbPlusC P agents goods order d).cost ≤ 310 * N ^ 4 := by
  have ha' : agents.length ≤ N := by omega
  have ho2 : order.length + 1 ≤ 2 * N := by omega
  -- every bound below is stated in the form `cost ≤ K * N ^ 4`, so that `omega` sees one power of `N`
  have hY : (mkTable n (fun k => phase1C P order goods k)).cost ≤ 17 * N ^ 4 := by
    refine up4 hN (d := 3) (by omega)
      (Nat.le_trans (mkTable_cost n _ (16 * N ^ 2) (fun k => ?_)) (loop3 hN hn (Nat.le_refl _)))
    have h1 := phase1C_cost P hN order goods k hg
    have h2 : (order.length + 1) * (8 * N) ≤ 2 * N * (8 * N) := Nat.mul_le_mul_right _ ho2
    have e : 2 * N * (8 * N) = 16 * N ^ 2 := by
      rw [Nat.pow_two, Nat.mul_assoc, Nat.mul_left_comm N 8 N, ← Nat.mul_assoc]
    omega
  have hblk : (mkTable n (fun k => blkAuxC P order goods 0 k)).cost ≤ 31 * N ^ 4 := by
    refine up4 hN (d := 3) (by omega)
      (Nat.le_trans (mkTable_cost n _ (30 * N ^ 2) (fun k => ?_)) (loop3 hN hn (Nat.le_refl _)))
    have h1 := blkAuxC_cost P hN order goods 0 k hg
    have h2 : (order.length + 1) * (15 * N) ≤ 2 * N * (15 * N) := Nat.mul_le_mul_right _ ho2
    have e : 2 * N * (15 * N) = 30 * N ^ 2 := by
      rw [Nat.pow_two, Nat.mul_assoc, Nat.mul_left_comm N 15 N, ← Nat.mul_assoc]
    omega
  generalize hYd : (mkTable n (fun k => phase1C P order goods k)).val = Y
  have hup := lbUpC_cost P hN Y ha' hg
  have hupl : (lbUp P agents goods Y).length ≤ agents.length := by
    have := (length_upgrades P agents Y agents.length [] (junk0 agents Y goods)).1
    simpa [lbUp] using this
  generalize hupd : lbUp P agents goods Y = up at hupl
  have hu : up.length ≤ N := by omega
  have hu' : ∀ k : Fin n, (k :: up).length ≤ N := fun k => by simp; omega
  clear hupl
  have hJl : (junkList P agents up Y goods).length ≤ N := Nat.le_trans (List.length_filter_le _ _) hg
  have hJ := up4 hN (d := 2) (by omega) (junkListC_cost P hN Y ha' hu hg)
  have hcapT : (mkTable n (capC P agents up Y)).cost ≤ 21 * N ^ 4 := up4 hN (d := 3) (by omega)
    (Nat.le_trans (mkTable_cost n _ (20 * N ^ 2) (fun k => capC_cost P hN Y k ha' hu)) (loop3 hN hn (Nat.le_refl _)))
  have hcap2 : ∀ k, (mkTable n (capC P agents up Y)).val k ≤ 2 := fun k => by
    simp only [mkTable_val, capC_val]; exact cap_le_two P agents up Y k
  have hS : (sumTabC (mkTable n (capC P agents up Y)).val agents).cost ≤ 2 * N ^ 4 :=
    up4 hN (d := 1) (by omega) (by rw [Nat.pow_one]; exact sumTabC_cost _ ha')
  have hlJ : (lengthC (junkList P agents up Y goods)).cost ≤ 1 * N ^ 4 := by
    rw [lengthC_cost]; exact up4_len hN hJl
  have hct := fun (o : Option (Fin n)) (H : List (Fin m)) (hH : H.length ≤ N) =>
    up4 hN (d := 2) (by omega)
      (completeTabC_cost P hN (up := up) Y _ hcap2 (J := junkList P agents up Y goods) o d hm ha' hu hJl hH)
  have hlo : (lastOutC up order).cost ≤ 2 * N ^ 4 := by
    have h1 := lastOutC_cost up hu order
    have h2 : order.length * (N + 1) ≤ N * (2 * N) := Nat.mul_le_mul ho (by omega)
    have e : N * (2 * N) = 2 * N ^ 2 := by rw [Nat.pow_two, Nat.mul_left_comm]
    exact up4 hN (d := 2) (by omega) (by omega)
  unfold lbPlusC
  simp only [bind_cost, hYd, lbUpC_val, hupd, junkListC_val, tick_cost]
  clear hYd hupd
  have h1 : (1 : Nat) ≤ 1 * N ^ 4 := up4 hN (d := 0) (by omega) (by simp)
  split
  · rename_i hc; clear hc; have := hct none [] (by simp); cost_sum
  rename_i hc; clear hc
  simp only [bind_cost]
  split
  · rename_i hc; clear hc; have := hct none [] (by simp); cost_sum
  rename_i r hc; clear hc
  have hEl : (exposedL P agents up Y goods r).length ≤ N := Nat.le_trans (List.length_filter_le _ _) ha'
  have hE := up4 hN (d := 2) (by omega) (exposedLC_cost P hN Y (J := junkList P agents up Y goods) r ha' hu hJl)
  simp only [bind_cost, exposedLC_val]
  have hH := up4 hN (d := 3) (by omega) (hitSetC_cost P hN (J := junkList P agents up Y goods) hJl hEl)
  have hHl : (hitSet P (junkList P agents up Y goods) (exposedL P agents up Y goods r)).length ≤ N :=
    Nat.le_trans hitSet_length.1 hEl
  have hlH : (lengthC (hitSet P (junkList P agents up Y goods) (exposedL P agents up Y goods r))).cost ≤
      1 * N ^ 4 := by rw [lengthC_cost]; exact up4_len hN hHl
  have hSr : (sumExceptC (mkTable n (capC P agents up Y)).val (some r) agents).cost ≤ 3 * N ^ 4 :=
    up4 hN (d := 1) (by omega) (by rw [Nat.pow_one]; exact sumExceptC_cost _ _ ha')
  simp only [hitSetC_val, tick_cost]
  split
  · rename_i hc; clear hc; have := hct (some r) _ hHl; cost_sum
  rename_i hc; clear hc
  simp only [bind_cost]
  have hks : (kstarC (mkTable n (fun k => blkAuxC P order goods 0 k)).val (exposedL P agents up Y goods r) r).cost ≤
      4 * N ^ 4 := up4 hN (d := 1) (by omega) (by rw [Nat.pow_one]; exact kstarC_cost _ r hEl)
  split
  · rename_i hc; clear hc; have := hct (some r) _ hHl; cost_sum
  rename_i k hc; clear hc hct hHl hEl
  simp only [bind_cost]
  -- the rotation
  have haf : (afterC order k).cost ≤ 1 * N ^ 4 := up4_len hN (Nat.le_trans (afterC_cost order k) ho)
  have hafl := length_after order k
  have hch : (chainFromC P agents up Y k (after order k)).cost ≤ 34 * N ^ 4 := up4 hN (d := 3) (by omega)
    (Nat.le_trans (chainFromC_cost P hN Y ha' hu k (after order k))
      (loop3 hN (Nat.le_trans hafl ho) (K := 33) (B := 33 * N ^ 2) (Nat.le_refl _)))
  have hchl : (chainFrom P agents up Y k (after order k)).length ≤ N :=
    Nat.le_trans (chainFrom_sublist k (after order k)).length_le (Nat.le_trans hafl ho)
  simp only [afterC_val, chainFromC_val]
  generalize chainFrom P agents up Y k (after order k) = ch at hchl hch
  have hY2 : (mkTable n (fun x => rotPicksC P Y k ch x)).cost ≤ 6 * N ^ 4 := up4 hN (d := 2) (by omega)
    (Nat.le_trans (mkTable_cost n _ (5 * N) (fun x => rotPicksC_cost P hN Y k x hchl)) (loop2 hN hn (Nat.le_refl _)))
  generalize (mkTable n (fun x => rotPicksC P Y k ch x)).val = Y'
  have hJl' : (junkList P agents (k :: up) Y' goods).length ≤ N := Nat.le_trans (List.length_filter_le _ _) hg
  have hJ' := up4 hN (d := 2) (by omega) (junkListC_cost P hN Y' ha' (hu' k) hg)
  have hcapT2 : (mkTable n (capC P agents (k :: up) Y')).cost ≤ 21 * N ^ 4 := up4 hN (d := 3) (by omega)
    (Nat.le_trans (mkTable_cost n _ (20 * N ^ 2) (fun x => capC_cost P hN Y' x ha' (hu' k)))
      (loop3 hN hn (Nat.le_refl _)))
  have hcap22 : ∀ x, (mkTable n (capC P agents (k :: up) Y')).val x ≤ 2 := fun x => by
    simp only [mkTable_val, capC_val]; exact cap_le_two P agents (k :: up) Y' x
  have hS' : (sumTabC (mkTable n (capC P agents (k :: up) Y')).val agents).cost ≤ 2 * N ^ 4 :=
    up4 hN (d := 1) (by omega) (by rw [Nat.pow_one]; exact sumTabC_cost _ ha')
  have hlJ' : (lengthC (junkList P agents (k :: up) Y' goods)).cost ≤ 1 * N ^ 4 := by
    rw [lengthC_cost]; exact up4_len hN hJl'
  have hct' := fun (o : Option (Fin n)) (H : List (Fin m)) (hH : H.length ≤ N) =>
    up4 hN (d := 2) (by omega)
      (completeTabC_cost P hN (up := k :: up) Y' _ hcap22 (J := junkList P agents (k :: up) Y' goods) o d hm ha'
        (hu' k) hJl' hH)
  simp only [junkListC_val, tick_cost]
  split
  · rename_i hc; clear hc; have := hct' none [] (by simp); cost_sum
  rename_i hc; clear hc
  have hEl' : (exposedL P agents (k :: up) Y' goods k).length ≤ N := Nat.le_trans (List.length_filter_le _ _) ha'
  have hE' := up4 hN (d := 2) (by omega)
    (exposedLC_cost P hN Y' (J := junkList P agents (k :: up) Y' goods) k ha' (hu' k) hJl')
  have hH' := up4 hN (d := 3) (by omega) (hitSetC_cost P hN (J := junkList P agents (k :: up) Y' goods) hJl' hEl')
  have hHl' := Nat.le_trans (hitSet_length (P := P) (J := junkList P agents (k :: up) Y' goods)
    (E := exposedL P agents (k :: up) Y' goods k)).1 hEl'
  have := hct' (some k) _ hHl'
  simp only [bind_cost, exposedLC_val, hitSetC_val]
  cost_sum

theorem length_reduceC_peels (v : Fin n → Fin m → Nat) (d : Fin n) : ∀ (fuel : Nat) (agents : List (Fin n))
    (goods : List (Fin m)), (reduceC v d fuel agents goods).val.1.length ≤ fuel
  | 0, _, _ => by simp [reduceC]
  | fuel + 1, agents, goods => by
    unfold reduceC
    simp only [bind_val, lengthC_val]
    split
    · simp
    cases goods with
    | nil => simp
    | cons g0 gs =>
      simp only [bind_val]
      split
      · rename_i i _
        have := length_reduceC_peels v d fuel ((eraseC i agents).val) (g0 :: gs)
        simp only [bind_val]; omega
      · rename_i i p _
        have := length_reduceC_peels v d fuel ((eraseC i agents).val) ((eraseC p (g0 :: gs)).val)
        simp only [bind_val, pure_val, List.length_cons]; omega
      · simp

/-- The peeling loop: at most `15 N²` per peeled agent, and LB⁺ once. -/
theorem reduceC_cost (v : Fin n → Fin m → Nat) (d : Fin n) (hN : 1 ≤ N) (hn : n ≤ N) (hm : m ≤ N) :
    ∀ (fuel : Nat) (agents : List (Fin n)) (goods : List (Fin m)), agents.length + 1 ≤ N → goods.length ≤ N →
      (reduceC v d fuel agents goods).cost ≤ fuel * (15 * N ^ 2) + 340 * N ^ 4
  | 0, _, _, _, _ => by simp [reduceC]
  | fuel + 1, agents, goods, ha, hg => by
    have hf := pw_facts hN
    have ha' : agents.length ≤ N := by omega
    have hl := lengthC_cost agents
    have e : (fuel + 1) * (15 * N ^ 2) = fuel * (15 * N ^ 2) + 15 * N ^ 2 := Nat.succ_mul _ _
    rw [e]
    unfold reduceC
    simp only [bind_cost, lengthC_val, tick_cost]
    split
    · simp only [pure_cost]; omega
    cases goods with
    | nil => simp only [pure_cost]; omega
    | cons g0 gs =>
      have hR := findR1C_cost v hN (goods := g0 :: gs) ha' hg
      simp only [bind_cost]
      split
      · rename_i i _
        have h1 := eraseC_cost i agents
        have ih := reduceC_cost v d hN hn hm fuel ((eraseC i agents).val) (g0 :: gs)
          (by rw [eraseC_val]; have := List.length_erase_le (a := i) (l := agents); omega) hg
        simp only [bind_cost]; omega
      · rename_i i p _
        have h1 := eraseC_cost i agents
        have h2 := eraseC_cost p (g0 :: gs)
        have ih := reduceC_cost v d hN hn hm fuel ((eraseC i agents).val) ((eraseC p (g0 :: gs)).val)
          (by rw [eraseC_val]; have := List.length_erase_le (a := i) (l := agents); omega)
          (by rw [eraseC_val]; have := List.length_erase_le (a := p) (l := g0 :: gs); omega)
        simp only [bind_cost, pure_cost]; omega
      · have hP := profTabC_cost v hN (goods := g0 :: gs) g0 hn hg
        have hl' := lengthC_cost agents
        have hO := r1OrderC_cost (profTabC v (g0 :: gs) g0).val hN agents.length agents (g0 :: gs)
          ha' hg
        have hO' : agents.length * (15 * N ^ 2) ≤ 15 * N ^ 3 := mul_pw ha'
        have hL := lbPlusC_cost (profTabC v (g0 :: gs) g0).val hN (agents := agents) (goods := g0 :: gs)
          (order := (r1OrderC (profTabC v (g0 :: gs) g0).val agents.length agents (g0 :: gs)).val) d hn hm ha hg
          (by rw [r1OrderC_val]; exact Nat.le_trans (length_r1Order _ _ _ _) ha')
        simp only [bind_cost, lengthC_val, pure_cost]
        omega

end fin

/-- **The running-time theorem.** Algorithm K3ALG (`algo`) performs at most `400 · (n + m + 1)⁴` counted
operations on every instance with `n ≥ 1` agents and `m` goods (the cost model: `EFX.Timed`, `EFX.K3CostLB`,
`EFX.K3Cost`). The bound holds for every instance, whatever the number of relevant goods per agent. -/
theorem algoC_cost (I : Inst) (hn : 0 < I.n) : (algoC I hn).cost ≤ 400 * (I.n + I.m + 1) ^ 4 := by
  have hN : 1 ≤ I.n + I.m + 1 := by omega
  have hf := pw_facts hN
  have hR := reduceC_cost I.v ⟨0, hn⟩ hN (N := I.n + I.m + 1) (by omega) (by omega) I.n (List.finRange I.n)
    (List.finRange I.m) (by simp only [List.length_finRange]; omega) (by simp only [List.length_finRange]; omega)
  have hR' : I.n * (15 * (I.n + I.m + 1) ^ 2) ≤ 15 * (I.n + I.m + 1) ^ 3 := mul_pw (by omega)
  have hpl := length_reduceC_peels I.v ⟨0, hn⟩ I.n (List.finRange I.n) (List.finRange I.m)
  simp only [algoC, bind_cost, finRangeC, tick_cost, pure_cost, bind_val, pure_val]
  generalize reduceC I.v ⟨0, hn⟩ I.n (List.finRange I.n) (List.finRange I.m) = R at hR hpl ⊢
  have hT := mkTable_cost I.m (fun g => do
    let q ← findC (fun q => do tick 1; pure (q.2 == g)) R.val.1
    tick 1
    pure ((q.map Prod.fst).getD (R.val.2 g))) (3 * (I.n + I.m + 1)) (fun g => by
      have := findC_cost (fun q => do tick 1; pure (q.2 == g)) 1 R.val.1 (fun _ _ => by simp)
      simp only [bind_cost, tick_cost, pure_cost]
      omega)
  have hT' := loop2 hN (show I.m ≤ I.n + I.m + 1 by omega) (K := 3) (Nat.le_refl (3 * (I.n + I.m + 1)))
  have hnm : I.n + I.m ≤ I.n + I.m + 1 := by omega
  generalize I.n + I.m + 1 = N at *
  omega

/-- The running-time theorem in the form `c · (n + m)^d`: at most `6400 · (n + m)⁴` counted operations (from
`algoC_cost`, as `n + m + 1 ≤ 2 (n + m)` when `n ≥ 1`). -/
theorem algoC_cost' (I : Inst) (hn : 0 < I.n) : (algoC I hn).cost ≤ 6400 * (I.n + I.m) ^ 4 := by
  have h1 : (I.n + I.m + 1) ^ 4 ≤ (2 * (I.n + I.m)) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h2 : (2 * (I.n + I.m)) ^ 4 = 16 * (I.n + I.m) ^ 4 := by rw [Nat.mul_pow]
  have := algoC_cost I hn
  omega

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.K3.lbPlusC_cost
#print axioms EFX.K3.reduceC_cost
#print axioms EFX.K3.algoC_cost
#print axioms EFX.K3.algoC_cost'
