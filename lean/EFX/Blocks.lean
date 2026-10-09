import EFX.PreAlloc

/-!
# Phase 1 with R1 priority, its blocks, and LB's upgrades (`proofs/lb_last_step.md` §1, §3)

Phase 1 processes the agents in an order `order`; each takes its favourite remaining good (`EFX.LB.phase1`).
LB⁺ allows any order with *R1 priority* (`R1Prio`): an agent all three of whose goods remain (`full`) is
processed only when every unprocessed agent's three goods all remain. Such a step is an *insertion step*
and its agent a *leader*; the other steps are R1 steps. A *block* is an insertion step with the R1 steps
that follow it; `blkAux` numbers the blocks and `leadB` marks the leaders. Every run of Phase 1 in the
sense of §1 (any choice at every R1 step and every insertion step) is `phase1` for an order with
`R1Prio`, and conversely.

`Run` collects what Theorems A and B use of Phase 1, with `idx order` for the processing time:
- `b2` (B2, which includes (I1)): a good that agent `j` ranks above its pick was picked before `j`'s turn,
  in `j`'s block;
- `i3` (I3): an agent all of whose goods were still there at its turn is a leader;
- `lead_unique`: a block has one leader;
- `first`: some agent picked its top.

`phase1_run`: Phase 1 in any order with R1 priority satisfies `Run`.

LB's upgrades (`EFX.LB.upgrades`) run to a fixpoint (`upgrades_fix`, which gives (UT)), and LB's state after
them is a valid pre-allocation (`lbState_valid`, §3). The upgrade order does not matter: `UpReach` makes the
upgrade steps in any order, `UpFinal` is any end state (no agent can be upgraded any more), and every end state
is a valid pre-allocation with (UT) (`upFinal_valid`); LB's is one (`lbUp_final`).
-/

set_option autoImplicit false

namespace EFX
namespace LB

variable {A G : Type} [DecidableEq G]

open Profile

/-- The profile is well formed on `agents` and `goods`: each agent's three goods are distinct goods of
`goods`. -/
def WF (P : Profile A G) (agents : List A) (goods : List G) : Prop :=
  ∀ i ∈ agents, P.a i ∈ goods ∧ P.b i ∈ goods ∧ P.c i ∈ goods ∧
    P.a i ≠ P.b i ∧ P.a i ≠ P.c i ∧ P.b i ≠ P.c i

/-- All three goods of `i` are in `pool`. -/
def full (P : Profile A G) (pool : List G) (i : A) : Bool :=
  decide (P.a i ∈ pool ∧ P.b i ∈ pool ∧ P.c i ∈ pool)

theorem mem_of_rank_lt {P : Profile A G} {i : A} {g : G} (h : P.rank i g < 3) :
    g = P.a i ∨ g = P.b i ∨ g = P.c i := by
  unfold Profile.rank at h
  by_cases ha : g = P.a i <;> by_cases hb : g = P.b i <;> by_cases hc : g = P.c i <;> simp_all

theorem mem_of_full {P : Profile A G} {pool : List G} {i : A} (h : full P pool i = true) {g : G}
    (hg : P.rank i g < 3) : g ∈ pool := by
  simp only [full, decide_eq_true_eq] at h
  rcases mem_of_rank_lt hg with rfl | rfl | rfl <;> simp [h]

theorem rank_le_three (P : Profile A G) (i : A) (g : G) : P.rank i g ≤ 3 := by
  unfold Profile.rank; split
  · omega
  · split
    · omega
    · split <;> omega

theorem pickRank_le_three (P : Profile A G) (Y : A → Option G) (i : A) : P.pickRank Y i ≤ 3 := by
  unfold Profile.pickRank; split
  · exact Nat.le_refl 3
  · exact rank_le_three P i _

theorem rank_lt_three_of_prefers {P : Profile A G} {Y : A → Option G} {i : A} {g : G}
    (h : P.Prefers Y i g) : P.rank i g < 3 :=
  Nat.lt_of_lt_of_le h (pickRank_le_three P Y i)

variable [DecidableEq A]

/-- R1 priority: an agent all of whose goods remain is processed only if every unprocessed agent's goods
all remain (otherwise an R1 step is due). -/
def R1Prio (P : Profile A G) : List A → List G → Prop
  | [], _ => True
  | i :: order, pool => (full P pool i = true → ∀ j ∈ order, full P pool j = true) ∧
      R1Prio P order (removePick pool (fav P pool i))

instance decR1Prio (P : Profile A G) : (order : List A) → (pool : List G) → Decidable (R1Prio P order pool)
  | [], _ => isTrue trivial
  | i :: order, pool =>
    have := decR1Prio P order (removePick pool (fav P pool i))
    inferInstanceAs (Decidable ((full P pool i = true → ∀ j ∈ order, full P pool j = true) ∧ _))

/-- The block of each agent: the number of insertion steps up to and including its turn, plus `n`. -/
def blkAux (P : Profile A G) : List A → List G → Nat → A → Nat
  | [], _, _, _ => 0
  | i :: order, pool, n, k =>
    if k = i then (if full P pool i then n + 1 else n)
    else blkAux P order (removePick pool (fav P pool i)) (if full P pool i then n + 1 else n) k

/-- `k` is a leader: all its goods remain at its turn (it is processed in an insertion step). -/
def leadB (P : Profile A G) : List A → List G → A → Bool
  | [], _, _ => false
  | i :: order, pool, k => if k = i then full P pool i else leadB P order (removePick pool (fav P pool i)) k

/-- The position of `k` in `order` (its processing time). -/
def idx : List A → A → Nat
  | [], _ => 0
  | i :: order, k => if k = i then 0 else idx order k + 1

/-! ## Positions -/

theorem idx_lt : ∀ {order : List A} {k : A}, k ∈ order → idx order k < order.length
  | [], _, h => by simp at h
  | i :: order, k, h => by
    unfold idx
    by_cases hk : k = i
    · simp [hk]
    · simp only [hk, ↓reduceIte, List.length_cons]
      have := idx_lt ((List.mem_cons.mp h).resolve_left hk)
      omega

theorem idx_inj : ∀ {order : List A} {k k' : A}, k ∈ order → k' ∈ order → idx order k = idx order k' →
    k = k'
  | [], _, _, h, _, _ => by simp at h
  | i :: order, k, k', h, h', e => by
    unfold idx at e
    by_cases hk : k = i <;> by_cases hk' : k' = i
    · rw [hk, hk']
    · simp [hk, hk'] at e
    · simp [hk, hk'] at e
    · simp only [hk, hk', ↓reduceIte, Nat.add_right_cancel_iff] at e
      exact idx_inj ((List.mem_cons.mp h).resolve_left hk) ((List.mem_cons.mp h').resolve_left hk') e

theorem idx_append_of_not_mem {pre l : List A} {x : A} (hx : x ∉ pre) :
    idx (pre ++ l) x = pre.length + idx l x := by
  induction pre with
  | nil => simp
  | cons i pre ih =>
    have hxi : x ≠ i := fun e => hx (by simp [e])
    simp only [List.cons_append, idx, hxi, ↓reduceIte, List.length_cons]
    rw [ih (fun h => hx (by simp [h]))]
    omega

theorem idx_append_of_mem {pre l : List A} {x : A} (hx : x ∈ pre) : idx (pre ++ l) x < pre.length := by
  induction pre with
  | nil => simp at hx
  | cons i pre ih =>
    simp only [List.cons_append, idx, List.length_cons]
    by_cases hxi : x = i
    · simp [hxi]
    · simp only [hxi, ↓reduceIte]
      have := ih ((List.mem_cons.mp hx).resolve_left hxi)
      omega

/-- In `pre ++ x :: l` (duplicate-free), an agent processed after `x` lies in `l`. -/
theorem mem_of_idx_gt {pre l : List A} {x y : A} (hnd : (pre ++ x :: l).Nodup) (hy : y ∈ pre ++ x :: l)
    (hxy : idx (pre ++ x :: l) x < idx (pre ++ x :: l) y) : y ∈ l := by
  have hxpre : x ∉ pre := fun h => by
    have := (List.nodup_append.mp hnd).2.2 x h x (by simp)
    exact this rfl
  rw [idx_append_of_not_mem hxpre] at hxy
  simp only [idx, ↓reduceIte, Nat.add_zero] at hxy
  rcases List.mem_append.mp hy with hy | hy
  · have := idx_append_of_mem (l := x :: l) hy
    omega
  · rcases List.mem_cons.mp hy with rfl | hy
    · have hypre : y ∉ pre := hxpre
      rw [idx_append_of_not_mem hypre] at hxy
      simp [idx] at hxy
    · exact hy

/-- The agents processed after `x`. -/
def after : List A → A → List A
  | [], _ => []
  | i :: order, x => if x = i then order else after order x

theorem eq_after {x : A} : ∀ {order : List A}, x ∈ order → ∃ pre, order = pre ++ x :: after order x
  | [], h => by simp at h
  | i :: order, h => by
    by_cases hx : x = i
    · subst hx; exact ⟨[], by simp [after]⟩
    · obtain ⟨pre, hpre⟩ := eq_after ((List.mem_cons.mp h).resolve_left hx)
      refine ⟨i :: pre, ?_⟩
      simp only [after, hx, ↓reduceIte, List.cons_append]
      rw [← hpre]

/-! ## Phase 1 facts -/

section phase1
variable {P : Profile A G}

theorem phase1_cons (i : A) (order : List A) (pool : List G) (k : A) :
    phase1 P (i :: order) pool k =
      if k = i then fav P pool i else phase1 P order (removePick pool (fav P pool i)) k := rfl

theorem blkAux_cons (i : A) (order : List A) (pool : List G) (n : Nat) (k : A) :
    blkAux P (i :: order) pool n k =
      if k = i then (if full P pool i then n + 1 else n)
      else blkAux P order (removePick pool (fav P pool i)) (if full P pool i then n + 1 else n) k := rfl

theorem removePick_sub {pool : List G} {p : Option G} {g : G} (h : g ∈ removePick pool p) : g ∈ pool :=
  mem_removePick h

/-- An agent processed while one of its goods is already gone stays in the current block. -/
theorem blk_const : ∀ {order : List A} {pool : List G} {n : Nat} {j : A} {g : G},
    R1Prio P order pool → j ∈ order → P.rank j g < 3 → g ∉ pool → blkAux P order pool n j = n
  | [], _, _, _, _, _, hj, _, _ => by simp at hj
  | i :: order, pool, n, j, g, hR, hj, hr, hg => by
    have hnf : full P pool i = false := by
      cases hfi : full P pool i with
      | false => rfl
      | true =>
        exfalso
        have hjf : full P pool j = true := by
          rcases List.mem_cons.mp hj with rfl | hj'
          · exact hfi
          · exact hR.1 hfi j hj'
        exact hg (mem_of_full hjf hr)
    rw [blkAux_cons]
    simp only [hnf, Bool.false_eq_true, ↓reduceIte]
    by_cases hji : j = i
    · simp [hji]
    · simp only [hji, ↓reduceIte]
      exact blk_const hR.2 ((List.mem_cons.mp hj).resolve_left hji) hr
        (fun h => hg (mem_removePick h))

/-- (B2): a good that `j` ranks above its pick was picked before `j`'s turn, in `j`'s block. -/
theorem phase1_b2 : ∀ {order : List A} {pool : List G} {n : Nat}, order.Nodup → pool.Nodup →
    R1Prio P order pool → ∀ j ∈ order, ∀ g ∈ pool, P.Prefers (phase1 P order pool) j g →
      ∃ k, phase1 P order pool k = some g ∧ idx order k < idx order j ∧
        blkAux P order pool n k = blkAux P order pool n j
  | [], _, _, _, _, _, j, hj, _, _, _ => by simp at hj
  | i :: order, pool, n, hord, hpool, hR, j, hj, g, hg, hp => by
    have hi : i ∉ order := (List.nodup_cons.mp hord).1
    by_cases hji : j = i
    · -- `i` took its favourite: nothing in the pool ranks above it
      subst hji
      exfalso
      have e : P.pickRank (phase1 P (j :: order) pool) j = favRank P pool j := by
        unfold Profile.pickRank favRank; rw [phase1_cons]; simp only [↓reduceIte]
        cases fav P pool j <;> rfl
      unfold Profile.Prefers at hp
      rw [e] at hp
      exact fav_best P pool j g hg hp
    have hj' : j ∈ order := (List.mem_cons.mp hj).resolve_left hji
    have hp' : P.Prefers (phase1 P order (removePick pool (fav P pool i))) j g := by
      unfold Profile.Prefers Profile.pickRank at hp ⊢
      rw [phase1_cons] at hp
      simpa [hji] using hp
    have hrg : P.rank j g < 3 := rank_lt_three_of_prefers hp'
    have hn' := phase1_spec P order (removePick pool (fav P pool i)) (List.nodup_cons.mp hord).2
      (nodup_removePick hpool _)
    by_cases hgf : fav P pool i = some g
    · refine ⟨i, by rw [phase1_cons]; simp [hgf], by simp [idx, hji], ?_⟩
      rw [blkAux_cons, blkAux_cons]
      simp only [hji, ↓reduceIte]
      refine (blk_const hR.2 hj' hrg ?_).symm
      rw [hgf]
      exact fun h => ((List.Nodup.mem_erase_iff hpool).mp h).1 rfl
    · have hg' : g ∈ removePick pool (fav P pool i) := by
        cases hf : fav P pool i with
        | none => exact hg
        | some y =>
          have hyg : g ≠ y := fun e => hgf (by rw [hf, e])
          exact (List.Nodup.mem_erase_iff hpool).mpr ⟨hyg, hg⟩
      obtain ⟨k, hk, hidx, hblk⟩ := phase1_b2 (n := if full P pool i then n + 1 else n)
        (List.nodup_cons.mp hord).2 (nodup_removePick hpool _) hR.2 j hj' g hg' hp'
      have hki : k ≠ i := fun e => hi (e ▸ (hn'.1 k g hk).1)
      refine ⟨k, by rw [phase1_cons]; simp [hki, hk], ?_, ?_⟩
      · simp only [idx, hki, hji, ↓reduceIte]; omega
      · rw [blkAux_cons, blkAux_cons]; simp only [hki, hji, ↓reduceIte]; exact hblk

omit [DecidableEq A] in
theorem rank_a_lt (P : Profile A G) (x : A) : P.rank x (P.a x) < 3 := by simp [Profile.rank]

omit [DecidableEq A] in
theorem rank_b_lt (P : Profile A G) (x : A) : P.rank x (P.b x) < 3 := by
  unfold Profile.rank; split <;> simp

omit [DecidableEq A] in
theorem rank_c_lt (P : Profile A G) (x : A) : P.rank x (P.c x) < 3 := by
  unfold Profile.rank; split
  · omega
  · split <;> simp

theorem leadB_cons (i : A) (order : List A) (pool : List G) (k : A) :
    leadB P (i :: order) pool k =
      if k = i then full P pool i else leadB P order (removePick pool (fav P pool i)) k := rfl

/-- (I3): an agent all of whose goods remain until its turn is a leader. -/
theorem phase1_i3 : ∀ {order : List A} {pool : List G} {x : A}, order.Nodup → pool.Nodup → x ∈ order →
    P.a x ∈ pool → P.b x ∈ pool → P.c x ∈ pool →
    (∀ g, P.rank x g < 3 → ∀ k, phase1 P order pool k = some g → idx order x ≤ idx order k) →
    leadB P order pool x = true
  | [], _, _, _, _, hx, _, _, _, _ => by simp at hx
  | i :: order, pool, x, hord, hpool, hx, ha, hb, hc, ht => by
    rw [leadB_cons]
    by_cases hxi : x = i
    · subst hxi; simp [full, ha, hb, hc]
    · simp only [hxi, ↓reduceIte]
      have hi : i ∉ order := (List.nodup_cons.mp hord).1
      -- `i`'s pick is none of `x`'s goods
      have hfi : ∀ g, fav P pool i = some g → P.rank x g < 3 → False := by
        intro g hf hr
        have := ht g hr i (by rw [phase1_cons]; simp [hf])
        simp [idx, hxi] at this
      have hmem : ∀ g, P.rank x g < 3 → g ∈ pool → g ∈ removePick pool (fav P pool i) := by
        intro g hr hg
        cases hf : fav P pool i with
        | none => exact hg
        | some y =>
          have hgy : g ≠ y := fun e => hfi y hf (e ▸ hr)
          exact (List.Nodup.mem_erase_iff hpool).mpr ⟨hgy, hg⟩
      have hspec := phase1_spec P order (removePick pool (fav P pool i)) (List.nodup_cons.mp hord).2
        (nodup_removePick hpool _)
      refine phase1_i3 (List.nodup_cons.mp hord).2 (nodup_removePick hpool _)
        ((List.mem_cons.mp hx).resolve_left hxi) (hmem _ (rank_a_lt P x) ha) (hmem _ (rank_b_lt P x) hb)
        (hmem _ (rank_c_lt P x) hc) ?_
      intro g hr k hk
      have hki : k ≠ i := fun e => hi (e ▸ (hspec.1 k g hk).1)
      have := ht g hr k (by rw [phase1_cons]; simp [hki, hk])
      simp only [idx, hxi, hki, ↓reduceIte] at this
      omega

theorem blk_ge : ∀ {order : List A} {pool : List G} {n : Nat} {x : A}, x ∈ order →
    n ≤ blkAux P order pool n x
  | [], _, _, _, hx => by simp at hx
  | i :: order, pool, n, x, hx => by
    rw [blkAux_cons]
    by_cases hxi : x = i
    · simp only [hxi, ↓reduceIte]; split <;> omega
    · simp only [hxi, ↓reduceIte]
      have := blk_ge (pool := removePick pool (fav P pool i))
        (n := if full P pool i then n + 1 else n) ((List.mem_cons.mp hx).resolve_left hxi)
      by_cases hf : full P pool i = true <;> simp only [hf] at this ⊢ <;> simp at this ⊢ <;> omega

theorem lead_blk : ∀ {order : List A} {pool : List G} {n : Nat} {x : A}, leadB P order pool x = true →
    n + 1 ≤ blkAux P order pool n x
  | [], _, _, _, hx => by simp [leadB] at hx
  | i :: order, pool, n, x, hx => by
    rw [leadB_cons] at hx
    rw [blkAux_cons]
    by_cases hxi : x = i
    · simp only [hxi, ↓reduceIte] at hx ⊢; simp [hx]
    · simp only [hxi, ↓reduceIte] at hx ⊢
      have := lead_blk (n := if full P pool i then n + 1 else n) hx
      by_cases hf : full P pool i = true <;> simp only [hf] at this ⊢ <;> simp at this ⊢ <;> omega

/-- A block has one leader. -/
theorem phase1_lead_unique : ∀ {order : List A} {pool : List G} {n : Nat} {x x' : A},
    x ∈ order → x' ∈ order → leadB P order pool x = true → leadB P order pool x' = true →
    blkAux P order pool n x = blkAux P order pool n x' → x = x'
  | [], _, _, _, _, hx, _, _, _, _ => by simp at hx
  | i :: order, pool, n, x, x', hx, hx', hl, hl', he => by
    rw [leadB_cons] at hl hl'
    rw [blkAux_cons, blkAux_cons] at he
    by_cases hxi : x = i <;> by_cases hx'i : x' = i
    · rw [hxi, hx'i]
    · simp only [hxi, hx'i, ↓reduceIte] at hl hl' he
      have := lead_blk (n := if full P pool i then n + 1 else n) hl'
      simp only [hl, ↓reduceIte] at he this
      omega
    · simp only [hxi, hx'i, ↓reduceIte] at hl hl' he
      have := lead_blk (n := if full P pool i then n + 1 else n) hl
      simp only [hl', ↓reduceIte] at he this
      omega
    · simp only [hxi, hx'i, ↓reduceIte] at hl hl' he
      exact phase1_lead_unique ((List.mem_cons.mp hx).resolve_left hxi)
        ((List.mem_cons.mp hx').resolve_left hx'i) hl hl' he

end phase1

/-! ## The facts Theorems A and B use -/

/-- What Theorems A and B use of Phase 1 (`proofs/lb_last_step.md` §1), for picks `Y`, the processing
order `order` (time `idx order`), blocks `blk` and leaders `lead`. -/
structure Run (P : Profile A G) (agents : List A) (goods : List G) (order : List A) (Y : A → Option G)
    (blk : A → Nat) (lead : A → Prop) : Prop where
  order_nodup : order.Nodup
  mem_order : ∀ i, i ∈ order ↔ i ∈ agents
  pick : ∀ k y, Y k = some y → k ∈ agents ∧ y ∈ goods ∧ P.rank k y < 3
  pick_inj : ∀ k k' y, Y k = some y → Y k' = some y → k = k'
  b2 : ∀ j ∈ agents, ∀ g ∈ goods, P.Prefers Y j g →
    ∃ k, Y k = some g ∧ idx order k < idx order j ∧ blk k = blk j
  i3 : ∀ x ∈ agents, (∀ g, P.rank x g < 3 → ∀ k, Y k = some g → idx order x ≤ idx order k) → lead x
  lead_unique : ∀ x ∈ agents, ∀ x' ∈ agents, lead x → lead x' → blk x = blk x' → x = x'
  first : agents ≠ [] → ∃ x ∈ agents, Y x = some (P.a x)

/-- **Phase 1 with R1 priority.** For every processing order with R1 priority (any choice at every R1
step and every insertion step), Phase 1 satisfies (B2), (I3), one leader per block, and its first agent
takes its top. -/
theorem phase1_run {P : Profile A G} {agents : List A} {goods : List G} {order : List A}
    (hWF : WF P agents goods) (hgd : goods.Nodup) (hord : order.Nodup)
    (hperm : ∀ i, i ∈ order ↔ i ∈ agents) (hR : R1Prio P order goods) :
    Run P agents goods order (phase1 P order goods) (blkAux P order goods 0)
      (fun x => leadB P order goods x = true) := by
  obtain ⟨h1, h2, -⟩ := phase1_spec P order goods hord hgd
  refine ⟨hord, hperm, fun k y hk => ?_, h2, fun j hj g hg hp => ?_, fun x hx ht => ?_,
    fun x hx x' hx' hl hl' he => ?_, fun hne => ?_⟩
  · obtain ⟨a, b, c⟩ := h1 k y hk; exact ⟨(hperm k).mp a, b, c⟩
  · exact phase1_b2 hord hgd hR j ((hperm j).mpr hj) g hg hp
  · obtain ⟨ha, hb, hc, -⟩ := hWF x hx
    exact phase1_i3 hord hgd ((hperm x).mpr hx) ha hb hc ht
  · exact phase1_lead_unique ((hperm x).mpr hx) ((hperm x').mpr hx') hl hl' he
  · cases order with
    | nil =>
      obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil agents hne
      exact absurd ((hperm i).mpr hi) (by simp)
    | cons i rest =>
      have hi := (hperm i).mp (by simp)
      refine ⟨i, hi, ?_⟩
      rw [phase1_cons]
      simp [fav, (hWF i hi).1]

/-! ## LB's upgrades -/

omit [DecidableEq A] in
theorem picker_eq_none_iff {agents : List A} {Y : A → Option G} {g : G}
    (hpick : ∀ k y, Y k = some y → k ∈ agents) : picker agents Y g = none ↔ ∀ k, Y k ≠ some g := by
  constructor
  · intro h k hk; exact picker_none h k (hpick k g hk) hk
  · intro h
    cases hp : picker agents Y g with
    | none => rfl
    | some k => exact absurd (picker_some hp).2 (h k)

theorem upgrades_mem (P : Profile A G) (agents : List A) (Y : A → Option G) :
    ∀ (fuel : Nat) (up : List A) (J : List G), (∀ u ∈ up, u ∈ agents) →
      ∀ u ∈ (upgrades P agents Y fuel up J).1, u ∈ agents
  | 0, _, _, h => h
  | fuel + 1, up, J, h => by
    unfold upgrades
    cases hf : agents.find? (canUp P agents up Y J) with
    | none => exact h
    | some k =>
      apply upgrades_mem P agents Y fuel
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact List.mem_of_find?_eq_some hf
      · exact h u hu

/-- The upgrade loop runs to a fixpoint: at the end no agent can be upgraded (this is (UT)). -/
theorem upgrades_fix (P : Profile A G) (agents : List A) (Y : A → Option G) :
    ∀ (fuel : Nat) (up : List A) (J : List G), (agents.filter (fun x => x ∉ up)).length ≤ fuel →
      ∀ k ∈ agents, canUp P agents (upgrades P agents Y fuel up J).1 Y (upgrades P agents Y fuel up J).2 k
        = false
  | 0, up, J, h, k, hk => by
    have hku : k ∈ up := by
      refine Classical.byContradiction fun hn => ?_
      have hkf : k ∈ agents.filter (fun x => decide (x ∉ up)) :=
        List.mem_filter.mpr ⟨hk, decide_eq_true hn⟩
      have := List.length_pos_iff_exists_mem.mpr ⟨k, hkf⟩
      omega
    simp [upgrades, canUp, hku]
  | fuel + 1, up, J, h, k, hk => by
    unfold upgrades
    cases hf : agents.find? (canUp P agents up Y J) with
    | none => exact Bool.eq_false_iff.mpr (List.find?_eq_none.mp hf k hk)
    | some k' =>
      apply upgrades_fix P agents Y fuel (k' :: up) (J.erase (P.c k')) _ k hk
      have hc := List.find?_some hf
      have hk'u : k' ∉ up := by
        intro hin
        simp [canUp, hin] at hc
      have e : agents.filter (fun x => decide (x ∉ k' :: up)) =
          (agents.filter (fun x => decide (x ∉ up))).filter (fun x => decide (x ≠ k')) := by
        rw [List.filter_filter]
        apply List.filter_congr
        intro x _
        by_cases h1 : x = k' <;> by_cases h2 : x ∈ up <;> simp [h1, h2]
      have hlt : (agents.filter (fun x => decide (x ∉ k' :: up))).length <
          (agents.filter (fun x => decide (x ∉ up))).length := by
        rw [e, List.length_filter_lt_length_iff_exists]
        exact ⟨k', List.mem_filter.mpr ⟨List.mem_of_find?_eq_some hf, by simpa using hk'u⟩, by simp⟩
      omega

/-- The junk after Phase 1 (the goods nobody picked). -/
def junk0 (agents : List A) (Y : A → Option G) (goods : List G) : List G :=
  goods.filter (fun g => (picker agents Y g).isNone)

/-- LB's upgraded agents: the upgrade loop run to its end from `U = ∅`, `J = J₀`. -/
def lbUp (P : Profile A G) (agents : List A) (goods : List G) (Y : A → Option G) : List A :=
  (upgrades P agents Y agents.length [] (junk0 agents Y goods)).1

/-- The state of the upgrade loop, if its invariant holds and no agent can be upgraded any more, is a valid
pre-allocation, and (UT) holds. -/
theorem valid_of_inv {P : Profile A G} {agents : List A} {goods : List G} {order : List A}
    {Y : A → Option G} {blk : A → Nat} {lead : A → Prop}
    (hrun : Run P agents goods order Y blk lead) (hWF : WF P agents goods) {up : List A} {J : List G}
    (hinv : UpInv P agents Y (junk0 agents Y goods) up J) (hmem : ∀ u ∈ up, u ∈ agents)
    (hfix : ∀ k ∈ agents, canUp P agents up Y J k = false) :
    Valid P agents goods Y up ∧
    ∀ k ∈ agents, k ∉ up → Y k = some (P.b k) → P.c k ∈ junkList P agents up Y goods →
      P.NA agents (· ∈ up) Y (P.b k) := by
  have hpick : ∀ k y, Y k = some y → k ∈ agents := fun k y hk => (hrun.pick k y hk).1
  obtain ⟨hJnd, hJ0, hcov, hup⟩ := hinv
  -- an unpicked good is in no `N_i`, by (B2)
  have hunp : ∀ g ∈ goods, (∀ k, Y k ≠ some g) → ¬ P.NA agents (· ∈ up) Y g := by
    intro g hg hn hna
    obtain ⟨i, hi, -, hp⟩ := hna
    obtain ⟨k, hk, -⟩ := hrun.b2 i hi g hg hp
    exact hn k hk
  have hc0 : ∀ u ∈ up, P.c u ∈ goods ∧ ∀ k, Y k ≠ some (P.c u) := by
    intro u hu
    have := List.mem_filter.mp (hup u hu).2.2.1
    refine ⟨this.1, (picker_eq_none_iff hpick).mp ?_⟩
    simpa using this.2
  refine ⟨⟨hrun.pick, hrun.pick_inj, hmem, fun u hu => pickRank_one (hup u hu).1, hc0,
    fun u hu u' hu' e => (hup u' hu').2.2.2.2 u hu e, fun g hg hn _ => hunp g hg hn,
    fun u hu => ⟨(hup u hu).2.1, hunp _ (hc0 u hu).1 (hc0 u hu).2⟩⟩, ?_⟩
  intro k hk hku hkb hcj
  have hfix := hfix k hk
  -- `c k` is still in the loop's junk
  obtain ⟨hcg, hcp, hcu⟩ := mem_junkList.mp hcj
  have hcJ : P.c k ∈ J := by
    refine Classical.byContradiction fun hn => ?_
    obtain ⟨u, hu, e⟩ := hcov (P.c k) (List.mem_filter.mpr ⟨hcg, by simp [hcp]⟩) hn
    exact upOf_none hcu u hu e
  have hr : P.pickRank Y k = 1 := by
    unfold Profile.pickRank; rw [hkb]
    obtain ⟨-, -, -, hab, -, -⟩ := hWF k hk
    simp [Profile.rank, Ne.symm hab]
  simp only [canUp, Bool.and_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false,
    List.contains_iff_mem, hr, beq_self_eq_true] at hfix
  rcases hfix with ((h | h) | h) | h
  · exact absurd (by simpa using h) hku
  · simp at h
  · exact absurd hcJ (by simpa using h)
  · exact naB_iff.mp h

/-- **LB's state after the upgrades is a valid pre-allocation** (`proofs/lb_last_step.md` §3), and (UT)
holds: no agent outside `U` with pick `b k`, `c k` junk and `b k ∉ NA` remains. -/
theorem lbState_valid {P : Profile A G} {agents : List A} {goods : List G} {order : List A}
    {Y : A → Option G} {blk : A → Nat} {lead : A → Prop}
    (hrun : Run P agents goods order Y blk lead) (hWF : WF P agents goods) (hgd : goods.Nodup) :
    Valid P agents goods Y (lbUp P agents goods Y) ∧
    ∀ k ∈ agents, k ∉ lbUp P agents goods Y → Y k = some (P.b k) →
      P.c k ∈ junkList P agents (lbUp P agents goods Y) Y goods →
      P.NA agents (· ∈ lbUp P agents goods Y) Y (P.b k) :=
  valid_of_inv hrun hWF
    (upInv_upgrades P agents Y (junk0 agents Y goods) agents.length [] _
      (upInv_init P agents Y (hgd.sublist List.filter_sublist)))
    (upgrades_mem P agents Y agents.length [] (junk0 agents Y goods) (fun u hu => by simp at hu))
    (upgrades_fix P agents Y agents.length [] (junk0 agents Y goods)
      (Nat.le_trans (List.length_filter_le _ _) (Nat.le_refl _)))

/-! ## The upgrades in any order -/

/-- Upgrade steps in any order: from `(up, J)`, upgrading one listed agent at a time, each passing LB's test
(`canUp`) at its turn, reaches `(up', J')`. -/
inductive UpReach (P : Profile A G) (agents : List A) (Y : A → Option G) :
    List A → List G → List A → List G → Prop
  | refl (up : List A) (J : List G) : UpReach P agents Y up J up J
  | step {up : List A} {J : List G} {up' : List A} {J' : List G} (k : A) :
      k ∈ agents → canUp P agents up Y J k = true →
      UpReach P agents Y (k :: up) (J.erase (P.c k)) up' J' → UpReach P agents Y up J up' J'

/-- An end state of the upgrades, in any order: reached from `U = ∅` and `J = J₀`, and no agent can be
upgraded any more. -/
def UpFinal (P : Profile A G) (agents : List A) (Y : A → Option G) (goods : List G) (up : List A) : Prop :=
  ∃ J, UpReach P agents Y [] (junk0 agents Y goods) up J ∧ ∀ k ∈ agents, canUp P agents up Y J k = false

theorem upInv_step {P : Profile A G} {agents : List A} {Y : A → Option G} {J0 : List G} {up : List A}
    {J : List G} {k : A} (h : UpInv P agents Y J0 up J) (hc : canUp P agents up Y J k = true) :
    UpInv P agents Y J0 (k :: up) (J.erase (P.c k)) := by
  simp only [canUp, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem, beq_iff_eq] at hc
  obtain ⟨⟨⟨hku, hr⟩, hcJ⟩, hna⟩ := hc
  have hku : k ∉ up := by simpa using hku
  have hna : ¬ P.NA agents (· ∈ up) Y (P.b k) := fun h' => by
    rw [← naB_iff] at h'; rw [h'] at hna; cases hna
  obtain ⟨hJnd, hJ0, hcov, hup⟩ := h
  have hmono : ∀ {g}, P.NA agents (· ∈ k :: up) Y g → P.NA agents (· ∈ up) Y g :=
    NA_mono (fun x hx => List.mem_cons_of_mem k hx)
  refine ⟨hJnd.erase _, fun g hg => hJ0 g (List.mem_of_mem_erase hg), fun g hg hgn => ?_,
    fun k' hk' => ?_⟩
  · by_cases hgc : g = P.c k
    · exact ⟨k, by simp, hgc.symm⟩
    · have : g ∉ J := fun hgJ => hgn ((List.Nodup.mem_erase_iff hJnd).mpr ⟨hgc, hgJ⟩)
      obtain ⟨k'', hk'', he⟩ := hcov g hg this
      exact ⟨k'', List.mem_cons_of_mem k hk'', he⟩
  · rcases List.mem_cons.mp hk' with rfl | hk'
    · refine ⟨hr, fun h' => hna (hmono h'), hJ0 _ hcJ, fun h' => ?_, fun k'' hk'' he => ?_⟩
      · exact absurd rfl ((List.Nodup.mem_erase_iff hJnd).mp h').1
      · rcases List.mem_cons.mp hk'' with rfl | hk''
        · rfl
        · exact absurd (he ▸ hcJ) (hup k'' hk'').2.2.2.1
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hup k' hk'
      refine ⟨h1, fun h' => h2 (hmono h'), h3, fun h' => h4 (List.mem_of_mem_erase h'),
        fun k'' hk'' he => ?_⟩
      rcases List.mem_cons.mp hk'' with rfl | hk''
      · exact absurd (he ▸ hcJ) h4
      · exact h5 k'' hk'' he

/-- Upgrade steps in any order keep the loop's invariant, and upgrade only listed agents. -/
theorem upReach_inv {P : Profile A G} {agents : List A} {Y : A → Option G} {J0 : List G}
    {up : List A} {J : List G} {up' : List A} {J' : List G} (h : UpReach P agents Y up J up' J') :
    UpInv P agents Y J0 up J → (∀ u ∈ up, u ∈ agents) →
      UpInv P agents Y J0 up' J' ∧ ∀ u ∈ up', u ∈ agents := by
  induction h with
  | refl => exact fun hi hm => ⟨hi, hm⟩
  | step k hk hc _ ih =>
    intro hi hm
    exact ih (upInv_step hi hc) (fun u hu => by
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hk
      · exact hm u hu)

/-- LB's loop is one order of the upgrades. -/
theorem upgrades_reach (P : Profile A G) (agents : List A) (Y : A → Option G) :
    ∀ (fuel : Nat) (up : List A) (J : List G),
      UpReach P agents Y up J (upgrades P agents Y fuel up J).1 (upgrades P agents Y fuel up J).2
  | 0, up, J => UpReach.refl up J
  | fuel + 1, up, J => by
    unfold upgrades
    cases hf : agents.find? (canUp P agents up Y J) with
    | none => exact UpReach.refl up J
    | some k =>
      exact UpReach.step k (List.mem_of_find?_eq_some hf) (List.find?_some hf)
        (upgrades_reach P agents Y fuel (k :: up) (J.erase (P.c k)))

/-- LB's upgraded agents are an end state of the upgrades. -/
theorem lbUp_final (P : Profile A G) (agents : List A) (Y : A → Option G) (goods : List G) :
    UpFinal P agents Y goods (lbUp P agents goods Y) :=
  ⟨_, upgrades_reach P agents Y agents.length [] (junk0 agents Y goods),
    upgrades_fix P agents Y agents.length [] (junk0 agents Y goods)
      (Nat.le_trans (List.length_filter_le _ _) (Nat.le_refl _))⟩

/-- **The upgrades in any order** (`proofs/lb_last_step.md` §3). Every end state of the upgrades, whatever
order they are made in, is a valid pre-allocation, and (UT) holds. -/
theorem upFinal_valid {P : Profile A G} {agents : List A} {goods : List G} {order : List A}
    {Y : A → Option G} {blk : A → Nat} {lead : A → Prop}
    (hrun : Run P agents goods order Y blk lead) (hWF : WF P agents goods) (hgd : goods.Nodup)
    {up : List A} (hup : UpFinal P agents Y goods up) :
    Valid P agents goods Y up ∧
    ∀ k ∈ agents, k ∉ up → Y k = some (P.b k) → P.c k ∈ junkList P agents up Y goods →
      P.NA agents (· ∈ up) Y (P.b k) := by
  obtain ⟨J, hreach, hfix⟩ := hup
  obtain ⟨hinv, hmem⟩ := upReach_inv hreach (upInv_init P agents Y (hgd.sublist List.filter_sublist))
    (fun u hu => by simp at hu)
  exact valid_of_inv hrun hWF hinv hmem hfix

end LB
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB.phase1_run
#print axioms EFX.LB.lbState_valid
#print axioms EFX.LB.upgrades_fix
#print axioms EFX.LB.upFinal_valid
#print axioms EFX.LB.lbUp_final
