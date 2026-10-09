import EFX.Blocks
import EFX.Junk

/-!
# Theorem A: the owner r, and the bad case (`proofs/lb_last_step.md` §4)

Fix a run of Phase 1 with R1 priority (`EFX.LB.Run`) and a valid pre-allocation `(Y, up)` with (UT), as
LB's upgrades produce (`EFX.LB.lbState_valid`). This file proves Theorem A.

- `lastOut up order`: `r`, the last-processed agent not in `up`. (A1) `lastOut_terminal`: `r` is a terminal.
- Need chains (A4): `isNext cur j` (`cur` is frozen and `j`, not upgraded, needs `cur`'s pick);
  `chainFrom cur rest` scans the agents processed after `cur` and follows the first agent that needs the
  current pick; `chainEnd x` is the end of the chain from `x`. `chainEnd_spec`: it is a terminal in `x`'s
  block (and `x` itself when `x` is a terminal).
- `exposedB w x`: `x` is exposed for owner `w` (not upgraded, `x ≠ w`, pick `a x`, and `b x`, `c x` each
  junk or in `w`'s base); `exposedL w` lists them. (A3) `exposed_lead`: every agent exposed for `r` is a
  leader, so exposed agents lie in distinct blocks.
- `meet`: two distinct exposed agents whose junk parts `π_x = {b x, c x} ∩ J` share a good. `hitSet`: one
  good from each `π_x`, the shared good for such a pair.
- `OwnerOK w H`: the hypotheses of Lemma 1 (`EFX.LB.complete_some`) for owner `w` and set `H`.
- `Bad`: a weaker form of the bad case of `proofs/lb_last_step.md`. The agent `k` exposed for `r` in `r`'s
  block (if any) has the need chain `chainEnd` follows ending at `r`, and the sets `π_x` are pairwise disjoint.
  The text asks *every* need chain from `k*` to end at `r`, and `k*` to be frozen (implicit here: a chain from
  `k` that ends at `r ≠ k` is non-empty). The text's bad case implies `Bad`.
- `theoremA`: unless `Bad`, `r` is a valid owner with `H = hitSet`. Its hypothesis `¬ Bad` is stronger than the
  negation of the text's bad case, so this is a weaker corollary of the text's Theorem A; `kstar_spec` records
  the structure of `k*`.
- `ValidOwner w`: `w` is a valid owner, i.e. Lemma 1's condition holds for *some* set `H` (the reading of
  `proofs/lb_last_step.md`: a hitting set of the exposed pairs' junk parts that fits the free slots).
  `validOwner_iff`: `r` is a valid owner exactly when `hitSet` fits (when the sets `π_x` are disjoint,
  `hitSet` is a smallest hitting set; otherwise `hitSet` fits by Theorem A's counting).
- **Theorem A, as written** (`theoremA_invalid`): if `r` is not a valid owner, then `k*` exists and is
  frozen, the sets `π_x` are pairwise disjoint, and *every* need chain from `k*` that ends at a terminal ends
  at `r`.
-/

set_option autoImplicit false

namespace EFX
namespace LB

variable {A G : Type} [DecidableEq A] [DecidableEq G]

open Profile

/-! ## The last agent not upgraded -/

/-- The last agent of `order` that is not in `up`. -/
def lastOut (up : List A) : List A → Option A
  | [] => none
  | i :: order =>
    match lastOut up order with
    | some r => some r
    | none => if i ∈ up then none else some i

theorem lastOut_none {up : List A} : ∀ {order : List A}, lastOut up order = none → ∀ x ∈ order, x ∈ up
  | [], _, x, hx => by simp at hx
  | i :: order, h, x, hx => by
    unfold lastOut at h
    cases hl : lastOut up order with
    | some r => rw [hl] at h; cases h
    | none =>
      rw [hl] at h
      simp only at h
      rcases List.mem_cons.mp hx with rfl | hx
      · by_cases hi : x ∈ up
        · exact hi
        · simp [hi] at h
      · exact lastOut_none hl x hx

theorem lastOut_some {up : List A} : ∀ {order : List A} {r : A}, order.Nodup → lastOut up order = some r →
    r ∈ order ∧ r ∉ up ∧ ∀ x ∈ order, x ∉ up → idx order x ≤ idx order r
  | [], _, _, h => by simp [lastOut] at h
  | i :: order, r, hnd, h => by
    have hi : i ∉ order := (List.nodup_cons.mp hnd).1
    unfold lastOut at h
    cases hl : lastOut up order with
    | some r' =>
      rw [hl] at h
      have e : r' = r := Option.some.inj h
      subst e
      obtain ⟨h1, h2, h3⟩ := lastOut_some (List.nodup_cons.mp hnd).2 hl
      have hri : r' ≠ i := fun e => hi (e ▸ h1)
      refine ⟨List.mem_cons_of_mem _ h1, h2, fun x hx hxu => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [idx]
      · have hxi : x ≠ i := fun e => hi (e ▸ hx)
        have := h3 x hx hxu
        simp only [idx, hxi, hri, ↓reduceIte]
        omega
    | none =>
      rw [hl] at h
      simp only at h
      by_cases hiu : i ∈ up
      · simp [hiu] at h
      · simp only [hiu, ↓reduceIte, Option.some.injEq] at h
        subst h
        refine ⟨by simp, hiu, fun x hx hxu => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.le_refl _
        · exact absurd (lastOut_none hl x hx) hxu

/-! ## Terminals and slots -/

/-- `t` is a terminal: listed, not upgraded, not frozen. -/
def IsTerm (P : Profile A G) (agents up : List A) (Y : A → Option G) (t : A) : Prop :=
  t ∈ agents ∧ t ∉ up ∧ frozenB P agents up Y t = false

theorem frozenB_iff {P : Profile A G} {agents up : List A} {Y : A → Option G} {j : A} :
    frozenB P agents up Y j = true ↔ ∃ y, Y j = some y ∧ P.NA agents (· ∈ up) Y y := by
  unfold frozenB
  cases hy : Y j with
  | none => simp
  | some y => simp [naB_iff]

theorem not_frozen_iff {P : Profile A G} {agents up : List A} {Y : A → Option G} {j : A} :
    frozenB P agents up Y j = false ↔ ∀ y, Y j = some y → ¬ P.NA agents (· ∈ up) Y y := by
  rw [← Bool.not_eq_true, frozenB_iff]
  constructor
  · intro h y hy hna; exact h ⟨y, hy, hna⟩
  · rintro h ⟨y, hy, hna⟩; exact h y hy hna

theorem cap_pos {P : Profile A G} {agents up : List A} {Y : A → Option G} {t : A}
    (h : IsTerm P agents up Y t) : 1 ≤ cap P agents up Y t := by
  obtain ⟨-, hu, hf⟩ := h
  unfold cap
  simp only [hf, Bool.false_or]
  have : up.contains t = false := by simpa using hu
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  split <;> omega

omit [DecidableEq A] [DecidableEq G] in
/-- Distinct agents of `agents`, each with at least one slot, are at most the number of slots. -/
theorem length_le_sum {agents L : List A} {s : A → Nat} (hL : L.Nodup)
    (h : ∀ t ∈ L, t ∈ agents ∧ 1 ≤ s t) : L.length ≤ (agents.map s).sum := by
  classical
  have h1 : L.length ≤ (agents.filter (fun j => j ∈ L)).length :=
    length_le_of_subset hL (fun t ht => List.mem_filter.mpr ⟨(h t ht).1, by simp [ht]⟩)
  have h2 : (agents.filter (fun j => j ∈ L)).length =
      (agents.map (fun j => if j ∈ L then 1 else 0)).sum := by
    rw [sum_map_ite (fun j => j ∈ L) (fun _ => 1), sum_map_one]
  have h3 : (agents.map (fun j => if j ∈ L then 1 else 0)).sum ≤ (agents.map s).sum := by
    apply sum_map_le
    intro j _
    by_cases hj : j ∈ L
    · simp only [hj, ↓reduceIte]; exact (h j hj).2
    · simp [hj]
  omega

/-! ## Need chains (A4) -/

/-- `j` follows `cur` in a need chain: `cur` is frozen, and `j`, not upgraded, ranks `cur`'s pick above
its own. -/
def isNext (P : Profile A G) (agents up : List A) (Y : A → Option G) (cur j : A) : Bool :=
  frozenB P agents up Y cur && !(up.contains j) &&
    (match Y cur with
     | some y => decide (P.Prefers Y j y)
     | none => false)

/-- The need chain from `cur`, scanning `rest` (the agents processed after `cur`, in order): the next
agent is the first of `rest` that follows the current one. -/
def chainFrom (P : Profile A G) (agents up : List A) (Y : A → Option G) : A → List A → List A
  | _, [] => []
  | cur, j :: rest =>
    if isNext P agents up Y cur j then j :: chainFrom P agents up Y j rest
    else chainFrom P agents up Y cur rest

/-- The end of the need chain from `x`. -/
def chainEnd (P : Profile A G) (agents up : List A) (Y : A → Option G) (order : List A) (x : A) : A :=
  (chainFrom P agents up Y x (after order x)).getLastD x

/-- `cur :: l` is a need chain. -/
def IsChain (P : Profile A G) (agents up : List A) (Y : A → Option G) : A → List A → Prop
  | _, [] => True
  | cur, j :: l => isNext P agents up Y cur j = true ∧ IsChain P agents up Y j l

section chains
variable {P : Profile A G} {agents up : List A} {Y : A → Option G}

theorem isNext_spec {cur j : A} (h : isNext P agents up Y cur j = true) :
    j ∉ up ∧ ∃ y, Y cur = some y ∧ P.NA agents (· ∈ up) Y y ∧ P.Prefers Y j y := by
  unfold isNext at h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨hf, hj⟩, hp⟩ := h
  refine ⟨by simpa using hj, ?_⟩
  obtain ⟨y, hy, hna⟩ := frozenB_iff.mp hf
  rw [hy] at hp
  exact ⟨y, hy, hna, by simpa using hp⟩

theorem isNext_of {cur j : A} {y : G} (hf : frozenB P agents up Y cur = true) (hj : j ∉ up)
    (hy : Y cur = some y) (hp : P.Prefers Y j y) : isNext P agents up Y cur j = true := by
  unfold isNext
  simp [hf, hj, hy, hp]

theorem chainFrom_isChain : ∀ (cur : A) (rest : List A), IsChain P agents up Y cur (chainFrom P agents up Y cur rest)
  | _, [] => trivial
  | cur, j :: rest => by
    unfold chainFrom
    split
    · exact ⟨by assumption, chainFrom_isChain j rest⟩
    · exact chainFrom_isChain cur rest

theorem chainFrom_sublist : ∀ (cur : A) (rest : List A), (chainFrom P agents up Y cur rest).Sublist rest
  | _, [] => List.Sublist.slnil
  | cur, j :: rest => by
    unfold chainFrom
    split
    · exact (chainFrom_sublist j rest).cons_cons j
    · exact (chainFrom_sublist cur rest).cons j

/-- A chain from an agent that is not frozen is empty. -/
theorem chainFrom_of_not_frozen {cur : A} (h : frozenB P agents up Y cur = false) :
    ∀ rest, chainFrom P agents up Y cur rest = []
  | [] => rfl
  | j :: rest => by
    unfold chainFrom
    have : isNext P agents up Y cur j = false := by simp [isNext, h]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    exact chainFrom_of_not_frozen h rest

variable {goods : List G} {order : List A} {blk : A → Nat} {lead : A → Prop}

/-- Consecutive agents of a need chain: processed later, same block. -/
theorem isNext_run (hrun : Run P agents goods order Y blk lead) {cur j : A} (hj : j ∈ agents)
    (h : isNext P agents up Y cur j = true) :
    idx order cur < idx order j ∧ blk j = blk cur := by
  obtain ⟨-, y, hy, -, hp⟩ := isNext_spec h
  obtain ⟨k, hk, hlt, hb⟩ := hrun.b2 j hj y (hrun.pick cur y hy).2.1 hp
  have := hrun.pick_inj k cur y hk hy
  subst this
  exact ⟨hlt, hb.symm⟩

/-- The scan ends at a terminal: if the current agent is frozen, some later agent follows it. -/
theorem chainFrom_end (hrun : Run P agents goods order Y blk lead) :
    ∀ (rest : List A) (cur : A) (pre : List A), order = pre ++ rest →
      (frozenB P agents up Y cur = true → ∃ j ∈ rest, isNext P agents up Y cur j = true) →
      frozenB P agents up Y ((chainFrom P agents up Y cur rest).getLastD cur) = false
  | [], cur, _, _, h => by
    simp only [chainFrom, List.getLastD_nil]
    cases hf : frozenB P agents up Y cur with
    | false => rfl
    | true => obtain ⟨j, hj, -⟩ := h hf; simp at hj
  | j :: rest, cur, pre, hpre, h => by
    unfold chainFrom
    split
    · rename_i hnx
      rw [List.getLastD_cons]
      refine chainFrom_end hrun rest j (pre ++ [j]) (by simp [hpre]) (fun hf => ?_)
      obtain ⟨y, hy, hna⟩ := frozenB_iff.mp hf
      obtain ⟨i, hi, hiu, hp⟩ := hna
      refine ⟨i, ?_, isNext_of hf hiu hy hp⟩
      have hnx' := isNext_of (P := P) (agents := agents) (up := up) hf hiu hy hp
      have hlt := (isNext_run hrun hi hnx').1
      have hio : i ∈ pre ++ j :: rest := hpre ▸ (hrun.mem_order i).mpr hi
      exact mem_of_idx_gt (hpre ▸ hrun.order_nodup) hio (hpre ▸ hlt)
    · rename_i hnx
      refine chainFrom_end hrun rest cur (pre ++ [j]) (by simp [hpre]) (fun hf => ?_)
      obtain ⟨j', hj', hn'⟩ := h hf
      rcases List.mem_cons.mp hj' with rfl | hj'
      · exact absurd hn' hnx
      · exact ⟨j', hj', hn'⟩

/-- The agents of the chain from `cur` are listed, not upgraded, and in `cur`'s block. -/
theorem chainFrom_mem (hrun : Run P agents goods order Y blk lead) :
    ∀ (cur : A) (rest : List A), (∀ j ∈ rest, j ∈ agents) →
      ∀ j ∈ chainFrom P agents up Y cur rest, j ∈ agents ∧ j ∉ up ∧ blk j = blk cur
  | _, [], _, j, hj => by simp [chainFrom] at hj
  | cur, j :: rest, hrest, j', hj' => by
    unfold chainFrom at hj'
    split at hj'
    · rename_i hnx
      have hja := hrest j (by simp)
      rcases List.mem_cons.mp hj' with rfl | hj'
      · exact ⟨hja, (isNext_spec hnx).1, (isNext_run hrun hja hnx).2⟩
      · obtain ⟨h1, h2, h3⟩ := chainFrom_mem hrun j rest (fun x hx => hrest x (by simp [hx])) j' hj'
        exact ⟨h1, h2, h3.trans (isNext_run hrun hja hnx).2⟩
    · exact chainFrom_mem hrun cur rest (fun x hx => hrest x (by simp [hx])) j' hj'

theorem after_mem (hrun : Run P agents goods order Y blk lead) {x : A} :
    ∀ j ∈ after order x, j ∈ agents := by
  intro j hj
  by_cases hx : x ∈ order
  · obtain ⟨pre, hpre⟩ := eq_after hx
    exact (hrun.mem_order j).mp (by rw [hpre]; simp [hj])
  · -- `after` of an agent not in the order is empty
    have : ∀ l : List A, x ∉ l → after l x = [] := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons i l ih =>
        intro hxl
        have hxi : x ≠ i := fun e => hxl (by simp [e])
        simp only [after, hxi, ↓reduceIte]
        exact ih (fun h => hxl (by simp [h]))
    rw [this order hx] at hj
    simp at hj

/-- **(A4)** The end `τ(x)` of the need chain from an agent `x` that is not upgraded is a terminal in
`x`'s block; it is `x` itself if `x` is a terminal. -/
theorem chainEnd_spec (hrun : Run P agents goods order Y blk lead) {x : A} (hx : x ∈ agents)
    (hxu : x ∉ up) :
    IsTerm P agents up Y (chainEnd P agents up Y order x) ∧
      blk (chainEnd P agents up Y order x) = blk x ∧
      (frozenB P agents up Y x = false → chainEnd P agents up Y order x = x) := by
  obtain ⟨pre, hpre⟩ := eq_after ((hrun.mem_order x).mpr hx)
  have hmem := chainFrom_mem (up := up) hrun x (after order x) (after_mem hrun)
  -- the end is `x` or an agent of the chain
  have hlast : chainEnd P agents up Y order x = x ∨
      chainEnd P agents up Y order x ∈ chainFrom P agents up Y x (after order x) := by
    unfold chainEnd
    cases hc : chainFrom P agents up Y x (after order x) with
    | nil => exact Or.inl rfl
    | cons j l =>
      right
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast (by simp)]
      exact List.getLast_mem _
  have hend : frozenB P agents up Y (chainEnd P agents up Y order x) = false := by
    refine chainFrom_end hrun (after order x) x (pre ++ [x]) (by simp [← hpre]) (fun hf => ?_)
    obtain ⟨y, hy, hna⟩ := frozenB_iff.mp hf
    obtain ⟨i, hi, hiu, hp⟩ := hna
    have hnx := isNext_of (P := P) (agents := agents) (up := up) hf hiu hy hp
    refine ⟨i, ?_, hnx⟩
    have hlt := (isNext_run hrun hi hnx).1
    rw [hpre] at hlt
    exact mem_of_idx_gt (hpre ▸ hrun.order_nodup) (hpre ▸ (hrun.mem_order i).mpr hi) hlt
  refine ⟨?_, ?_, fun hf => ?_⟩
  · rcases hlast with h | h
    · rw [h] at hend ⊢; exact ⟨hx, hxu, hend⟩
    · exact ⟨(hmem _ h).1, (hmem _ h).2.1, hend⟩
  · rcases hlast with h | h
    · rw [h]
    · exact (hmem _ h).2.2
  · unfold chainEnd
    rw [chainFrom_of_not_frozen hf]
    rfl

end chains

omit [DecidableEq A] in
theorem getLastD_mem' : ∀ (l : List A) (cur : A), l.getLastD cur ∈ cur :: l
  | [], cur => by simp
  | j :: l, cur => by
    rw [List.getLastD_cons]
    exact List.mem_cons_of_mem _ (getLastD_mem' l j)

/-! ## Exposed agents, the hitting set, and the owner criterion -/

instance (P : Profile A G) (up : List A) (Y : A → Option G) (w : A) (g : G) :
    Decidable (InBase P up Y w g) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- `x` is exposed for owner `w` (`E_w` in `proofs/lb_last_step.md` Lemma 1): not upgraded, not `w`, its pick
is its top, and `b x`, `c x` are each junk or in `w`'s base. -/
def Exposed (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (w x : A) : Prop :=
  x ≠ w ∧ x ∉ up ∧ Y x = some (P.a x) ∧
    (P.b x ∈ junkList P agents up Y goods ∨ InBase P up Y w (P.b x)) ∧
    (P.c x ∈ junkList P agents up Y goods ∨ InBase P up Y w (P.c x))

instance (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (w x : A) :
    Decidable (Exposed P agents up Y goods w x) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The agents exposed for owner `w`. -/
def exposedL (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (w : A) : List A :=
  agents.filter (fun x => decide (Exposed P agents up Y goods w x))

/-- One good of `π_x = {b x, c x} ∩ J`: `b x` if it is junk, else `c x`. -/
def pickOne (P : Profile A G) (J : List G) (x : A) : G := if P.b x ∈ J then P.b x else P.c x

/-- Two distinct agents of `E` whose sets `π` share a good, with that good. -/
def meet (P : Profile A G) (J : List G) (E : List A) : Option (A × A × G) :=
  E.findSome? fun x => E.findSome? fun y =>
    if x = y then none else
      ([P.b x, P.c x].find? (fun g => decide (g ∈ J ∧ (g = P.b y ∨ g = P.c y)))).map (fun g => (x, y, g))

/-- One good from each `π_x` (`x ∈ E`), using a shared good for the pair that `meet` finds. -/
def hitSet (P : Profile A G) (J : List G) (E : List A) : List G :=
  match meet P J E with
  | some (x, y, g) => g :: (E.filter (fun z => decide (z ≠ x ∧ z ≠ y))).map (pickOne P J)
  | none => E.map (pickOne P J)

/-- The hypotheses of Lemma 1 (`complete_some`) for owner `w` and set `H`: `w` is a listed agent, upgraded
or a terminal; `H` is junk, fits the slots of the other agents, and meets `{b x, c x}` for every agent `x`
exposed for `w`. -/
structure OwnerOK (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (w : A)
    (H : List G) : Prop where
  mem : w ∈ agents
  term : w ∈ up ∨ ∀ y, Y w = some y → ¬ P.NA agents (· ∈ up) Y y
  sub : ∀ h ∈ H, h ∈ junkList P agents up Y goods
  fit : H.length ≤ (agents.map (slotsExcept (cap P agents up Y) (some w))).sum
  hit : ∀ x ∈ agents, Exposed P agents up Y goods w x → P.b x ∈ H ∨ P.c x ∈ H

section hit
variable {P : Profile A G} {J : List G} {E : List A}

theorem meet_some {x y : A} {g : G} (h : meet P J E = some (x, y, g)) :
    x ∈ E ∧ y ∈ E ∧ x ≠ y ∧ g ∈ J ∧ (g = P.b x ∨ g = P.c x) ∧ (g = P.b y ∨ g = P.c y) := by
  obtain ⟨x', hx', h1⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨y', hy', h2⟩ := List.exists_of_findSome?_eq_some h1
  by_cases hxy : x' = y'
  · simp [hxy] at h2
  · simp only [hxy, ↓reduceIte, Option.map_eq_some_iff] at h2
    obtain ⟨g', hg', he⟩ := h2
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have hm := List.mem_of_find?_eq_some hg'
    have hp := List.find?_some hg'
    simp only [decide_eq_true_eq] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    exact ⟨hx', hy', hxy, hp.1, hm, hp.2⟩

theorem meet_none (h : meet P J E = none) :
    ∀ x ∈ E, ∀ y ∈ E, x ≠ y → ∀ g ∈ J, (g = P.b x ∨ g = P.c x) → (g = P.b y ∨ g = P.c y) → False := by
  intro x hx y hy hxy g hg hgx hgy
  have h1 := List.findSome?_eq_none_iff.mp h x hx
  have h2 := List.findSome?_eq_none_iff.mp h1 y hy
  simp only [hxy, ↓reduceIte, Option.map_eq_none_iff] at h2
  have := List.find?_eq_none.mp h2 g (by rcases hgx with rfl | rfl <;> simp)
  simp [hg, hgy] at this

omit [DecidableEq A] in
theorem pickOne_mem (x : A) : pickOne P J x = P.b x ∨ pickOne P J x = P.c x := by
  unfold pickOne; split <;> simp

omit [DecidableEq A] in
theorem pickOne_junk {x : A} (hx : P.b x ∈ J ∨ P.c x ∈ J) : pickOne P J x ∈ J := by
  unfold pickOne; split
  · assumption
  · exact hx.resolve_left (by assumption)

theorem hitSet_sub (hE : ∀ x ∈ E, P.b x ∈ J ∨ P.c x ∈ J) : ∀ h ∈ hitSet P J E, h ∈ J := by
  unfold hitSet
  split
  · rename_i x y g hm
    intro h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · exact (meet_some hm).2.2.2.1
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hh
      exact pickOne_junk (hE z (List.mem_filter.mp hz).1)
  · intro h hh
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hh
    exact pickOne_junk (hE z hz)

theorem hitSet_hit : ∀ x ∈ E, P.b x ∈ hitSet P J E ∨ P.c x ∈ hitSet P J E := by
  intro x hx
  have hpick : ∀ L : List A, x ∈ L →
      P.b x ∈ L.map (pickOne P J) ∨ P.c x ∈ L.map (pickOne P J) := by
    intro L hL
    rcases pickOne_mem (P := P) (J := J) x with h | h
    · exact Or.inl (List.mem_map.mpr ⟨x, hL, h⟩)
    · exact Or.inr (List.mem_map.mpr ⟨x, hL, h⟩)
  unfold hitSet
  split
  · rename_i a b g hm
    obtain ⟨-, -, -, -, hga, hgb⟩ := meet_some hm
    by_cases hxa : x = a
    · subst hxa; rcases hga with rfl | rfl <;> simp
    · by_cases hxb : x = b
      · subst hxb; rcases hgb with rfl | rfl <;> simp
      · have hmemf : x ∈ E.filter (fun z => decide (z ≠ a ∧ z ≠ b)) :=
          List.mem_filter.mpr ⟨hx, decide_eq_true ⟨hxa, hxb⟩⟩
        rcases hpick _ hmemf with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr (List.mem_cons_of_mem _ h)
  · exact hpick E hx

theorem hitSet_length : (hitSet P J E).length ≤ E.length ∧
    (meet P J E ≠ none → E.Nodup → (hitSet P J E).length + 1 ≤ E.length) := by
  unfold hitSet
  split
  · rename_i a b g hm
    obtain ⟨ha, hb, hab, -⟩ := meet_some hm
    have key : ((E.filter (fun z => decide (z ≠ a ∧ z ≠ b))).map (pickOne P J)).length + 2 ≤
        E.length := by
      rw [List.length_map, length_filter_add E (fun z => decide (z ≠ a ∧ z ≠ b))]
      have : 2 ≤ (E.filter (fun z => !decide (z ≠ a ∧ z ≠ b))).length := by
        have := length_le_of_subset (S := [a, b]) (T := E.filter (fun z => !decide (z ≠ a ∧ z ≠ b)))
          (by simp [hab]) (by
            intro z hz
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with rfl | rfl <;> simp [ha, hb])
        simpa using this
      omega
    refine ⟨by simp only [List.length_cons]; omega, fun _ _ => by simp only [List.length_cons]; omega⟩
  · rename_i hm
    exact ⟨by simp, fun h => absurd hm h⟩

end hit

omit [DecidableEq A] [DecidableEq G] in
theorem nodup_map_of_inj {β : Type} {f : A → β} : ∀ {l : List A}, l.Nodup →
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hnd, h => by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_of_inj (List.nodup_cons.mp hnd).2
      (fun x hx y hy => h x (by simp [hx]) y (by simp [hy]))⟩
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
    have := h b (by simp [hb]) a (by simp) he
    exact (List.nodup_cons.mp hnd).1 (this ▸ hb)

/-! ## Theorem A -/

/-- The state Theorems A and B start from: a run of Phase 1 with R1 priority, a valid pre-allocation with
(UT) (LB's state after its upgrades, `lbState_valid`), a well-formed profile, and no repeated agents or
goods. -/
structure State (P : Profile A G) (agents : List A) (goods : List G) (order : List A) (Y : A → Option G)
    (blk : A → Nat) (lead : A → Prop) (up : List A) : Prop where
  run : Run P agents goods order Y blk lead
  valid : Valid P agents goods Y up
  ut : ∀ k ∈ agents, k ∉ up → Y k = some (P.b k) → P.c k ∈ junkList P agents up Y goods →
    P.NA agents (· ∈ up) Y (P.b k)
  wf : WF P agents goods
  agents_nodup : agents.Nodup
  goods_nodup : goods.Nodup

/-- The agent exposed for `r` in `r`'s block (`k*`), if any. -/
def kstar (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (blk : A → Nat)
    (r : A) : Option A :=
  (exposedL P agents up Y goods r).find? (fun x => blk x == blk r)

/-- A weaker form of the bad case: `k*` exists, the need chain `chainEnd` follows from it ends at `r`, and the
sets `π_x` (`x` exposed for `r`) are pairwise disjoint. The text's bad case asks *every* need chain from `k*` to
end at `r` (see `theoremA_invalid`), and `k*` frozen, which is implicit here. -/
def Bad (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (order : List A)
    (blk : A → Nat) (r : A) : Prop :=
  ∃ k, kstar P agents up Y goods blk r = some k ∧ chainEnd P agents up Y order k = r ∧
    meet P (junkList P agents up Y goods) (exposedL P agents up Y goods r) = none

section theoremA
variable {P : Profile A G} {agents : List A} {goods : List G} {order : List A} {Y : A → Option G}
  {blk : A → Nat} {lead : A → Prop} {up : List A}

omit [DecidableEq A] in
theorem junk_not_picked {g : G} (hg : g ∈ junkList P agents up Y goods) (hpick : ∀ k y, Y k = some y → k ∈ agents) :
    ∀ k, Y k ≠ some g :=
  (picker_eq_none_iff hpick).mp (mem_junkList.mp hg).2.1

/-- `r` exists when there is an agent. -/
theorem lastOut_exists (hS : State P agents goods order Y blk lead up) (hne : agents ≠ []) :
    ∃ r, lastOut up order = some r := by
  obtain ⟨x, hx, hxa⟩ := hS.run.first hne
  cases hl : lastOut up order with
  | some r => exact ⟨r, rfl⟩
  | none =>
    have hxu := lastOut_none hl x ((hS.run.mem_order x).mpr hx)
    rw [hS.valid.up_b x hxu] at hxa
    obtain ⟨-, -, -, hab, -⟩ := hS.wf x hx
    exact absurd (Option.some.inj hxa).symm hab

/-- **(A1)** `r` is a terminal. -/
theorem lastOut_terminal (hS : State P agents goods order Y blk lead up) {r : A}
    (hr : lastOut up order = some r) :
    r ∈ agents ∧ r ∉ up ∧ ∀ y, Y r = some y → ¬ P.NA agents (· ∈ up) Y y := by
  obtain ⟨hro, hru, hmax⟩ := lastOut_some hS.run.order_nodup hr
  refine ⟨(hS.run.mem_order r).mp hro, hru, fun y hy hna => ?_⟩
  obtain ⟨j, hj, hju, hp⟩ := hna
  obtain ⟨k, hk, hlt, -⟩ := hS.run.b2 j hj y (hS.run.pick r y hy).2.1 hp
  have := hS.run.pick_inj k r y hk hy
  subst this
  have := hmax j ((hS.run.mem_order j).mpr hj) hju
  omega

omit [DecidableEq A] [DecidableEq G] in
/-- The base of an agent that is not upgraded is its pick. -/
theorem inBase_of_not_up {w : A} (hw : w ∉ up) {g : G} : InBase P up Y w g ↔ Y w = some g := by
  unfold InBase
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact h
    · exact absurd h hw
  · exact Or.inl

/-- Agents exposed for `r` are listed, not upgraded, and have a junk good among `b x`, `c x`. -/
theorem exposed_r (hS : State P agents goods order Y blk lead up) {r : A} (hr : lastOut up order = some r)
    {x : A} (hx : x ∈ exposedL P agents up Y goods r) :
    x ∈ agents ∧ Exposed P agents up Y goods r x ∧
      (P.b x ∈ junkList P agents up Y goods ∨ P.c x ∈ junkList P agents up Y goods) := by
  obtain ⟨hxa, hxe⟩ := List.mem_filter.mp hx
  have hxe : Exposed P agents up Y goods r x := of_decide_eq_true hxe
  refine ⟨hxa, hxe, ?_⟩
  obtain ⟨-, -, -, hb, hc⟩ := hxe
  have hru := (lastOut_terminal hS hr).2.1
  rw [inBase_of_not_up hru] at hb hc
  rcases hb with hb | hb
  · exact Or.inl hb
  rcases hc with hc | hc
  · exact Or.inr hc
  obtain ⟨-, -, -, -, -, hbc⟩ := hS.wf x hxa
  rw [hb] at hc
  exact absurd (Option.some.inj hc) hbc

/-- **(A3)** An agent exposed for `r` is a leader. -/
theorem exposed_lead (hS : State P agents goods order Y blk lead up) {r : A}
    (hr : lastOut up order = some r) {x : A} (hx : x ∈ exposedL P agents up Y goods r) : lead x := by
  obtain ⟨hxa, ⟨-, hxu, hxt, hb, hc⟩, -⟩ := exposed_r hS hr hx
  have hpick : ∀ k y, Y k = some y → k ∈ agents := fun k y hk => (hS.run.pick k y hk).1
  obtain ⟨-, hru, -⟩ := lastOut_terminal hS hr
  obtain ⟨-, -, hmax⟩ := lastOut_some hS.run.order_nodup hr
  have hxo := (hS.run.mem_order x).mpr hxa
  -- a good of `{b x, c x}` is junk (never picked) or `r`'s pick, taken after `x`'s turn
  have late : ∀ g, (g ∈ junkList P agents up Y goods ∨ InBase P up Y r g) →
      ∀ k, Y k = some g → idx order x ≤ idx order k := by
    intro g hg k hk
    rw [inBase_of_not_up hru] at hg
    rcases hg with hg | hg
    · exact absurd hk (junk_not_picked hg hpick k)
    · have := hS.run.pick_inj k r g hk hg
      subst this
      exact hmax x hxo hxu
  refine hS.run.i3 x hxa (fun g hg k hk => ?_)
  rcases mem_of_rank_lt hg with rfl | rfl | rfl
  · have := hS.run.pick_inj k x _ hk hxt
    subst this; exact Nat.le_refl _
  · exact late _ hb k hk
  · exact late _ hc k hk

/-- Distinct agents exposed for `r` lie in distinct blocks. -/
theorem exposed_blk_inj (hS : State P agents goods order Y blk lead up) {r : A}
    (hr : lastOut up order = some r) {x x' : A} (hx : x ∈ exposedL P agents up Y goods r)
    (hx' : x' ∈ exposedL P agents up Y goods r) (he : blk x = blk x') : x = x' :=
  hS.run.lead_unique x (exposed_r hS hr hx).1 x' (exposed_r hS hr hx').1 (exposed_lead hS hr hx)
    (exposed_lead hS hr hx') he

/-- The structure of `k*`: it is exposed for `r`, lies in `r`'s block, and is the only such agent. -/
theorem kstar_spec (hS : State P agents goods order Y blk lead up) {r k : A}
    (hr : lastOut up order = some r) (hk : kstar P agents up Y goods blk r = some k) :
    k ∈ exposedL P agents up Y goods r ∧ blk k = blk r ∧
      ∀ x ∈ exposedL P agents up Y goods r, blk x = blk r → x = k := by
  have hkE := List.mem_of_find?_eq_some hk
  have hkb : blk k = blk r := by simpa using List.find?_some hk
  exact ⟨hkE, hkb, fun x hx hxb => exposed_blk_inj hS hr hx hkE (hxb.trans hkb.symm)⟩

theorem kstar_none {r : A} (hk : kstar P agents up Y goods blk r = none) :
    ∀ x ∈ exposedL P agents up Y goods r, blk x ≠ blk r := by
  intro x hx hxb
  have := List.find?_eq_none.mp hk x hx
  simp [hxb] at this

/-- The terminals `τ(x)` of the agents `x` exposed for `r` outside `r`'s block: distinct terminals other
than `r`, as many as those agents. -/
theorem outside_terminals (hS : State P agents goods order Y blk lead up) {r : A}
    (hr : lastOut up order = some r) :
    let Eo := (exposedL P agents up Y goods r).filter (fun x => decide (blk x ≠ blk r))
    let L := Eo.map (chainEnd P agents up Y order)
    L.Nodup ∧ L.length = Eo.length ∧
      ∀ t ∈ L, IsTerm P agents up Y t ∧ t ≠ r ∧ blk t ≠ blk r := by
  intro Eo L
  have hE : ∀ x ∈ Eo, x ∈ exposedL P agents up Y goods r ∧ blk x ≠ blk r := fun x hx =>
    ⟨(List.mem_filter.mp hx).1, by simpa using (List.mem_filter.mp hx).2⟩
  have hτ : ∀ x ∈ Eo, IsTerm P agents up Y (chainEnd P agents up Y order x) ∧
      blk (chainEnd P agents up Y order x) = blk x := by
    intro x hx
    obtain ⟨hxa, ⟨-, hxu, -⟩, -⟩ := exposed_r hS hr (hE x hx).1
    have := chainEnd_spec (up := up) hS.run hxa hxu
    exact ⟨this.1, this.2.1⟩
  have hEnd : (exposedL P agents up Y goods r).Nodup := hS.agents_nodup.sublist List.filter_sublist
  refine ⟨nodup_map_of_inj (hEnd.sublist List.filter_sublist) (fun x hx y hy he => ?_),
    List.length_map _, fun t ht => ?_⟩
  · have := (hτ x hx).2.symm.trans ((congrArg blk he).trans (hτ y hy).2)
    exact exposed_blk_inj hS hr (hE x hx).1 (hE y hy).1 this
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
    refine ⟨(hτ x hx).1, fun e => (hE x hx).2 ?_, ?_⟩
    · rw [← (hτ x hx).2, e]
    · rw [(hτ x hx).2]; exact (hE x hx).2

/-- Terminals other than `w` have at least one slot when `w` owns the overflow. -/
theorem slots_le {L : List A} (hL : L.Nodup) {w : A} (h : ∀ t ∈ L, IsTerm P agents up Y t ∧ t ≠ w) :
    L.length ≤ (agents.map (slotsExcept (cap P agents up Y) (some w))).sum := by
  refine length_le_sum hL (fun t ht => ⟨(h t ht).1.1, ?_⟩)
  have hne : some w ≠ some t := fun e => (h t ht).2 (Option.some.inj e).symm
  simp only [slotsExcept, hne, ↓reduceIte]
  exact cap_pos (h t ht).1

/-- At most one agent exposed for `r` lies in `r`'s block. -/
theorem exposed_split (hS : State P agents goods order Y blk lead up) {r : A}
    (hr : lastOut up order = some r) :
    (exposedL P agents up Y goods r).length ≤
      ((exposedL P agents up Y goods r).filter (fun x => decide (blk x ≠ blk r))).length + 1 ∧
    (kstar P agents up Y goods blk r ≠ none → (exposedL P agents up Y goods r).length =
      ((exposedL P agents up Y goods r).filter (fun x => decide (blk x ≠ blk r))).length + 1) ∧
    (kstar P agents up Y goods blk r = none → (exposedL P agents up Y goods r).length =
      ((exposedL P agents up Y goods r).filter (fun x => decide (blk x ≠ blk r))).length) := by
  have hEnd : (exposedL P agents up Y goods r).Nodup := hS.agents_nodup.sublist List.filter_sublist
  have hsplit := length_filter_add (exposedL P agents up Y goods r) (fun x => decide (blk x ≠ blk r))
  have hin : ∀ x ∈ (exposedL P agents up Y goods r).filter (fun x => !decide (blk x ≠ blk r)),
      x ∈ exposedL P agents up Y goods r ∧ blk x = blk r := fun x hx =>
    ⟨(List.mem_filter.mp hx).1, by simpa using (List.mem_filter.mp hx).2⟩
  have hle1 : ((exposedL P agents up Y goods r).filter (fun x => !decide (blk x ≠ blk r))).length ≤ 1 := by
    cases hl : (exposedL P agents up Y goods r).filter (fun x => !decide (blk x ≠ blk r)) with
    | nil => simp
    | cons x0 l =>
      have h0 := hin x0 (by rw [hl]; simp)
      refine length_le_one (hEnd.sublist List.filter_sublist |> fun h => hl ▸ h) (y := x0) (fun x hx => ?_)
      have hx' := hin x (by rw [hl]; exact hx)
      exact exposed_blk_inj hS hr hx'.1 h0.1 (hx'.2.trans h0.2.symm)
  refine ⟨by omega, fun hk => ?_, fun hk => ?_⟩
  · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hk
    obtain ⟨hkE, hkb, -⟩ := kstar_spec hS hr hk
    have : 1 ≤ ((exposedL P agents up Y goods r).filter (fun x => !decide (blk x ≠ blk r))).length :=
      List.length_pos_iff_exists_mem.mpr ⟨k, List.mem_filter.mpr ⟨hkE, by simp [hkb]⟩⟩
    omega
  · have : ((exposedL P agents up Y goods r).filter (fun x => !decide (blk x ≠ blk r))).length = 0 := by
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro x hx
      simpa using kstar_none hk x hx
    omega

/-- The counting of Theorem A: `H = hitSet` fits the slots of the terminals other than `r` when two sets `π`
meet, or no agent exposed for `r` lies in `r`'s block, or that agent `k*` comes with a terminal in `r`'s block
other than `r` (the end of a need chain from `k*`). -/
theorem hitSet_fits (hS : State P agents goods order Y blk lead up) {r : A} (hr : lastOut up order = some r)
    (hno : meet P (junkList P agents up Y goods) (exposedL P agents up Y goods r) ≠ none ∨
      kstar P agents up Y goods blk r = none ∨
      ∃ k t, kstar P agents up Y goods blk r = some k ∧ IsTerm P agents up Y t ∧ blk t = blk r ∧ t ≠ r) :
    (hitSet P (junkList P agents up Y goods) (exposedL P agents up Y goods r)).length ≤
      (agents.map (slotsExcept (cap P agents up Y) (some r))).sum := by
  have hEnd : (exposedL P agents up Y goods r).Nodup := hS.agents_nodup.sublist List.filter_sublist
  obtain ⟨hLnd, hLlen, hLt⟩ := outside_terminals hS hr
  obtain ⟨hs1, hs2, hs3⟩ := exposed_split hS hr
  obtain ⟨hl1, hl2⟩ := hitSet_length (P := P) (J := junkList P agents up Y goods)
    (E := exposedL P agents up Y goods r)
  have hout := slots_le hLnd (w := r) (fun t ht => ⟨(hLt t ht).1, (hLt t ht).2.1⟩)
  rcases hno with hm | hk | ⟨k, t, hk, ht, htb, htr⟩
  · have := hl2 hm hEnd
    omega
  · have := hs3 hk
    omega
  · have hLnd' : (((exposedL P agents up Y goods r).filter (fun x => decide (blk x ≠ blk r))).map
        (chainEnd P agents up Y order) ++ [t]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hLnd, by simp, fun a ha b hb e => ?_⟩
      simp only [List.mem_singleton] at hb
      subst hb
      exact (hLt a ha).2.2 (e ▸ htb)
    have := slots_le hLnd' (w := r) (fun t' ht' => by
      rcases List.mem_append.mp ht' with ht' | ht'
      · exact ⟨(hLt t' ht').1, (hLt t' ht').2.1⟩
      · simp only [List.mem_singleton] at ht'; subst ht'; exact ⟨ht, htr⟩)
    simp only [List.length_append, List.length_singleton] at this
    have := hs2 (by simp [hk])
    omega

/-- Lemma 1 applies to `r` with `H = hitSet` as soon as `hitSet` fits. -/
theorem ownerOK_of_fits (hS : State P agents goods order Y blk lead up) {r : A}
    (hr : lastOut up order = some r)
    (hfit : (hitSet P (junkList P agents up Y goods) (exposedL P agents up Y goods r)).length ≤
      (agents.map (slotsExcept (cap P agents up Y) (some r))).sum) :
    OwnerOK P agents up Y goods r
      (hitSet P (junkList P agents up Y goods) (exposedL P agents up Y goods r)) := by
  obtain ⟨hra, hru, hrt⟩ := lastOut_terminal hS hr
  have hEj : ∀ x ∈ exposedL P agents up Y goods r,
      P.b x ∈ junkList P agents up Y goods ∨ P.c x ∈ junkList P agents up Y goods :=
    fun x hx => (exposed_r hS hr hx).2.2
  exact ⟨hra, Or.inr hrt, hitSet_sub hEj, hfit,
    fun x hx hxe => hitSet_hit x (List.mem_filter.mpr ⟨hx, decide_eq_true hxe⟩)⟩

/-- **Theorem A (the owner r), weaker corollary.** After a run of Phase 1 with R1 priority and LB's upgrades, `r`
(the last agent not upgraded) is a valid owner, with `H = hitSet`, unless `Bad` holds. `Bad` is a weaker form of
the bad case (the text's bad case implies it), so the hypothesis `¬ Bad` is stronger and this follows from the
text's Theorem A; the text's Theorem A is `theoremA_invalid` (with `kstar_spec`, `exposed_lead`). -/
theorem theoremA (hS : State P agents goods order Y blk lead up) {r : A}
    (hr : lastOut up order = some r) (hnb : ¬ Bad P agents up Y goods order blk r) :
    OwnerOK P agents up Y goods r
      (hitSet P (junkList P agents up Y goods) (exposedL P agents up Y goods r)) := by
  refine ownerOK_of_fits hS hr (hitSet_fits hS hr ?_)
  by_cases hm : meet P (junkList P agents up Y goods) (exposedL P agents up Y goods r) = none
  · cases hk : kstar P agents up Y goods blk r with
    | none => exact Or.inr (Or.inl rfl)
    | some k =>
      -- not `Bad`: the chain from `k*` ends at a terminal other than `r`
      have hkr : chainEnd P agents up Y order k ≠ r := fun e => hnb ⟨k, hk, e, hm⟩
      obtain ⟨hkE, hkb, -⟩ := kstar_spec hS hr hk
      obtain ⟨hka, ⟨-, hku, -⟩, -⟩ := exposed_r hS hr hkE
      obtain ⟨hτt, hτb, -⟩ := chainEnd_spec (up := up) hS.run hka hku
      exact Or.inr (Or.inr ⟨k, _, rfl, hτt, hτb.trans hkb, hkr⟩)
  · exact Or.inl hm

/-! ### Theorem A with "valid owner" meaning exactly Lemma 1's condition -/

/-- `w` is a valid owner: Lemma 1 applies to `w` with some set `H` of junk goods (it fits the slots of the
other terminals and meets every pair exposed for `w`). -/
def ValidOwner (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (w : A) : Prop :=
  ∃ H, OwnerOK P agents up Y goods w H

/-- If the sets `π_x` are pairwise disjoint, a set of goods meeting each of them in `J` has at least as
many goods as there are sets. -/
theorem length_le_of_hits {J H : List G} {E : List A} (hm : meet P J E = none) (hE : E.Nodup)
    (hhit : ∀ x ∈ E, (P.b x ∈ H ∧ P.b x ∈ J) ∨ (P.c x ∈ H ∧ P.c x ∈ J)) : E.length ≤ H.length := by
  let f : A → G := fun x => if P.b x ∈ H ∧ P.b x ∈ J then P.b x else P.c x
  have hf : ∀ x ∈ E, f x ∈ H ∧ f x ∈ J ∧ (f x = P.b x ∨ f x = P.c x) := by
    intro x hx
    by_cases hb : P.b x ∈ H ∧ P.b x ∈ J
    · have e : f x = P.b x := by simp [f, hb]
      rw [e]; exact ⟨hb.1, hb.2, Or.inl rfl⟩
    · have e : f x = P.c x := by simp only [f]; split <;> simp_all
      rw [e]
      obtain ⟨h1, h2⟩ := (hhit x hx).resolve_left hb
      exact ⟨h1, h2, Or.inr rfl⟩
  have hnd : (E.map f).Nodup := nodup_map_of_inj hE (fun x hx y hy he => by
    refine Classical.byContradiction fun hxy => ?_
    obtain ⟨-, hJ, hx'⟩ := hf x hx
    obtain ⟨-, -, hy'⟩ := hf y hy
    exact meet_none hm x hx y hy hxy (f x) hJ hx' (he ▸ hy'))
  have := length_le_of_subset hnd (fun g hg => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg
    exact (hf x hx).1)
  simpa using this

/-- `r` is a valid owner (Lemma 1's condition, for some `H`) exactly when `H = hitSet` fits. -/
theorem validOwner_iff (hS : State P agents goods order Y blk lead up) {r : A}
    (hr : lastOut up order = some r) :
    ValidOwner P agents up Y goods r ↔
      (hitSet P (junkList P agents up Y goods) (exposedL P agents up Y goods r)).length ≤
        (agents.map (slotsExcept (cap P agents up Y) (some r))).sum := by
  constructor
  · rintro ⟨H, hH⟩
    by_cases hm : meet P (junkList P agents up Y goods) (exposedL P agents up Y goods r) = none
    · -- the sets `π_x` are disjoint: `hitSet` has one good per exposed agent, the least possible
      have hlen : (hitSet P (junkList P agents up Y goods) (exposedL P agents up Y goods r)).length =
          (exposedL P agents up Y goods r).length := by
        unfold hitSet; rw [hm]; simp
      rw [hlen]
      refine Nat.le_trans (length_le_of_hits hm (hS.agents_nodup.sublist List.filter_sublist)
        (fun x hx => ?_)) hH.fit
      obtain ⟨hxa, hxe, -⟩ := exposed_r hS hr hx
      rcases hH.hit x hxa hxe with h | h
      · exact Or.inl ⟨h, hH.sub _ h⟩
      · exact Or.inr ⟨h, hH.sub _ h⟩
    · exact hitSet_fits hS hr (Or.inl hm)
  · intro hfit
    exact ⟨_, ownerOK_of_fits hS hr hfit⟩

/-- The agents of a need chain of listed agents are not upgraded, lie in the block of its first agent, and
are processed after it. -/
theorem isChain_props (hS : State P agents goods order Y blk lead up) :
    ∀ {cur : A} {l : List A}, IsChain P agents up Y cur l → (∀ j ∈ l, j ∈ agents) →
      ∀ j ∈ l, j ∉ up ∧ blk j = blk cur ∧ idx order cur < idx order j
  | _, [], _, _, j, hj => by simp at hj
  | cur, i :: l, ⟨hnx, hc⟩, ha, j, hj => by
    have hi := isNext_run hS.run (ha i (by simp)) hnx
    rcases List.mem_cons.mp hj with rfl | hj
    · exact ⟨(isNext_spec hnx).1, hi.2, hi.1⟩
    · obtain ⟨h1, h2, h3⟩ := isChain_props hS hc (fun x hx => ha x (by simp [hx])) j hj
      exact ⟨h1, h2.trans hi.2, Nat.lt_trans hi.1 h3⟩

/-- A need chain of listed agents has no repeated agent. -/
theorem isChain_nodup (hS : State P agents goods order Y blk lead up) :
    ∀ {cur : A} {l : List A}, IsChain P agents up Y cur l → (∀ j ∈ l, j ∈ agents) → (cur :: l).Nodup
  | cur, [], _, _ => by simp
  | cur, i :: l, hc, ha => by
    have hp := isChain_props hS hc ha
    refine List.nodup_cons.mpr ⟨fun h => ?_, isChain_nodup hS hc.2 (fun x hx => ha x (by simp [hx]))⟩
    have := (hp cur h).2.2
    omega

/-- **Theorem A, as written** (`proofs/lb_last_step.md` §4). If `r` is not a valid owner (no set `H`
satisfies Lemma 1's condition), the bad case holds: `k*` exists and is frozen, the sets `π_x` are pairwise
disjoint, and *every* need chain from `k*` that ends at a terminal ends at `r`. -/
theorem theoremA_invalid (hS : State P agents goods order Y blk lead up) {r : A}
    (hr : lastOut up order = some r) (hinv : ¬ ValidOwner P agents up Y goods r) :
    ∃ k, kstar P agents up Y goods blk r = some k ∧ frozenB P agents up Y k = true ∧
      meet P (junkList P agents up Y goods) (exposedL P agents up Y goods r) = none ∧
      ∀ ch, IsChain P agents up Y k ch → (∀ j ∈ ch, j ∈ agents) →
        frozenB P agents up Y (ch.getLastD k) = false → ch.getLastD k = r := by
  have hnf := fun h => hinv ((validOwner_iff hS hr).mpr (hitSet_fits hS hr h))
  have hm : meet P (junkList P agents up Y goods) (exposedL P agents up Y goods r) = none :=
    Classical.byContradiction fun h => hnf (Or.inl h)
  cases hk : kstar P agents up Y goods blk r with
  | none => exact absurd (Or.inr (Or.inl hk)) hnf
  | some k =>
    obtain ⟨hkE, hkb, -⟩ := kstar_spec hS hr hk
    obtain ⟨hka, ⟨hkr, hku, -⟩, -⟩ := exposed_r hS hr hkE
    -- the end of any complete need chain from `k` is a terminal in `r`'s block, so it must be `r`
    have hall : ∀ ch, IsChain P agents up Y k ch → (∀ j ∈ ch, j ∈ agents) →
        frozenB P agents up Y (ch.getLastD k) = false → ch.getLastD k = r := by
      intro ch hch ha hf
      refine Classical.byContradiction fun hne => hnf (Or.inr (Or.inr ⟨k, ch.getLastD k, hk, ?_, ?_, hne⟩))
      · rcases List.mem_cons.mp (getLastD_mem' ch k) with h | h
        · rw [h]; exact ⟨hka, hku, h ▸ hf⟩
        · exact ⟨ha _ h, (isChain_props hS hch ha _ h).1, hf⟩
      · rcases List.mem_cons.mp (getLastD_mem' ch k) with h | h
        · rw [h]; exact hkb
        · exact (isChain_props hS hch ha _ h).2.1.trans hkb
    refine ⟨k, rfl, ?_, hm, hall⟩
    -- `k` is frozen: otherwise its need chain is empty and ends at `k ≠ r`
    cases hf : frozenB P agents up Y k with
    | true => rfl
    | false =>
      have := hall [] trivial (by simp) (by simpa using hf)
      exact (hkr (by simpa using this)).elim

end theoremA

end LB
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB.lastOut_terminal
#print axioms EFX.LB.chainEnd_spec
#print axioms EFX.LB.exposed_lead
#print axioms EFX.LB.theoremA
#print axioms EFX.LB.validOwner_iff
#print axioms EFX.LB.theoremA_invalid
#print axioms EFX.LB.exposed_blk_inj
#print axioms EFX.LB.kstar_spec
