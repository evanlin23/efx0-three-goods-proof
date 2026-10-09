import EFX.Rankings

/-!
# The draft, and valid pre-allocations with their soundness theorem (`proofs/lb_last_step.md` §2)

The rank-based states of Draft and Exchange (`EFX/K3DE*.lean`) and their soundness theorem, Theorem 1′. They come
from the research repository's construction LB (`proofs/construction.md` §3) and its generalization
(`proofs/lb_last_step.md` §2); only what the formalization of the paper uses is kept here. The rankings are those
of `EFX.Rankings`.

**The draft** (`phase1`, Phase 1 of LB): the agents of a list take, one at a time, their favourite remaining good;
`phase1_spec`: each pick is one of the picker's goods, no good is picked twice, and invariant (I1) holds (a good
that an agent ranks above its pick was picked). `fill` distributes a list of goods over the slots of a list of
agents (`fill_count`, `fill_cover`); `picker`, `upOf`, `frozenB`, `naB` are the lookups.

A pre-allocation consists of picks `Y` (each agent's pick is one of its three goods, or none; picks are
distinct) and a list `up` of upgraded agents (pair holders): each `u ∈ up` picked its `b u` and also holds its
`c u`; the goods `c u` are distinct and nobody's pick. The junk is every other good (`junkList`). The
pre-allocation is *valid* (`Valid`) if (V1) no junk is in `NA` and (V2) `b u`, `c u ∉ NA` for every `u ∈ up`.

An agent outside `up` is *frozen* if its pick is in `NA`, and a *terminal* otherwise; a terminal has one
slot if it has a pick and two if not. A *completion* with an optional owner `o` (`Completion`) gives every
pick to its picker and `c u` to `u`; a frozen agent holds only its pick, an upgraded agent other than `o`
only `b u` and `c u`, and a terminal other than `o` at most its slots beyond its pick. It satisfies the
owner constraint (OC) if no agent `x ∉ up`, `x ≠ o`, with pick `a x`, finds both `b x` and `c x` in `o`'s
bundle.

- `HypNA`, `HypNA.efx0`, `HypNA.length_le_two`: the hypotheses of Theorem 1 of `proofs/construction.md`, with
  (I1) replaced by what its proof uses of it (every good of `NA` is somebody's pick) and an optional owner, and
  the theorem for them.
- `Valid`, `Completion`, `Valid.sound`: **Theorem 1′**. Every completion of a valid pre-allocation that
  satisfies (OC) is EFX₀ for every additive valuation consistent with the rankings (ties allowed), and every
  bundle but the owner's has at most two goods.

As in the written proof, only the envier's own values are used; L5 is not used.
-/

set_option autoImplicit false

namespace EFX
namespace LB

variable {A G : Type} [DecidableEq G]

/-! ## Phase 1: serial dictatorship in a given order -/

/-- `i`'s favourite remaining good: the first of `a i`, `b i`, `c i` still in `pool`. -/
def fav (P : Profile A G) (pool : List G) (i : A) : Option G :=
  if P.a i ∈ pool then some (P.a i) else if P.b i ∈ pool then some (P.b i)
  else if P.c i ∈ pool then some (P.c i) else none

/-- The pool after a pick. -/
def removePick (pool : List G) : Option G → List G
  | none => pool
  | some g => pool.erase g

/-- The rank of `fav`, `3` if none. -/
def favRank (P : Profile A G) (pool : List G) (i : A) : Nat :=
  match fav P pool i with
  | none => 3
  | some y => P.rank i y

theorem fav_some {P : Profile A G} {pool : List G} {i : A} {y : G} (h : fav P pool i = some y) :
    y ∈ pool ∧ P.rank i y < 3 := by
  unfold fav at h
  unfold Profile.rank
  by_cases ha : P.a i ∈ pool <;> by_cases hb : P.b i ∈ pool <;> by_cases hc : P.c i ∈ pool <;>
    simp [ha, hb, hc] at h <;> subst h <;> grind

/-- No good of the pool ranks above the favourite. -/
theorem fav_best (P : Profile A G) (pool : List G) (i : A) :
    ∀ g ∈ pool, ¬ P.rank i g < favRank P pool i := by
  intro g hg hlt
  unfold favRank fav at hlt
  unfold Profile.rank at hlt
  by_cases ha : P.a i ∈ pool <;> by_cases hb : P.b i ∈ pool <;> by_cases hc : P.c i ∈ pool <;>
    simp [ha, hb, hc] at hlt <;> grind

theorem nodup_removePick {pool : List G} (h : pool.Nodup) (p : Option G) :
    (removePick pool p).Nodup := by
  cases p with
  | none => exact h
  | some g => exact h.erase g

theorem mem_removePick {pool : List G} {p : Option G} {g : G} (h : g ∈ removePick pool p) :
    g ∈ pool := by
  cases p with
  | none => exact h
  | some y => exact List.mem_of_mem_erase h

variable [DecidableEq A]

/-- Phase 1: the agents of `order` take, one at a time, their favourite remaining good (or nothing if
none of their goods remains). The result is each agent's pick. -/
def phase1 (P : Profile A G) : List A → List G → A → Option G
  | [], _, _ => none
  | i :: order, pool, k =>
    if k = i then fav P pool i else phase1 P order (removePick pool (fav P pool i)) k

/-- Phase 1 in any order of distinct agents: each pick is a good of the picker taken from the pool,
no good is picked twice, and invariant (I1) holds. -/
theorem phase1_spec (P : Profile A G) :
    ∀ (order : List A) (pool : List G), order.Nodup → pool.Nodup →
      (∀ k y, phase1 P order pool k = some y → k ∈ order ∧ y ∈ pool ∧ P.rank k y < 3) ∧
      (∀ k k' y, phase1 P order pool k = some y → phase1 P order pool k' = some y → k = k') ∧
      (∀ i ∈ order, ∀ g ∈ pool, P.Prefers (phase1 P order pool) i g →
        ∃ k, phase1 P order pool k = some g)
  | [], pool, _, _ => by simp [phase1]
  | i :: order, pool, hord, hpool => by
    have hi : i ∉ order := (List.nodup_cons.mp hord).1
    obtain ⟨ih1, ih2, ih3⟩ :=
      phase1_spec P order (removePick pool (fav P pool i)) (List.nodup_cons.mp hord).2
        (nodup_removePick hpool _)
    have hY : ∀ k, phase1 P (i :: order) pool k =
        if k = i then fav P pool i else phase1 P order (removePick pool (fav P pool i)) k :=
      fun k => rfl
    have hYi : phase1 P order (removePick pool (fav P pool i)) i = none := by
      cases h : phase1 P order (removePick pool (fav P pool i)) i with
      | none => rfl
      | some y => exact absurd (ih1 i y h).1 hi
    -- a pick of a later agent is not `i`'s pick
    have hnot : ∀ k y, fav P pool i = some y →
        phase1 P order (removePick pool (fav P pool i)) k ≠ some y := by
      intro k y hf hk
      have := (ih1 k y hk).2.1
      rw [hf] at this
      exact absurd rfl ((List.Nodup.mem_erase_iff hpool).mp this).1
    refine ⟨fun k y hk => ?_, fun k k' y hk hk' => ?_, fun i' hi' g hg hp => ?_⟩
    · rw [hY] at hk
      by_cases hki : k = i
      · subst hki; simp at hk; exact ⟨by simp, fav_some hk⟩
      · simp [hki] at hk
        obtain ⟨h1, h2, h3⟩ := ih1 k y hk
        exact ⟨by simp [h1], mem_removePick h2, h3⟩
    · rw [hY] at hk hk'
      by_cases hki : k = i <;> by_cases hki' : k' = i
      · rw [hki, hki']
      · simp [hki, hki'] at hk hk'; exact absurd hk' (hnot k' y hk)
      · simp [hki, hki'] at hk hk'; exact absurd hk (hnot k y hk')
      · simp [hki, hki'] at hk hk'; exact ih2 k k' y hk hk'
    · by_cases hii : i' = i
      · subst hii
        apply absurd hp
        have e : P.pickRank (phase1 P (i' :: order) pool) i' = favRank P pool i' := by
          unfold Profile.pickRank favRank; rw [hY]; simp only [↓reduceIte]; cases fav P pool i' <;> rfl
        unfold Profile.Prefers; rw [e]; exact fav_best P pool i' g hg
      · have hi'o : i' ∈ order := by simpa [hii] using hi'
        have hp' : P.Prefers (phase1 P order (removePick pool (fav P pool i))) i' g := by
          unfold Profile.Prefers Profile.pickRank at hp ⊢
          rw [hY] at hp
          simpa [hii] using hp
        by_cases hgf : fav P pool i = some g
        · exact ⟨i, by rw [hY]; simp [hgf]⟩
        · have hg' : g ∈ removePick pool (fav P pool i) := by
            cases hf : fav P pool i with
            | none => exact hg
            | some y =>
              have hyg : g ≠ y := fun e => hgf (by rw [hf, e])
              exact (List.Nodup.mem_erase_iff hpool).mpr ⟨hyg, hg⟩
          obtain ⟨k, hk⟩ := ih3 i' hi'o g hg' hp'
          have hki : k ≠ i := fun e => by rw [e, hYi] at hk; cases hk
          exact ⟨k, by rw [hY]; simp [hki, hk]⟩

/-! ## `NA` as a Boolean -/

/-- `NA` for the upgraded agents `up`, as a Boolean. -/
def naB (P : Profile A G) (agents up : List A) (Y : A → Option G) (g : G) : Bool :=
  agents.any (fun i => !(up.contains i) && decide (P.Prefers Y i g))

theorem naB_iff {P : Profile A G} {agents up : List A} {Y : A → Option G} {g : G} :
    naB P agents up Y g = true ↔ P.NA agents (· ∈ up) Y g := by
  simp [naB, Profile.NA]

/-! ## Pickers, frozen agents, and the placement of the junk -/

/-- The agent of `agents` that picked `g`, if any. -/
def picker (agents : List A) (Y : A → Option G) (g : G) : Option A :=
  agents.find? (fun k => Y k == some g)

/-- The upgraded agent whose `c` is `g`, if any. -/
def upOf (P : Profile A G) (up : List A) (g : G) : Option A :=
  up.find? (fun k => P.c k == g)

/-- `k` is frozen: its pick is in `NA`. -/
def frozenB (P : Profile A G) (agents up : List A) (Y : A → Option G) (k : A) : Bool :=
  match Y k with
  | none => false
  | some y => naB P agents up Y y

/-- Distribute `rest` over the agents of `ks` in order, `s k` goods to `k`: the agent of each good. -/
def fill (s : A → Nat) : List A → List G → G → Option A
  | [], _, _ => none
  | k :: ks, rest, g => if g ∈ rest.take (s k) then some k else fill s ks (rest.drop (s k)) g

/-! ## Lemmas on the placement -/

omit [DecidableEq A] in
theorem length_le_of_subset : ∀ {S T : List G}, S.Nodup → (∀ x ∈ S, x ∈ T) → S.length ≤ T.length
  | [], _, _, _ => by simp
  | x :: S, T, hS, h => by
    have hxT := h x (by simp)
    have ih := length_le_of_subset (T := T.erase x) (List.nodup_cons.mp hS).2 (fun y hy => by
      have hyx : y ≠ x := fun e => (List.nodup_cons.mp hS).1 (e ▸ hy)
      exact (List.mem_erase_of_ne hyx).mpr (h y (by simp [hy])))
    rw [List.length_erase_of_mem hxT] at ih
    have := List.length_pos_of_mem hxT
    simp only [List.length_cons]
    omega

omit [DecidableEq A] in
theorem fill_some {s : A → Nat} : ∀ {ks : List A} {rest : List G} {g : G} {j : A},
    fill s ks rest g = some j → j ∈ ks ∧ g ∈ rest ∧ 0 < s j
  | [], _, _, _, h => by simp [fill] at h
  | k :: ks, rest, g, j, h => by
    unfold fill at h
    split at h
    · rename_i hg
      cases h
      refine ⟨by simp, List.mem_of_mem_take hg, ?_⟩
      exact Nat.pos_of_ne_zero (fun hs => by rw [hs] at hg; simp at hg)
    · obtain ⟨h1, h2, h3⟩ := fill_some h
      exact ⟨List.mem_cons_of_mem k h1, List.mem_of_mem_drop h2, h3⟩

/-- Each agent receives at most its slots. -/
theorem fill_count {s : A → Nat} {j : A} : ∀ {ks : List A} {rest S : List G}, ks.Nodup → S.Nodup →
    (∀ g ∈ S, fill s ks rest g = some j) → S.length ≤ s j
  | [], _, S, _, _, h => by
    cases S with
    | nil => simp
    | cons g _ => have := h g (by simp); simp [fill] at this
  | k :: ks, rest, S, hks, hS, h => by
    by_cases hjk : j = k
    · subst hjk
      have hsub : ∀ g ∈ S, g ∈ rest.take (s j) := by
        intro g hg
        have := h g hg
        unfold fill at this
        split at this
        · assumption
        · exact absurd (fill_some this).1 (List.nodup_cons.mp hks).1
      exact Nat.le_trans (length_le_of_subset hS hsub) (List.length_take_le _ _)
    · apply fill_count (ks := ks) (rest := rest.drop (s k)) (List.nodup_cons.mp hks).2 hS
      intro g hg
      have := h g hg
      unfold fill at this
      split at this
      · cases this; exact absurd rfl hjk
      · exact this

omit [DecidableEq A] in
/-- Every good of `rest` is placed when the slots suffice. -/
theorem fill_cover {s : A → Nat} : ∀ {ks : List A} {rest : List G} {g : G}, g ∈ rest →
    rest.length ≤ (ks.map s).sum → ∃ j, fill s ks rest g = some j
  | [], rest, g, hg, hl => by
    cases rest with
    | nil => simp at hg
    | cons _ _ => simp at hl
  | k :: ks, rest, g, hg, hl => by
    unfold fill
    split
    · exact ⟨k, rfl⟩
    · rename_i hgt
      have hgd : g ∈ rest.drop (s k) := by
        rw [← List.take_append_drop (s k) rest] at hg
        exact (List.mem_append.mp hg).resolve_left hgt
      apply fill_cover hgd
      simp only [List.map_cons, List.sum_cons] at hl
      rw [List.length_drop]
      omega

omit [DecidableEq A] in
theorem picker_some {agents : List A} {Y : A → Option G} {g : G} {k : A}
    (h : picker agents Y g = some k) : k ∈ agents ∧ Y k = some g :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

omit [DecidableEq A] in
theorem picker_none {agents : List A} {Y : A → Option G} {g : G} (h : picker agents Y g = none) :
    ∀ k ∈ agents, Y k ≠ some g := by
  intro k hk hY
  have := List.find?_eq_none.mp h k hk
  simp [hY] at this

omit [DecidableEq A] in
theorem upOf_some {P : Profile A G} {up : List A} {g : G} {k : A} (h : upOf P up g = some k) :
    k ∈ up ∧ P.c k = g :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

omit [DecidableEq A] in
theorem upOf_none {P : Profile A G} {up : List A} {g : G} (h : upOf P up g = none) :
    ∀ k ∈ up, P.c k ≠ g := by
  intro k hk hc
  have := List.find?_eq_none.mp h k hk
  simp [hc] at this

end LB
end EFX

namespace EFX
namespace LB

variable {A G : Type} [DecidableEq A] [DecidableEq G]

open Profile

/-! ## Theorem 1 with (I1) weakened -/

/-- The hypotheses of Theorem 1 (`proofs/construction.md` §3, on LB's output), with (I1) replaced by `na`: every
good of `NA` is somebody's pick. The owner `o` is optional; with `o = none` the slot bounds apply to every agent:
- `pick`: each pick is a good its picker values, and the picker holds it;
- `upgraded`: an agent of `U` picked its `b`, holds its `c`, and its `b` is not in `NA`; unless it is the owner,
  it holds nothing else;
- `frozen`: an agent outside `U` whose pick is in `NA` holds only its pick;
- `slots`: every other agent outside `U` except the owner holds, beyond its pick, at most its slots (1 with a
  pick, 2 without);
- `owner`: if the owner's bundle has more than two goods, it contains `b k` and `c k` of no other agent `k`
  outside `U` that picked its top `a k`. -/
structure HypNA (P : Profile A G) (agents : List A) (goods : List G) (X : G → A) (Y : A → Option G)
    (U : A → Prop) (o : Option A) : Prop where
  pick : ∀ k y, Y k = some y → y ∈ goods ∧ X y = k ∧ P.rank k y < 3
  na : ∀ g ∈ goods, P.NA agents U Y g → ∃ k, Y k = some g
  upgraded : ∀ k ∈ agents, U k → Y k = some (P.b k) ∧ P.c k ∈ goods ∧ X (P.c k) = k ∧
    ¬ P.NA agents U Y (P.b k) ∧ (o ≠ some k → ∀ g ∈ goods, X g = k → g = P.b k ∨ g = P.c k)
  frozen : ∀ j ∈ agents, ¬ U j → ∀ y, Y j = some y → P.NA agents U Y y →
    ∀ g ∈ goods, X g = j → g = y
  slots : ∀ j ∈ agents, o ≠ some j → ¬ U j → (∀ y, Y j = some y → ¬ P.NA agents U Y y) →
    ((bundle goods X j).filter (fun g => Y j ≠ some g)).length ≤ (if Y j = none then 2 else 1)
  owner : ∀ w, o = some w → 2 < (bundle goods X w).length → ∀ k ∈ agents, k ≠ w → ¬ U k →
    Y k = some (P.a k) → ¬ (P.b k ∈ bundle goods X w ∧ P.c k ∈ bundle goods X w)

variable {P : Profile A G} {agents : List A} {goods : List G} {X : G → A} {Y : A → Option G}
  {U : A → Prop}

variable {o : Option A}

/-- Every bundle except the owner's has at most two goods. -/
theorem HypNA.length_le_two (h : HypNA P agents goods X Y U o) (hg : goods.Nodup) :
    ∀ j ∈ agents, o ≠ some j → (bundle goods X j).length ≤ 2 := fun j hj hjo =>
  bundle_length_le_two hg (fun hU => ((h.upgraded j hj hU).2.2.2.2 hjo)) (h.frozen j hj)
    (h.slots j hj hjo)

/-- A good in a bundle of at least two goods is not in `NA`. -/
theorem HypNA.not_NA (h : HypNA P agents goods X Y U o) (hg : goods.Nodup) {j : A} (hj : j ∈ agents)
    (hlen : 2 ≤ (bundle goods X j).length) {x : G} (hx : x ∈ bundle goods X j) :
    ¬ P.NA agents U Y x := by
  intro hna
  obtain ⟨hxg, hXx⟩ := mem_bundle.mp hx
  obtain ⟨k, hk⟩ := h.na x hxg hna
  have hXk := (h.pick k x hk).2.1
  rw [hXx] at hXk
  subst hXk
  by_cases hU : U j
  · obtain ⟨hYb, -, -, hnb, -⟩ := h.upgraded j hj hU
    rw [hYb] at hk
    cases hk
    exact hnb hna
  · have := length_le_one (nodup_bundle hg X j) (y := x)
      (fun g hg' => h.frozen j hj hU x hk hna g (mem_bundle.mp hg').1 (mem_bundle.mp hg').2)
    omega

/-- **Theorem 1, weakened hypotheses.** An allocation satisfying `HypNA` is EFX₀ for every additive
valuation consistent with the rankings. -/
theorem HypNA.efx0 (h : HypNA P agents goods X Y U o) (hg : goods.Nodup) {v : A → G → Nat}
    (hv : P.Consistent agents v) : EFX0L v agents goods X := by
  intro i hi j hj hij g hgj
  have hndj := nodup_bundle hg X j
  have hndi := nodup_bundle hg X i
  -- singletons are never strongly envied
  by_cases hsmall : (bundle goods X j).length ≤ 1
  · have hlen : ((bundle goods X j).erase g).length = 0 := by
      rw [List.length_erase_of_mem hgj]; omega
    rw [List.length_eq_zero_iff.mp hlen]; simp
  have hnotNA : ∀ x ∈ bundle goods X j, ¬ P.NA agents U Y x :=
    fun x hx => h.not_NA hg hj (by omega) hx
  have hle : value v i ((bundle goods X j).erase g) ≤ value v i (bundle goods X j) :=
    value_sublist v i List.erase_sublist
  have hdisj : ∀ x, x ∈ bundle goods X j → x ∉ bundle goods X i := fun x hx hx' =>
    hij ((mem_bundle.mp hx').2.symm.trans (mem_bundle.mp hx).2)
  have e1 := value_eq hv hi hndj
  have e2 := value_eq hv hi hndi
  have ra : P.rank i (P.a i) = 0 := rank_a i
  have rb := rank_b hv hi
  have rc := rank_c hv hi
  obtain ⟨h1, h2, h3, h4, -⟩ := hv i hi
  by_cases hUi : U i
  · -- `i` is upgraded: it holds `b i` and `c i`, worth at least `a i`
    obtain ⟨hYb, hcg, hXc, -, -⟩ := h.upgraded i hi hUi
    have hbi : P.b i ∈ bundle goods X i :=
      mem_bundle.mpr ⟨(h.pick i _ hYb).1, (h.pick i _ hYb).2.1⟩
    have hci : P.c i ∈ bundle goods X i := mem_bundle.mpr ⟨hcg, hXc⟩
    have hbj := fun hb => hdisj _ hb hbi
    have hcj := fun hc => hdisj _ hc hci
    rw [e1] at hle
    rw [e2]
    grind
  -- `i` is not upgraded: the goods it ranks above its pick are in `NA`, so not in `X_j`
  have hnp : ∀ x ∈ bundle goods X j, ¬ P.Prefers Y i x :=
    fun x hx hp => hnotNA x hx ⟨i, hi, hUi, hp⟩
  cases hY : Y i with
  | none =>
    have hn : ∀ x, P.rank i x < 3 → x ∉ bundle goods X j := fun x hx hxj =>
      hnp x hxj (by unfold Prefers pickRank; rw [hY]; exact hx)
    have := hn _ (by omega : P.rank i (P.a i) < 3)
    have := hn _ (by omega : P.rank i (P.b i) < 3)
    have := hn _ (by omega : P.rank i (P.c i) < 3)
    rw [e1] at hle
    grind
  | some y =>
    obtain ⟨hyg, hXy, hry⟩ := h.pick i y hY
    have hyi : y ∈ bundle goods X i := mem_bundle.mpr ⟨hyg, hXy⟩
    have hvy := le_value_of_mem v i hyi
    have hn : ∀ x, P.rank i x < P.rank i y → x ∉ bundle goods X j := fun x hx hxj =>
      hnp x hxj (by unfold Prefers pickRank; rw [hY]; exact hx)
    have hyj := fun hy => hdisj _ hy hyi
    have hy3 : y = P.a i ∨ y = P.b i ∨ y = P.c i := by
      unfold rank at hry; grind
    rcases hy3 with rfl | rfl | rfl
    · -- `i` picked its top `a i`
      by_cases hboth : P.b i ∈ bundle goods X j ∧ P.c i ∈ bundle goods X j
      · by_cases hbig : 2 < (bundle goods X j).length
        · -- then `X_j` is the owner's bundle, and the owner constraint excludes this
          have hjo : o = some j := by
            refine Classical.byContradiction fun hjo => ?_
            have := h.length_le_two hg j hj hjo
            omega
          exact absurd hboth (h.owner j hjo hbig i hi hij hUi hY)
        · -- `X_j = {b i, c i}`: without `g` it is one good, worth at most `a i`
          have hl1 : ((bundle goods X j).erase g).length = 1 := by
            rw [List.length_erase_of_mem hgj]; omega
          obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl1
          rw [hx, value_cons, value_nil]
          have := rank_le hv hi (g := P.a i) (h := x) (by omega)
          omega
      · rw [e1] at hle
        grind
    · have := hn (P.a i) (by omega)
      rw [e1] at hle
      grind
    · have := hn (P.a i) (by omega)
      have := hn (P.b i) (by omega)
      rw [e1] at hle
      grind

/-! ## Valid pre-allocations and completions -/

/-- A valid pre-allocation (`proofs/lb_last_step.md` §2): picks `Y` and upgraded agents `up` with
- `pick`, `pick_inj`: each pick is a good of `goods` that its picker, a listed agent, values; picks are
  distinct;
- `up_mem`, `up_b`, `up_c`, `up_c_inj`: each upgraded agent is listed and picked its `b`; its `c` is a good
  that is nobody's pick; the `c`s of distinct upgraded agents are distinct;
- (V1) `v1`: a junk good (nobody's pick and not the `c` of an upgraded agent) is not in `NA`;
- (V2) `v2`: `b u` and `c u` are not in `NA`, for every upgraded `u`. -/
structure Valid (P : Profile A G) (agents : List A) (goods : List G) (Y : A → Option G) (up : List A) :
    Prop where
  pick : ∀ k y, Y k = some y → k ∈ agents ∧ y ∈ goods ∧ P.rank k y < 3
  pick_inj : ∀ k k' y, Y k = some y → Y k' = some y → k = k'
  up_mem : ∀ u ∈ up, u ∈ agents
  up_b : ∀ u ∈ up, Y u = some (P.b u)
  up_c : ∀ u ∈ up, P.c u ∈ goods ∧ ∀ k, Y k ≠ some (P.c u)
  up_c_inj : ∀ u ∈ up, ∀ u' ∈ up, P.c u = P.c u' → u = u'
  v1 : ∀ g ∈ goods, (∀ k, Y k ≠ some g) → (∀ u ∈ up, P.c u ≠ g) → ¬ P.NA agents (· ∈ up) Y g
  v2 : ∀ u ∈ up, ¬ P.NA agents (· ∈ up) Y (P.b u) ∧ ¬ P.NA agents (· ∈ up) Y (P.c u)

/-- A completion of the pre-allocation `(Y, up)` with optional owner `o`, satisfying the owner constraint:
- `alloc`, `pick`, `upc`: every good goes to a listed agent, every pick to its picker, `c u` to `u`;
- `frozen`: an agent outside `up` whose pick is in `NA` holds only its pick;
- `upOnly`: an upgraded agent other than the owner holds only its `b` and `c`;
- `slots`: a terminal (outside `up`, pick not in `NA`) other than the owner holds at most one good beyond
  its pick, or two if it has none;
- `oc`: the owner constraint (OC). -/
structure Completion (P : Profile A G) (agents : List A) (goods : List G) (Y : A → Option G)
    (up : List A) (o : Option A) (X : G → A) : Prop where
  alloc : ∀ g ∈ goods, X g ∈ agents
  pick : ∀ k y, Y k = some y → X y = k
  upc : ∀ u ∈ up, X (P.c u) = u
  frozen : ∀ j ∈ agents, j ∉ up → ∀ y, Y j = some y → P.NA agents (· ∈ up) Y y →
    ∀ g ∈ goods, X g = j → g = y
  upOnly : ∀ u ∈ up, o ≠ some u → ∀ g ∈ goods, X g = u → g = P.b u ∨ g = P.c u
  slots : ∀ j ∈ agents, o ≠ some j → j ∉ up → (∀ y, Y j = some y → ¬ P.NA agents (· ∈ up) Y y) →
    ((bundle goods X j).filter (fun g => Y j ≠ some g)).length ≤ (if Y j = none then 2 else 1)
  oc : ∀ w, o = some w → ∀ x ∈ agents, x ≠ w → x ∉ up → Y x = some (P.a x) →
    ¬ (P.b x ∈ bundle goods X w ∧ P.c x ∈ bundle goods X w)

variable {up : List A}

omit [DecidableEq A] in
/-- Every good of `NA` is somebody's pick: it is not junk (V1) and not the `c` of an upgraded agent (V2). -/
theorem Valid.na_picked (hV : Valid P agents goods Y up) {g : G} (hg : g ∈ goods)
    (hna : P.NA agents (· ∈ up) Y g) : ∃ k, Y k = some g := by
  refine Classical.byContradiction fun hno => ?_
  have hnp : ∀ k, Y k ≠ some g := fun k hk => hno ⟨k, hk⟩
  by_cases hc : ∃ u ∈ up, P.c u = g
  · obtain ⟨u, hu, rfl⟩ := hc
    exact (hV.v2 u hu).2 hna
  · exact hV.v1 g hg hnp (fun u hu e => hc ⟨u, hu, e⟩) hna

/-- A completion of a valid pre-allocation satisfies `HypNA`. -/
theorem Completion.hypNA (hV : Valid P agents goods Y up) (hC : Completion P agents goods Y up o X) :
    HypNA P agents goods X Y (· ∈ up) o where
  pick := fun k y hk => ⟨(hV.pick k y hk).2.1, hC.pick k y hk, (hV.pick k y hk).2.2⟩
  na := fun _ hg hna => hV.na_picked hg hna
  upgraded := fun k _ hk => ⟨hV.up_b k hk, (hV.up_c k hk).1, hC.upc k hk, (hV.v2 k hk).1,
    hC.upOnly k hk⟩
  frozen := hC.frozen
  slots := hC.slots
  owner := fun w hw _ => hC.oc w hw

/-- **Theorem 1′ (soundness of pre-allocations).** Every completion `X` of a valid pre-allocation that
satisfies the owner constraint is EFX₀ for every additive valuation consistent with the rankings (ties
allowed), and every bundle except the owner's has at most two goods. -/
theorem Valid.sound (hV : Valid P agents goods Y up) (hC : Completion P agents goods Y up o X)
    (hg : goods.Nodup) :
    (∀ v : A → G → Nat, P.Consistent agents v → EFX0L v agents goods X) ∧
    ∀ j ∈ agents, o ≠ some j → (bundle goods X j).length ≤ 2 :=
  ⟨fun _ hv => (hC.hypNA hV).efx0 hg hv, (hC.hypNA hV).length_le_two hg⟩

/-! ## The junk -/

/-- The junk of the pre-allocation `(Y, up)`: the goods that are no listed agent's pick and not the `c` of
an upgraded agent. -/
def junkList (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) : List G :=
  goods.filter (fun g => (picker agents Y g).isNone && (upOf P up g).isNone)

/-- `g` is in the base of `w`: `w`'s pick, or `w`'s `c` if `w` is upgraded. -/
def InBase (P : Profile A G) (up : List A) (Y : A → Option G) (w : A) (g : G) : Prop :=
  Y w = some g ∨ (w ∈ up ∧ P.c w = g)

omit [DecidableEq A] in
theorem mem_junkList {g : G} :
    g ∈ junkList P agents up Y goods ↔ g ∈ goods ∧ picker agents Y g = none ∧ upOf P up g = none := by
  simp [junkList, Option.isNone_iff_eq_none]

end LB
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB.phase1_spec
#print axioms EFX.LB.HypNA.efx0
#print axioms EFX.LB.Valid.sound
