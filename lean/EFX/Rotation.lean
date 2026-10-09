import EFX.OwnerR

/-!
# Theorem B: the rotation (`proofs/lb_last_step.md` §5)

In the bad case of Theorem A, let `k = k*` and let `k = x₀, x₁, …, x_t = r` be a need chain from `k` to `r`
(any one: `BadCase` takes it as an argument; LB⁺ uses `k :: chainFrom k (after order k)`). The rotation moves
every agent of the chain one step up: `x_i` takes `Y x_{i-1}` (`rotY`), `k` gives up `a k` and takes
`b k`, and `k` is upgraded, so it also holds `c k` (`rotPicks`, `k :: up`). `r`'s pick, if any, is released.

- `Adj cur l p x`: `p` immediately precedes `x` in `cur :: l`; the lemmas `adj_*` and `rotY_adj` describe
  the rotation along any duplicate-free chain.
- `BadCase`: the bad case (`k*` exists, the sets `π_x` are pairwise disjoint) with a need chain from `k*` to
  `r`; `EFX.LB.theoremA_invalid` shows that it holds, for every such chain, whenever `r` is not a valid owner.
- **Theorem B** (`theoremB`): the rotated pre-allocation is valid, and `k` is a valid owner of it (Lemma 1
  applies with `H = hitSet`). Along the way: (b) `NA` only shrinks (`rot_NA`), (d) terminals outside `r`'s
  block survive, (e) the agents exposed for `k` after the rotation were exposed for `r` before, and are not
  `k`, (f) none of them has both `b x`, `c x` in `k`'s new base.
-/

set_option autoImplicit false

namespace EFX
namespace LB

variable {A G : Type} [DecidableEq A] [DecidableEq G]

open Profile

/-! ## Rotating picks along a chain -/

/-- `p` immediately precedes `x` in `cur :: l`. -/
def Adj : A → List A → A → A → Prop
  | _, [], _, _ => False
  | cur, j :: l, p, x => (p = cur ∧ x = j) ∨ Adj j l p x

/-- Each agent of `l` takes the pick of the agent before it in `cur :: l`; the others keep theirs. -/
def rotY (Y : A → Option G) : A → List A → A → Option G
  | _, [], x => Y x
  | cur, j :: l, x => if x = j then Y cur else rotY Y j l x

section adj
variable {cur p x x' p' : A} {l : List A}

omit [DecidableEq A] in
theorem getLastD_mem : ∀ (l : List A) (cur : A), l.getLastD cur ∈ cur :: l
  | [], cur => by simp
  | j :: l, cur => by
    rw [List.getLastD_cons]
    exact List.mem_cons_of_mem _ (getLastD_mem l j)

omit [DecidableEq A] in
theorem adj_mem : ∀ {cur : A} {l : List A}, Adj cur l p x → x ∈ l ∧ (p = cur ∨ p ∈ l)
  | _, [], h => h.elim
  | cur, j :: l, h => by
    rcases h with ⟨rfl, rfl⟩ | h
    · simp
    · obtain ⟨h1, h2⟩ := adj_mem h
      refine ⟨List.mem_cons_of_mem _ h1, Or.inr ?_⟩
      rcases h2 with rfl | h2
      · simp
      · exact List.mem_cons_of_mem _ h2

omit [DecidableEq A] in
theorem adj_exists_pred : ∀ {cur : A} {l : List A}, x ∈ l → ∃ p, Adj cur l p x
  | _, [], h => by simp at h
  | cur, j :: l, h => by
    by_cases hx : x = j
    · exact ⟨cur, Or.inl ⟨rfl, hx⟩⟩
    · obtain ⟨p, hp⟩ := adj_exists_pred (cur := j) ((List.mem_cons.mp h).resolve_left hx)
      exact ⟨p, Or.inr hp⟩

omit [DecidableEq A] in
theorem adj_exists_succ : ∀ {cur : A} {l : List A}, (p = cur ∨ p ∈ l) → p ≠ l.getLastD cur →
    ∃ x, Adj cur l p x
  | cur, [], hp, hne => by
    rcases hp with rfl | hp
    · exact absurd rfl hne
    · simp at hp
  | cur, j :: l, hp, hne => by
    rw [List.getLastD_cons] at hne
    rcases hp with rfl | hp
    · exact ⟨j, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨x, hx⟩ := adj_exists_succ (cur := j) (List.mem_cons.mp hp) hne
      exact ⟨x, Or.inr hx⟩

omit [DecidableEq A] in
theorem adj_not_last : ∀ {cur : A} {l : List A}, (cur :: l).Nodup → Adj cur l p x → p ≠ l.getLastD cur
  | _, [], _, h => h.elim
  | cur, j :: l, hnd, h => by
    rw [List.getLastD_cons]
    rcases h with ⟨rfl, rfl⟩ | h
    · intro e
      exact (List.nodup_cons.mp hnd).1 (e ▸ getLastD_mem l x)
    · exact adj_not_last (List.nodup_cons.mp hnd).2 h

omit [DecidableEq A] in
theorem adj_inj_left : ∀ {cur : A} {l : List A}, (cur :: l).Nodup → Adj cur l p x → Adj cur l p' x →
    p = p'
  | _, [], _, h, _ => h.elim
  | cur, j :: l, hnd, h, h' => by
    have hj : j ∉ l := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
    rcases h with ⟨rfl, rfl⟩ | h <;> rcases h' with ⟨rfl, e⟩ | h'
    · rfl
    · exact absurd (adj_mem h').1 hj
    · subst e; exact absurd (adj_mem h).1 hj
    · exact adj_inj_left (List.nodup_cons.mp hnd).2 h h'

omit [DecidableEq A] in
theorem adj_inj_right : ∀ {cur : A} {l : List A}, (cur :: l).Nodup → Adj cur l p x → Adj cur l p x' →
    x = x'
  | _, [], _, h, _ => h.elim
  | cur, j :: l, hnd, h, h' => by
    have hc : cur ∉ j :: l := (List.nodup_cons.mp hnd).1
    rcases h with ⟨rfl, rfl⟩ | h <;> rcases h' with ⟨e, rfl⟩ | h'
    · rfl
    · exact absurd (by rcases (adj_mem h').2 with e' | e' <;> simp [e']) hc
    · subst e
      exact absurd (by rcases (adj_mem h).2 with e' | e' <;> simp [e']) hc
    · exact adj_inj_right (List.nodup_cons.mp hnd).2 h h'

theorem adj_isNext {P : Profile A G} {agents up : List A} {Y : A → Option G} :
    ∀ {cur : A} {l : List A}, IsChain P agents up Y cur l → Adj cur l p x →
      isNext P agents up Y p x = true
  | _, [], _, h => h.elim
  | cur, j :: l, hc, h => by
    rcases h with ⟨rfl, rfl⟩ | h
    · exact hc.1
    · exact adj_isNext hc.2 h

omit [DecidableEq G] in
theorem rotY_adj {Y : A → Option G} : ∀ {cur : A} {l : List A}, (cur :: l).Nodup → Adj cur l p x →
    rotY Y cur l x = Y p
  | _, [], _, h => h.elim
  | cur, j :: l, hnd, h => by
    rcases h with ⟨rfl, rfl⟩ | h
    · simp [rotY]
    · have hxj : x ≠ j := fun e => (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (e ▸ (adj_mem h).1)
      simp only [rotY, hxj, ↓reduceIte]
      exact rotY_adj (List.nodup_cons.mp hnd).2 h

omit [DecidableEq G] in
theorem rotY_not_mem {Y : A → Option G} : ∀ {cur : A} {l : List A}, x ∉ l → rotY Y cur l x = Y x
  | _, [], _ => rfl
  | cur, j :: l, h => by
    have hxj : x ≠ j := fun e => h (by simp [e])
    simp only [rotY, hxj, ↓reduceIte]
    exact rotY_not_mem (fun h' => h (List.mem_cons_of_mem _ h'))

end adj

/-- The rotated picks: `k` takes `b k`, and each agent of `c` takes the pick of the agent before it in
`k :: c`. -/
def rotPicks (P : Profile A G) (Y : A → Option G) (k : A) (c : List A) (x : A) : Option G :=
  if x = k then some (P.b k) else rotY Y k c x

omit [DecidableEq A] in
theorem upOf_eq_none_iff {P : Profile A G} {up : List A} {g : G} :
    upOf P up g = none ↔ ∀ u ∈ up, P.c u ≠ g := by
  constructor
  · exact fun h => upOf_none h
  · intro h
    cases hu : upOf P up g with
    | none => rfl
    | some u => exact absurd (upOf_some hu).2 (h u (upOf_some hu).1)

omit [DecidableEq A] in
theorem mem_junkList_iff {P : Profile A G} {agents up : List A} {Y : A → Option G} {goods : List G}
    (hpick : ∀ k y, Y k = some y → k ∈ agents) {g : G} :
    g ∈ junkList P agents up Y goods ↔ g ∈ goods ∧ (∀ k, Y k ≠ some g) ∧ ∀ u ∈ up, P.c u ≠ g := by
  rw [mem_junkList, picker_eq_none_iff hpick, upOf_eq_none_iff]

/-! ## The bad case -/

/-- The bad case of Theorem A, with `r`, `k = k*`, and a need chain `k :: ch` from `k` to `r` (of listed
agents): the sets `π_x` of the agents exposed for `r` are pairwise disjoint. -/
structure BadCase (P : Profile A G) (agents : List A) (goods : List G) (order : List A)
    (Y : A → Option G) (blk : A → Nat) (lead : A → Prop) (up : List A) (r k : A) (ch : List A) : Prop where
  state : State P agents goods order Y blk lead up
  hr : lastOut up order = some r
  hk : kstar P agents up Y goods blk r = some k
  hm : meet P (junkList P agents up Y goods) (exposedL P agents up Y goods r) = none
  hch : IsChain P agents up Y k ch
  hcha : ∀ j ∈ ch, j ∈ agents
  hend : ch.getLastD k = r

namespace BadCase
variable {P : Profile A G} {agents : List A} {goods : List G} {order : List A} {Y : A → Option G}
  {blk : A → Nat} {lead : A → Prop} {up : List A} {r k : A} {ch : List A}
  (hB : BadCase P agents goods order Y blk lead up r k ch)

include hB

/-- `W = J ∪ {Y r}`: the goods free for the rotation. -/
theorem r_facts : r ∈ agents ∧ r ∉ up ∧ ∀ y, Y r = some y → ¬ P.NA agents (· ∈ up) Y y :=
  lastOut_terminal hB.state hB.hr

theorem k_facts : k ∈ agents ∧ k ∉ up ∧ Y k = some (P.a k) ∧ k ≠ r ∧ blk k = blk r ∧
    (P.b k ∈ junkList P agents up Y goods ∨ Y r = some (P.b k)) ∧
    (P.c k ∈ junkList P agents up Y goods ∨ Y r = some (P.c k)) ∧
    (P.b k ∈ junkList P agents up Y goods ∨ P.c k ∈ junkList P agents up Y goods) := by
  obtain ⟨hkE, hkb, -⟩ := kstar_spec hB.state hB.hr hB.hk
  obtain ⟨hka, ⟨hkr, hku, hkt, hb, hc⟩, hbc⟩ := exposed_r hB.state hB.hr hkE
  have hru := hB.r_facts.2.1
  rw [inBase_of_not_up hru] at hb hc
  exact ⟨hka, hku, hkt, hkr, hkb, hb, hc, hbc⟩

/-- The chain `k :: ch`: duplicate-free, a need chain of listed agents outside `up` in `k`'s block, ending at
`r`. -/
theorem chain :
    (k :: ch).Nodup ∧ IsChain P agents up Y k ch ∧
    (∀ j ∈ ch, j ∈ agents ∧ j ∉ up ∧ blk j = blk k) ∧ ch.getLastD k = r ∧ r ∈ ch := by
  obtain ⟨-, -, -, hkr, -⟩ := hB.k_facts
  have hp := isChain_props hB.state hB.hch hB.hcha
  refine ⟨isChain_nodup hB.state hB.hch hB.hcha, hB.hch,
    fun j hj => ⟨hB.hcha j hj, (hp j hj).1, (hp j hj).2.1⟩, hB.hend, ?_⟩
  have := getLastD_mem ch k
  rw [hB.hend] at this
  rcases List.mem_cons.mp this with h | h
  · exact absurd h.symm hkr
  · exact h

/-- A good picked by an agent other than `r` is not in `W`. -/
theorem picked_not_W {p : A} {g : G} (hp : Y p = some g) (hpr : p ≠ r) :
    ¬ (g ∈ junkList P agents up Y goods ∨ Y r = some g) := by
  rintro (hg | hg)
  · exact junk_not_picked hg (fun k y hk => (hB.state.run.pick k y hk).1) p hp
  · exact hpr (hB.state.run.pick_inj p r g hp hg)

/-- No good of `W` is in `NA`: junk by (V1), `Y r` by (A1). -/
theorem W_not_NA {g : G} (hg : g ∈ junkList P agents up Y goods ∨ Y r = some g) :
    ¬ P.NA agents (· ∈ up) Y g := by
  rcases hg with hg | hg
  · obtain ⟨hgg, hgp, hgu⟩ := (mem_junkList_iff (fun k y hk => (hB.state.run.pick k y hk).1)).mp hg
    exact hB.state.valid.v1 g hgg hgp hgu
  · exact hB.r_facts.2.2 g hg

/-! ### The rotated picks -/

omit hB [DecidableEq G] in
theorem rot_k : rotPicks P Y k (ch) k = some (P.b k) := by
  simp [rotPicks]

omit hB [DecidableEq G] in
theorem rot_out {x : A} (hxk : x ≠ k) (hxc : x ∉ ch) :
    rotPicks P Y k (ch) x = Y x := by
  simp only [rotPicks, hxk, ↓reduceIte]
  exact rotY_not_mem hxc

theorem rot_in {x : A} (hxc : x ∈ ch) :
    ∃ p, Adj k (ch) p x ∧
      rotPicks P Y k (ch) x = Y p ∧
      isNext P agents up Y p x = true ∧ p ≠ r := by
  obtain ⟨hnd, hch, -, hlast, -⟩ := hB.chain
  obtain ⟨p, hp⟩ := adj_exists_pred (cur := k) hxc
  have hxk : x ≠ k := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hxc)
  refine ⟨p, hp, ?_, adj_isNext hch hp, fun e => adj_not_last hnd hp (e.trans hlast.symm)⟩
  simp only [rotPicks, hxk, ↓reduceIte]
  exact rotY_adj hnd hp

/-- Every rotated pick other than `k`'s is a pick of `Y` by an agent other than `r`. -/
theorem rot_src {x : A} {y : G} (hxk : x ≠ k)
    (h : rotPicks P Y k (ch) x = some y) :
    ∃ p, Y p = some y ∧ p ≠ r := by
  by_cases hxc : x ∈ ch
  · obtain ⟨p, -, hrot, -, hpr⟩ := hB.rot_in hxc
    exact ⟨p, hrot ▸ h, hpr⟩
  · rw [rot_out hxk hxc] at h
    refine ⟨x, h, fun e => hxc (e ▸ hB.chain.2.2.2.2)⟩

/-- Every pick of `Y` other than `r`'s is still a pick after the rotation. -/
theorem rot_keep {p : A} {y : G} (hp : Y p = some y) (hpr : p ≠ r) :
    ∃ x, x ≠ k ∧ rotPicks P Y k (ch) x = some y := by
  obtain ⟨hnd, -, -, hlast, -⟩ := hB.chain
  by_cases hpc : p = k ∨ p ∈ ch
  · obtain ⟨x, hx⟩ := adj_exists_succ hpc (fun e => hpr (e.trans hlast))
    have hxc := (adj_mem hx).1
    have hxk : x ≠ k := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hxc)
    refine ⟨x, hxk, ?_⟩
    simp only [rotPicks, hxk, ↓reduceIte]
    rw [rotY_adj hnd hx, hp]
  · have hpk : p ≠ k := fun e => hpc (Or.inl e)
    have hpc' : p ∉ ch := fun h => hpc (Or.inr h)
    exact ⟨p, hpk, by rw [rot_out hpk hpc', hp]⟩

/-- **(b)** `NA` only shrinks. -/
theorem rot_NA {g : G}
    (h : P.NA agents (· ∈ k :: up) (rotPicks P Y k (ch)) g) :
    P.NA agents (· ∈ up) Y g := by
  obtain ⟨i, hi, hiu, hp⟩ := h
  have hik : i ≠ k := fun e => hiu (by simp [e])
  have hiu' : i ∉ up := fun h => hiu (List.mem_cons_of_mem _ h)
  refine ⟨i, hi, hiu', ?_⟩
  by_cases hic : i ∈ ch
  · obtain ⟨p, -, hrot, hnx, -⟩ := hB.rot_in hic
    obtain ⟨-, y, hy, -, hpy⟩ := isNext_spec hnx
    unfold Profile.Prefers Profile.pickRank at hp hpy ⊢
    rw [hrot, hy] at hp
    simp only at hp
    omega
  · unfold Profile.Prefers Profile.pickRank at hp ⊢
    rw [rot_out hik hic] at hp
    exact hp

theorem rot_pick_inj {x x' : A} {y : G}
    (h : rotPicks P Y k (ch) x = some y)
    (h' : rotPicks P Y k (ch) x' = some y) : x = x' := by
  obtain ⟨hnd, -, -, -, -⟩ := hB.chain
  obtain ⟨-, -, -, -, -, hbW, -, -⟩ := hB.k_facts
  -- `b k` is in `W`, so it is not a pick of `Y` by an agent other than `r`
  have hkb : ∀ z, z ≠ k → rotPicks P Y k (ch) z ≠ some (P.b k) := by
    intro z hzk hz
    obtain ⟨p, hp, hpr⟩ := hB.rot_src hzk hz
    exact hB.picked_not_W hp hpr hbW
  by_cases hxk : x = k <;> by_cases hx'k : x' = k
  · rw [hxk, hx'k]
  · subst hxk; rw [rot_k] at h; cases h; exact absurd h' (hkb x' hx'k)
  · subst hx'k; rw [rot_k] at h'; cases h'; exact absurd h (hkb x hxk)
  · by_cases hxc : x ∈ ch <;>
      by_cases hx'c : x' ∈ ch
    · obtain ⟨p, hp, hrot, -⟩ := hB.rot_in hxc
      obtain ⟨p', hp', hrot', -⟩ := hB.rot_in hx'c
      have := hB.state.run.pick_inj p p' y (hrot ▸ h) (hrot' ▸ h')
      subst this
      exact adj_inj_right hnd hp hp'
    · obtain ⟨p, hp, hrot, -⟩ := hB.rot_in hxc
      rw [rot_out hx'k hx'c] at h'
      have := hB.state.run.pick_inj p x' y (hrot ▸ h) h'
      subst this
      rcases (adj_mem hp).2 with e | e
      · exact absurd e hx'k
      · exact absurd e hx'c
    · obtain ⟨p', hp', hrot', -⟩ := hB.rot_in hx'c
      rw [rot_out hxk hxc] at h
      have := hB.state.run.pick_inj x p' y h (hrot' ▸ h')
      subst this
      rcases (adj_mem hp').2 with e | e
      · exact absurd e hxk
      · exact absurd e hxc
    · rw [rot_out hxk hxc] at h
      rw [rot_out hx'k hx'c] at h'
      exact hB.state.run.pick_inj x x' y h h'

/-- A junk good after the rotation was in `W` before. -/
theorem rot_junk_W {g : G} (hg : g ∈ goods)
    (hn : ∀ x, rotPicks P Y k (ch) x ≠ some g)
    (hu : ∀ u ∈ up, P.c u ≠ g) : g ∈ junkList P agents up Y goods ∨ Y r = some g := by
  by_cases hr : Y r = some g
  · exact Or.inr hr
  · left
    refine (mem_junkList_iff (fun k y hk => (hB.state.run.pick k y hk).1)).mpr ⟨hg, fun p hp => ?_, hu⟩
    have hpr : p ≠ r := fun e => hr (e ▸ hp)
    obtain ⟨x, -, hx⟩ := hB.rot_keep hp hpr
    exact hn x hx

/-- **(a), (c)** The rotated pre-allocation is valid. -/
theorem rot_valid :
    Valid P agents goods (rotPicks P Y k (ch)) (k :: up) := by
  obtain ⟨hnd, -, hcm, -, -⟩ := hB.chain
  obtain ⟨hka, hku, -, -, -, hbW, hcW, -⟩ := hB.k_facts
  have hV := hB.state.valid
  have hwf := hB.state.wf k hka
  -- the `c` of an upgraded agent is not in `W`
  have hcu_W : ∀ u ∈ up, ¬ (P.c u ∈ junkList P agents up Y goods ∨ Y r = some (P.c u)) := by
    rintro u hu (h | h)
    · exact ((mem_junkList_iff (fun k y hk => (hV.pick k y hk).1)).mp h).2.2 u hu rfl
    · exact (hV.up_c u hu).2 r h
  refine ⟨fun x y hx => ?_, fun x x' y h h' => hB.rot_pick_inj h h', fun u hu => ?_, fun u hu => ?_,
    fun u hu => ?_, fun u hu u' hu' e => ?_, fun g hg hn hu hna => ?_, fun u hu => ?_⟩
  · -- `pick`
    by_cases hxk : x = k
    · subst hxk
      rw [rot_k] at hx; cases hx
      exact ⟨hka, hwf.2.1, rank_b_lt P x⟩
    by_cases hxc : x ∈ ch
    · obtain ⟨p, -, hrot, hnx, -⟩ := hB.rot_in hxc
      obtain ⟨-, y', hy', -, hpy⟩ := isNext_spec hnx
      rw [hrot, hy'] at hx
      have e := Option.some.inj hx
      exact ⟨(hcm x hxc).1, e ▸ (hB.state.run.pick p y' hy').2.1, e ▸ rank_lt_three_of_prefers hpy⟩
    · rw [rot_out hxk hxc] at hx
      exact hB.state.run.pick x y hx
  · -- `up_mem`
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hka
    · exact hV.up_mem u hu
  · -- `up_b`
    rcases List.mem_cons.mp hu with rfl | hu
    · exact rot_k
    · have huk : u ≠ k := fun e => hku (e ▸ hu)
      have huc : u ∉ ch := fun h => (hcm u h).2.1 hu
      rw [rot_out huk huc]
      exact hV.up_b u hu
  · -- `up_c`
    rcases List.mem_cons.mp hu with rfl | hu2
    · refine ⟨hwf.2.2.1, fun x hx => ?_⟩
      by_cases hxk : x = u
      · rw [hxk, rot_k] at hx; exact hwf.2.2.2.2.2 (Option.some.inj hx)
      · obtain ⟨p, hp, hpr⟩ := hB.rot_src hxk hx
        exact hB.picked_not_W hp hpr hcW
    · refine ⟨(hV.up_c u hu2).1, fun x hx => ?_⟩
      by_cases hxk : x = k
      · rw [hxk, rot_k] at hx
        have e := Option.some.inj hx
        exact hcu_W u hu2 (e ▸ hbW)
      · obtain ⟨p, hp, -⟩ := hB.rot_src hxk hx
        exact (hV.up_c u hu2).2 p hp
  · -- `up_c_inj`
    rcases List.mem_cons.mp hu with rfl | hu2 <;> rcases List.mem_cons.mp hu' with rfl | hu2'
    · rfl
    · exact absurd (e ▸ hcW) (hcu_W u' hu2')
    · exact absurd (e.symm ▸ hcW) (hcu_W u hu2)
    · exact hV.up_c_inj u hu2 u' hu2' e
  · -- (V1)
    exact hB.W_not_NA (hB.rot_junk_W hg hn (fun u' hu' => hu u' (List.mem_cons_of_mem _ hu')))
      (hB.rot_NA hna)
  · -- (V2)
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ⟨fun h => hB.W_not_NA hbW (hB.rot_NA h), fun h => hB.W_not_NA hcW (hB.rot_NA h)⟩
    · exact ⟨fun h => (hV.v2 u hu).1 (hB.rot_NA h), fun h => (hV.v2 u hu).2 (hB.rot_NA h)⟩

/-- **(d)** A terminal outside `r`'s block is still a terminal after the rotation, with the same slots. -/
theorem rot_term {t : A} (ht : IsTerm P agents up Y t) (hb : blk t ≠ blk r) :
    IsTerm P agents (k :: up) (rotPicks P Y k (ch)) t := by
  obtain ⟨hta, htu, htf⟩ := ht
  obtain ⟨-, -, hcm, -, -⟩ := hB.chain
  obtain ⟨-, -, -, -, hkb, -⟩ := hB.k_facts
  have htk : t ≠ k := fun e => hb (e ▸ hkb)
  have htc : t ∉ ch := fun h => hb ((hcm t h).2.2.trans hkb)
  refine ⟨hta, fun h => (List.mem_cons.mp h).elim htk htu, not_frozen_iff.mpr fun y hy hna => ?_⟩
  rw [rot_out htk htc] at hy
  exact not_frozen_iff.mp htf y hy (hB.rot_NA hna)

/-- **(e)** An agent exposed for `k` after the rotation was exposed for `r` before, and is not `k`. -/
theorem rot_exposed {x : A} (hx : x ∈ agents)
    (h : Exposed P agents (k :: up) (rotPicks P Y k (ch)) goods k x) :
    x ∈ exposedL P agents up Y goods r ∧ x ≠ k := by
  obtain ⟨hxk, hxu, hxa, hb, hc⟩ := h
  have hxu' : x ∉ up := fun h => hxu (List.mem_cons_of_mem _ h)
  obtain ⟨-, -, hcm, -, hrc⟩ := hB.chain
  obtain ⟨hra, hru, hrt⟩ := hB.r_facts
  obtain ⟨-, -, -, -, -, hbW, hcW, -⟩ := hB.k_facts
  have hpick : ∀ k y, Y k = some y → k ∈ agents := fun k y hk => (hB.state.run.pick k y hk).1
  have hpick' : ∀ k' y, rotPicks P Y k (ch) k' = some y →
      k' ∈ agents := fun k' y hk' => (hB.rot_valid.pick k' y hk').1
  -- `b x` and `c x` lie in `W`
  have toW : ∀ g, (g ∈ junkList P agents (k :: up)
        (rotPicks P Y k (ch)) goods ∨
      InBase P (k :: up) (rotPicks P Y k (ch)) k g) →
      (g ∈ junkList P agents up Y goods ∨ Y r = some g) := by
    intro g hg
    rcases hg with hg | hg
    · obtain ⟨hgg, hgp, hgu⟩ := (mem_junkList_iff hpick').mp hg
      exact hB.rot_junk_W hgg hgp (fun u hu => hgu u (List.mem_cons_of_mem _ hu))
    · rcases hg with hg | ⟨-, hg⟩
      · rw [rot_k] at hg; cases hg; exact hbW
      · subst hg; exact hcW
  have hbx := toW _ hb
  have hcx := toW _ hc
  obtain ⟨-, -, -, hab, hac, hbc⟩ := hB.state.wf x hx
  refine ⟨List.mem_filter.mpr ⟨hx, decide_eq_true ?_⟩, hxk⟩
  by_cases hxc : x ∈ ch
  · exfalso
    obtain ⟨p, -, hrot, hnx, -⟩ := hB.rot_in hxc
    obtain ⟨-, y, hy, -, hpy⟩ := isNext_spec hnx
    rw [hrot, hy] at hxa
    cases hxa
    -- `x` ranks `a x` above its pick
    by_cases hxr : x = r
    · subst hxr
      cases hYr : Y x with
      | none =>
        -- `b x` is in `NA`, so picked by another agent: not in `W`
        have hna : P.NA agents (· ∈ up) Y (P.b x) :=
          ⟨x, hx, hxu', by unfold Profile.Prefers Profile.pickRank; rw [hYr]; exact rank_b_lt P x⟩
        obtain ⟨q, hq⟩ := hB.state.valid.na_picked (hB.state.wf x hx).2.1 hna
        have hqx : q ≠ x := fun e => by rw [e, hYr] at hq; cases hq
        exact hB.picked_not_W hq hqx hbx
      | some z =>
        have hz3 := (hB.state.run.pick x z hYr).2.2
        have hza : z ≠ P.a x := fun e => by
          unfold Profile.Prefers Profile.pickRank at hpy; rw [hYr, e] at hpy; simp [Profile.rank] at hpy
        rcases mem_of_rank_lt hz3 with e | e | e
        · exact hza e
        · -- `z = b x`: by (UT) and (A1), `c x` is not junk, and it is not `x`'s pick
          subst e
          have hcj : P.c x ∉ junkList P agents up Y goods := fun hcj =>
            hrt _ hYr (hB.state.ut x hx hxu' hYr hcj)
          rcases hcx with h | h
          · exact hcj h
          · rw [hYr] at h; exact hbc (Option.some.inj h)
        · -- `z = c x`: `b x` is in `NA`, so picked by another agent
          subst e
          have hna : P.NA agents (· ∈ up) Y (P.b x) :=
            ⟨x, hx, hxu', by
              unfold Profile.Prefers Profile.pickRank; rw [hYr]
              simp [Profile.rank, Ne.symm hab, Ne.symm hac, Ne.symm hbc]⟩
          obtain ⟨q, hq⟩ := hB.state.valid.na_picked (hB.state.wf x hx).2.1 hna
          have hqx : q ≠ x := fun e => by rw [e, hYr] at hq; exact hbc (Option.some.inj hq).symm
          exact hB.picked_not_W hq hqx hbx
    · -- `x` is inside the chain: it is frozen, so its pick is `b x` or `c x`, a pick outside `W`
      obtain ⟨hnd, -, -, hlast, -⟩ := hB.chain
      obtain ⟨x', hx'⟩ := adj_exists_succ (cur := k) (Or.inr hxc) (fun e => hxr (e.trans hlast))
      obtain ⟨hff, -⟩ : frozenB P agents up Y x = true ∧ _ := by
        have := adj_isNext hB.chain.2.1 hx'
        unfold isNext at this
        simp only [Bool.and_eq_true] at this
        exact ⟨this.1.1, trivial⟩
      obtain ⟨z, hz, -⟩ := frozenB_iff.mp hff
      have hz3 := (hB.state.run.pick x z hz).2.2
      have hza : z ≠ P.a x := fun e => by
        unfold Profile.Prefers Profile.pickRank at hpy; rw [hz, e] at hpy; simp [Profile.rank] at hpy
      rcases mem_of_rank_lt hz3 with e | e | e
      · exact hza e
      · subst e; exact hB.picked_not_W hz hxr hbx
      · subst e; exact hB.picked_not_W hz hxr hcx
  · -- `x` is off the chain: nothing changed for it
    have hxr : x ≠ r := fun e => hxc (e ▸ hrc)
    rw [rot_out hxk hxc] at hxa
    refine ⟨hxr, hxu', hxa, ?_, ?_⟩
    · rw [inBase_of_not_up hru]; exact hbx
    · rw [inBase_of_not_up hru]; exact hcx

/-- **(f)** No agent exposed for `k` after the rotation has both `b x` and `c x` in `k`'s new base
`{b k, c k}`: one of them is junk. -/
theorem rot_pair {x : A} (hx : x ∈ agents)
    (h : Exposed P agents (k :: up) (rotPicks P Y k (ch)) goods k x) :
    P.b x ∈ junkList P agents (k :: up) (rotPicks P Y k (ch)) goods ∨
    P.c x ∈ junkList P agents (k :: up) (rotPicks P Y k (ch)) goods := by
  obtain ⟨hxE, hxk⟩ := hB.rot_exposed hx h
  obtain ⟨-, -, -, hb, hc⟩ := h
  refine Classical.byContradiction fun hno => ?_
  have hbase : ∀ g, (g ∈ junkList P agents (k :: up)
        (rotPicks P Y k (ch)) goods ∨
      InBase P (k :: up) (rotPicks P Y k (ch)) k g) →
      g ∉ junkList P agents (k :: up) (rotPicks P Y k (ch)) goods →
      g = P.b k ∨ g = P.c k := by
    intro g hg hgj
    rcases hg with hg | hg | ⟨-, hg⟩
    · exact absurd hg hgj
    · rw [rot_k] at hg; exact Or.inl (Option.some.inj hg).symm
    · exact Or.inr hg.symm
  have hbx := hbase _ hb (fun h => hno (Or.inl h))
  have hcx := hbase _ hc (fun h => hno (Or.inr h))
  obtain ⟨-, -, -, -, -, -, -, hkj⟩ := hB.k_facts
  obtain ⟨hkE, -, -⟩ := kstar_spec hB.state hB.hr hB.hk
  obtain ⟨-, -, -, -, -, hbc⟩ := hB.state.wf x hx
  -- the pairs are equal, so `π_x` meets `π_k`
  have hshare : ∀ g, (g = P.b k ∨ g = P.c k) → (g = P.b x ∨ g = P.c x) := by
    intro g hg
    rcases hbx with e1 | e1 <;> rcases hcx with e2 | e2 <;> rcases hg with rfl | rfl
    all_goals first
      | exact Or.inl e1.symm
      | exact Or.inr e2.symm
      | exact absurd (e1.trans e2.symm) hbc
  rcases hkj with hkj | hkj
  · exact meet_none hB.hm x hxE k hkE hxk _ hkj (hshare _ (Or.inl rfl)) (Or.inl rfl)
  · exact meet_none hB.hm x hxE k hkE hxk _ hkj (hshare _ (Or.inr rfl)) (Or.inr rfl)

/-- **(g)** The agents exposed for `k` after the rotation fit the slots of the terminals other than `k`. -/
theorem rot_count :
    (exposedL P agents (k :: up) (rotPicks P Y k (ch)) goods k).length ≤
      (agents.map (slotsExcept (cap P agents (k :: up)
        (rotPicks P Y k (ch))) (some k))).sum := by
  obtain ⟨hLnd, hLlen, hLt⟩ := outside_terminals hB.state hB.hr
  obtain ⟨hkE, hkb, huniq⟩ := kstar_spec hB.state hB.hr hB.hk
  -- `E'_k ⊆ E_r ∖ {k}`, and `E_r ∖ {k}` is `E_r` outside `r`'s block
  have h1 : (exposedL P agents (k :: up) (rotPicks P Y k (ch))
      goods k).length ≤ ((exposedL P agents up Y goods r).filter (fun x => decide (x ≠ k))).length := by
    unfold exposedL
    rw [List.filter_filter, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro x hx hxe
    obtain ⟨hxE, hxk⟩ := hB.rot_exposed hx (of_decide_eq_true hxe)
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hxk, of_decide_eq_true (List.mem_filter.mp hxE).2⟩
  have h2 : (exposedL P agents up Y goods r).filter (fun x => decide (x ≠ k)) =
      (exposedL P agents up Y goods r).filter (fun x => decide (blk x ≠ blk r)) := by
    apply List.filter_congr
    intro x hx
    by_cases hxk : x = k
    · subst hxk; simp [hkb]
    · have : blk x ≠ blk r := fun e => hxk (huniq x hx e)
      simp [hxk, this]
  -- the terminals `τ(x)` outside `r`'s block survive and are not `k`
  have h3 := slots_le (P := P) (agents := agents) (up := k :: up)
    (Y := rotPicks P Y k (ch)) hLnd (w := k) (fun t ht =>
      ⟨hB.rot_term (hLt t ht).1 (hLt t ht).2.2, fun e => (hLt t ht).2.2 (e ▸ hkb)⟩)
  rw [h2] at h1
  rw [List.length_map] at h3
  omega

end BadCase

/-- **Theorem B (rotation).** In the bad case, the rotation along the need chain from `k` to `r` gives a
valid pre-allocation (`k` upgraded, each agent of the chain taking its predecessor's pick), and `k` is a
valid owner of it: Lemma 1 applies with `H = hitSet`. -/
theorem theoremB {P : Profile A G} {agents : List A} {goods : List G} {order : List A}
    {Y : A → Option G} {blk : A → Nat} {lead : A → Prop} {up : List A} {r k : A} {ch : List A}
    (hB : BadCase P agents goods order Y blk lead up r k ch) :
    Valid P agents goods (rotPicks P Y k (ch)) (k :: up) ∧
    OwnerOK P agents (k :: up) (rotPicks P Y k (ch)) goods k
      (hitSet P (junkList P agents (k :: up) (rotPicks P Y k (ch)) goods)
        (exposedL P agents (k :: up) (rotPicks P Y k (ch)) goods k)) := by
  refine ⟨hB.rot_valid, hB.k_facts.1, Or.inl (List.mem_cons_self), hitSet_sub (fun x hx => ?_), ?_,
    fun x hx hxe => hitSet_hit x (List.mem_filter.mpr ⟨hx, decide_eq_true hxe⟩)⟩
  · obtain ⟨hxa, hxe⟩ := List.mem_filter.mp hx
    exact hB.rot_pair hxa (of_decide_eq_true hxe)
  · exact Nat.le_trans hitSet_length.1 hB.rot_count

end LB
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB.BadCase.rot_NA
#print axioms EFX.LB.BadCase.rot_exposed
#print axioms EFX.LB.theoremB
#print axioms EFX.LB.BadCase.rot_valid
#print axioms EFX.LB.BadCase.rot_term
#print axioms EFX.LB.BadCase.rot_pair
#print axioms EFX.LB.BadCase.rot_count
