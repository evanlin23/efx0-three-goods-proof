import EFX.K3DEAlgo

/-!
# Draft and Exchange, part 4: when short moves are not enough (Proposition short)

Proposition "when short moves are not enough" of `paper/k3-simple/long.tex` Appendix A (`prop:short`; written source
`k3/simplify/po/potential/NOTES.md`, Lemma 3), over the states of `EFX/K3DE.lean` (a pick map `Y` and a list `up`
of pair holders, `EFX.LB.Valid`). The worked example of §7 and the instances that attain the bounds are in
`EFX/K3DEShortExamples.lean`.

**Definitions.**
- `NeedArc j j'` (an arc of the need digraph `D`, paper Definition need digraph): `j` and `j'` are listed agents
  outside `up`, `j` holds the single good `y` (`Y j = some y`), and `j'` needs it (`P.Prefers Y j' y`).
  `needArcB` decides it.
- `HasNeedCycle`: `D` has a closed walk `j → ⋯ → j` (`Relation.TransGen` of `NeedArc`).
- `PairChain`: a pair chain applies, i.e. some listed agent passes `pairB` (it holds only its top, is not a pair
  holder, and its `b`, `c` are junk); `pairChain_iff`: this is the negation of (P) (`PropP`).
- `OneExposure`: an exchange cycle with exactly one exposure arc: a free agent `o` that holds a good, an agent `x`
  exposed for `o` (`Exposed`), and a walk of need arcs from `x` back to `o`.
- `ShortMove`: one of the three (the paper's "short move").
- `nFree`: `|F|`, the number of listed free agents; `Eset o`: the listed agents exposed for `o` (`E_o`).

**Results.**
- `walk_ends_free` (the first step of the paper's proof): if `D` has no cycle, every walk along need arcs ends at a
  free agent: from every listed agent outside `up` some free agent is reachable (it is the start or the end of a
  walk of need arcs).
- `exposed_walk`: with no short move, the walk from an agent exposed for a free agent `o` that holds a good ends at
  a free agent other than `o`.
- `exposed_disjoint`: under (P), the sets `E_o` of two different agents outside `up` are disjoint (the remark after
  Lemma forced).
- `short_counts`: with no short move (and the hypotheses of the Improvement Lemma), `|F| ≥ 2`, `n ≥ |F|²`,
  `m ≥ n + |F|`, and `n ≥ 6` if `|F| = 2`.
- `prop_short` (**Proposition short**): `|F| ≥ 2`, `n ≥ 6`, `m ≥ 8`; and if `|F| ≥ 3`, then `n ≥ 9` and `m ≥ 12`.
  Here `n = agents.length` and `m = goods.length`.

**Choices where the prose leaves room.**
1. The vertices of `D` are the listed agents outside `up`, so both ends of a need arc are listed and outside `up`.
   `D` has no loops (`needArc_irrefl`), so a closed walk (`HasNeedCycle`) contains a cycle of distinct agents, and a
   walk from `x` to `o` contains a path; a free agent has no out-arc (`needArc_of_free`), so such a walk does not pass
   `o` before its end. The cycle `o → x → ⋯ → o` of `OneExposure` is thus the paper's cycle of `D⁺` with one
   exposure arc. (P) is not part of `OneExposure`: without (P) a pair chain applies anyway.
2. The paper's walk "ends" because `D` is acyclic and finite. Here the walk follows `walkMap` (a free agent stays, an
   agent with an out-arc moves to its out-neighbour `outNb`) for `|V|` steps, `V` the agents outside `up`; by
   pigeonhole (`exists_period`) it then sits on a cycle of `walkMap`, which is a fixed point (a free agent) because
   `D` has no cycle.
3. Counting. `n` and `m` are the lengths of the lists `agents` and `goods`; goods that nobody values may exist and are
   counted in `m`. The bound `m ≥ n + |F|` counts `n` distinct picks (every listed agent picks a good: pair holders
   their `b`, frozen agents a needed good, free agents a good by Lemma empty) and the `≥ |F|` protecting goods of one
   free agent, which are junk and hence nobody's pick. These are distinct members of `goods`, so `goods.Nodup` is
   not needed (and not assumed).
4. `n ≥ |F|²`: the lists `E_o`, `o ∈ F`, are disjoint (`exposed_disjoint`) and each has at least `|H_o| ≥ |F|`
   agents. For `|F| = 2` no free agent is exposed for a free agent (the paper's argument), so `F` and the two sets
   `E_o` give `n ≥ 2 + 2 + 2`.
-/

set_option autoImplicit false

namespace EFX
namespace DE

open LB Profile

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## The need digraph and short moves -/

/-- **A need arc** `j → j'` of the need digraph `D`: `j` and `j'` are listed agents outside `up`, `j` holds the single
good `y`, and `j'` needs `y`. -/
def NeedArc (P : Profile A G) (agents up : List A) (Y : A → Option G) (j j' : A) : Prop :=
  j ∈ agents ∧ j ∉ up ∧ j' ∈ agents ∧ j' ∉ up ∧ ∃ y, Y j = some y ∧ P.Prefers Y j' y

/-- `NeedArc`, as a Boolean. -/
def needArcB (P : Profile A G) (agents up : List A) (Y : A → Option G) (j j' : A) : Bool :=
  agents.contains j && !(up.contains j) && agents.contains j' && !(up.contains j') &&
    (match Y j with
     | none => false
     | some y => decide (P.Prefers Y j' y))

/-- **`D` has a cycle**: a closed walk `j → ⋯ → j` of need arcs. -/
def HasNeedCycle (P : Profile A G) (agents up : List A) (Y : A → Option G) : Prop :=
  ∃ j, Relation.TransGen (NeedArc P agents up Y) j j

/-- **A pair chain applies**: some listed agent holds only its top, is not a pair holder, and its `b` and `c` are
junk (it passes `pairB`). -/
def PairChain (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) : Prop :=
  ∃ x ∈ agents, pairB P agents up Y goods x = true

/-- **An exchange cycle with exactly one exposure arc**: a free agent `o` that holds a good, an agent `x` exposed for
`o` (the exposure arc `o → x`), and a walk of need arcs from `x` back to `o`. -/
def OneExposure (P : Profile A G) (agents : List A) (goods : List G) (Y : A → Option G) (up : List A) : Prop :=
  ∃ o x, Free P agents up Y o ∧ (∃ y, Y o = some y) ∧ Exposed P agents up Y goods o x ∧
    Relation.TransGen (NeedArc P agents up Y) x o

/-- **A short move applies**: a need cycle, a pair chain, or an exchange cycle with exactly one exposure arc. -/
def ShortMove (P : Profile A G) (agents : List A) (goods : List G) (Y : A → Option G) (up : List A) : Prop :=
  HasNeedCycle P agents up Y ∨ PairChain P agents up Y goods ∨ OneExposure P agents goods Y up

/-- `|F|`: the number of listed free agents. -/
def nFree (P : Profile A G) (agents up : List A) (Y : A → Option G) : Nat :=
  (agents.filter (freeB P agents up Y)).length

/-- `E_o`: the listed agents exposed for `o`. -/
def Eset (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (o : A) : List A :=
  agents.filter (expB P agents up Y goods o)

variable {P : Profile A G} {agents : List A} {goods : List G} {Y : A → Option G} {up : List A}

theorem needArcB_iff {j j' : A} : needArcB P agents up Y j j' = true ↔ NeedArc P agents up Y j j' := by
  unfold needArcB NeedArc
  cases hY : Y j with
  | none => simp
  | some y => simp [and_assoc]

instance (P : Profile A G) (agents up : List A) (Y : A → Option G) (j j' : A) :
    Decidable (NeedArc P agents up Y j j') :=
  decidable_of_iff _ needArcB_iff

theorem pairChain_iff : PairChain P agents up Y goods ↔ ¬ PropP P agents up Y goods := by
  constructor
  · rintro ⟨x, hx, hpx⟩ hPP
    obtain ⟨hxu, hxa, hb, hc⟩ := pairB_iff.mp hpx
    exact hPP x hx hxu hxa ⟨hb, hc⟩
  · intro hPP
    refine Classical.byContradiction fun hno => hPP fun x hx hxu hxa hj => hno ⟨x, hx, ?_⟩
    exact pairB_iff.mpr ⟨hxu, hxa, hj.1, hj.2⟩

theorem mem_Eset {o x : A} : x ∈ Eset P agents up Y goods o ↔ Exposed P agents up Y goods o x := by
  unfold Eset
  rw [List.mem_filter, expB_iff]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

theorem mem_free_filter {z : A} : z ∈ agents.filter (freeB P agents up Y) ↔ Free P agents up Y z := by
  rw [List.mem_filter, freeB_iff]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

omit [DecidableEq A] in
/-- `D` has no loops: no agent needs its own good. -/
theorem needArc_irrefl {j : A} : ¬ NeedArc P agents up Y j j := by
  rintro ⟨-, -, -, -, y, hy, hp⟩
  unfold Profile.Prefers Profile.pickRank at hp
  rw [hy] at hp
  exact Nat.lt_irrefl _ hp

omit [DecidableEq A] in
/-- A free agent has no out-arc in `D`: nobody needs its good. -/
theorem needArc_of_free {o j : A} (ho : Free P agents up Y o) : ¬ NeedArc P agents up Y o j := by
  rintro ⟨-, -, hj, hju, y, hy, hp⟩
  exact ho.2.2 y hy ⟨j, hj, hju, hp⟩

omit [DecidableEq A] in
/-- The head of a need arc needs a good, so it does not hold only its top. -/
theorem not_top_of_arc {j f : A} (h : NeedArc P agents up Y j f) : Y f ≠ some (P.a f) := by
  intro hf
  obtain ⟨-, -, -, -, y, -, hp⟩ := h
  unfold Profile.Prefers Profile.pickRank at hp
  simp [hf, rank_a] at hp

omit [DecidableEq A] in
/-- The end of a nonempty walk of need arcs does not hold only its top. -/
theorem not_top_of_reach {x f : A} (h : Relation.TransGen (NeedArc P agents up Y) x f) : Y f ≠ some (P.a f) := by
  cases h with
  | single h => exact not_top_of_arc h
  | tail _ h => exact not_top_of_arc h

/-! ## Walks along need arcs end at free agents -/

/-- **The walk map**: a free agent stays; another agent moves to its out-neighbour in `D` (`outNb`). -/
def walkMap (P : Profile A G) (agents up : List A) (Y : A → Option G) (j : A) : A :=
  if freeB P agents up Y j then j else (outNb P agents up Y j).getD j

/-- On a listed agent outside `up`, the walk map stays at a free agent and follows a need arc otherwise. -/
theorem walkMap_spec {j : A} (hj : j ∈ agents) (hju : j ∉ up) :
    (Free P agents up Y j ∧ walkMap P agents up Y j = j) ∨
      (¬ Free P agents up Y j ∧ NeedArc P agents up Y j (walkMap P agents up Y j)) := by
  by_cases hf : Free P agents up Y j
  · exact Or.inl ⟨hf, by simp [walkMap, freeB_iff.mpr hf]⟩
  · right
    obtain ⟨y, hy, hna⟩ := needed_of_not_free hj hju hf
    obtain ⟨j', hj', h1, h2, h3⟩ := outNb_spec hy hna
    have hfb : freeB P agents up Y j = false := by
      cases h : freeB P agents up Y j with
      | false => rfl
      | true => exact absurd (freeB_iff.mp h) hf
    have e : walkMap P agents up Y j = j' := by simp [walkMap, hfb, hj']
    rw [e]
    exact ⟨hf, hj, hju, h1, h2, y, hy, h3⟩

/-- Following the walk map from a listed agent outside `up` stays among them, along need arcs. -/
theorem walk_reach {s : A} (hs : s ∈ agents) (hsu : s ∉ up) : ∀ i : Nat,
    (iter (walkMap P agents up Y) i s ∈ agents ∧ iter (walkMap P agents up Y) i s ∉ up) ∧
      (s = iter (walkMap P agents up Y) i s ∨
        Relation.TransGen (NeedArc P agents up Y) s (iter (walkMap P agents up Y) i s))
  | 0 => ⟨⟨hs, hsu⟩, Or.inl rfl⟩
  | i + 1 => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := walk_reach hs hsu i
    show (walkMap P agents up Y (iter (walkMap P agents up Y) i s) ∈ agents ∧
        walkMap P agents up Y (iter (walkMap P agents up Y) i s) ∉ up) ∧
      (s = walkMap P agents up Y (iter (walkMap P agents up Y) i s) ∨
        Relation.TransGen (NeedArc P agents up Y) s (walkMap P agents up Y (iter (walkMap P agents up Y) i s)))
    rcases walkMap_spec (P := P) (Y := Y) h1 h2 with ⟨-, he⟩ | ⟨-, ha⟩
    · rw [he]; exact ⟨⟨h1, h2⟩, h3⟩
    · refine ⟨⟨ha.2.2.1, ha.2.2.2.1⟩, Or.inr ?_⟩
      rcases h3 with e | t
      · rw [← e] at ha ⊢; exact .single ha
      · exact t.tail ha

/-- **Walks end at free agents** (the paper's proof of Proposition short, first paragraph): if `D` has no cycle, then
from every listed agent `s` outside `up` a free agent is reachable along need arcs (it is `s`, or the end of a walk
from `s`). -/
theorem walk_ends_free (hNC : ¬ HasNeedCycle P agents up Y) {s : A} (hs : s ∈ agents) (hsu : s ∉ up) :
    ∃ f, Free P agents up Y f ∧ (s = f ∨ Relation.TransGen (NeedArc P agents up Y) s f) := by
  let V := agents.filter (fun k => !(up.contains k))
  have hVm : ∀ k, k ∈ V ↔ k ∈ agents ∧ k ∉ up := by intro k; simp [V]
  have hVσ : ∀ a ∈ V, walkMap P agents up Y a ∈ V := fun a ha => by
    obtain ⟨h1, h2⟩ := (hVm a).mp ha
    rcases walkMap_spec (P := P) (Y := Y) h1 h2 with ⟨-, he⟩ | ⟨-, ha'⟩
    · rw [he]; exact ha
    · exact (hVm _).mpr ⟨ha'.2.2.1, ha'.2.2.2.1⟩
  obtain ⟨k, -, hk⟩ := exists_period (walkMap P agents up Y) hVσ ((hVm s).mpr ⟨hs, hsu⟩) (Nat.le_refl V.length)
  obtain ⟨⟨hp1, hp2⟩, hsp⟩ := walk_reach (P := P) (Y := Y) hs hsu V.length
  by_cases hpf : Free P agents up Y (iter (walkMap P agents up Y) V.length s)
  · exact ⟨_, hpf, hsp⟩
  · exfalso
    obtain ⟨⟨hq1, hq2⟩, hpq⟩ := walk_reach (P := P) (Y := Y) hp1 hp2 k
    have hk' : walkMap P agents up Y (iter (walkMap P agents up Y) k (iter (walkMap P agents up Y) V.length s)) =
        iter (walkMap P agents up Y) V.length s := hk
    rcases walkMap_spec (P := P) (Y := Y) hq1 hq2 with ⟨hqf, he⟩ | ⟨-, ha⟩
    · rw [he] at hk'
      rw [hk'] at hqf
      exact hpf hqf
    · rw [hk'] at ha
      rcases hpq with e | t
      · rw [← e] at ha; exact hNC ⟨_, .single ha⟩
      · exact hNC ⟨_, t.tail ha⟩

/-! ## Exposed agents -/

/-- **The walk from an exposed agent** (the case `|F| = 1` of the paper's proof): with no need cycle and no exchange
cycle with one exposure arc, the walk from an agent `x` exposed for a free agent `o` that holds a good ends at a free
agent other than `o`. -/
theorem exposed_walk (hNC : ¬ HasNeedCycle P agents up Y) (hOE : ¬ OneExposure P agents goods Y up) {o x : A}
    (ho : Free P agents up Y o) (hoy : ∃ y, Y o = some y) (hx : Exposed P agents up Y goods o x) :
    ∃ f, Free P agents up Y f ∧ f ≠ o ∧ (x = f ∨ Relation.TransGen (NeedArc P agents up Y) x f) := by
  obtain ⟨f, hf, hxf⟩ := walk_ends_free hNC hx.1 hx.2.2.1
  refine ⟨f, hf, fun hfo => ?_, hxf⟩
  subst hfo
  rcases hxf with e | t
  · exact hx.2.1 e
  · exact hOE ⟨f, x, hf, hoy, hx, t⟩

omit [DecidableEq A] in
/-- **The sets `E_o` are disjoint** (the remark after the paper's Lemma forced): under (P), no agent is exposed for
two different agents outside `up`. -/
theorem exposed_disjoint (hV : Valid P agents goods Y up) (hWF : WF P agents goods) (hPP : PropP P agents up Y goods)
    {o o' x : A} (ho : o ∉ up) (ho' : o' ∉ up) (hne : o ≠ o') (hx : Exposed P agents up Y goods o x)
    (hx' : Exposed P agents up Y goods o' x) : False := by
  have hbc := (hWF x hx.1).2.2.2.2.2
  rcases (forced_hOf hWF hPP ho hx).2.2 with ⟨hb, hY⟩ | ⟨hc, hY⟩ <;>
    rcases (forced_hOf hWF hPP ho' hx').2.2 with ⟨hb', hY'⟩ | ⟨hc', hY'⟩
  · exact hne (hV.pick_inj o o' _ hY hY')
  · exact hbc (hb.trans hc'.symm)
  · exact hbc (hb'.trans hc.symm)
  · exact hne (hV.pick_inj o o' _ hY hY')

/-- `|H_o| ≤ |E_o|`: each protecting good is the protecting good of an exposed agent. -/
theorem Hset_le_Eset (o : A) : (Hset P agents up Y goods o).length ≤ (Eset P agents up Y goods o).length := by
  have h := length_le_of_subset (nodup_dd ((Eset P agents up Y goods o).map (hOf P agents up Y goods)))
    (fun h hh => mem_dd.mp hh)
  rw [List.length_map] at h
  exact h

/-! ## Counting -/

omit [DecidableEq A] in
/-- Disjoint duplicate-free lists of length at least `k` over a duplicate-free list `os`: their concatenation is
duplicate-free and has at least `k · |os|` members. -/
theorem flatMap_count {B : Type} {E : A → List B} {k : Nat} : ∀ {os : List A}, os.Nodup →
    (∀ o ∈ os, (E o).Nodup ∧ k ≤ (E o).length) →
    (∀ o ∈ os, ∀ o' ∈ os, o ≠ o' → ∀ x ∈ E o, x ∉ E o') →
    (os.flatMap E).Nodup ∧ k * os.length ≤ (os.flatMap E).length
  | [], _, _, _ => by simp
  | o :: os, hnd, hE, hdisj => by
    have hos := List.nodup_cons.mp hnd
    obtain ⟨ih1, ih2⟩ := flatMap_count (E := E) hos.2 (fun o' h => hE o' (List.mem_cons_of_mem _ h))
      (fun a ha b hb hab => hdisj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hab)
    rw [List.flatMap_cons]
    refine ⟨List.nodup_append.mpr ⟨(hE o List.mem_cons_self).1, ih1, fun a ha b hb hab => ?_⟩, ?_⟩
    · obtain ⟨o', ho', hb'⟩ := List.mem_flatMap.mp hb
      subst hab
      have hne : o ≠ o' := fun e => hos.1 (e ▸ ho')
      exact hdisj o List.mem_cons_self o' (List.mem_cons_of_mem _ ho') hne a ha hb'
    · have := (hE o List.mem_cons_self).2
      simp only [List.length_append, List.length_cons, Nat.mul_succ]
      omega

omit [DecidableEq A] in
/-- The picks of a duplicate-free list of agents that all pick are distinct, one per agent. -/
theorem picks_count (hV : Valid P agents goods Y up) : ∀ {l : List A}, l.Nodup → (∀ i ∈ l, ∃ y, Y i = some y) →
    (l.filterMap Y).Nodup ∧ (l.filterMap Y).length = l.length
  | [], _, _ => by simp
  | i :: l, hnd, hh => by
    obtain ⟨y, hy⟩ := hh i List.mem_cons_self
    have hl := List.nodup_cons.mp hnd
    obtain ⟨ih1, ih2⟩ := picks_count hV hl.2 (fun j hj => hh j (List.mem_cons_of_mem _ hj))
    rw [List.filterMap_cons_some hy]
    refine ⟨List.nodup_cons.mpr ⟨fun hm => ?_, ih1⟩, by simp [ih2]⟩
    obtain ⟨j, hj, hjy⟩ := List.mem_filterMap.mp hm
    have := hV.pick_inj i j y hy hjy
    subst this
    exact hl.1 hj

/-- **Every agent holds a good** (the paper's proof, first paragraph): pair holders hold their pair, other agents
outside `F` a needed good, and free agents a good, since one holding nothing would absorb (Lemma empty). -/
theorem holds_good (hV : Valid P agents goods Y up) (hPP : PropP P agents up Y goods)
    (hno : ¬ ∃ o H, Free P agents up Y o ∧ Absorber P agents goods Y up o H) {i : A} (hi : i ∈ agents) :
    ∃ y, Y i = some y := by
  by_cases hiu : i ∈ up
  · exact ⟨_, hV.up_b i hiu⟩
  · by_cases hf : Free P agents up Y i
    · cases hY : Y i with
      | none => exact absurd ⟨i, [], hf, absorber_empty hPP hf hY⟩ hno
      | some y => exact ⟨y, rfl⟩
    · obtain ⟨y, hy, -⟩ := needed_of_not_free hi hiu hf
      exact ⟨y, hy⟩

/-! ## Proposition short -/

/-- **The counts behind Proposition short.** In the core case, let `(Y, up)` be a valid state in which no free agent
is a valid absorber, some agent is not a pair holder, and no short move applies. Then `|F| ≥ 2`, `n ≥ |F|²`,
`m ≥ n + |F|`, and `n ≥ 6` if `|F| = 2`. -/
theorem short_counts (hWF : WF P agents goods) (hV : Valid P agents goods Y up) (hag : agents.Nodup)
    (hno : ¬ ∃ o H, Free P agents up Y o ∧ Absorber P agents goods Y up o H) (hU : ∃ i ∈ agents, i ∉ up)
    (hS : ¬ ShortMove P agents goods Y up) :
    2 ≤ nFree P agents up Y ∧ nFree P agents up Y * nFree P agents up Y ≤ agents.length ∧
      agents.length + nFree P agents up Y ≤ goods.length ∧ (nFree P agents up Y = 2 → 6 ≤ agents.length) := by
  have hNC : ¬ HasNeedCycle P agents up Y := fun h => hS (Or.inl h)
  have hPP : PropP P agents up Y goods := fun x hx hxu hxa hj =>
    hS (Or.inr (Or.inl ⟨x, hx, pairB_iff.mpr ⟨hxu, hxa, hj⟩⟩))
  have hOE : ¬ OneExposure P agents goods Y up := fun h => hS (Or.inr (Or.inr h))
  have hFnd : (agents.filter (freeB P agents up Y)).Nodup := hag.sublist List.filter_sublist
  have hk : nFree P agents up Y = (agents.filter (freeB P agents up Y)).length := rfl
  -- every free agent `o` has `|E_o| ≥ |H_o| ≥ |F|` (Lemmas empty and forced)
  have hcount : ∀ o, Free P agents up Y o → nFree P agents up Y ≤ (Hset P agents up Y goods o).length := by
    intro o ho
    refine Classical.byContradiction fun hlt => hno ⟨o, _, ho, absorber_forced hWF hag hPP ho ?_⟩
    rw [hk] at hlt
    omega
  have hE : ∀ o, Free P agents up Y o → nFree P agents up Y ≤ (Eset P agents up Y goods o).length :=
    fun o ho => Nat.le_trans (hcount o ho) (Hset_le_Eset o)
  have hEnd : ∀ o, (Eset P agents up Y goods o).Nodup := fun o => hag.sublist List.filter_sublist
  -- a free agent exists, and an agent exposed for it
  obtain ⟨s, hs, hsu⟩ := hU
  obtain ⟨f0, hf0, -⟩ := walk_ends_free hNC hs hsu
  have h1 : 1 ≤ nFree P agents up Y := List.length_pos_of_mem (mem_free_filter.mpr hf0)
  obtain ⟨h0, hh0⟩ := List.exists_mem_of_length_pos (Nat.lt_of_lt_of_le h1 (hcount f0 hf0))
  obtain ⟨x0, hx0, -⟩ := mem_Hset.mp hh0
  -- `|F| ≥ 2`: the walk from `x0` ends at a second free agent
  obtain ⟨f1, hf1, hf10, -⟩ := exposed_walk hNC hOE hf0 (holds_good hV hPP hno hf0.1) hx0
  have h2 : 2 ≤ nFree P agents up Y := by
    have := length_le_of_nodup_of_subset (l := [f1, f0]) (m := agents.filter (freeB P agents up Y))
      (by simp [hf10]) (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact mem_free_filter.mpr hf1
        · exact mem_free_filter.mpr hf0)
    rw [hk]
    simpa using this
  -- `n ≥ |F|²`: the disjoint sets `E_o`
  have hdisj : ∀ o ∈ agents.filter (freeB P agents up Y), ∀ o' ∈ agents.filter (freeB P agents up Y), o ≠ o' →
      ∀ x ∈ Eset P agents up Y goods o, x ∉ Eset P agents up Y goods o' := by
    intro o ho o' ho' hne x hx hx'
    exact exposed_disjoint hV hWF hPP (mem_free_filter.mp ho).2.1 (mem_free_filter.mp ho').2.1 hne
      (mem_Eset.mp hx) (mem_Eset.mp hx')
  obtain ⟨hU1, hU2⟩ := flatMap_count (E := Eset P agents up Y goods) (k := nFree P agents up Y) hFnd
    (fun o ho => ⟨hEnd o, hE o (mem_free_filter.mp ho)⟩) hdisj
  have hUsub : ∀ x ∈ (agents.filter (freeB P agents up Y)).flatMap (Eset P agents up Y goods), x ∈ agents := by
    intro x hx
    obtain ⟨o, -, hxo⟩ := List.mem_flatMap.mp hx
    exact (mem_Eset.mp hxo).1
  have hsq : nFree P agents up Y * nFree P agents up Y ≤ agents.length := by
    have := length_le_of_nodup_of_subset hU1 hUsub
    rw [← hk] at hU2
    omega
  -- `m ≥ n + |F|`: the picks and the protecting goods of `f0`
  have hgoods : agents.length + nFree P agents up Y ≤ goods.length := by
    obtain ⟨hp1, hp2⟩ := picks_count hV hag (fun i hi => holds_good hV hPP hno hi)
    have hHj : ∀ h ∈ Hset P agents up Y goods f0, h ∈ junkList P agents up Y goods := by
      intro h hh
      obtain ⟨x, hx, rfl⟩ := mem_Hset.mp hh
      exact (forced_hOf hWF hPP hf0.2.1 hx).1
    have hnd : (agents.filterMap Y ++ Hset P agents up Y goods f0).Nodup := by
      refine List.nodup_append.mpr ⟨hp1, nodup_dd _, fun a ha b hb hab => ?_⟩
      subst hab
      obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp ha
      exact ((junk_iff hV).mp (hHj a hb)).2.1 i hi
    have hsub : ∀ g ∈ agents.filterMap Y ++ Hset P agents up Y goods f0, g ∈ goods := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp hg
        exact (hV.pick i g hi).2.1
      · exact ((junk_iff hV).mp (hHj g hg)).1
    have := length_le_of_subset hnd hsub
    rw [List.length_append, hp2] at this
    have := hcount f0 hf0
    omega
  refine ⟨h2, hsq, hgoods, fun h2eq => ?_⟩
  -- `|F| = 2`: no free agent is exposed for a free agent, so `F` and the two sets `E_o` give `n ≥ 6`
  have hnotF : ∀ o ∈ agents.filter (freeB P agents up Y), ∀ z ∈ Eset P agents up Y goods o,
      z ∉ agents.filter (freeB P agents up Y) := by
    intro o ho z hz hzF
    have ho' := mem_free_filter.mp ho
    have hzE := mem_Eset.mp hz
    have hzf := mem_free_filter.mp hzF
    -- another agent `x` exposed for `o`
    obtain ⟨x, hx, hxz⟩ : ∃ x ∈ Eset P agents up Y goods o, x ≠ z := by
      refine Classical.byContradiction fun hno' => ?_
      have hsub : ∀ x ∈ Eset P agents up Y goods o, x ∈ [z] := fun x hx =>
        List.mem_singleton.mpr (Classical.byContradiction fun hxz => hno' ⟨x, hx, hxz⟩)
      have := length_le_of_nodup_of_subset (hEnd o) hsub
      have := hE o ho'
      simp only [List.length_singleton] at *
      omega
    obtain ⟨f, hf, hfo, hxf⟩ := exposed_walk hNC hOE ho' (holds_good hV hPP hno ho'.1) (mem_Eset.mp hx)
    -- `f = z`: otherwise `o`, `z`, `f` are three free agents
    have hfz : f = z := by
      refine Classical.byContradiction fun hfz => ?_
      have := length_le_of_nodup_of_subset (l := [o, z, f]) (m := agents.filter (freeB P agents up Y))
        (by simp [Ne.symm hzE.2.1, Ne.symm hfo, Ne.symm hfz]) (by
          intro w hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl | rfl
          · exact ho
          · exact hzF
          · exact mem_free_filter.mpr hf)
      simp only [List.length_cons, List.length_nil] at this
      omega
    subst hfz
    rcases hxf with e | t
    · exact hxz e
    · exact not_top_of_reach t hzE.2.2.2.1
  have hall : ((agents.filter (freeB P agents up Y)) ++
      (agents.filter (freeB P agents up Y)).flatMap (Eset P agents up Y goods)).Nodup := by
    refine List.nodup_append.mpr ⟨hFnd, hU1, fun a ha b hb hab => ?_⟩
    subst hab
    obtain ⟨o, ho, hao⟩ := List.mem_flatMap.mp hb
    exact hnotF o ho a hao ha
  have := length_le_of_nodup_of_subset hall (by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (List.mem_filter.mp hx).1
    · exact hUsub x hx)
  rw [List.length_append, ← hk, h2eq] at this
  rw [h2eq] at hU2
  omega

/-- **Proposition short** (`paper/k3-simple/long.tex` Appendix A, "when short moves are not enough"). In the core case, let
`(Y, up)` be a valid state in which no free agent is a valid absorber, some agent is not a pair holder, and no short
move applies (no need cycle, no pair chain, no exchange cycle with exactly one exposure arc). Then `|F| ≥ 2`, `n ≥ 6`
and `m ≥ 8`; if `|F| ≥ 3`, then `n ≥ 9` and `m ≥ 12` (`n = |agents|`, `m = |goods|`, `F` the free agents). -/
theorem prop_short (hWF : WF P agents goods) (hV : Valid P agents goods Y up) (hag : agents.Nodup)
    (hno : ¬ ∃ o H, Free P agents up Y o ∧ Absorber P agents goods Y up o H) (hU : ∃ i ∈ agents, i ∉ up)
    (hS : ¬ ShortMove P agents goods Y up) :
    2 ≤ nFree P agents up Y ∧ 6 ≤ agents.length ∧ 8 ≤ goods.length ∧
      (3 ≤ nFree P agents up Y → 9 ≤ agents.length ∧ 12 ≤ goods.length) := by
  obtain ⟨h2, hsq, hm, h6⟩ := short_counts hWF hV hag hno hU hS
  have h3 : 3 ≤ nFree P agents up Y → 9 ≤ agents.length ∧ 12 ≤ goods.length := fun h3 => by
    have := Nat.mul_le_mul h3 h3
    omega
  by_cases hk : nFree P agents up Y = 2
  · have := h6 hk
    exact ⟨h2, this, by omega, h3⟩
  · have := h3 (by omega)
    exact ⟨h2, by omega, by omega, h3⟩

end DE
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE.needArcB_iff
#print axioms EFX.DE.pairChain_iff
#print axioms EFX.DE.walk_ends_free
#print axioms EFX.DE.exposed_walk
#print axioms EFX.DE.exposed_disjoint
#print axioms EFX.DE.short_counts
#print axioms EFX.DE.prop_short
