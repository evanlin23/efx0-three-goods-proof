import EFX.K3DE

/-!
# Draft and Exchange, part 2: the Improvement Lemma (ledger K3S.PO.LEAN)

The Improvement Lemma of `paper/k3-simple/long.tex` §5 (`k3/simplify/po/hall/NOTES.md`), with Lemma chain and the
finishing test (Lemma `lem:test`): in the core case, a valid state in which no free agent is a valid absorber (no free
agent can finish) and some agent is not a pair holder is Pareto-dominated by a valid state, obtained by one chain or
ring. It is proved for a computable step (`step`), which either stops with a valid absorber or returns the dominating
state, in the order of the three steps of the loop of the paper's Algorithm DE (chain, finish, ring). The names are
those of `EFX/K3DE.lean`: exposed for blocker, protecting good `hOf x` for the leftover good `h_x`, need arcs and
exposure arcs for want and pair arrows, pair chain for chain, (P) (`PropP`) for (NC).

1. **Chain.** (P) fails at some `x` (`pairB`: `x` holds only `a x`, and `b x`, `c x` are junk): the chain from `x`,
   or the ring of want arrows it runs into (Lemma chain).
2. **Finish.** Every agent is a pair holder: the first agent absorbs with `H = ∅` (Theorem soundness, the case where
   every agent holds its pair). Otherwise, the first free agent `o` with `|H_o| ≤ |F| − 1` absorbs with `H = H_o`
   (the finishing test (c), `absorber_forced`). This covers a free agent that holds nothing: under (P) nobody is
   exposed for it (the finishing test (a), `not_exposed_of_none`), so `H_o = ∅` (`Hset_eq_nil`) and it passes the
   count (`count_of_none`); `absorber_empty` is this case.
3. **Ring.** Otherwise every free agent `o` has `|H_o| ≥ |F|`, and so holds a good (`holds_of_count`): greedy
   distinct representatives `q_o ∈ H_o` (`reps`; the paper's distinct leftover goods: `q_o` is the leftover good of
   the first agent exposed for `o` whose good no earlier free agent took, `reps_first_blocker`), the map `σ`
   (`sigmaMap`: a free agent `o ↦ x_o`, that agent; any other agent to the first agent that needs its good), and the
   ring of `σ` (the proof of the Improvement Lemma; with `F = ∅`, a ring of want arrows).

In the chain and ring steps the move is the exchange along the cycle of `σ` through `σⁿ(s)` (`cycleStep`), an
instance of `EFX.DE.exchange`. In the chain step, `σ` sends every free agent to `x`, so the cycle is the chain closed
by its last arc, or a ring of want arrows.

**Results.**
- `step_stop`: a stop returns a valid absorber, free unless every agent is a pair holder; `step_stop_of_none`: under
  (P), if some free agent holds nothing, the step stops.
- `step_next_cycle`: a move is one exchange along an exchange cycle (`EFX.DE.Cycle`: a chain closed by its last arc,
  or a ring); `step_next`: it returns a valid state that Pareto-dominates the state; `step_next_scores`: every agent
  of the cycle gets a strictly higher utility (score), every other agent the same (Lemmas ring and chain, through
  `EFX.DE.exchange_scores`).
- `improvement` (**the Improvement Lemma**), `completable_of_undominated` (**Corollary**, Pareto-optimal states).
- The finishing test: `forced_hOf` ((b): the pair of a blocker `x` is `o`'s good and `h_x`), `absorber_forced`,
  `Hset_le_of_absorber` and `absorber_iff` ((c), both directions: `o` absorbs iff `|H_o| ≤ |F| − 1`, and then with
  `H_o`); `not_exposed_of_none` ((a)), `Hset_eq_nil`, `count_of_none`, `holds_of_count` (a free agent holding
  nothing passes the count) and `absorber_empty` ((c), a free agent holding nothing can finish).
- `find?_Hset`: `H_o` lists the leftover goods in the order of their first exposed agents; `reps_first_blocker`: the
  paper's rule for the distinct leftover goods `q_o` and the blockers `x_o = σ(o)`.

**Choices where the prose leaves room.**
1. The protecting good of an exposed agent `x` is `hOf x`, the one of `b x`, `c x` that is junk; under (P) exactly
   one is (`forced_hOf`), so this is the paper's `h_x`.
2. The paper starts at the first agent outside `U` and follows `σ` until an agent repeats; here the start `s` is the
   same, and `p = σⁿ(s)` with `n = |agents|` lies on the cycle so reached, whose period is found by search (`period`).
   The cycle is `{σʲ p : j < per}`, with predecessor `σ^(per−1)`.
3. In the chain step the paper walks from `x`, each time to the first agent that wants the current agent's good; here
   every free agent points to `x`, so the cycle through `σⁿ(x)` is that chain closed by the arc from its last agent
   back to `x`, or the ring of want arrows it runs into (both moves of `EFX.DE.exchange`).
4. With no free agent, the ring step follows want arrows only (a ring of want arrows).
5. `dd` keeps the first occurrence of each good, so `Hset` lists the goods of `H_o` in the order of their first
   exposed agents in `agents` (`find?_Hset`). The greedy representatives take, for each free agent in the order of
   `agents`, the first good of `H_o` not taken yet: the leftover good of its first exposed agent whose good is not
   taken yet, as in the paper (`reps_first_blocker`). The completion gives the goods of `H = H_o`, in this order, to
   the free agents other than `o` in the order of `agents`.
-/

set_option autoImplicit false

namespace EFX
namespace DE

open LB Profile

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-! ## Computable tests -/

/-- `g` is junk, as a Boolean. -/
def junkB (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (g : G) : Bool :=
  (junkList P agents up Y goods).contains g

/-- (P) fails at `x`: `x` is not a pair holder, holds only its top, and its other two goods are junk. -/
def pairB (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (x : A) : Bool :=
  !(up.contains x) && (Y x == some (P.a x)) && junkB P agents up Y goods (P.b x) &&
    junkB P agents up Y goods (P.c x)

/-- An out-neighbour of `j` in the need digraph: the first listed agent outside `up` that needs `j`'s good. -/
def outNb (P : Profile A G) (agents up : List A) (Y : A → Option G) (j : A) : Option A :=
  match Y j with
  | none => none
  | some y => agents.find? (fun j' => !(up.contains j') && decide (P.Prefers Y j' y))

/-- `g` is in `o`'s holding, as a Boolean (`EFX.LB.InBase`). -/
def inBaseB (P : Profile A G) (up : List A) (Y : A → Option G) (o : A) (g : G) : Bool :=
  (Y o == some g) || (up.contains o && P.c o == g)

/-- Exposure, as a Boolean (`Exposed`). -/
def expB (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (o x : A) : Bool :=
  agents.contains x && (x != o) && !(up.contains x) && (Y x == some (P.a x)) &&
    (junkB P agents up Y goods (P.b x) || inBaseB P up Y o (P.b x)) &&
    (junkB P agents up Y goods (P.c x) || inBaseB P up Y o (P.c x))

/-- The protecting good of an exposed agent: the one of `b x`, `c x` that is junk. -/
def hOf (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (x : A) : G :=
  if junkB P agents up Y goods (P.b x) then P.b x else P.c x

/-- A list without repetitions: each element at its first occurrence, in the order of the list. -/
def dd : List G → List G
  | [] => []
  | x :: l => x :: (dd l).filter (· != x)

/-- `H_o`: the protecting goods of the agents exposed for `o`. -/
def Hset (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (o : A) : List G :=
  dd ((agents.filter (expB P agents up Y goods o)).map (hOf P agents up Y goods))

/-- Greedy distinct representatives: each agent of `os` in turn takes the first good of `Hs o` not used yet. -/
def reps (Hs : A → List G) : List A → List G → List (A × G)
  | [], _ => []
  | o :: os, used =>
    match (Hs o).find? (fun h => !(used.contains h)) with
    | some q => (o, q) :: reps Hs os (q :: used)
    | none => reps Hs os used

/-- The representative of `j`, if any. -/
def repOf : List (A × G) → A → Option G
  | [], _ => none
  | (o, q) :: r, j => if j = o then some q else repOf r j

/-- **The map `σ`.** A frozen agent goes to its out-neighbour (`outNb`: the first agent that needs its good, a want
arrow). A free agent goes to `x` if (P) fails at `x` (`px = some x`), and otherwise to the first agent exposed for it
whose protecting good is its representative (a pair arrow). -/
def sigmaMap (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) (px : Option A)
    (rp : List (A × G)) (j : A) : A :=
  if freeB P agents up Y j then
    match px with
    | some x => x
    | none =>
      match repOf rp j with
      | some q => (agents.find? (fun x => expB P agents up Y goods j x && hOf P agents up Y goods x == q)).getD j
      | none => j
  else (outNb P agents up Y j).getD j

/-- The least `per ∈ [1, n]` with `σ^per p = p` (or `1` if there is none). -/
def period (σ : A → A) (n : Nat) (p : A) : Nat :=
  (((List.range n).find? (fun k => iter σ (k + 1) p == p)).map (· + 1)).getD 1

/-- The orbit `{σʲ p : j < per}`. -/
def onOrbit (σ : A → A) (per : Nat) (p w : A) : Bool :=
  (List.range per).any (fun j => iter σ j p == w)

/-- **The move along the cycle of `σ` through `σⁿ(s)`**, `n = |agents|`: the exchange (`exchY`, `exchUp`) on the
orbit, with predecessor `σ^(per − 1)`. -/
def cycleStep (P : Profile A G) (agents up : List A) (Y : A → Option G) (σ : A → A) (s : A) :
    (A → Option G) × List A :=
  let p := iter σ agents.length s
  let per := period σ agents.length p
  (exchY P agents up Y (onOrbit σ per p) (iter σ (per - 1)), exchUp P agents up Y (onOrbit σ per p) (iter σ (per - 1)))

/-- The outcome of a step: stop with an absorber `o` and its set `H`, or move to a new state. -/
inductive Out (A G : Type) where
  | stop (o : A) (H : List G)
  | next (Y : A → Option G) (up : List A)

/-- **One step of DE** (the body of the loop of the paper's Algorithm DE), in three steps. *Chain*: if (P) fails at
some `x`, move along the cycle of `σ` through `σⁿ(x)`, every free agent sent to `x`. *Finish*: if every agent is a
pair holder, stop with the first agent and `H = ∅`; otherwise, if some free agent `o` has `|H_o| + 1 ≤ |F|`, stop
with the first such `o` and `H = H_o` (this covers a free agent that holds nothing: `count_of_none`). *Ring*:
otherwise move along the cycle of `σ` through `σⁿ(s)`, `s` the first agent outside `up`. `d` is a default agent. -/
def step (P : Profile A G) (agents : List A) (goods : List G) (d : A) (Y : A → Option G) (up : List A) : Out A G :=
  match agents.find? (pairB P agents up Y goods) with
  | some x =>
    let r := cycleStep P agents up Y (sigmaMap P agents up Y goods (some x) []) x
    .next r.1 r.2
  | none =>
    match agents.find? (fun k => !(up.contains k)) with
    | none => .stop (agents.headD d) []
    | some s =>
      let F := agents.filter (freeB P agents up Y)
      match agents.find? (fun o => freeB P agents up Y o &&
          decide ((Hset P agents up Y goods o).length + 1 ≤ F.length)) with
      | some o => .stop o (Hset P agents up Y goods o)
      | none =>
        let r := cycleStep P agents up Y (sigmaMap P agents up Y goods none (reps (Hset P agents up Y goods) F [])) s
        .next r.1 r.2

/-! ## The tests, as propositions -/

variable {P : Profile A G} {agents : List A} {goods : List G} {Y : A → Option G} {up : List A}

omit [DecidableEq A] in
theorem junkB_iff {g : G} : junkB P agents up Y goods g = true ↔ g ∈ junkList P agents up Y goods := by
  simp [junkB]

theorem inBaseB_iff {o : A} {g : G} : inBaseB P up Y o g = true ↔ InBase P up Y o g := by
  simp [inBaseB, InBase]

theorem expB_iff {o x : A} : expB P agents up Y goods o x = true ↔ Exposed P agents up Y goods o x := by
  simp [expB, Exposed, junkB_iff, inBaseB_iff, and_assoc]

theorem pairB_iff {x : A} : pairB P agents up Y goods x = true ↔
    x ∉ up ∧ Y x = some (P.a x) ∧ P.b x ∈ junkList P agents up Y goods ∧ P.c x ∈ junkList P agents up Y goods := by
  simp [pairB, junkB_iff, and_assoc]

/-- **(P)**: no listed agent outside `up` that holds only its top has both other goods in the junk. -/
def PropP (P : Profile A G) (agents up : List A) (Y : A → Option G) (goods : List G) : Prop :=
  ∀ x ∈ agents, x ∉ up → Y x = some (P.a x) →
    ¬ (P.b x ∈ junkList P agents up Y goods ∧ P.c x ∈ junkList P agents up Y goods)

theorem propP_of_find (h : agents.find? (pairB P agents up Y goods) = none) : PropP P agents up Y goods := by
  intro x hx hxu hxa hj
  have := List.find?_eq_none.mp h x hx
  exact this (pairB_iff.mpr ⟨hxu, hxa, hj⟩)

/-! ## Lists without repetitions, `H_o`, counting -/

omit [DecidableEq A] in
theorem mem_dd {g : G} : ∀ {l : List G}, g ∈ dd l ↔ g ∈ l
  | [] => by simp [dd]
  | x :: l => by
    have ih := @mem_dd g l
    simp only [dd, List.mem_cons, List.mem_filter, ih, bne_iff_ne, ne_eq]
    by_cases h : g = x <;> simp [h]

omit [DecidableEq A] in
theorem nodup_dd : ∀ l : List G, (dd l).Nodup
  | [] => by simp [dd]
  | x :: l => by
    simp only [dd]
    exact List.nodup_cons.mpr ⟨by simp, (nodup_dd l).sublist List.filter_sublist⟩

omit [DecidableEq A] in
/-- **`dd` keeps first occurrences**: the first element of `dd l` with a property is the first element of `l` with it.
-/
theorem find?_dd (p : G → Bool) : ∀ l : List G, (dd l).find? p = l.find? p
  | [] => by simp [dd]
  | x :: l => by
    simp only [dd, List.find?_cons]
    cases hp : p x with
    | true => rfl
    | false =>
      simp only
      rw [List.find?_filter, ← find?_dd p l]
      congr 1
      funext g
      by_cases h : g = x
      · subst h; simp [hp]
      · simp [h]

theorem mem_Hset {o : A} {h : G} : h ∈ Hset P agents up Y goods o ↔
    ∃ x, Exposed P agents up Y goods o x ∧ hOf P agents up Y goods x = h := by
  unfold Hset
  rw [mem_dd]
  simp only [List.mem_map, List.mem_filter, expB_iff]
  constructor
  · rintro ⟨x, ⟨-, hx⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, ⟨hx.1, hx⟩, rfl⟩

/-- **`H_o` lists the goods in the order of their first exposed agents**: the first good of `H_o` with a property
is the protecting good of the first agent (in the order of `agents`) exposed for `o` whose protecting good has it. -/
theorem find?_Hset (o : A) (p : G → Bool) :
    (Hset P agents up Y goods o).find? p =
      (agents.find? (fun x => expB P agents up Y goods o x && p (hOf P agents up Y goods x))).map
        (hOf P agents up Y goods) := by
  unfold Hset
  rw [find?_dd, List.find?_map, List.find?_filter]
  congr 2
  funext x
  cases expB P agents up Y goods o x <;> simp

omit [DecidableEq G] in
/-- Removing one member `o` with `p o` from a duplicate-free list removes one element from its filter. -/
theorem length_filter_erase (p : A → Bool) {o : A} : ∀ {l : List A}, l.Nodup → o ∈ l → p o = true →
    (l.filter p).length = (l.filter (fun k => k != o && p k)).length + 1
  | [], _, h, _ => by simp at h
  | k :: l, hnd, hmem, hpo => by
    have hkl := List.nodup_cons.mp hnd
    by_cases hko : k = o
    · subst hko
      have hcongr : l.filter (fun k' => k' != k && p k') = l.filter p :=
        List.filter_congr fun k' hk' => by
          have : k' ≠ k := fun e => hkl.1 (e ▸ hk')
          simp [this]
      simp [hpo, hcongr]
    · have hol : o ∈ l := by
        rcases List.mem_cons.mp hmem with e | h
        · exact absurd e.symm hko
        · exact h
      have ih := length_filter_erase p hkl.2 hol hpo
      by_cases hpk : p k = true
      · simp [hpk, hko, ih]
      · simp [hpk, ih]

/-- `|F| = |F ∖ {o}| + 1` for a free `o`. -/
theorem nFree_eq (hag : agents.Nodup) {o : A} (ho : Free P agents up Y o) :
    (agents.filter (freeB P agents up Y)).length = nFreeExcept P agents up Y o + 1 :=
  length_filter_erase _ hag ho.1 (freeB_iff.mpr ho)

/-! ## Greedy distinct representatives -/

/-- **Distinct representatives** (the step "distinct leftover goods" of the proof of the Improvement Lemma): if each
agent of `os` has at least `|used| + |os|` goods in `Hs o`, without repetitions, each receives a good of `Hs o`
outside `used`, and different agents receive different goods. -/
theorem reps_spec (Hs : A → List G) : ∀ (os : List A) (used : List G), os.Nodup →
    (∀ o ∈ os, (Hs o).Nodup ∧ used.length + os.length ≤ (Hs o).length) →
    (∀ o ∈ os, ∃ q, repOf (reps Hs os used) o = some q ∧ q ∈ Hs o ∧ q ∉ used) ∧
    (∀ o ∈ os, ∀ o' ∈ os, o ≠ o' → ∀ q q', repOf (reps Hs os used) o = some q →
      repOf (reps Hs os used) o' = some q' → q ≠ q')
  | [], _, _, _ => by simp
  | o :: os, used, hnd, hlen => by
    obtain ⟨hHo, hl⟩ := hlen o (by simp)
    have hex : ∃ h ∈ Hs o, h ∉ used := by
      refine Classical.byContradiction fun hno => ?_
      have hsub : ∀ h ∈ Hs o, h ∈ used := fun h hh => Classical.byContradiction fun hu => hno ⟨h, hh, hu⟩
      have := length_le_of_subset hHo hsub
      simp only [List.length_cons] at hl
      omega
    have hos := List.nodup_cons.mp hnd
    cases hf : (Hs o).find? (fun h => !(used.contains h)) with
    | none =>
      exfalso
      obtain ⟨h, hh, hu⟩ := hex
      have := List.find?_eq_none.mp hf h hh
      simp [hu] at this
    | some q =>
      have hq := List.find?_some hf
      have hqm := List.mem_of_find?_eq_some hf
      have hqu : q ∉ used := by simpa using hq
      obtain ⟨ih1, ih2⟩ := reps_spec Hs os (q :: used) hos.2 (fun o' ho' => by
        obtain ⟨h1, h2⟩ := hlen o' (List.mem_cons_of_mem _ ho')
        refine ⟨h1, ?_⟩
        simp only [List.length_cons] at h2 ⊢
        omega)
      have hreps : reps Hs (o :: os) used = (o, q) :: reps Hs os (q :: used) := by
        rw [reps.eq_2, hf]
      rw [hreps]
      have hro : repOf ((o, q) :: reps Hs os (q :: used)) o = some q := by simp [repOf]
      have hro' : ∀ o' ∈ os, repOf ((o, q) :: reps Hs os (q :: used)) o' = repOf (reps Hs os (q :: used)) o' := by
        intro o' ho'
        have : o' ≠ o := fun e => hos.1 (e ▸ ho')
        simp [repOf, this]
      refine ⟨fun o' ho' => ?_, fun o1 h1 o2 h2 hne q1 q2 hq1 hq2 => ?_⟩
      · rcases List.mem_cons.mp ho' with rfl | ho'
        · exact ⟨q, hro, hqm, hqu⟩
        · obtain ⟨q', h1, h2, h3⟩ := ih1 o' ho'
          exact ⟨q', by rw [hro' o' ho']; exact h1, h2, fun h => h3 (List.mem_cons_of_mem _ h)⟩
      · rcases List.mem_cons.mp h1 with rfl | h1' <;> rcases List.mem_cons.mp h2 with rfl | h2'
        · exact absurd rfl hne
        · rw [hro] at hq1
          cases hq1
          rw [hro' o2 h2'] at hq2
          obtain ⟨q', h1', -, h3'⟩ := ih1 o2 h2'
          rw [h1'] at hq2
          cases hq2
          exact fun e => h3' (e ▸ List.mem_cons_self)
        · rw [hro] at hq2
          cases hq2
          rw [hro' o1 h1'] at hq1
          obtain ⟨q', h1'', -, h3'⟩ := ih1 o1 h1'
          rw [h1''] at hq1
          cases hq1
          exact fun e => h3' (e.symm ▸ List.mem_cons_self)
        · rw [hro' o1 h1'] at hq1
          rw [hro' o2 h2'] at hq2
          exact ih2 o1 h1' o2 h2' hne q1 q2 hq1 hq2

/-- Only a listed agent has a representative. -/
theorem mem_of_repOf_reps (Hs : A → List G) : ∀ (os : List A) (used : List G) {o : A} {q : G},
    repOf (reps Hs os used) o = some q → o ∈ os
  | [], _, _, _, h => by simp [reps, repOf] at h
  | o' :: os, used, o, q, h => by
    rw [reps.eq_2] at h
    split at h
    · simp only [repOf] at h
      split at h
      · rename_i e; rw [e]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_of_repOf_reps Hs os _ h)
    · exact List.mem_cons_of_mem _ (mem_of_repOf_reps Hs os _ h)

/-- **The greedy rule**: in `reps Hs (os₁ ++ o :: os₂) used`, the representative of `o`, if any, is the first good of
`Hs o` outside `U`, where `U` holds the goods of `used` and the representatives of the agents of `os₁` (the agents
before `o`). -/
theorem repOf_reps_append (Hs : A → List G) {o : A} {q : G} : ∀ (os1 os2 : List A) (used : List G),
    (os1 ++ o :: os2).Nodup → repOf (reps Hs (os1 ++ o :: os2) used) o = some q →
    ∃ U : List G, (∀ h, h ∈ U ↔ h ∈ used ∨ ∃ o' ∈ os1, repOf (reps Hs (os1 ++ o :: os2) used) o' = some h) ∧
      (Hs o).find? (fun h => !(U.contains h)) = some q
  | [], os2, used, hnd, h => by
    refine ⟨used, fun h => by simp, ?_⟩
    simp only [List.nil_append] at h hnd
    rw [reps.eq_2] at h
    split at h
    · rename_i q' hq'
      simp only [repOf, ite_true, Option.some.injEq] at h
      rw [hq', h]
    · exact absurd (mem_of_repOf_reps Hs os2 used h) (List.nodup_cons.mp hnd).1
  | o1 :: os1, os2, used, hnd, h => by
    have hnd1 := List.nodup_cons.mp (List.cons_append ▸ hnd : (o1 :: (os1 ++ o :: os2)).Nodup)
    have ho1 : o ≠ o1 := fun e => hnd1.1 (by rw [e]; exact List.mem_append_right _ List.mem_cons_self)
    cases hf : (Hs o1).find? (fun h => !(used.contains h)) with
    | none =>
      have e : reps Hs (o1 :: os1 ++ o :: os2) used = reps Hs (os1 ++ o :: os2) used := by
        rw [List.cons_append, reps.eq_2, hf]
      rw [e] at h ⊢
      obtain ⟨U, hU, hq⟩ := repOf_reps_append Hs os1 os2 used hnd1.2 h
      refine ⟨U, fun g => ?_, hq⟩
      rw [hU g]
      constructor
      · rintro (h | ⟨o', ho', h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨o', List.mem_cons_of_mem _ ho', h⟩
      · rintro (h | ⟨o', ho', h⟩)
        · exact Or.inl h
        · rcases List.mem_cons.mp ho' with rfl | ho'
          · exact absurd (mem_of_repOf_reps Hs _ used h) hnd1.1
          · exact Or.inr ⟨o', ho', h⟩
    | some q1 =>
      have e : reps Hs (o1 :: os1 ++ o :: os2) used = (o1, q1) :: reps Hs (os1 ++ o :: os2) (q1 :: used) := by
        rw [List.cons_append, reps.eq_2, hf]
      rw [e] at h ⊢
      have hr : ∀ o', o' ≠ o1 → repOf ((o1, q1) :: reps Hs (os1 ++ o :: os2) (q1 :: used)) o' =
          repOf (reps Hs (os1 ++ o :: os2) (q1 :: used)) o' := fun o' h' => by simp [repOf, h']
      have hr1 : repOf ((o1, q1) :: reps Hs (os1 ++ o :: os2) (q1 :: used)) o1 = some q1 := by simp [repOf]
      rw [hr o ho1] at h
      obtain ⟨U, hU, hq⟩ := repOf_reps_append Hs os1 os2 (q1 :: used) hnd1.2 h
      refine ⟨U, fun g => ?_, hq⟩
      rw [hU g, List.mem_cons]
      have hne : ∀ o' ∈ os1, o' ≠ o1 := fun o' h' e => hnd1.1 (e ▸ List.mem_append_left _ h')
      constructor
      · rintro ((rfl | h) | ⟨o', ho', h⟩)
        · exact Or.inr ⟨o1, List.mem_cons_self, hr1⟩
        · exact Or.inl h
        · exact Or.inr ⟨o', List.mem_cons_of_mem _ ho', by rw [hr o' (hne o' ho')]; exact h⟩
      · rintro (h | ⟨o', ho', h⟩)
        · exact Or.inl (Or.inr h)
        · rcases List.mem_cons.mp ho' with rfl | ho'
          · rw [hr1] at h; cases h; exact Or.inl (Or.inl rfl)
          · exact Or.inr ⟨o', ho', by rw [← hr o' (hne o' ho')]; exact h⟩

/-! ## Want arrows and the finishing test -/

omit [DecidableEq A] in
/-- A listed agent outside `up` that is not free holds a needed good. -/
theorem needed_of_not_free {z : A} (hz : z ∈ agents) (hzu : z ∉ up) (hf : ¬ Free P agents up Y z) :
    ∃ y, Y z = some y ∧ P.NA agents (· ∈ up) Y y :=
  Classical.byContradiction fun hno => hf ⟨hz, hzu, fun y hy hna => hno ⟨y, hy, hna⟩⟩

/-- **(F2)**: an agent holding a needed good has an out-arc in the need digraph: `outNb` finds one. -/
theorem outNb_spec {j : A} {y : G} (hy : Y j = some y) (hna : P.NA agents (· ∈ up) Y y) :
    ∃ j', outNb P agents up Y j = some j' ∧ j' ∈ agents ∧ j' ∉ up ∧ P.Prefers Y j' y := by
  unfold outNb
  rw [hy]
  dsimp only
  obtain ⟨i, hi, hiu, hp⟩ := hna
  have hiu' : i ∉ up := hiu
  cases hf : agents.find? (fun j' => !(up.contains j') && decide (P.Prefers Y j' y)) with
  | none =>
    have := List.find?_eq_none.mp hf i hi
    simp [hiu', hp] at this
  | some j' =>
    have h := List.find?_some hf
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
      decide_eq_true_eq] at h
    exact ⟨j', rfl, List.mem_of_find?_eq_some hf, h.1, h.2⟩

omit [DecidableEq A] [DecidableEq G] in
theorem inBase_of_not_up {o : A} {g : G} (ho : o ∉ up) (h : InBase P up Y o g) : Y o = some g := by
  rcases h with h | ⟨h, -⟩
  · exact h
  · exact absurd h ho

omit [DecidableEq A] in
/-- **The finishing test (b)** (Lemma forced of the earlier version): under (P), an agent `x` exposed for an agent
`o` outside `up` has exactly one of `b x`, `c x` in the junk, its protecting good `hOf x` (the paper's `h_x`); the
other is `o`'s good. -/
theorem forced_hOf (hWF : WF P agents goods) (hPP : PropP P agents up Y goods) {o x : A} (ho : o ∉ up)
    (hx : Exposed P agents up Y goods o x) :
    hOf P agents up Y goods x ∈ junkList P agents up Y goods ∧
      (∀ g ∈ junkList P agents up Y goods, (g = P.b x ∨ g = P.c x) → g = hOf P agents up Y goods x) ∧
      ((P.b x = hOf P agents up Y goods x ∧ Y o = some (P.c x)) ∨
        (P.c x = hOf P agents up Y goods x ∧ Y o = some (P.b x))) := by
  obtain ⟨hxa, -, hxu, hxt, hb, hc⟩ := hx
  have hbc := (hWF x hxa).2.2.2.2.2
  by_cases hbj : P.b x ∈ junkList P agents up Y goods
  · have hh : hOf P agents up Y goods x = P.b x := by
      unfold hOf; rw [junkB_iff.mpr hbj]; rfl
    rw [hh]
    have hcj : P.c x ∉ junkList P agents up Y goods := fun h => hPP x hxa hxu hxt ⟨hbj, h⟩
    refine ⟨hbj, fun g hg hg' => ?_, Or.inl ⟨rfl, inBase_of_not_up ho (hc.resolve_left hcj)⟩⟩
    rcases hg' with rfl | rfl
    · rfl
    · exact absurd hg hcj
  · have hh : hOf P agents up Y goods x = P.c x := by
      unfold hOf
      cases h : junkB P agents up Y goods (P.b x) with
      | false => rfl
      | true => exact absurd (junkB_iff.mp h) hbj
    rw [hh]
    have hYb := inBase_of_not_up ho (hb.resolve_left hbj)
    have hcj : P.c x ∈ junkList P agents up Y goods := by
      rcases hc with h | h
      · exact h
      · rw [inBase_of_not_up ho h] at hYb
        exact absurd (Option.some.inj hYb).symm hbc
    refine ⟨hcj, fun g hg hg' => ?_, Or.inr ⟨rfl, hYb⟩⟩
    rcases hg' with rfl | rfl
    · exact absurd hg hbj
    · rfl

/-! ## From a successor map to an exchange cycle -/

/-- **A successor map** on the agents outside `up`: each is sent to an agent outside `up`; a non-free agent to an
agent that needs its good (a need arc); a free agent to an agent whose `b` and `c` are each junk or the free agent's
good (an exposure arc, or the arc that closes a pair chain); and two free agents with different images use different
junk goods. -/
structure SuccMap (P : Profile A G) (agents : List A) (goods : List G) (Y : A → Option G) (up : List A)
    (σ : A → A) : Prop where
  vmem : ∀ z ∈ agents, z ∉ up → σ z ∈ agents ∧ σ z ∉ up
  need : ∀ z ∈ agents, z ∉ up → ¬ Free P agents up Y z → ∃ y, Y z = some y ∧ P.Prefers Y (σ z) y
  free : ∀ z, Free P agents up Y z →
    (P.b (σ z) ∈ junkList P agents up Y goods ∨ Y z = some (P.b (σ z))) ∧
    (P.c (σ z) ∈ junkList P agents up Y goods ∨ Y z = some (P.c (σ z)))
  disj : ∀ z z', Free P agents up Y z → Free P agents up Y z' → σ z ≠ σ z' →
    ∀ g ∈ junkList P agents up Y goods, (g = P.b (σ z) ∨ g = P.c (σ z)) → (g = P.b (σ z') ∨ g = P.c (σ z')) →
      False

omit [DecidableEq A] [DecidableEq G] in
theorem iter_succ (σ : A → A) (k : Nat) (a : A) : iter σ (k + 1) a = σ (iter σ k a) := rfl

/-- **Pigeonhole**: if `σ` maps a list `V` with `|V| ≤ n` into itself, then `σⁿ(s)` lies on a cycle
of length at most `n`, for every `s ∈ V`. -/
theorem exists_period (σ : A → A) {V : List A} (hσ : ∀ a ∈ V, σ a ∈ V) {s : A} (hs : s ∈ V)
    {n : Nat} (hn : V.length ≤ n) : ∃ k < n, iter σ (k + 1) (iter σ n s) = iter σ n s := by
  have hrep : ∃ i j, i < j ∧ j ≤ n ∧ iter σ i s = iter σ j s := by
    apply Classical.byContradiction
    intro hno
    have hnd : ((List.range (n + 1)).map (fun k => iter σ k s)).Nodup := by
      rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
      exact List.pairwise_lt_range.imp_of_mem (fun {i j} _ hj hij heq =>
        hno ⟨i, j, hij, by simp at hj; omega, heq⟩)
    have hlen := length_le_of_nodup_of_subset hnd (by
      intro x hx
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
      exact iter_mem σ hσ hs k)
    simp only [List.length_map, List.length_range] at hlen
    omega
  obtain ⟨i, j, hij, hjn, he⟩ := hrep
  refine ⟨j - i - 1, by omega, ?_⟩
  have e1 : j - i - 1 + 1 = j - i := by omega
  rw [e1, ← iter_add]
  calc iter σ (j - i + n) s = iter σ (n - i) (iter σ j s) := by rw [← iter_add]; congr 1; omega
    _ = iter σ (n - i) (iter σ i s) := by rw [he]
    _ = iter σ n s := by rw [← iter_add]; congr 1; omega

omit [DecidableEq G] in
theorem period_spec (σ : A → A) (n : Nat) (p : A) (h : ∃ k < n, iter σ (k + 1) p = p) :
    0 < period σ n p ∧ iter σ (period σ n p) p = p := by
  unfold period
  cases hf : (List.range n).find? (fun k => iter σ (k + 1) p == p) with
  | none =>
    obtain ⟨k, hk, he⟩ := h
    have := List.find?_eq_none.mp hf k (List.mem_range.mpr hk)
    simp [he] at this
  | some k =>
    have := List.find?_some hf
    simp only [beq_iff_eq] at this
    simp [this]

omit [DecidableEq G] in
theorem onOrbit_iff {σ : A → A} {per : Nat} {p w : A} : onOrbit σ per p w = true ↔ ∃ j < per, iter σ j p = w := by
  simp [onOrbit, List.any_eq_true, List.mem_range]

omit [DecidableEq G] in
/-- On the orbit of a point of period `per`, `σ^per` is the identity. -/
theorem iter_per_orbit {σ : A → A} {per : Nat} {p : A} (hpp : iter σ per p = p) {w : A}
    (hw : onOrbit σ per p w = true) : iter σ per w = w := by
  obtain ⟨j, -, rfl⟩ := onOrbit_iff.mp hw
  rw [← iter_add, Nat.add_comm, iter_add, hpp]

/-- **The orbit of a periodic point of a successor map is an exchange cycle** (`EFX.DE.Cycle`), with predecessor
`σ^(per − 1)`. -/
theorem orbit_cycle {σ : A → A} (hS : SuccMap P agents goods Y up σ) {p : A} (hpa : p ∈ agents) (hpu : p ∉ up)
    {per : Nat} (hper : 0 < per) (hpp : iter σ per p = p) :
    Cycle P agents goods Y up (onOrbit σ per p) σ (iter σ (per - 1)) := by
  have hV : ∀ k, iter σ k p ∈ agents ∧ iter σ k p ∉ up := by
    intro k
    induction k with
    | zero => exact ⟨hpa, hpu⟩
    | succ k ih => exact hS.vmem _ ih.1 ih.2
  have hmem : ∀ w, onOrbit σ per p w = true → w ∈ agents ∧ w ∉ up := by
    intro w hw
    obtain ⟨j, -, rfl⟩ := onOrbit_iff.mp hw
    exact hV j
  have hpred : ∀ w, onOrbit σ per p w = true → σ (iter σ (per - 1) w) = w := by
    intro w hw
    rw [← iter_succ σ (per - 1) w, Nat.sub_add_cancel hper, iter_per_orbit hpp hw]
  refine ⟨hmem, ⟨p, onOrbit_iff.mpr ⟨0, hper, rfl⟩⟩, fun z hz => ?_, fun w hw => ?_, hpred, fun z hz => ?_,
    fun z hz hf => hS.need z (hmem z hz).1 (hmem z hz).2 hf, fun z _ hf => hS.free z hf,
    fun z z' _ _ hf hf' hne => hS.disj z z' hf hf' hne⟩
  · obtain ⟨j, hj, rfl⟩ := onOrbit_iff.mp hz
    rw [← iter_succ σ j p]
    by_cases hj1 : j + 1 < per
    · exact onOrbit_iff.mpr ⟨j + 1, hj1, rfl⟩
    · have : j + 1 = per := by omega
      rw [this, hpp]
      exact onOrbit_iff.mpr ⟨0, hper, rfl⟩
  · obtain ⟨j, hj, rfl⟩ := onOrbit_iff.mp hw
    rw [← iter_add]
    cases j with
    | zero => exact onOrbit_iff.mpr ⟨per - 1, by omega, rfl⟩
    | succ j =>
      have : per - 1 + (j + 1) = j + per := by omega
      rw [this, iter_add, hpp]
      exact onOrbit_iff.mpr ⟨j, by omega, rfl⟩
  · show iter σ (per - 1) (iter σ 1 z) = z
    rw [← iter_add, Nat.sub_add_cancel hper, iter_per_orbit hpp hz]

/-- **The move along the cycle of `σ` through `σⁿ(s)` is an exchange along an exchange cycle** (`Cycle`): the orbit
of `σⁿ(s)`, with predecessor `σ^(per − 1)`. -/
theorem cycleStep_cycle {σ : A → A} (hS : SuccMap P agents goods Y up σ) {s : A} (hs : s ∈ agents) (hsu : s ∉ up) :
    ∃ (onC : A → Bool) (π : A → A), Cycle P agents goods Y up onC σ π ∧
      cycleStep P agents up Y σ s = (exchY P agents up Y onC π, exchUp P agents up Y onC π) := by
  let V := agents.filter (fun k => !(up.contains k))
  have hVm : ∀ k, k ∈ V ↔ k ∈ agents ∧ k ∉ up := by intro k; simp [V]
  have hVσ : ∀ a ∈ V, σ a ∈ V := fun a ha => (hVm _).mpr (hS.vmem a ((hVm a).mp ha).1 ((hVm a).mp ha).2)
  have hVl : V.length ≤ agents.length := List.length_filter_le _ _
  obtain ⟨hper, hpp⟩ := period_spec σ agents.length _
    (exists_period σ hVσ ((hVm s).mpr ⟨hs, hsu⟩) hVl)
  have hp := (hVm _).mp (iter_mem σ hVσ ((hVm s).mpr ⟨hs, hsu⟩) agents.length)
  exact ⟨_, _, orbit_cycle hS hp.1 hp.2 hper hpp, rfl⟩

/-- **The move along the cycle of `σ` through `σⁿ(s)`** is a valid state that dominates the state. -/
theorem cycleStep_spec (hV : Valid P agents goods Y up) (hWF : WF P agents goods)
    {σ : A → A} (hS : SuccMap P agents goods Y up σ) {s : A} (hs : s ∈ agents) (hsu : s ∉ up) :
    Valid P agents goods (cycleStep P agents up Y σ s).1 (cycleStep P agents up Y σ s).2 ∧
      Dominates P agents (cycleStep P agents up Y σ s).1 (cycleStep P agents up Y σ s).2 Y up := by
  obtain ⟨onC, π, hC, e⟩ := cycleStep_cycle hS hs hsu
  rw [e]
  exact exchange hV hWF hC

/-! ## The two successor maps -/

theorem sigma_free_some {px : Option A} {rp : List (A × G)} {j x : A} (hj : Free P agents up Y j)
    (hpx : px = some x) : sigmaMap P agents up Y goods px rp j = x := by
  simp [sigmaMap, freeB_iff.mpr hj, hpx]

theorem sigma_free_none {rp : List (A × G)} {j : A} {q : G} (hj : Free P agents up Y j) (hq : repOf rp j = some q) :
    sigmaMap P agents up Y goods none rp j =
      (agents.find? (fun x => expB P agents up Y goods j x && hOf P agents up Y goods x == q)).getD j := by
  simp [sigmaMap, freeB_iff.mpr hj, hq]

/-- **The rule of the ring step, in the paper's words** (proof of the Improvement Lemma, "distinct leftover goods"):
list the free agents in the order of `agents` as `os₁ ++ o :: os₂`. If `o` has a representative `q`, then `q` is
the protecting good `h_x` of the first agent `x` (in the order of `agents`) exposed for `o` whose protecting good is
not the representative of an earlier free agent (one of `os₁`): `x` is exposed for `o`, `h_x = q`, no agent of `os₁`
has representative `q`, and every agent before `x` exposed for `o` has as protecting good the representative of an
agent of `os₁`. And `σ(o) = x` (`sigmaMap`: the first agent exposed for `o` with protecting good `q` is `x`). -/
theorem reps_first_blocker (hag : agents.Nodup) {o : A} {q : G} (ho : Free P agents up Y o)
    (hq : repOf (reps (Hset P agents up Y goods) (agents.filter (freeB P agents up Y)) []) o = some q) :
    ∃ os1 os2 x as bs, agents.filter (freeB P agents up Y) = os1 ++ o :: os2 ∧ agents = as ++ x :: bs ∧
      Exposed P agents up Y goods o x ∧ hOf P agents up Y goods x = q ∧
      (∀ o' ∈ os1, repOf (reps (Hset P agents up Y goods) (agents.filter (freeB P agents up Y)) []) o' ≠ some q) ∧
      (∀ x' ∈ as, Exposed P agents up Y goods o x' → ∃ o' ∈ os1,
        repOf (reps (Hset P agents up Y goods) (agents.filter (freeB P agents up Y)) []) o' =
          some (hOf P agents up Y goods x')) ∧
      sigmaMap P agents up Y goods none (reps (Hset P agents up Y goods) (agents.filter (freeB P agents up Y)) [])
        o = x := by
  have hoF : o ∈ agents.filter (freeB P agents up Y) := List.mem_filter.mpr ⟨ho.1, freeB_iff.mpr ho⟩
  obtain ⟨os1, os2, hF⟩ := List.append_of_mem hoF
  have hnd : (os1 ++ o :: os2).Nodup := hF ▸ hag.sublist List.filter_sublist
  have hσ := sigma_free_none (goods := goods) ho hq
  rw [hF] at hq hσ ⊢
  obtain ⟨U, hU, hfind⟩ := repOf_reps_append (Hset P agents up Y goods) os1 os2 [] hnd hq
  rw [find?_Hset] at hfind
  obtain ⟨x, hx, hxq⟩ := Option.map_eq_some_iff.mp hfind
  obtain ⟨hxp, as, bs, hag', has⟩ := List.find?_eq_some_iff_append.mp hx
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hxp
  have hqU : q ∉ U := hxq ▸ hxp.2
  have hbefore : ∀ x' ∈ as, Exposed P agents up Y goods o x' → hOf P agents up Y goods x' ∈ U := by
    intro x' hx' hE
    have := has x' hx'
    simp only [expB_iff.mpr hE, Bool.true_and, Bool.not_not, List.contains_eq_mem, decide_eq_true_eq] at this
    exact this
  refine ⟨os1, os2, x, as, bs, rfl, hag', expB_iff.mp hxp.1, hxq, fun o' ho' h => hqU ((hU q).mpr
    (Or.inr ⟨o', ho', h⟩)), fun x' hx' hE => ?_, ?_⟩
  · rcases (hU _).mp (hbefore x' hx' hE) with h | h
    · simp at h
    · exact h
  · rw [hσ]
    have : agents.find? (fun x => expB P agents up Y goods o x && hOf P agents up Y goods x == q) = some x := by
      refine List.find?_eq_some_iff_append.mpr ⟨by simp [hxp.1, hxq], as, bs, hag', fun x' hx' => ?_⟩
      cases hE : expB P agents up Y goods o x' with
      | false => rfl
      | true =>
        have := hbefore x' hx' (expB_iff.mp hE)
        have hne : hOf P agents up Y goods x' ≠ q := fun e => hqU (e ▸ this)
        simp [hne]
    rw [this]
    rfl

/-- A non-free agent outside `up` goes to an agent outside `up` that needs its good. -/
theorem sigma_need {px : Option A} {rp : List (A × G)} {z : A} (hz : z ∈ agents) (hzu : z ∉ up)
    (hf : ¬ Free P agents up Y z) :
    ∃ y, Y z = some y ∧ P.Prefers Y (sigmaMap P agents up Y goods px rp z) y ∧
      sigmaMap P agents up Y goods px rp z ∈ agents ∧ sigmaMap P agents up Y goods px rp z ∉ up := by
  obtain ⟨y, hy, hna⟩ := needed_of_not_free hz hzu hf
  obtain ⟨j', hj', h1, h2, h3⟩ := outNb_spec hy hna
  have hfb : freeB P agents up Y z = false := by
    cases h : freeB P agents up Y z with
    | false => rfl
    | true => exact absurd (freeB_iff.mp h) hf
  have : sigmaMap P agents up Y goods px rp z = j' := by simp [sigmaMap, hfb, hj']
  rw [this]
  exact ⟨y, hy, h3, h1, h2⟩

/-- **The successor map of a chain** (Lemma chain: the chain, or the ring of want arrows it may run into): if (P)
fails at `x`, every free agent goes to `x`, every frozen agent to an out-neighbour. -/
theorem succ_pair {x : A} (hx : x ∈ agents) (hpx : pairB P agents up Y goods x = true) :
    SuccMap P agents goods Y up (sigmaMap P agents up Y goods (some x) []) := by
  obtain ⟨hxu, -, hbj, hcj⟩ := pairB_iff.mp hpx
  refine ⟨fun z hz hzu => ?_, fun z hz hzu hf => ?_, fun z hf => ?_, fun z z' hf hf' hne => ?_⟩
  · by_cases hf : Free P agents up Y z
    · rw [sigma_free_some hf rfl]; exact ⟨hx, hxu⟩
    · obtain ⟨-, -, -, h1, h2⟩ := sigma_need (px := some x) (rp := []) hz hzu hf
      exact ⟨h1, h2⟩
  · obtain ⟨y, hy, hp, -⟩ := sigma_need (px := some x) (rp := []) hz hzu hf
    exact ⟨y, hy, hp⟩
  · rw [sigma_free_some hf rfl]; exact ⟨Or.inl hbj, Or.inl hcj⟩
  · exact absurd (by rw [sigma_free_some hf rfl, sigma_free_some hf' rfl]) hne

/-- **The successor map of a ring** (the proof of the Improvement Lemma; a ring of want arrows when there is no free
agent): under (P), if every free agent `o` has `|H_o| ≥ |F|`, each free agent goes to an agent exposed for it whose
protecting good is its representative, every frozen agent to an out-neighbour. -/
theorem succ_exchange (hWF : WF P agents goods) (hag : agents.Nodup) (hPP : PropP P agents up Y goods)
    (hcount : ∀ o, Free P agents up Y o →
      (agents.filter (freeB P agents up Y)).length ≤ (Hset P agents up Y goods o).length) :
    SuccMap P agents goods Y up (sigmaMap P agents up Y goods none
      (reps (Hset P agents up Y goods) (agents.filter (freeB P agents up Y)) [])) := by
  have hFs : ∀ z, Free P agents up Y z → z ∈ agents.filter (freeB P agents up Y) :=
    fun z hz => List.mem_filter.mpr ⟨hz.1, freeB_iff.mpr hz⟩
  obtain ⟨rs1, rs2⟩ := reps_spec (Hset P agents up Y goods) (agents.filter (freeB P agents up Y)) []
    (hag.sublist List.filter_sublist) (fun o ho => ⟨nodup_dd _, by
      simp only [List.length_nil, Nat.zero_add]
      exact hcount o (freeB_iff.mp (List.mem_filter.mp ho).2)⟩)
  have hfree : ∀ z, Free P agents up Y z → ∃ q,
      repOf (reps (Hset P agents up Y goods) (agents.filter (freeB P agents up Y)) []) z = some q ∧
      Exposed P agents up Y goods z (sigmaMap P agents up Y goods none
        (reps (Hset P agents up Y goods) (agents.filter (freeB P agents up Y)) []) z) ∧
      hOf P agents up Y goods (sigmaMap P agents up Y goods none
        (reps (Hset P agents up Y goods) (agents.filter (freeB P agents up Y)) []) z) = q := by
    intro z hz
    obtain ⟨q, hq, hqH, -⟩ := rs1 z (hFs z hz)
    obtain ⟨x, hxE, hxq⟩ := mem_Hset.mp hqH
    rw [sigma_free_none hz hq]
    cases hf : agents.find? (fun x => expB P agents up Y goods z x && hOf P agents up Y goods x == q) with
    | none =>
      exfalso
      have := List.find?_eq_none.mp hf x hxE.1
      simp [expB_iff.mpr hxE, hxq] at this
    | some x' =>
      have h := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨q, hq, expB_iff.mp h.1, h.2⟩
  refine ⟨fun z hz hzu => ?_, fun z hz hzu hf => ?_, fun z hf => ?_, fun z z' hf hf' hne => ?_⟩
  · by_cases hf : Free P agents up Y z
    · obtain ⟨-, -, hE, -⟩ := hfree z hf
      exact ⟨hE.1, hE.2.2.1⟩
    · obtain ⟨-, -, -, h1, h2⟩ := sigma_need (px := none)
        (rp := reps (Hset P agents up Y goods) (agents.filter (freeB P agents up Y)) []) hz hzu hf
      exact ⟨h1, h2⟩
  · obtain ⟨y, hy, hp, -⟩ := sigma_need (px := none)
      (rp := reps (Hset P agents up Y goods) (agents.filter (freeB P agents up Y)) []) hz hzu hf
    exact ⟨y, hy, hp⟩
  · obtain ⟨-, -, hE, -⟩ := hfree z hf
    obtain ⟨-, -, -, -, hb, hc⟩ := hE
    exact ⟨hb.imp_right (inBase_of_not_up hf.2.1), hc.imp_right (inBase_of_not_up hf.2.1)⟩
  · intro g hg hgz hgz'
    obtain ⟨q, hq, hE, hhq⟩ := hfree z hf
    obtain ⟨q', hq', hE', hhq'⟩ := hfree z' hf'
    have e1 := (forced_hOf hWF hPP hf.2.1 hE).2.1 g hg hgz
    have e2 := (forced_hOf hWF hPP hf'.2.1 hE').2.1 g hg hgz'
    have hzz : z ≠ z' := fun e => hne (by rw [e])
    exact rs2 z (hFs z hf) z' (hFs z' hf') hzz q q' hq hq' (by rw [← hhq, ← hhq', ← e1, ← e2])

/-! ## The finishing test: the absorbers -/

omit [DecidableEq A] in
/-- **The finishing test (a)**: under (P), nobody is exposed for an agent outside `up` that holds nothing: exposure
would need `b x` and `c x` in the junk (the agent's holding is empty), which (P) excludes. -/
theorem not_exposed_of_none (hPP : PropP P agents up Y goods) {o x : A} (ho : o ∉ up) (hY : Y o = none) :
    ¬ Exposed P agents up Y goods o x := by
  intro hx
  obtain ⟨hxa, -, hxu, hxt, hb, hc⟩ := hx
  have hnot : ∀ g, ¬ InBase P up Y o g := fun g h => by
    have := inBase_of_not_up ho h
    rw [hY] at this; cases this
  exact hPP x hxa hxu hxt ⟨hb.resolve_right (hnot _), hc.resolve_right (hnot _)⟩

/-- Under (P), an agent outside `up` that holds nothing has `H_o = ∅`. -/
theorem Hset_eq_nil (hPP : PropP P agents up Y goods) {o : A} (ho : o ∉ up) (hY : Y o = none) :
    Hset P agents up Y goods o = [] := by
  cases h : Hset P agents up Y goods o with
  | nil => rfl
  | cons g l =>
    obtain ⟨x, hx, -⟩ := mem_Hset.mp (h ▸ List.mem_cons_self : g ∈ Hset P agents up Y goods o)
    exact absurd hx (not_exposed_of_none hPP ho hY)

/-- **A free agent holding nothing passes the count**: under (P), `|H_o| = 0 ≤ |F| − 1`. So the finish step of DE
covers it (`step_stop_of_none`), with `H = H_o = ∅`. -/
theorem count_of_none (hPP : PropP P agents up Y goods) {o : A} (ho : Free P agents up Y o) (hY : Y o = none) :
    (Hset P agents up Y goods o).length + 1 ≤ (agents.filter (freeB P agents up Y)).length := by
  rw [Hset_eq_nil hPP ho.2.1 hY]
  exact List.length_pos_of_mem (List.mem_filter.mpr ⟨ho.1, freeB_iff.mpr ho⟩)

/-- **In the ring step every free agent holds a good**: under (P), if every free agent `o` has `|H_o| ≥ |F|`, a free
agent holding nothing would pass the count (`count_of_none`). -/
theorem holds_of_count (hPP : PropP P agents up Y goods)
    (hcount : ∀ o, Free P agents up Y o →
      (agents.filter (freeB P agents up Y)).length ≤ (Hset P agents up Y goods o).length)
    {o : A} (ho : Free P agents up Y o) : ∃ y, Y o = some y := by
  cases hY : Y o with
  | none =>
    have h1 := count_of_none hPP ho hY
    have h2 := hcount o ho
    omega
  | some y => exact ⟨y, rfl⟩

/-- **The finishing test (c), a free agent holding nothing** (Lemma empty of the earlier version): under (P), a free
agent that holds nothing is a valid absorber with `H = ∅` (the case `H_o = ∅`: `Hset_eq_nil`, `count_of_none`). -/
theorem absorber_empty (hPP : PropP P agents up Y goods) {o : A} (ho : Free P agents up Y o) (hY : Y o = none) :
    Absorber P agents goods Y up o [] :=
  ⟨ho.1, Or.inr ho, by simp, by simp, fun x hx => absurd hx (not_exposed_of_none hPP ho.2.1 hY)⟩

/-- **The finishing test (c)** (sufficiency): under (P), a free agent `o` with `|H_o| ≤ |F| − 1` is a valid absorber
with `H = H_o`. -/
theorem absorber_forced (hWF : WF P agents goods) (hag : agents.Nodup) (hPP : PropP P agents up Y goods) {o : A}
    (ho : Free P agents up Y o)
    (hle : (Hset P agents up Y goods o).length + 1 ≤ (agents.filter (freeB P agents up Y)).length) :
    Absorber P agents goods Y up o (Hset P agents up Y goods o) := by
  refine ⟨ho.1, Or.inr ho, fun h hh => ?_, ?_, fun x hx => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := mem_Hset.mp hh
    exact (forced_hOf hWF hPP ho.2.1 hx).1
  · have := nFree_eq hag ho
    omega
  · have hm : hOf P agents up Y goods x ∈ Hset P agents up Y goods o := mem_Hset.mpr ⟨x, hx, rfl⟩
    unfold hOf at hm
    split at hm
    · exact Or.inl hm
    · exact Or.inr hm

/-- **The finishing test (c)** (necessity): under (P), every set `H` of a free absorber `o` contains `H_o`; so
`|H_o| ≤ |F| − 1`. -/
theorem Hset_le_of_absorber (hWF : WF P agents goods) (hPP : PropP P agents up Y goods) {o : A} {H : List G}
    (ho : Free P agents up Y o) (hA : Absorber P agents goods Y up o H) :
    (Hset P agents up Y goods o).length ≤ nFreeExcept P agents up Y o := by
  have hsub : ∀ h ∈ Hset P agents up Y goods o, h ∈ H := by
    intro h hh
    obtain ⟨x, hx, rfl⟩ := mem_Hset.mp hh
    have hf := forced_hOf hWF hPP ho.2.1 hx
    rcases hA.hit x hx with hb | hc
    · rw [← hf.2.1 _ (hA.junk _ hb) (Or.inl rfl)]; exact hb
    · rw [← hf.2.1 _ (hA.junk _ hc) (Or.inr rfl)]; exact hc
  exact Nat.le_trans (length_le_of_subset (nodup_dd _) hsub) hA.fit

/-- **The finishing test (c)** (Lemma forced of the earlier version): under (P), a free agent `o` is a valid absorber
(with some set) iff `|H_o| ≤ |F| − 1`, and then with `H_o`. -/
theorem absorber_iff (hWF : WF P agents goods) (hag : agents.Nodup) (hPP : PropP P agents up Y goods) {o : A}
    (ho : Free P agents up Y o) :
    (∃ H, Absorber P agents goods Y up o H) ↔
      (Hset P agents up Y goods o).length + 1 ≤ (agents.filter (freeB P agents up Y)).length := by
  constructor
  · rintro ⟨H, hA⟩
    have := Hset_le_of_absorber hWF hPP ho hA
    have := nFree_eq hag ho
    omega
  · exact fun h => ⟨_, absorber_forced hWF hag hPP ho h⟩

/-! ## The step, and the Improvement Lemma -/

/-- **A stop returns a valid absorber**, which is free unless every agent is a pair holder. -/
theorem step_stop (hWF : WF P agents goods) (hag : agents.Nodup) (hne : agents ≠ []) {d o : A} {H : List G}
    (h : step P agents goods d Y up = .stop o H) :
    Absorber P agents goods Y up o H ∧ (Free P agents up Y o ∨ ∀ i ∈ agents, i ∈ up) := by
  unfold step at h
  cases hA : agents.find? (pairB P agents up Y goods) with
  | some x => simp [hA] at h
  | none =>
    have hPP := propP_of_find hA
    cases hB : agents.find? (fun k => !(up.contains k)) with
    | none =>
      simp only [hA, hB, Out.stop.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hall : ∀ i ∈ agents, i ∈ up := fun i hi => by
        have := List.find?_eq_none.mp hB i hi
        simpa using this
      have hmem : agents.headD d ∈ agents := by
        cases agents with
        | nil => exact absurd rfl hne
        | cons a l => simp
      exact ⟨⟨hmem, Or.inl (hall _ hmem), by simp, by simp, fun x hx => absurd (hall x hx.1) hx.2.2.1⟩,
        Or.inr hall⟩
    | some s =>
      cases hD : agents.find? (fun o => freeB P agents up Y o &&
          decide ((Hset P agents up Y goods o).length + 1 ≤ (agents.filter (freeB P agents up Y)).length)) with
      | some o' =>
        simp only [hA, hB, hD, Out.stop.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h1 := List.find?_some hD
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
        exact ⟨absorber_forced hWF hag hPP (freeB_iff.mp h1.1) h1.2, Or.inl (freeB_iff.mp h1.1)⟩
      | none => simp only [hA, hB, hD, reduceCtorEq] at h

/-- **The finish step covers a free agent that holds nothing**: under (P), if some free agent holds nothing, the step
stops (it passes the count, `count_of_none`, so the first free agent passing the count exists). -/
theorem step_stop_of_none (hPP : PropP P agents up Y goods) {d o : A} (ho : Free P agents up Y o)
    (hY : Y o = none) : ∃ o' H, step P agents goods d Y up = .stop o' H := by
  have hA : agents.find? (pairB P agents up Y goods) = none :=
    List.find?_eq_none.mpr fun x hx hp => by
      obtain ⟨h1, h2, h3, h4⟩ := pairB_iff.mp hp
      exact hPP x hx h1 h2 ⟨h3, h4⟩
  unfold step
  cases hB : agents.find? (fun k => !(up.contains k)) with
  | none => simp only [hA]; exact ⟨_, _, rfl⟩
  | some s =>
    cases hD : agents.find? (fun o => freeB P agents up Y o &&
        decide ((Hset P agents up Y goods o).length + 1 ≤ (agents.filter (freeB P agents up Y)).length)) with
    | some o' => simp only [hA, hD]; exact ⟨_, _, rfl⟩
    | none =>
      have := List.find?_eq_none.mp hD o ho.1
      simp [freeB_iff.mpr ho, count_of_none hPP ho hY] at this

/-- **A move is one exchange along an exchange cycle** (`Cycle`): a chain closed by its last arc, or a ring (of want
arrows only, or with pair arrows). -/
theorem step_next_cycle (hWF : WF P agents goods) (hag : agents.Nodup) {d : A} {Y' : A → Option G} {up' : List A}
    (h : step P agents goods d Y up = .next Y' up') :
    ∃ (onC : A → Bool) (σ π : A → A), Cycle P agents goods Y up onC σ π ∧
      Y' = exchY P agents up Y onC π ∧ up' = exchUp P agents up Y onC π := by
  unfold step at h
  cases hA : agents.find? (pairB P agents up Y goods) with
  | some x =>
    simp only [hA, Out.next.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hx := List.mem_of_find?_eq_some hA
    have hpx := List.find?_some hA
    obtain ⟨onC, π, hC, e⟩ := cycleStep_cycle (succ_pair hx hpx) hx (pairB_iff.mp hpx).1
    exact ⟨onC, _, π, hC, by rw [e], by rw [e]⟩
  | none =>
    have hPP := propP_of_find hA
    cases hB : agents.find? (fun k => !(up.contains k)) with
    | none => simp only [hA, hB, reduceCtorEq] at h
    | some s =>
      cases hD : agents.find? (fun o => freeB P agents up Y o &&
          decide ((Hset P agents up Y goods o).length + 1 ≤ (agents.filter (freeB P agents up Y)).length)) with
      | some o' => simp only [hA, hB, hD, reduceCtorEq] at h
      | none =>
        simp only [hA, hB, hD, Out.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hs := List.mem_of_find?_eq_some hB
        have hsu : s ∉ up := by simpa using List.find?_some hB
        have hcount : ∀ o, Free P agents up Y o →
            (agents.filter (freeB P agents up Y)).length ≤ (Hset P agents up Y goods o).length := by
          intro o ho
          have := List.find?_eq_none.mp hD o ho.1
          simp only [freeB_iff.mpr ho, Bool.true_and, decide_eq_true_eq] at this
          omega
        obtain ⟨onC, π, hC, e⟩ := cycleStep_cycle (succ_exchange hWF hag hPP hcount) hs hsu
        exact ⟨onC, _, π, hC, by rw [e], by rw [e]⟩

/-- **A move returns a valid state that Pareto-dominates the state.** -/
theorem step_next (hV : Valid P agents goods Y up) (hWF : WF P agents goods) (hag : agents.Nodup) {d : A}
    {Y' : A → Option G} {up' : List A} (h : step P agents goods d Y up = .next Y' up') :
    Valid P agents goods Y' up' ∧ Dominates P agents Y' up' Y up := by
  obtain ⟨onC, σ, π, hC, rfl, rfl⟩ := step_next_cycle hWF hag h
  exact exchange hV hWF hC

/-- **The scores of a move** (Lemmas ring and chain, the scores): a move of `step` is the exchange along a `Cycle`
(the ring, or the chain closed by its last arc) in which every agent of the cycle gets a strictly higher utility and
every other agent the same utility (`exchange_scores`). -/
theorem step_next_scores (hWF : WF P agents goods) (hag : agents.Nodup) {d : A} {Y' : A → Option G} {up' : List A}
    (h : step P agents goods d Y up = .next Y' up') :
    ∃ (onC : A → Bool) (σ π : A → A), Cycle P agents goods Y up onC σ π ∧
      Y' = exchY P agents up Y onC π ∧ up' = exchUp P agents up Y onC π ∧
      (∀ w, onC w = true → util P up Y w < util P up' Y' w) ∧
      (∀ w, onC w = false → util P up' Y' w = util P up Y w) := by
  obtain ⟨onC, σ, π, hC, rfl, rfl⟩ := step_next_cycle hWF hag h
  exact ⟨onC, σ, π, hC, rfl, rfl, exchange_scores hC⟩

/-- **The Improvement Lemma** (`paper/k3-simple/long.tex`, Theorem Improvement Lemma). In the core case, let `(Y, up)`
be a valid state in which no free agent is a valid absorber and some agent is not a pair holder. Then some valid state
Pareto-dominates it (the one `step` returns: a chain or a ring). -/
theorem improvement (hV : Valid P agents goods Y up) (hWF : WF P agents goods) (hag : agents.Nodup)
    (hno : ¬ ∃ o H, Free P agents up Y o ∧ Absorber P agents goods Y up o H) (hU : ∃ i ∈ agents, i ∉ up) :
    ∃ Y' up', Valid P agents goods Y' up' ∧ Dominates P agents Y' up' Y up := by
  obtain ⟨i, hi, hiu⟩ := hU
  cases h : step P agents goods i Y up with
  | stop o H =>
    obtain ⟨hA, hF | hall⟩ := step_stop hWF hag (List.ne_nil_of_mem hi) h
    · exact absurd ⟨o, H, hF, hA⟩ hno
    · exact absurd (hall i hi) hiu
  | next Y' up' => exact ⟨Y', up', step_next hV hWF hag h⟩

/-- **Corollary (Pareto-optimal states).** In the core case, a valid state that no valid state Pareto-dominates is
completable: it has a valid absorber, which is free unless every agent holds its pair. -/
theorem completable_of_undominated (hV : Valid P agents goods Y up) (hWF : WF P agents goods) (hag : agents.Nodup)
    (hne : agents ≠ []) (hmax : ∀ Y' up', Valid P agents goods Y' up' → ¬ Dominates P agents Y' up' Y up) :
    ∃ o H, Absorber P agents goods Y up o H ∧ (Free P agents up Y o ∨ ∀ i ∈ agents, i ∈ up) := by
  obtain ⟨d, -⟩ := List.exists_mem_of_ne_nil agents hne
  cases h : step P agents goods d Y up with
  | stop o H => exact ⟨o, H, step_stop hWF hag hne h⟩
  | next Y' up' =>
    obtain ⟨h1, h2⟩ := step_next hV hWF hag h
    exact absurd h2 (hmax Y' up' h1)

end DE
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.DE.find?_dd
#print axioms EFX.DE.find?_Hset
#print axioms EFX.DE.reps_spec
#print axioms EFX.DE.repOf_reps_append
#print axioms EFX.DE.reps_first_blocker
#print axioms EFX.DE.outNb_spec
#print axioms EFX.DE.forced_hOf
#print axioms EFX.DE.exists_period
#print axioms EFX.DE.orbit_cycle
#print axioms EFX.DE.cycleStep_cycle
#print axioms EFX.DE.cycleStep_spec
#print axioms EFX.DE.succ_pair
#print axioms EFX.DE.succ_exchange
#print axioms EFX.DE.not_exposed_of_none
#print axioms EFX.DE.Hset_eq_nil
#print axioms EFX.DE.count_of_none
#print axioms EFX.DE.holds_of_count
#print axioms EFX.DE.absorber_empty
#print axioms EFX.DE.absorber_forced
#print axioms EFX.DE.Hset_le_of_absorber
#print axioms EFX.DE.absorber_iff
#print axioms EFX.DE.step_stop
#print axioms EFX.DE.step_stop_of_none
#print axioms EFX.DE.step_next_cycle
#print axioms EFX.DE.step_next
#print axioms EFX.DE.step_next_scores
#print axioms EFX.DE.improvement
#print axioms EFX.DE.completable_of_undominated
