import EFX.LBSound

/-!
# Construction LB in Lean (LEDGER S2.S)

`EFX.LB.lb` is construction LB (`proofs/construction.md` §3) as `src/construct.py` implements it, with
one difference: Phase 1 takes its processing order as an argument. LB chooses that order adaptively (R1
steps by their key, insertions by their `NA` lookahead). Each agent is processed exactly once and takes
its favourite remaining good, so every run of LB's Phase 1 is `phase1` in some order. The theorems hold
for every order, so they cover LB whatever its order heuristic, which is not formalized.

- Phase 1: `phase1`; `phase1_spec`: each pick is one of the picker's goods, no good is picked twice,
  and invariant (I1) holds.
- Phase 2: `upgrades` (LB's loop, the first eligible agent first) with its invariant `UpInv` (`NA` only
  shrinks, so upgraded agents stay unfrozen; the `c`s given away are distinct junk); `frozenB`, `cap`
  (the slots), `fill` and `build` (the allocation, as `build` in `construct.py`), `ownerOK` (the owner
  constraint), `ownerSearch` (the first valid owner and overflow set, in LB's order), and `lb`, which
  returns `none` when LB fails.
- `lb_hyp`: every allocation `lb` returns satisfies `EFX.LB.Hyp` (`EFX.LBSound`).
- `lb_sound`, `lb_sound_model`: **Theorem 1**. Every allocation `lb` returns is EFX₀ for every additive
  valuation consistent with the rankings, and at most one of its bundles has more than two goods.

Not formalized: LB's order heuristic, and that LB never fails (S2.LB, a conjecture). That `lb` computes
what `construct.py` computes is evidence only: `lean/scripts/lb_crosscheck.py` runs both on the ranking
profiles of connected cores (with Python's Phase 1 order) and compares the allocations.
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

/-! ## Phase 2: upgrades -/

/-- `NA` for the upgraded agents `up`, as a Boolean. -/
def naB (P : Profile A G) (agents up : List A) (Y : A → Option G) (g : G) : Bool :=
  agents.any (fun i => !(up.contains i) && decide (P.Prefers Y i g))

theorem naB_iff {P : Profile A G} {agents up : List A} {Y : A → Option G} {g : G} :
    naB P agents up Y g = true ↔ P.NA agents (· ∈ up) Y g := by
  simp [naB, Profile.NA]

omit [DecidableEq A] in
/-- `NA` only shrinks as agents are upgraded. -/
theorem NA_mono {P : Profile A G} {agents : List A} {Y : A → Option G} {U U' : A → Prop}
    (hUU : ∀ k, U k → U' k) {g : G} (h : P.NA agents U' Y g) : P.NA agents U Y g := by
  obtain ⟨i, hi, hnu, hp⟩ := h
  exact ⟨i, hi, fun hu => hnu (hUU i hu), hp⟩

/-- LB's upgrade test for agent `k`: it is not upgraded, its pick is its `b`, its `c` is junk not yet
given away (in `J`), and its `b` is not in `NA`. -/
def canUp (P : Profile A G) (agents up : List A) (Y : A → Option G) (J : List G) (k : A) : Bool :=
  !(up.contains k) && P.pickRank Y k == 1 && J.contains (P.c k) && !(naB P agents up Y (P.b k))

/-- LB's upgrades: while some agent passes `canUp`, the first one in `agents` receives its `c`.
Returns the upgraded agents and the junk left. Each round upgrades a new agent of `agents`, so
`fuel = agents.length` rounds run the loop to the end, as LB does. -/
def upgrades (P : Profile A G) (agents : List A) (Y : A → Option G) :
    Nat → List A → List G → List A × List G
  | 0, up, J => (up, J)
  | fuel + 1, up, J =>
    match agents.find? (canUp P agents up Y J) with
    | none => (up, J)
    | some k => upgrades P agents Y fuel (k :: up) (J.erase (P.c k))

/-- The invariant of the upgrade loop, started from the junk `J0`. -/
def UpInv (P : Profile A G) (agents : List A) (Y : A → Option G) (J0 : List G) (up : List A)
    (J : List G) : Prop :=
  J.Nodup ∧ (∀ g ∈ J, g ∈ J0) ∧ (∀ g ∈ J0, g ∉ J → ∃ k ∈ up, P.c k = g) ∧
  ∀ k ∈ up, P.pickRank Y k = 1 ∧ ¬ P.NA agents (· ∈ up) Y (P.b k) ∧ P.c k ∈ J0 ∧ P.c k ∉ J ∧
    ∀ k' ∈ up, P.c k' = P.c k → k' = k

omit [DecidableEq A] in
theorem upInv_init (P : Profile A G) (agents : List A) (Y : A → Option G) {J0 : List G}
    (h : J0.Nodup) : UpInv P agents Y J0 [] J0 :=
  ⟨h, fun _ hg => hg, fun _ hg hn => absurd hg hn, fun _ hk => by simp at hk⟩

theorem upInv_upgrades (P : Profile A G) (agents : List A) (Y : A → Option G) (J0 : List G) :
    ∀ (fuel : Nat) (up : List A) (J : List G), UpInv P agents Y J0 up J →
      UpInv P agents Y J0 (upgrades P agents Y fuel up J).1 (upgrades P agents Y fuel up J).2
  | 0, _, _, h => h
  | fuel + 1, up, J, h => by
    unfold upgrades
    cases hf : agents.find? (canUp P agents up Y J) with
    | none => exact h
    | some k =>
      apply upInv_upgrades P agents Y J0 fuel
      have hc := List.find?_some hf
      simp only [canUp, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem,
        beq_iff_eq] at hc
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

/-! ## Phase 2: frozen agents, slots, and the placement of the junk -/

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

/-- `k`'s slots: none if frozen or upgraded, else 1 with a pick and 2 without. -/
def cap (P : Profile A G) (agents up : List A) (Y : A → Option G) (k : A) : Nat :=
  if frozenB P agents up Y k || up.contains k then 0 else if Y k = none then 2 else 1

/-- The slots of `k`, except that the owner (if any) has none: its extra goods are chosen apart. -/
def slotsExcept (s : A → Nat) (o : Option A) (k : A) : Nat := if o = some k then 0 else s k

/-- Distribute `rest` over the agents of `ks` in order, `s k` goods to `k`: the agent of each good. -/
def fill (s : A → Nat) : List A → List G → G → Option A
  | [], _, _ => none
  | k :: ks, rest, g => if g ∈ rest.take (s k) then some k else fill s ks (rest.drop (s k)) g

/-- The junk left after the owner takes `JL`. -/
def rest (J JL : List G) : List G := J.filter (fun g => g ∉ JL)

/-- The allocation: picks to their pickers, `c k` to each upgraded `k`, `JL` to the owner, the rest
of the junk into the slots of the other agents, in the order of `agents` (LB fills from the end of
the junk list, hence `reverse`). `d` receives goods not in `goods` (none of them are placed). -/
def build (P : Profile A G) (agents up : List A) (Y : A → Option G) (J : List G) (o : Option A)
    (JL : List G) (d : A) (g : G) : A :=
  match picker agents Y g with
  | some k => k
  | none =>
    match upOf P up g with
    | some k => k
    | none =>
      if g ∈ JL then o.getD d
      else (fill (slotsExcept (cap P agents up Y) o) agents (rest J JL).reverse g).getD d

/-- The owner constraint for owner `o` taking `JL`: no other agent `k`, not upgraded, whose pick is its
top, has `b k` and `c k` both in `o`'s bundle (its pick, its `c` if upgraded, and `JL`). -/
def ownerOK (P : Profile A G) (agents up : List A) (Y : A → Option G) (o : A) (JL : List G) : Bool :=
  let L := (match Y o with | none => [] | some y => [y]) ++
    (if up.contains o then [P.c o] else []) ++ JL
  agents.all (fun k => k == o || up.contains k || P.pickRank Y k != 0 ||
    !(L.contains (P.b k) && L.contains (P.c k)))

/-- A valid choice of owner `o` and overflow set `JL`: `o` is not frozen, the rest of the junk fits
the other agents' slots, and the owner constraint holds. -/
def validOwner (P : Profile A G) (agents up : List A) (Y : A → Option G) (J : List G) (o : A)
    (JL : List G) : Bool :=
  !(frozenB P agents up Y o) &&
    decide ((rest J JL).length ≤ (agents.map (slotsExcept (cap P agents up Y) (some o))).sum) &&
    ownerOK P agents up Y o JL

/-- The sublists of `l` of length `k`, in lexicographic order (as `itertools.combinations`). -/
def combos : Nat → List G → List (List G)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (combos k xs).map (x :: ·) ++ combos (k + 1) xs

/-- LB's search for the owner: the first valid `(o, JL)`, `o` in the order of `agents` and not
frozen, `JL` among the sets of junk of the size that fills the other slots. -/
def ownerSearch (P : Profile A G) (agents up : List A) (Y : A → Option G) (J : List G) :
    Option (A × List G) :=
  let s := cap P agents up Y
  ((agents.filter (fun o => !(frozenB P agents up Y o))).flatMap (fun o =>
      (combos (J.length - ((agents.map s).sum - s o)) J).map (fun JL => (o, JL)))).find?
    (fun q => validOwner P agents up Y J q.1 q.2)

/-- **Construction LB** (`proofs/construction.md` §3, `src/construct.py`), with Phase 1 run in the
given `order`. LB chooses the order adaptively (R1 steps and insertions); every such run is a run
of `phase1` in some order, so a statement for every `order` covers LB. Returns the allocation, or
`none` when LB fails (no valid owner). -/
def lb (P : Profile A G) (agents : List A) (goods : List G) (order : List A) (d : A) :
    Option (G → A) :=
  let Y := phase1 P order goods
  let J0 := goods.filter (fun g => (picker agents Y g).isNone)
  let r := upgrades P agents Y agents.length [] J0
  if r.2.length ≤ (agents.map (cap P agents r.1 Y)).sum then
    some (build P agents r.1 Y r.2 none [] d)
  else
    match ownerSearch P agents r.1 Y r.2 with
    | none => none
    | some q => some (build P agents r.1 Y r.2 (some q.1) q.2 d)

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

omit [DecidableEq A] in
theorem pickRank_one {P : Profile A G} {Y : A → Option G} {k : A} (h : P.pickRank Y k = 1) :
    Y k = some (P.b k) := by
  unfold Profile.pickRank at h
  cases hY : Y k with
  | none => rw [hY] at h; cases h
  | some y =>
    rw [hY] at h
    unfold Profile.rank at h
    by_cases ha : y = P.a k <;> by_cases hb : y = P.b k <;> by_cases hc : y = P.c k <;> simp_all

section assembly

variable {P : Profile A G} {agents : List A} {goods : List G} {Y : A → Option G} {up : List A}
  {J : List G} {owner : Option A} {JL : List G} {d : A}

theorem build_cases (g : G) :
    (∃ k, picker agents Y g = some k ∧ build P agents up Y J owner JL d g = k) ∨
    (picker agents Y g = none ∧ ∃ k, upOf P up g = some k ∧ build P agents up Y J owner JL d g = k) ∨
    (picker agents Y g = none ∧ upOf P up g = none ∧ g ∈ JL ∧
      build P agents up Y J owner JL d g = owner.getD d) ∨
    (picker agents Y g = none ∧ upOf P up g = none ∧ g ∉ JL ∧
      build P agents up Y J owner JL d g =
        (fill (slotsExcept (cap P agents up Y) owner) agents (rest J JL).reverse g).getD d) := by
  unfold build
  cases hp : picker agents Y g with
  | some k => exact Or.inl ⟨k, rfl, rfl⟩
  | none =>
    cases hu : upOf P up g with
    | some k => exact Or.inr (Or.inl ⟨rfl, k, rfl, rfl⟩)
    | none =>
      by_cases hJ : g ∈ JL
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hJ, by simp [hJ]⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hJ, by simp [hJ]⟩))

/-- Who holds a good under `build`: its picker, an upgraded agent whose `c` it is, the owner (a good of
`JL`), or an agent whose slot it fills. -/
theorem holder
    (hinv : UpInv P agents Y (goods.filter (fun g => (picker agents Y g).isNone)) up J)
    (hfit : (rest J JL).length ≤ (agents.map (slotsExcept (cap P agents up Y) owner)).sum)
    {g : G} (hg : g ∈ goods) {j : A} (hX : build P agents up Y J owner JL d g = j) :
    (j ∈ agents ∧ Y j = some g) ∨ (picker agents Y g = none ∧ j ∈ up ∧ P.c j = g) ∨
    (g ∈ JL ∧ j = owner.getD d) ∨
    fill (slotsExcept (cap P agents up Y) owner) agents (rest J JL).reverse g = some j := by
  rcases build_cases (P := P) (up := up) (J := J) (owner := owner) (JL := JL) (d := d) g with
    ⟨k, hp, hb⟩ | ⟨hp, k, hu, hb⟩ | ⟨-, -, hJ, hb⟩ | ⟨hp, hu, hJ, hb⟩
  · rw [hb] at hX; subst hX; exact Or.inl (picker_some hp)
  · rw [hb] at hX; subst hX; exact Or.inr (Or.inl ⟨hp, upOf_some hu⟩)
  · rw [hb] at hX; exact Or.inr (Or.inr (Or.inl ⟨hJ, hX.symm⟩))
  · refine Or.inr (Or.inr (Or.inr ?_))
    have hg0 : g ∈ goods.filter (fun g => (picker agents Y g).isNone) := by simp [hg, hp]
    have hgJ : g ∈ J := by
      refine Classical.byContradiction fun hn => ?_
      obtain ⟨k, hk, hc⟩ := hinv.2.2.1 g hg0 hn
      exact upOf_none hu k hk hc
    have hgr : g ∈ (rest J JL).reverse := by simp [rest, hgJ, hJ]
    obtain ⟨j', hj'⟩ := fill_cover hgr (by rw [List.length_reverse]; exact hfit)
    rw [hb, hj'] at hX
    simp at hX
    rw [← hX]; exact hj'

/-- The hypotheses of Theorem 1 hold for `build`, for picks with the properties of Phase 1
(`phase1_spec`), upgrades with the loop invariant, and an owner (if any) that is valid. -/
theorem build_hyp (hag : agents.Nodup) (hgd : goods.Nodup)
    (hY1 : ∀ k y, Y k = some y → k ∈ agents ∧ y ∈ goods ∧ P.rank k y < 3)
    (hY2 : ∀ k k' y, Y k = some y → Y k' = some y → k = k')
    (hY3 : ∀ i ∈ agents, ∀ g ∈ goods, P.Prefers Y i g → ∃ k, Y k = some g)
    (hinv : UpInv P agents Y (goods.filter (fun g => (picker agents Y g).isNone)) up J)
    (hfit : (rest J JL).length ≤ (agents.map (slotsExcept (cap P agents up Y) owner)).sum)
    (hJL : owner = none → JL = [])
    (hown : ∀ o, owner = some o → frozenB P agents up Y o = false ∧ ownerOK P agents up Y o JL = true) :
    Hyp P agents goods (build P agents up Y J owner JL d) Y (· ∈ up) (owner.getD d) := by
  have hold := fun {g} (hg : g ∈ goods) {j} (hX : build P agents up Y J owner JL d g = j) =>
    holder (d := d) hinv hfit hg hX
  -- a good placed by `fill` goes to an agent with slots, so neither frozen nor upgraded
  have hfillj : ∀ {g j}, fill (slotsExcept (cap P agents up Y) owner) agents (rest J JL).reverse g =
      some j → owner ≠ some j ∧ frozenB P agents up Y j = false ∧ j ∉ up := by
    intro g j hf
    have h3 := (fill_some hf).2.2
    unfold slotsExcept cap at h3
    by_cases ho : owner = some j
    · simp [ho] at h3
    · by_cases hfz : frozenB P agents up Y j = true
      · simp [ho, hfz] at h3
      · by_cases hu : j ∈ up
        · simp [ho, hu] at h3
        · exact ⟨ho, by simpa using hfz, hu⟩
  -- a good of `JL` goes to the owner
  have hJLo : ∀ {g j}, g ∈ JL → j = owner.getD d → ∃ o, owner = some o ∧ j = o := by
    intro g j hg hj
    cases ho : owner with
    | none => rw [hJL ho] at hg; simp at hg
    | some o => rw [ho] at hj; exact ⟨o, rfl, hj⟩
  -- per-agent facts, for every agent that is not the owner
  have perj_up : ∀ j, j ∈ up → owner ≠ some j → ∀ g ∈ goods,
      build P agents up Y J owner JL d g = j → g = P.b j ∨ g = P.c j := by
    intro j hj hjo g hg hX
    rcases hold hg hX with ⟨-, hY⟩ | ⟨-, -, hc⟩ | ⟨hJ, hjo'⟩ | hf
    · rw [pickRank_one (hinv.2.2.2 j hj).1] at hY; cases hY; exact Or.inl rfl
    · exact Or.inr hc.symm
    · obtain ⟨o, ho, rfl⟩ := hJLo hJ hjo'; exact absurd ho hjo
    · exact absurd hj (hfillj hf).2.2
  have perj_fz : ∀ j, j ∉ up → ∀ y, Y j = some y → P.NA agents (· ∈ up) Y y → ∀ g ∈ goods,
      build P agents up Y J owner JL d g = j → g = y := by
    intro j hj y hy hna g hg hX
    have hfz : frozenB P agents up Y j = true := by
      unfold frozenB; rw [hy]; exact naB_iff.mpr hna
    rcases hold hg hX with ⟨-, hY⟩ | ⟨-, hj', -⟩ | ⟨hJ, hjo'⟩ | hf
    · rw [hy] at hY; cases hY; rfl
    · exact absurd hj' hj
    · obtain ⟨o, ho, rfl⟩ := hJLo hJ hjo'
      rw [(hown _ ho).1] at hfz; cases hfz
    · rw [(hfillj hf).2.1] at hfz; cases hfz
  have perj_sl : ∀ j, j ∉ up → owner ≠ some j → (∀ y, Y j = some y → ¬ P.NA agents (· ∈ up) Y y) →
      ((bundle goods (build P agents up Y J owner JL d) j).filter (fun g => Y j ≠ some g)).length ≤
        (if Y j = none then 2 else 1) := by
    intro j hj hjo hnf
    have hS : ∀ g ∈ (bundle goods (build P agents up Y J owner JL d) j).filter
        (fun g => Y j ≠ some g),
        fill (slotsExcept (cap P agents up Y) owner) agents (rest J JL).reverse g = some j := by
      intro g hgS
      obtain ⟨hgb, hne⟩ := List.mem_filter.mp hgS
      obtain ⟨hg, hX⟩ := mem_bundle.mp hgb
      rcases hold hg hX with ⟨-, hY⟩ | ⟨-, hj', -⟩ | ⟨hJ, hjo'⟩ | hf
      · simp [hY] at hne
      · exact absurd hj' hj
      · obtain ⟨o, ho, rfl⟩ := hJLo hJ hjo'; exact absurd ho hjo
      · exact hf
    have hc := fill_count hag ((nodup_bundle hgd _ j).sublist List.filter_sublist) hS
    have hfz : frozenB P agents up Y j = false := by
      unfold frozenB
      cases hy : Y j with
      | none => rfl
      | some y =>
        show naB P agents up Y y = false
        cases hb : naB P agents up Y y with
        | false => rfl
        | true => exact absurd (naB_iff.mp hb) (hnf y hy)
    have : slotsExcept (cap P agents up Y) owner j = if Y j = none then 2 else 1 := by
      simp [slotsExcept, cap, hjo, hfz, hj]
    omega
  refine ⟨fun k y hk => ?_, hY3, fun k _ hk => ?_, fun j _ hj => perj_fz j hj,
    fun j _ hjo hj hnf => perj_sl j hj (fun ho => hjo (by simp [ho])) hnf, fun hbig => ?_⟩
  · -- `pick`
    obtain ⟨hka, hyg, hr⟩ := hY1 k y hk
    refine ⟨hyg, ?_, hr⟩
    cases hp : picker agents Y y with
    | none => exact absurd hk (picker_none hp k hka)
    | some k' =>
      have := picker_some hp
      have hkk := hY2 k' k y this.2 hk
      unfold build; rw [hp]; exact hkk
  · -- `upgraded`
    obtain ⟨h1, h2, h3, h4, h5⟩ := hinv.2.2.2 k hk
    have hc0 := List.mem_filter.mp h3
    have hpn : picker agents Y (P.c k) = none := by simpa using hc0.2
    refine ⟨pickRank_one h1, hc0.1, ?_, h2, fun hko => perj_up k hk (fun ho => hko (by simp [ho]))⟩
    unfold build; rw [hpn]
    cases hu : upOf P up (P.c k) with
    | none => exact absurd rfl (upOf_none hu k hk)
    | some k' => exact h5 k' (upOf_some hu).1 (upOf_some hu).2
  · -- `owner`
    rcases (show owner = none ∨ ∃ o, owner = some o by cases owner <;> simp) with ho | ⟨o, ho⟩
    · have e : owner.getD d = d := by simp [ho]
      rw [e] at hbig
      have hd := bundle_length_le_two (P := P) (agents := agents) (U := (· ∈ up)) (Y := Y) hgd
        (j := d) (fun hu => perj_up d hu (by simp [ho])) (fun hu => perj_fz d hu)
        (fun hu hnf => perj_sl d hu (by simp [ho]) hnf)
      exact absurd hbig (by omega)
    · have e : owner.getD d = o := by simp [ho]
      rw [e] at hbig ⊢
      intro k hk hko hku hYk hboth
      have hok := (hown o ho).2
      simp only [ownerOK, List.all_eq_true] at hok
      have := hok k hk
      have hr : P.pickRank Y k = 0 := by
        unfold Profile.pickRank; rw [hYk]; exact Profile.rank_a k
      -- `o`'s bundle lies in `L`
      have hL : ∀ g ∈ bundle goods (build P agents up Y J owner JL d) o,
          g ∈ (match Y o with | none => [] | some y => [y]) ++
            (if up.contains o then [P.c o] else []) ++ JL := by
        intro g hgb
        obtain ⟨hg, hX⟩ := mem_bundle.mp hgb
        rcases hold hg hX with ⟨-, hY⟩ | ⟨-, hou, hc⟩ | ⟨hJ, -⟩ | hf
        · simp [hY]
        · simp [hou, hc]
        · simp [hJ]
        · exact absurd ho (hfillj hf).1
      have hb := hL _ hboth.1
      have hc := hL _ hboth.2
      simp [hko, hku, hr] at this
      simp at hb hc
      grind

end assembly

/-- Whatever `lb` returns satisfies the hypotheses of Theorem 1, with LB's picks, upgraded agents and
owner (any agent when the junk fits the slots). -/
theorem lb_hyp {P : Profile A G} {agents : List A} {goods : List G} {order : List A} {d : A}
    (hag : agents.Nodup) (hgd : goods.Nodup) (hord : order.Nodup)
    (hperm : ∀ i, i ∈ order ↔ i ∈ agents) {X : G → A} (h : lb P agents goods order d = some X) :
    ∃ (U : A → Prop) (o : A), Hyp P agents goods X (phase1 P order goods) U o := by
  obtain ⟨h1, h2, h3⟩ := phase1_spec P order goods hord hgd
  have hY1 : ∀ k y, phase1 P order goods k = some y → k ∈ agents ∧ y ∈ goods ∧ P.rank k y < 3 :=
    fun k y hk => by obtain ⟨a, b, c⟩ := h1 k y hk; exact ⟨(hperm k).mp a, b, c⟩
  have hY3 : ∀ i ∈ agents, ∀ g ∈ goods, P.Prefers (phase1 P order goods) i g →
      ∃ k, phase1 P order goods k = some g := fun i hi => h3 i ((hperm i).mpr hi)
  have hinv := upInv_upgrades P agents (phase1 P order goods)
    (goods.filter (fun g => (picker agents (phase1 P order goods) g).isNone)) agents.length [] _
    (upInv_init P agents _ (hgd.sublist List.filter_sublist))
  unfold lb at h
  simp only at h
  split at h
  · rename_i hfit
    cases h
    refine ⟨_, _, build_hyp hag hgd hY1 h2 hY3 hinv ?_ (fun _ => rfl) (fun o ho => by cases ho)⟩
    have e1 : ∀ J : List G, rest J [] = J := fun J => by simp [rest]
    have e2 : ∀ s : A → Nat, slotsExcept s none = s := fun s => by funext k; simp [slotsExcept]
    rw [e1, e2]
    exact hfit
  · split at h
    · cases h
    · rename_i q hq
      cases h
      have hv := List.find?_some hq
      simp only [validOwner, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hv
      obtain ⟨⟨hfz, hfit⟩, hok⟩ := hv
      exact ⟨_, _, build_hyp hag hgd hY1 h2 hY3 hinv hfit (fun ho => by cases ho)
        (fun o ho => by cases ho; exact ⟨hfz, hok⟩)⟩

/-- **Theorem 1 (soundness of LB), over lists.** If construction LB, run with any processing order
of the agents in Phase 1, returns an allocation `X`, then `X` is EFX₀ for every additive valuation
consistent with the rankings, and at most one bundle of `X` has more than two goods. -/
theorem lb_sound {P : Profile A G} {agents : List A} {goods : List G} {order : List A} {d : A}
    (hag : agents.Nodup) (hgd : goods.Nodup) (hord : order.Nodup)
    (hperm : ∀ i, i ∈ order ↔ i ∈ agents) {X : G → A} (h : lb P agents goods order d = some X) :
    (∀ v : A → G → Nat, P.Consistent agents v → EFX0L v agents goods X) ∧
    ∃ o, ∀ j ∈ agents, j ≠ o → (bundle goods X j).length ≤ 2 := by
  obtain ⟨U, o, hH⟩ := lb_hyp hag hgd hord hperm h
  exact ⟨fun v hv => hH.efx0 hgd hv, o, hH.length_le_two hgd⟩

/-- **Theorem 1 (soundness of LB), in the model's terms.** Agents `Fin n`, goods `Fin m`, a ranking
profile `P`, and any processing order of the agents for Phase 1 (LB's adaptive order is one). If LB
returns an allocation `X`, then `X` is EFX₀ for every additive valuation consistent with `P`, and all
bundles but one have at most two goods. -/
theorem lb_sound_model {n m : Nat} (P : Profile (Fin n) (Fin m)) (order : List (Fin n))
    (hord : order.Nodup) (hperm : ∀ i, i ∈ order) (d : Fin n) {X : Fin m → Fin n}
    (h : lb P (List.finRange n) (List.finRange m) order d = some X) :
    (∀ v : Fin n → Fin m → Nat, P.Consistent (List.finRange n) v → (Inst.mk n m v).EFX0 X) ∧
    ∃ o, ∀ j, j ≠ o → finSum m (fun g => if X g = j then 1 else 0) ≤ 2 := by
  obtain ⟨U, o, hH⟩ := lb_hyp (List.nodup_finRange n) (List.nodup_finRange m) hord
    (fun i => ⟨fun _ => List.mem_finRange i, fun _ => hperm i⟩) h
  exact ⟨(sound hH).1, o, (sound hH).2⟩

/-! ## Examples (checked by `decide`; the allocations are those of `src/construct.py`) -/

/-- Two agents ranking the goods `0 > 1 > 2` alike (n = 2, m = 3): agent 0 takes `0`; agent 1 picks
`1` and is upgraded with `2`. -/
example : (lb (⟨fun _ => 0, fun _ => 1, fun _ => 2⟩ : Profile Nat Nat) [0, 1] [0, 1, 2] [0, 1] 0).map
    (fun X => [0, 1, 2].map X) = some [0, 1, 1] := by decide

/-- Core H3 (`proofs/construction.md` §1; n = 3, m = 5, every agent ranks `0 > 1 >` its private good):
LB returns `{0}, {1}, {2, 3, 4}`, the large bundle owned by agent 2. -/
example : (lb (⟨fun _ => 0, fun _ => 1, fun i => i + 2⟩ : Profile Nat Nat) [0, 1, 2] [0, 1, 2, 3, 4]
    [0, 1, 2] 0).map (fun X => [0, 1, 2, 3, 4].map X) = some [0, 1, 2, 2, 2] := by decide

end LB
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB.phase1_spec
#print axioms EFX.LB.lb_hyp
#print axioms EFX.LB.lb_sound
#print axioms EFX.LB.lb_sound_model
