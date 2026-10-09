import EFX.Bridge

/-!
# Soundness of construction LB (LEDGER S2.S, `proofs/construction.md` §3, Theorem 1)

Theorem 1 says that every allocation construction LB returns is EFX₀ for every additive valuation
consistent with the rankings, and has at most one bundle of more than two goods. Its proof uses only a
few properties of LB's output. This file states them as `Hyp` and proves that they imply both
conclusions; `EFX.LBRun` defines LB and proves that its output satisfies `Hyp` (`EFX.LB.lb_hyp`).

A ranking profile `P` gives each agent `i` three distinct goods `a i`, `b i`, `c i`. A valuation is
consistent with `P` (`Profile.Consistent`) if agent `i` values exactly these three goods, with
`a i ≥ b i ≥ c i > 0` (ties allowed) and `a i ≤ b i + c i` (every core agent has `a i < b i + c i`). An allocation `X` comes with picks
`Y : A → Option G` (LB's Phase 1), a set `U` of upgraded agents and an owner `o` (Phase 2).
`NA` is the set of goods that some agent outside `U` ranks above its pick (all three of its goods if
it has no pick). `Hyp` asks:
- `pick`: each pick is one of the picker's three goods, and the picker holds it;
- `i1`: invariant (I1): a good that an agent ranks above its pick was picked;
- `upgraded`: an agent of `U` picked its `b`, holds its `c`, and its `b` is not in `NA`; unless it is
  the owner, it holds nothing else (LB's implementation lets an upgraded agent own the large bundle);
- `frozen`: an agent outside `U` whose pick is in `NA` holds only its pick;
- `slots`: every other agent outside `U` except `o` holds at most 1 good beyond its pick, or at most
  2 goods if it has no pick;
- `owner`: if `o`'s bundle has more than two goods, it does not contain both `b k` and `c k` of an
  agent `k ≠ o` outside `U` whose pick is its top `a k` (the owner constraint).

Invariant (I2) and the order in which (I1) says goods were picked are not needed, and neither is
anything about how the junk was split beyond the slots; the theorem therefore covers every tie-break
and every choice of owner and overflow set.

- `EFX.LB.Hyp.efx0`: `Hyp` ⟹ EFX₀ over lists, for every consistent valuation.
- `EFX.LB.Hyp.length_le_two`: `Hyp` ⟹ every bundle except `o`'s has at most two goods.
- `EFX.LB.sound`: both, in the model's terms (`EFX.Inst.EFX0`).

As in the written proof, the argument uses only the envier's own values: L5 is not used.
-/

namespace EFX
namespace LB

variable {A G : Type}

/-- A ranking profile: agent `i` ranks its three goods `a i`, `b i`, `c i` in this order. -/
structure Profile (A G : Type) where
  a : A → G
  b : A → G
  c : A → G

namespace Profile
variable [DecidableEq G] (P : Profile A G)

/-- The rank of `g` for `i`: `0`, `1`, `2` for `a i`, `b i`, `c i`, and `3` for a good `i` does not
value. -/
def rank (i : A) (g : G) : Nat :=
  if g = P.a i then 0 else if g = P.b i then 1 else if g = P.c i then 2 else 3

/-- An additive valuation consistent with the profile on `agents`: agent `i` values its three distinct
goods `a i ≥ b i ≥ c i > 0` (ties allowed), `a i ≤ b i + c i` (core agents are balanced,
`a i < b i + c i`), and values nothing else. -/
def Consistent (agents : List A) (v : A → G → Nat) : Prop :=
  ∀ i ∈ agents, 0 < v i (P.c i) ∧ v i (P.c i) ≤ v i (P.b i) ∧ v i (P.b i) ≤ v i (P.a i) ∧
    v i (P.a i) ≤ v i (P.b i) + v i (P.c i) ∧ (∀ g, P.rank i g = 3 → v i g = 0) ∧
    P.a i ≠ P.b i ∧ P.a i ≠ P.c i ∧ P.b i ≠ P.c i

variable {P}

theorem value_eq {agents : List A} {v : A → G → Nat} (hv : P.Consistent agents v) {i : A}
    (hi : i ∈ agents) : ∀ {S : List G}, S.Nodup →
    value v i S = (if P.a i ∈ S then v i (P.a i) else 0) + (if P.b i ∈ S then v i (P.b i) else 0) +
      (if P.c i ∈ S then v i (P.c i) else 0)
  | [], _ => by simp
  | g :: S, h => by
    have ih := value_eq hv hi (List.nodup_cons.mp h).2
    have hg := (List.nodup_cons.mp h).1
    obtain ⟨h1, h2, h3, h4, h0, hab, hac, hbc⟩ := hv i hi
    rw [value_cons, ih]
    unfold rank at h0
    by_cases ha : g = P.a i <;> by_cases hb : g = P.b i <;> by_cases hc : g = P.c i <;>
      simp_all <;> grind

/-- The rank of `i`'s pick, `3` if it has none. -/
def pickRank (P : Profile A G) (Y : A → Option G) (i : A) : Nat :=
  match Y i with
  | none => 3
  | some y => P.rank i y

/-- `i` ranks `g` above its pick `Y i`; every good `i` values if it has no pick. -/
def Prefers (P : Profile A G) (Y : A → Option G) (i : A) (g : G) : Prop :=
  P.rank i g < P.pickRank Y i

instance (P : Profile A G) (Y : A → Option G) (i : A) (g : G) : Decidable (P.Prefers Y i g) :=
  inferInstanceAs (Decidable (_ < _))

/-- `NA`: the goods that some listed agent outside `U` (not upgraded) ranks above its pick. -/
def NA (P : Profile A G) (agents : List A) (U : A → Prop) (Y : A → Option G) (g : G) : Prop :=
  ∃ i ∈ agents, ¬ U i ∧ P.Prefers Y i g

theorem rank_le {agents : List A} {v : A → G → Nat} (hv : P.Consistent agents v) {i : A}
    (hi : i ∈ agents) {g h : G} (hgh : P.rank i g ≤ P.rank i h) : v i h ≤ v i g := by
  obtain ⟨h1, h2, h3, h4, h0, hab, hac, hbc⟩ := hv i hi
  have e3 : P.rank i g = 3 → v i g = 0 := h0 g
  have f3 : P.rank i h = 3 → v i h = 0 := h0 h
  unfold rank at hgh e3 f3
  by_cases ha : g = P.a i <;> by_cases hb : g = P.b i <;> by_cases hc : g = P.c i <;>
    by_cases ha' : h = P.a i <;> by_cases hb' : h = P.b i <;> by_cases hc' : h = P.c i <;>
    simp_all <;> omega

theorem rank_a (i : A) : P.rank i (P.a i) = 0 := by simp [rank]

theorem rank_b {agents : List A} {v : A → G → Nat} (hv : P.Consistent agents v) {i : A}
    (hi : i ∈ agents) : P.rank i (P.b i) = 1 := by
  obtain ⟨-, -, -, -, -, hab, -, -⟩ := hv i hi
  simp [rank, Ne.symm hab]

theorem rank_c {agents : List A} {v : A → G → Nat} (hv : P.Consistent agents v) {i : A}
    (hi : i ∈ agents) : P.rank i (P.c i) = 2 := by
  obtain ⟨-, -, -, -, -, -, hac, hbc⟩ := hv i hi
  simp [rank, Ne.symm hac, Ne.symm hbc]

end Profile

open Profile

/-! ## Counting lemmas -/

theorem length_le_one {S : List G} (hS : S.Nodup) {y : G} (h : ∀ g ∈ S, g = y) : S.length ≤ 1 := by
  match S, hS, h with
  | [], _, _ => simp
  | [_], _, _ => simp
  | g :: g' :: t, hS, h =>
    have e1 := h g (by simp)
    have e2 := h g' (by simp)
    subst e1
    exact absurd (by simp [e2]) (List.nodup_cons.mp hS).1

theorem length_filter_add (S : List G) (p : G → Bool) :
    S.length = (S.filter p).length + (S.filter (fun g => !p g)).length := by
  induction S with
  | nil => simp
  | cons g S ih => by_cases hp : p g = true <;> simp [hp, ih] <;> omega

theorem length_le_two [DecidableEq G] {S : List G} (hS : S.Nodup) {x y : G}
    (h : ∀ g ∈ S, g = x ∨ g = y) : S.length ≤ 2 := by
  rw [length_filter_add S (fun g => decide (g = x))]
  have h1 := length_le_one (hS.sublist List.filter_sublist) (y := x) (S := S.filter (fun g => decide (g = x)))
    (fun g hg => by simpa using (List.mem_filter.mp hg).2)
  have h2 := length_le_one (hS.sublist List.filter_sublist) (y := y)
    (S := S.filter (fun g => !decide (g = x)))
    (fun g hg => by
      have ⟨hgS, hgx⟩ := List.mem_filter.mp hg
      simp at hgx
      exact (h g hgS).resolve_left hgx)
  omega

variable [DecidableEq A]

theorem mem_bundle {goods : List G} {X : G → A} {j : A} {g : G} :
    g ∈ bundle goods X j ↔ g ∈ goods ∧ X g = j := by
  simp [bundle]

theorem nodup_bundle {goods : List G} (hg : goods.Nodup) (X : G → A) (j : A) :
    (bundle goods X j).Nodup :=
  hg.sublist List.filter_sublist

variable [DecidableEq G]

/-- The hypotheses of Theorem 1 (`proofs/construction.md` §3) on an allocation `X` of `goods` to
`agents`, built from picks `Y`, a set `U` of upgraded agents and an owner `o`:
- `pick`: each pick is a good `k` values, and `k` holds it;
- `i1`: invariant (I1), in the form the proof uses: a good that an agent ranks above its pick was picked
  (by some agent; LB's stronger "before `i`" is not needed);
- `upgraded`: an upgraded agent picked its `b`, holds its `c`, and its `b` is not in `NA`; unless it
  is the owner, it holds nothing else;
- `frozen`: an agent that is not upgraded and whose pick is in `NA` holds only its pick;
- `slots`: every other agent except the owner holds, beyond its pick, at most its slots (1 with a pick,
  2 without);
- `owner`: if the owner's bundle has more than two goods, it contains `b k` and `c k` of no other agent
  `k` that is not upgraded and picked its top `a k`.
Invariant (I2) is not needed. -/
structure Hyp (P : Profile A G) (agents : List A) (goods : List G) (X : G → A) (Y : A → Option G)
    (U : A → Prop) (o : A) : Prop where
  pick : ∀ k y, Y k = some y → y ∈ goods ∧ X y = k ∧ P.rank k y < 3
  i1 : ∀ i ∈ agents, ∀ g ∈ goods, P.Prefers Y i g → ∃ k, Y k = some g
  upgraded : ∀ k ∈ agents, U k → Y k = some (P.b k) ∧ P.c k ∈ goods ∧ X (P.c k) = k ∧
    ¬ P.NA agents U Y (P.b k) ∧ (k ≠ o → ∀ g ∈ goods, X g = k → g = P.b k ∨ g = P.c k)
  frozen : ∀ j ∈ agents, ¬ U j → ∀ y, Y j = some y → P.NA agents U Y y →
    ∀ g ∈ goods, X g = j → g = y
  slots : ∀ j ∈ agents, j ≠ o → ¬ U j → (∀ y, Y j = some y → ¬ P.NA agents U Y y) →
    ((bundle goods X j).filter (fun g => Y j ≠ some g)).length ≤ (if Y j = none then 2 else 1)
  owner : 2 < (bundle goods X o).length → ∀ k ∈ agents, k ≠ o → ¬ U k → Y k = some (P.a k) →
    ¬ (P.b k ∈ bundle goods X o ∧ P.c k ∈ bundle goods X o)

variable {P : Profile A G} {agents : List A} {goods : List G} {X : G → A} {Y : A → Option G}
  {U : A → Prop} {o : A}

/-- A bundle has at most two goods if its holder, when upgraded, holds only its `b` and `c`; when
frozen, only its pick; and otherwise at most its slots beyond its pick. -/
theorem bundle_length_le_two (hg : goods.Nodup) {j : A}
    (hup : U j → ∀ g ∈ goods, X g = j → g = P.b j ∨ g = P.c j)
    (hfz : ¬ U j → ∀ y, Y j = some y → P.NA agents U Y y → ∀ g ∈ goods, X g = j → g = y)
    (hsl : ¬ U j → (∀ y, Y j = some y → ¬ P.NA agents U Y y) →
      ((bundle goods X j).filter (fun g => Y j ≠ some g)).length ≤ (if Y j = none then 2 else 1)) :
    (bundle goods X j).length ≤ 2 := by
  have hnd := nodup_bundle hg X j
  by_cases hU : U j
  · exact EFX.LB.length_le_two hnd
      (fun g hg' => hup hU g (mem_bundle.mp hg').1 (mem_bundle.mp hg').2)
  by_cases hfz' : ∃ y, Y j = some y ∧ P.NA agents U Y y
  · obtain ⟨y, hy, hna⟩ := hfz'
    have := length_le_one hnd (y := y)
      (fun g hg' => hfz hU y hy hna g (mem_bundle.mp hg').1 (mem_bundle.mp hg').2)
    omega
  have hsl := hsl hU (fun y hy hna => hfz' ⟨y, hy, hna⟩)
  rw [length_filter_add (bundle goods X j) (fun g => decide (Y j ≠ some g))]
  cases hY : Y j with
  | none =>
    rw [hY] at hsl
    have h0 : (bundle goods X j).filter (fun g => !decide ((none : Option G) ≠ some g)) = [] := by
      rw [List.filter_eq_nil_iff]; intro g _; simp
    have h2 : (if (none : Option G) = none then 2 else 1) = 2 := by simp
    rw [h0]; simp only [List.length_nil]; omega
  | some y =>
    rw [hY] at hsl
    have h1 := length_le_one (hnd.sublist List.filter_sublist) (y := y)
      (S := (bundle goods X j).filter (fun g => !decide (some y ≠ some g)))
      (fun g hg' => by
        have := (List.mem_filter.mp hg').2
        simp at this
        exact this.symm)
    have h2 : (if some y = none then 2 else 1) = 1 := by simp
    omega

/-- Every bundle except the owner's has at most two goods. -/
theorem Hyp.length_le_two (h : Hyp P agents goods X Y U o) (hg : goods.Nodup) :
    ∀ j ∈ agents, j ≠ o → (bundle goods X j).length ≤ 2 := fun j hj hjo =>
  bundle_length_le_two hg (fun hU => ((h.upgraded j hj hU).2.2.2.2 hjo)) (h.frozen j hj)
    (h.slots j hj hjo)

/-- A good in a bundle of at least two goods is not in `NA`: it is the holder's pick, which is not in
`NA` since the holder is neither frozen nor (being upgraded) has its pick in `NA`, or it is junk, and
junk is not in `NA` by (I1). -/
theorem Hyp.not_NA (h : Hyp P agents goods X Y U o) (hg : goods.Nodup) {j : A} (hj : j ∈ agents)
    (hlen : 2 ≤ (bundle goods X j).length) {x : G} (hx : x ∈ bundle goods X j) :
    ¬ P.NA agents U Y x := by
  intro hna
  obtain ⟨hxg, hXx⟩ := mem_bundle.mp hx
  obtain ⟨i, hi, -, hpref⟩ := id hna
  obtain ⟨k, hk⟩ := h.i1 i hi x hxg hpref
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

/-- **Theorem 1 (soundness), abstract form.** An allocation satisfying `Hyp` is EFX₀ for every additive
valuation consistent with the rankings. -/
theorem Hyp.efx0 (h : Hyp P agents goods X Y U o) (hg : goods.Nodup) {v : A → G → Nat}
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
  · -- `i` is upgraded: it holds `b i` and `c i`, worth more than `a i`
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
          have hjo : j = o := by
            refine Classical.byContradiction fun hjo => ?_
            have := h.length_le_two hg j hj hjo
            omega
          subst hjo
          exact absurd hboth (h.owner hbig i hi hij hUi hY)
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

/-- The number of goods in `j`'s bundle, as a length. -/
theorem finSum_bundle_eq (m n : Nat) (X : Fin m → Fin n) (j : Fin n) :
    finSum m (fun g => if X g = j then 1 else 0) = (bundle (List.finRange m) X j).length := by
  rw [finSum_eq_sum, sum_map_ite (fun g => X g = j) (fun _ => 1), sum_map_one]
  rfl

/-- **Theorem 1 (soundness of LB), in the model's terms.** Let `X` be an allocation of goods `Fin m`
to agents `Fin n` satisfying `Hyp` for a ranking profile `P`, picks `Y`, upgraded agents `U` and an
owner `o`. Then `X` is EFX₀ for every additive valuation consistent with `P`, and every bundle other
than `o`'s has at most two goods. -/
theorem sound {n m : Nat} {P : Profile (Fin n) (Fin m)} {X : Fin m → Fin n}
    {Y : Fin n → Option (Fin m)} {U : Fin n → Prop} {o : Fin n}
    (h : Hyp P (List.finRange n) (List.finRange m) X Y U o) :
    (∀ v : Fin n → Fin m → Nat, P.Consistent (List.finRange n) v →
      (Inst.mk n m v).EFX0 X) ∧
    ∀ j, j ≠ o → finSum m (fun g => if X g = j then 1 else 0) ≤ 2 := by
  refine ⟨fun v hv => ?_, fun j hj => ?_⟩
  · exact (Inst.efx0_iff (Inst.mk n m v) X).mpr (h.efx0 (List.nodup_finRange m) hv)
  · rw [finSum_bundle_eq]
    exact h.length_le_two (List.nodup_finRange m) j (List.mem_finRange j) hj

end LB
end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.LB.Hyp.efx0
#print axioms EFX.LB.Hyp.length_le_two
#print axioms EFX.LB.sound
