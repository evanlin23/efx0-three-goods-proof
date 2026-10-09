import EFX.PeelingR2
import EFX.Bridge

/-!
# Junk goods and envy cycles (LEDGER L3)

Goods relevant to no agent ("junk") can always be added: allocate the other goods EFX₀, eliminate
envy cycles, and give all the junk to an agent that nobody envies (a source of the envy graph).

- `EFX.rotate_efx0`: moving bundles along a permutation `π` of the agents (the bundle of `a` goes to
  `π a`) keeps an allocation EFX₀ when every agent weakly prefers the bundle it receives.
- `EFX.exists_unenvied`: from any EFX₀ allocation, rotating envy cycles reaches an EFX₀ allocation
  in which some agent is envied by nobody. Each rotation strictly raises the welfare
  `Σ_a v_a(X_a)`, which is bounded, so the process stops.
- `EFX.junkToSource`: goods worthless to every agent go to that agent; the result is EFX₀.
- `EFX.junk`: L3 as the ledger states it, for the goods relevant to no agent.
- `EFX.Inst.exists_efx0_of_junk`: L3 in the model's terms: an allocation satisfying the EFX₀
  condition whenever the removed good is relevant to some agent can be turned into an EFX₀ one.

The cycle comes from pigeonhole: following "is envied by" from any agent must repeat, and a point
that repeats lies on a cycle of the map (take its least period).
-/

set_option autoImplicit false

namespace EFX

variable {A G : Type}

/-! ## Pigeonhole and cycles of a map -/

/-- Pigeonhole: a duplicate-free list inside `m` is no longer than `m`. -/
theorem length_le_of_nodup_of_subset [DecidableEq A] :
    ∀ {l m : List A}, l.Nodup → (∀ x ∈ l, x ∈ m) → l.length ≤ m.length
  | [], _, _, _ => Nat.zero_le _
  | x :: l, m, hnd, hsub => by
    have hx : x ∈ m := hsub x (by simp)
    have hxl : x ∉ l := (List.nodup_cons.mp hnd).1
    have ih := length_le_of_nodup_of_subset (m := m.erase x) (List.nodup_cons.mp hnd).2 (by
      intro y hy
      have hyx : y ≠ x := fun h => hxl (h ▸ hy)
      exact (List.mem_erase_of_ne hyx).mpr (hsub y (by simp [hy])))
    rw [List.length_erase_of_mem hx] at ih
    have := List.length_pos_of_mem hx
    simp only [List.length_cons]
    omega

/-- `iter e k a`: the map `e` applied `k` times to `a`. -/
def iter (e : A → A) : Nat → A → A
  | 0, a => a
  | k + 1, a => e (iter e k a)

theorem iter_add (e : A → A) (a : A) : ∀ j k : Nat, iter e (j + k) a = iter e j (iter e k a)
  | 0, k => by simp [iter]
  | j + 1, k => by rw [Nat.add_right_comm, iter, iter_add e a j k, iter]

theorem iter_mem (e : A → A) {S : List A} (he : ∀ a ∈ S, e a ∈ S) {a : A} (ha : a ∈ S) :
    ∀ k : Nat, iter e k a ∈ S
  | 0 => ha
  | k + 1 => he _ (iter_mem e he ha k)

/-- A map of a finite set into itself has a periodic point. -/
theorem exists_periodic [DecidableEq A] (e : A → A) {S : List A} (he : ∀ a ∈ S, e a ∈ S) {a : A}
    (ha : a ∈ S) : ∃ z ∈ S, ∃ p, 0 < p ∧ iter e p z = z := by
  -- two of the `|S| + 1` points `iter e k a`, `k ≤ |S|`, coincide
  have hrep : ∃ s t, s < t ∧ iter e s a = iter e t a := by
    apply Classical.byContradiction
    intro hno
    have hnd : ((List.range (S.length + 1)).map (fun k => iter e k a)).Nodup := by
      rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
      exact List.pairwise_lt_range.imp_of_mem (fun {s t} _ _ hst heq => hno ⟨s, t, hst, heq⟩)
    have hlen := length_le_of_nodup_of_subset hnd (by
      intro x hx
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
      exact iter_mem e he ha k)
    simp only [List.length_map, List.length_range] at hlen
    omega
  obtain ⟨s, t, hst, heq⟩ := hrep
  refine ⟨iter e s a, iter_mem e he ha s, t - s, by omega, ?_⟩
  rw [← iter_add, Nat.sub_add_cancel (Nat.le_of_lt hst), heq]

/-- A periodic point has a least period. -/
theorem exists_least_period (e : A → A) (z : A) {p : Nat} (hp : 0 < p) (hz : iter e p z = z) :
    ∃ p, 0 < p ∧ iter e p z = z ∧ ∀ q, 0 < q → q < p → iter e q z ≠ z := by
  induction p using Nat.strongRecOn with
  | _ p ih =>
    by_cases h : ∃ q, 0 < q ∧ q < p ∧ iter e q z = z
    · obtain ⟨q, hq0, hqp, hqz⟩ := h
      exact ih q hqp hq0 hqz
    · exact ⟨p, hp, hz, fun q hq0 hqp hqz => h ⟨q, hq0, hqp, hqz⟩⟩

/-- The orbit of a point `z` of least period `p` is a cycle of `e`: `e` maps it into itself,
injectively, and onto it. -/
theorem cycle_of_least_period (e : A → A) {z : A} {p : Nat} (hp : 0 < p) (hz : iter e p z = z)
    (hmin : ∀ q, 0 < q → q < p → iter e q z ≠ z) :
    let C : A → Prop := fun x => ∃ j, j < p ∧ iter e j z = x
    (∀ x, C x → C (e x)) ∧ (∀ x y, C x → C y → e x = e y → x = y) ∧
      (∀ y, C y → ∃ x, C x ∧ e x = y) := by
  intro C
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨j, hj, rfl⟩
    by_cases hjp : j + 1 < p
    · exact ⟨j + 1, hjp, rfl⟩
    · have : j + 1 = p := by omega
      have h1 : iter e (j + 1) z = z := by rw [this]; exact hz
      exact ⟨0, hp, h1.symm⟩
  · -- `e (iter j z) = e (iter k z)` with `j < k < p` would give `z` a period `p - k + j < p`
    have key : ∀ j k, j < k → k < p → iter e (j + 1) z = iter e (k + 1) z → False := by
      intro j k hjk hkp h
      apply hmin (p - (k + 1) + (j + 1)) (by omega) (by omega)
      rw [iter_add, h, ← iter_add, Nat.sub_add_cancel (by omega), hz]
    rintro x y ⟨j, hj, rfl⟩ ⟨k, hk, rfl⟩ h
    rcases Nat.lt_trichotomy j k with hjk | rfl | hkj
    · exact (key j k hjk hk h).elim
    · rfl
    · exact (key k j hkj hj h.symm).elim
  · rintro y ⟨k, hk, rfl⟩
    cases k with
    | zero =>
      refine ⟨iter e (p - 1) z, ⟨p - 1, by omega, rfl⟩, ?_⟩
      show iter e (p - 1 + 1) z = z
      rw [Nat.sub_add_cancel hp, hz]
    | succ k => exact ⟨iter e k z, ⟨k, by omega, rfl⟩, rfl⟩

/-- A cycle `C` of `e` inside `agents` gives a permutation of `agents`: `e` on `C`, the identity
elsewhere. -/
theorem exists_perm_of_cycle (e : A → A) (C : A → Prop) {agents : List A}
    (he : ∀ x ∈ agents, e x ∈ agents) (hCe : ∀ x, C x → C (e x))
    (hCinj : ∀ x y, C x → C y → e x = e y → x = y) (hCsurj : ∀ y, C y → ∃ x, C x ∧ e x = y)
    (hCmem : ∀ x, C x → x ∈ agents) :
    ∃ π : A → A, (∀ a ∈ agents, π a ∈ agents) ∧
      (∀ a ∈ agents, ∀ b ∈ agents, π a = π b → a = b) ∧ (∀ b ∈ agents, ∃ a ∈ agents, π a = b) ∧
      (∀ a, (C a ∧ π a = e a) ∨ (¬ C a ∧ π a = a)) := by
  classical
  refine ⟨fun x => if C x then e x else x, ?_, ?_, ?_, ?_⟩
  · intro a ha
    by_cases h : C a <;> simp [h, ha, he a ha]
  · intro a _ b _ hab
    by_cases ha : C a <;> by_cases hb : C b <;> simp only [ha, hb, ↓reduceIte] at hab
    · exact hCinj a b ha hb hab
    · exact absurd (hab ▸ hCe a ha) hb
    · exact absurd (hab ▸ hCe b hb) ha
    · exact hab
  · intro b hb
    by_cases h : C b
    · obtain ⟨a, ha, rfl⟩ := hCsurj b h
      exact ⟨a, hCmem a ha, by simp [ha]⟩
    · exact ⟨b, hb, by simp [h]⟩
  · intro a
    by_cases h : C a
    · exact Or.inl ⟨h, by simp [h]⟩
    · exact Or.inr ⟨h, by simp [h]⟩

/-! ## Rotating bundles -/

theorem sum_map_le {l : List A} {f g : A → Nat} (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h a (by simp)
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

theorem sum_map_lt {l : List A} {f g : A → Nat} (h : ∀ a ∈ l, f a ≤ g a)
    (hlt : ∃ a ∈ l, f a < g a) : (l.map f).sum < (l.map g).sum := by
  induction l with
  | nil => obtain ⟨a, ha, _⟩ := hlt; simp at ha
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    obtain ⟨b, hb, hfg⟩ := hlt
    rcases List.mem_cons.mp hb with rfl | hb
    · have := sum_map_le (l := l) (fun x hx => h x (List.mem_cons_of_mem _ hx))
      omega
    · have := h a (by simp)
      have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) ⟨b, hb, hfg⟩
      omega

variable [DecidableEq A]

/-- Agent `a` envies agent `b` under `X`. -/
def Envies (v : A → G → Nat) (goods : List G) (X : G → A) (a b : A) : Prop :=
  value v a (bundle goods X a) < value v a (bundle goods X b)

/-- Utilitarian welfare `Σ_a v_a(X_a)`. -/
def welfare (v : A → G → Nat) (agents : List A) (goods : List G) (X : G → A) : Nat :=
  (agents.map (fun a => value v a (bundle goods X a))).sum

/-- Welfare is bounded by what the agents would get from all goods. -/
theorem welfare_le (v : A → G → Nat) (agents : List A) (goods : List G) (X : G → A) :
    welfare v agents goods X ≤ (agents.map (fun a => value v a goods)).sum :=
  sum_map_le (fun a _ => value_sublist v a List.filter_sublist)

theorem bundle_comp {agents : List A} {goods : List G} {X : G → A} {π : A → A}
    (hX : IsAllocation agents goods X) (hinj : ∀ a ∈ agents, ∀ b ∈ agents, π a = π b → a = b)
    {a : A} (ha : a ∈ agents) : bundle goods (fun g => π (X g)) (π a) = bundle goods X a := by
  unfold bundle
  apply List.filter_congr
  intro g hg
  by_cases h : X g = a
  · simp [h]
  · have hne : π (X g) ≠ π a := fun e => h (hinj _ (hX g hg) _ ha e)
    simp [h, hne]

variable [DecidableEq G]

/-- **Rotation preserves EFX₀.** Move every bundle along a permutation `π` of the agents (the
bundle of `a` goes to `π a`). If every agent weakly prefers the bundle it receives to its own, the
new allocation is EFX₀ whenever the old one is. -/
theorem rotate_efx0 (v : A → G → Nat) {agents : List A} {goods : List G} {X : G → A}
    {π : A → A} (hX : IsAllocation agents goods X) (hE : EFX0L v agents goods X)
    (hmaps : ∀ a ∈ agents, π a ∈ agents)
    (hinj : ∀ a ∈ agents, ∀ b ∈ agents, π a = π b → a = b)
    (hsurj : ∀ b ∈ agents, ∃ a ∈ agents, π a = b)
    (hgain : ∀ a ∈ agents,
      value v (π a) (bundle goods X (π a)) ≤ value v (π a) (bundle goods X a)) :
    IsAllocation agents goods (fun g => π (X g)) ∧ EFX0L v agents goods (fun g => π (X g)) := by
  refine ⟨fun g hg => hmaps _ (hX g hg), ?_⟩
  intro x hx y hy hxy g hg
  obtain ⟨ax, hax, rfl⟩ := hsurj x hx
  obtain ⟨ay, hay, rfl⟩ := hsurj y hy
  rw [bundle_comp hX hinj hay] at hg ⊢
  rw [bundle_comp hX hinj hax]
  have hgx := hgain ax hax
  by_cases hayx : ay = π ax
  · -- the bundle `π ax` looks at is its own old bundle
    rw [hayx] at hg ⊢
    calc value v (π ax) ((bundle goods X (π ax)).erase g)
        _ ≤ value v (π ax) (bundle goods X (π ax)) := value_sublist v _ List.erase_sublist
        _ ≤ value v (π ax) (bundle goods X ax) := hgx
  · exact Nat.le_trans (hE (π ax) (hmaps ax hax) ay hay (Ne.symm hayx) g hg) hgx

/-- If every agent is envied by some agent, rotating an envy cycle gives an EFX₀ allocation of
strictly larger welfare. -/
theorem exists_rotation (v : A → G → Nat) {agents : List A} {goods : List G} {X : G → A}
    (hX : IsAllocation agents goods X) (hE : EFX0L v agents goods X) (hne : agents ≠ [])
    (henv : ∀ b ∈ agents, ∃ a ∈ agents, Envies v goods X a b) :
    ∃ Y : G → A, IsAllocation agents goods Y ∧ EFX0L v agents goods Y ∧
      welfare v agents goods X < welfare v agents goods Y := by
  -- `e b`: an agent that envies `b`
  obtain ⟨e, he⟩ : ∃ e : A → A, ∀ b, b ∈ agents → e b ∈ agents ∧ Envies v goods X (e b) b := by
    apply Classical.axiomOfChoice (r := fun b a => b ∈ agents → a ∈ agents ∧ Envies v goods X a b)
    intro b
    by_cases hb : b ∈ agents
    · obtain ⟨a, ha, hab⟩ := henv b hb
      exact ⟨a, fun _ => ⟨ha, hab⟩⟩
    · exact ⟨b, fun h => absurd h hb⟩
  have hemaps : ∀ b ∈ agents, e b ∈ agents := fun b hb => (he b hb).1
  obtain ⟨a0, ha0⟩ : ∃ a, a ∈ agents := List.exists_mem_of_ne_nil agents hne
  obtain ⟨z, hz, p0, hp0, hzp0⟩ := exists_periodic e hemaps ha0
  obtain ⟨p, hp, hzp, hmin⟩ := exists_least_period e z hp0 hzp0
  obtain ⟨hCe, hCinj, hCsurj⟩ := cycle_of_least_period e hp hzp hmin
  obtain ⟨π, hmaps, hinj, hsurj, hπ⟩ := exists_perm_of_cycle e _ hemaps hCe hCinj hCsurj
    (by rintro x ⟨j, _, rfl⟩; exact iter_mem e hemaps hz j)
  -- every agent weakly gains, and the agents on the cycle strictly gain
  have hgain : ∀ a ∈ agents,
      value v (π a) (bundle goods X (π a)) ≤ value v (π a) (bundle goods X a) := by
    intro a ha
    rcases hπ a with ⟨_, h⟩ | ⟨_, h⟩
    · rw [h]; exact Nat.le_of_lt (he a ha).2
    · rw [h]; exact Nat.le_refl _
  obtain ⟨hY, hEY⟩ := rotate_efx0 v hX hE hmaps hinj hsurj hgain
  refine ⟨fun g => π (X g), hY, hEY, ?_⟩
  apply sum_map_lt
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := hsurj b hb
    rw [bundle_comp hX hinj ha]
    exact hgain a ha
  · refine ⟨π z, hmaps z hz, ?_⟩
    rw [bundle_comp hX hinj hz]
    rcases hπ z with ⟨_, h⟩ | ⟨h, _⟩
    · rw [h]; exact (he z hz).2
    · exact absurd ⟨0, hp, rfl⟩ h

/-- **Envy-cycle elimination.** Every EFX₀ allocation can be turned into an EFX₀ allocation of the
same goods in which some agent is envied by nobody (a source of the envy graph). -/
theorem exists_unenvied (v : A → G → Nat) {agents : List A} {goods : List G} (hne : agents ≠ [])
    {X : G → A} (hX : IsAllocation agents goods X) (hE : EFX0L v agents goods X) :
    ∃ Y : G → A, IsAllocation agents goods Y ∧ EFX0L v agents goods Y ∧
      ∃ s ∈ agents, ∀ a ∈ agents, ¬ Envies v goods Y a s := by
  -- induction on the welfare still available
  suffices h : ∀ k : Nat, ∀ X : G → A,
      (agents.map (fun a => value v a goods)).sum - welfare v agents goods X ≤ k →
      IsAllocation agents goods X → EFX0L v agents goods X →
      ∃ Y : G → A, IsAllocation agents goods Y ∧ EFX0L v agents goods Y ∧
        ∃ s ∈ agents, ∀ a ∈ agents, ¬ Envies v goods Y a s from h _ X (Nat.le_refl _) hX hE
  intro k
  induction k with
  | zero =>
    intro X hk hX hE
    apply Classical.byContradiction
    intro hno
    obtain ⟨Y, _, _, hlt⟩ := exists_rotation v hX hE hne (by
      intro b hb
      apply Classical.byContradiction
      intro hnb
      exact hno ⟨X, hX, hE, b, hb, fun a ha hab => hnb ⟨a, ha, hab⟩⟩)
    have := welfare_le v agents goods Y
    omega
  | succ k ih =>
    intro X hk hX hE
    by_cases hs : ∃ s ∈ agents, ∀ a ∈ agents, ¬ Envies v goods X a s
    · exact ⟨X, hX, hE, hs⟩
    · obtain ⟨Y, hY, hEY, hlt⟩ := exists_rotation v hX hE hne (by
        intro b hb
        apply Classical.byContradiction
        intro hnb
        exact hs ⟨b, hb, fun a ha hab => hnb ⟨a, ha, hab⟩⟩)
      have := welfare_le v agents goods Y
      exact ih Y (by omega) hY hEY

/-! ## Junk goods -/

omit [DecidableEq A] [DecidableEq G] in
/-- Goods worthless to `x` do not change `x`'s value of a list. -/
theorem value_filter_of_worthless (v : A → G → Nat) (x : A) (q : G → Bool) {S : List G}
    (h : ∀ g ∈ S, q g = true → v x g = 0) : value v x (S.filter (fun g => !q g)) = value v x S := by
  induction S with
  | nil => simp
  | cons g S ih =>
    have ih' := ih (fun y hy => h y (by simp [hy]))
    by_cases hq : q g = true
    · simp only [List.filter_cons, hq, Bool.not_true, Bool.false_eq_true, ↓reduceIte, value_cons,
        h g (by simp) hq, ih']
      omega
    · simp [hq, ih']

/-- **Junk to a source.** Let `q` mark goods worthless to every agent. If the other goods have an
EFX₀ allocation, then all goods have one: rotate envy cycles until some agent `s` is envied by
nobody (`EFX.exists_unenvied`), then give `s` every marked good. -/
theorem junkToSource (v : A → G → Nat) {agents : List A} {goods : List G} (q : G → Bool)
    (hq : ∀ g ∈ goods, q g = true → ∀ a ∈ agents, v a g = 0) (hne : agents ≠ [])
    {X' : G → A} (hX' : IsAllocation agents (goods.filter (fun g => !q g)) X')
    (hE : EFX0L v agents (goods.filter (fun g => !q g)) X') :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  obtain ⟨Y, hY, hEY, s, hs, hsrc⟩ := exists_unenvied v hne hX' hE
  refine ⟨extendBy s q Y, ?_, ?_⟩
  · intro g hg
    by_cases hqg : q g = true
    · simp [extendBy, hqg, hs]
    · have h1 : extendBy s q Y g = Y g := by simp [extendBy, hqg]
      rw [h1]
      exact hY g (List.mem_filter.mpr ⟨hg, by simp [hqg]⟩)
  -- every agent values every new bundle as it values the old one
  have hval : ∀ x ∈ agents, ∀ j, value v x (bundle goods (extendBy s q Y) j) =
      value v x (bundle (goods.filter (fun g => !q g)) Y j) := by
    intro x hx j
    rw [← value_filter_of_worthless v x q (S := bundle goods (extendBy s q Y) j) (fun g hg hqg =>
      hq g (List.mem_filter.mp hg).1 hqg x hx)]
    congr 1
    unfold bundle extendBy
    rw [List.filter_filter, List.filter_filter]
    apply List.filter_congr
    intro g _
    by_cases hqg : q g = true <;> simp [hqg]
  intro x hx y hy hxy g hg
  rw [hval x hx x]
  by_cases hys : y = s
  · -- `y = s` holds the junk; `x` envies `s` not at all
    subst hys
    calc value v x ((bundle goods (extendBy y q Y) y).erase g)
        _ ≤ value v x (bundle goods (extendBy y q Y) y) := value_sublist v x List.erase_sublist
        _ = value v x (bundle (goods.filter (fun g => !q g)) Y y) := hval x hx y
        _ ≤ value v x (bundle (goods.filter (fun g => !q g)) Y x) :=
          Nat.le_of_not_lt (hsrc x hx)
  · rw [bundle_extendBy_of_ne hys] at hg ⊢
    exact hEY x hx y hy hxy g hg

/-- Junk: the goods of `goods` relevant to no agent of `agents`. -/
def isJunk (v : A → G → Nat) (agents : List A) (g : G) : Bool := agents.all (fun a => v a g == 0)

/-- **L3.** If the goods relevant to some agent have an EFX₀ allocation, then so do all goods: the
goods relevant to no agent go to an agent that nobody envies, after rotating envy cycles. -/
theorem junk (v : A → G → Nat) {agents : List A} {goods : List G} (hne : agents ≠ [])
    {X' : G → A} (hX' : IsAllocation agents (goods.filter (fun g => !isJunk v agents g)) X')
    (hE : EFX0L v agents (goods.filter (fun g => !isJunk v agents g)) X') :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  refine junkToSource v (isJunk v agents) ?_ hne hX' hE
  intro g _ hg a ha
  simp only [isJunk, List.all_eq_true, beq_iff_eq] at hg
  exact hg a ha

omit [DecidableEq G] in
/-- Filtering the goods commutes with taking a bundle. -/
theorem bundle_filter (goods : List G) (p : G → Bool) (X : G → A) (j : A) :
    bundle (goods.filter p) X j = (bundle goods X j).filter p := by
  unfold bundle
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro g _
  exact Bool.and_comm _ _

/-- **L3** in the model's terms. If an allocation `X'` satisfies the EFX₀ condition whenever the
removed good is relevant to some agent (so it may fail only for removed goods that nobody values),
then some allocation is EFX₀. -/
theorem Inst.exists_efx0_of_junk (I : Inst) (hn : 0 < I.n) (X' : I.Alloc)
    (h : ∀ i j : Fin I.n, i ≠ j → ∀ g : Fin I.m, X' g = j → (∃ a, 0 < I.v a g) →
      I.bundleVal X' i j (some g) ≤ I.bundleVal X' i i none) :
    ∃ X : I.Alloc, I.EFX0 X := by
  let agents := List.finRange I.n
  -- junk is worthless to every agent
  have hq : ∀ x g, isJunk I.v agents g = true → I.v x g = 0 := by
    intro x g hg
    simp only [isJunk, List.all_eq_true, beq_iff_eq] at hg
    exact hg x (List.mem_finRange x)
  obtain ⟨X, _, hE⟩ := junk I.v (agents := agents) (goods := List.finRange I.m)
    (List.ne_nil_of_mem (List.mem_finRange ⟨0, hn⟩)) (X' := X') (fun g _ => List.mem_finRange _) (by
      intro x _ y _ hxy g hg
      have hg' := List.mem_filter.mp ((bundle_filter _ _ X' y) ▸ hg)
      have hXg : X' g = y := of_decide_eq_true (List.mem_filter.mp hg'.1).2
      -- `g` is relevant to some agent
      have hrel : ∃ a, 0 < I.v a g := by
        apply Classical.byContradiction
        intro hno
        have : isJunk I.v agents g = true := by
          simp only [isJunk, List.all_eq_true, beq_iff_eq]
          intro a _
          apply Classical.byContradiction
          intro ha
          exact hno ⟨a, Nat.pos_of_ne_zero ha⟩
        simp [this] at hg'
      have := h x y hxy g hXg hrel
      rw [bundleVal_some, bundleVal_none] at this
      rw [bundle_filter, bundle_filter, List.erase_filter,
        value_filter_of_worthless I.v x _ (fun g _ hg => hq x g hg),
        value_filter_of_worthless I.v x _ (fun g _ hg => hq x g hg)]
      exact this)
  exact ⟨X, (Inst.efx0_iff I X).mpr hE⟩

end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.rotate_efx0
#print axioms EFX.exists_unenvied
#print axioms EFX.junkToSource
#print axioms EFX.junk
#print axioms EFX.Inst.exists_efx0_of_junk
