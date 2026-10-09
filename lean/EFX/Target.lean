import EFX.CorollaryD
import EFX.Junk
import EFX.TwoOwnGoods

/-!
# The CORE reduction and TARGET (`proofs/lemmas.md` CORE; `proofs/lb_last_step.md` Corollary T)

- `IsCore`: a core (`proofs/lemmas.md`, CORE): at least two agents; (K1) every agent has exactly three
  relevant goods; (K2) every agent is balanced, each good worth less than its other goods together; (K3)
  every agent has at most one private good (relevant to no other agent); (K4) every good is relevant to
  some agent.
- `core_reduction`: **the CORE theorem**. If every core with at most `N` agents has an EFX₀ allocation, so
  does every instance with at most `N` agents in which every agent has at most three relevant goods. The
  proof is the induction of `proofs/lemmas.md`: junk goods by L3 (`EFX.junk`), then peeling by R1
  (`EFX.peel`), then by R2 (`EFX.peelR2`); what remains is a core.
- `target_lists`, `target`: **TARGET** (Corollary T). Every instance in which every agent positively values
  at most three goods has a complete EFX₀ allocation: the CORE theorem with Corollary D
  (`EFX.LB.corollaryD_lists`), which covers every core.
-/

set_option autoImplicit false

namespace EFX

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- The goods of `goods` private to `i` among `agents`: relevant to `i` and to no other agent. -/
def privateGoods (v : A → G → Nat) (agents : List A) (i : A) (goods : List G) : List G :=
  goods.filter (fun g => decide (0 < v i g ∧ ∀ j ∈ agents, j ≠ i → v j g = 0))

/-- A core (`proofs/lemmas.md`, CORE): (K1)–(K4), with at least two agents. -/
def IsCore (v : A → G → Nat) (agents : List A) (goods : List G) : Prop :=
  2 ≤ agents.length ∧
  (∀ i ∈ agents, (relevant v i goods).length = 3) ∧
  (∀ i ∈ agents, ∀ g ∈ goods, 2 * v i g < value v i goods) ∧
  (∀ i ∈ agents, (privateGoods v agents i goods).length ≤ 1) ∧
  (∀ g ∈ goods, ∃ i ∈ agents, 0 < v i g)

section lemmas
variable (v : A → G → Nat)

omit [DecidableEq A] in
theorem value_erase {i : A} {p : G} : ∀ {S : List G}, p ∈ S → value v i S = v i p + value v i (S.erase p)
  | [], h => by simp at h
  | g :: S, h => by
    by_cases hg : g = p
    · subst hg; simp
    · have hp : p ∈ S := (List.mem_cons.mp h).resolve_left (Ne.symm hg)
      have hne : (g == p) = false := by simp [hg]
      simp only [List.erase_cons, hne, Bool.false_eq_true, ↓reduceIte, value_cons]
      rw [value_erase hp]
      omega

theorem efx0L_congr {l l' : List A} {goods : List G} {X : G → A} (h : ∀ x, x ∈ l ↔ x ∈ l')
    (hE : EFX0L v l goods X) : EFX0L v l' goods X :=
  fun i hi j hj hij g hg => hE i ((h i).mpr hi) j ((h j).mpr hj) hij g hg

omit [DecidableEq G] in
theorem mem_cons_erase {agents : List A} {i : A} (hi : i ∈ agents) :
    ∀ x, x ∈ i :: agents.erase i ↔ x ∈ agents := by
  intro x
  constructor
  · intro hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hi
    · exact List.mem_of_mem_erase hx
  · intro hx
    by_cases hxi : x = i
    · simp [hxi]
    · exact List.mem_cons_of_mem _ (List.mem_erase_of_ne hxi |>.mpr hx)

omit [DecidableEq A] [DecidableEq G] in
theorem relevant_sublist {i : A} {S T : List G} (h : S.Sublist T) :
    (relevant v i S).length ≤ (relevant v i T).length :=
  (h.filter _).length_le

omit [DecidableEq A] in
/-- If R1 does not apply to `i` (no remaining good is worth at least all the others), then `i` has at
least three relevant goods and each good is worth less than half of all goods together. -/
theorem not_R1 {i : A} {goods : List G} (hne : goods ≠ [])
    (h : ¬ ∃ p ∈ goods, value v i (goods.erase p) ≤ v i p) :
    3 ≤ (relevant v i goods).length ∧ ∀ g ∈ goods, 2 * v i g < value v i goods := by
  have hlt : ∀ g ∈ goods, 2 * v i g < value v i goods := by
    intro g hg
    have := value_erase v (i := i) hg
    have : ¬ value v i (goods.erase g) ≤ v i g := fun h' => h ⟨g, hg, h'⟩
    omega
  refine ⟨Nat.lt_of_not_le fun hle => h ?_, hlt⟩
  cases hfav : favorite (v i) goods with
  | none => exact absurd ((favorite_eq_none_iff _).mp hfav) hne
  | some p =>
    obtain ⟨hp, hmax⟩ := favorite_spec _ hfav
    refine ⟨p, hp, value_le_of_countP_le_one v i (v i p) (fun g hg => hmax g (List.mem_of_mem_erase hg)) ?_⟩
    rw [relevant, ← List.countP_eq_length_filter] at hle
    by_cases hpos : 0 < v i p
    · have := countP_erase_add_one (p := fun g => decide (0 < v i g)) hp (by simp [hpos])
      omega
    · have h0 : goods.countP (fun g => decide (0 < v i g)) = 0 := by
        rw [List.countP_eq_zero]
        intro g hg
        have := hmax g hg
        simp only [decide_eq_true_eq]
        omega
      have := (List.erase_sublist (a := p) (l := goods)).countP_le (p := fun g => decide (0 < v i g))
      omega

omit [DecidableEq G] in
theorem isPrivate_iff {agents : List A} (hag : agents.Nodup) {i : A} {g : G} :
    isPrivate v i (agents.erase i) g = true ↔ (0 < v i g ∧ ∀ j ∈ agents, j ≠ i → v j g = 0) := by
  simp only [isPrivate, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj hji => h2 j ((List.Nodup.mem_erase_iff hag).mpr ⟨hji, hj⟩)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => h2 j (List.mem_of_mem_erase hj) ((List.Nodup.mem_erase_iff hag).mp hj).1⟩

omit [DecidableEq G] in
/-- R2's balance condition for a balanced agent with exactly three relevant goods, at least two of them
private: its private goods are worth at least its other goods. -/
theorem R2_balance {agents : List A} {goods : List G} (hag : agents.Nodup) {i : A}
    (h3 : (relevant v i goods).length = 3)
    (hlt : ∀ g ∈ goods, 2 * v i g < value v i goods)
    (h2 : 2 ≤ (goods.filter (isPrivate v i (agents.erase i))).length) :
    value v i (relevant v i (goods.filter (fun g => !isPrivate v i (agents.erase i) g))) ≤
      value v i (goods.filter (isPrivate v i (agents.erase i))) := by
  rw [value_relevant]
  have hqrel : ∀ g, isPrivate v i (agents.erase i) g = true → 0 < v i g :=
    fun g hg => ((isPrivate_iff v hag).mp hg).1
  generalize isPrivate v i (agents.erase i) = q at h2 hqrel ⊢
  have hsplit := value_filter_add v i q goods
  -- the private goods are relevant, so at most one relevant good is not private
  have hpriv_rel : (relevant v i (goods.filter q)).length = (goods.filter q).length := by
    unfold relevant
    congr 1
    rw [List.filter_eq_self]
    intro g hg
    simpa using hqrel g (List.mem_filter.mp hg).2
  have hrel_split : (relevant v i goods).length =
      (relevant v i (goods.filter q)).length + (relevant v i (goods.filter (fun g => !q g))).length := by
    unfold relevant
    rw [List.filter_filter, List.filter_filter]
    rw [LB.length_filter_add (goods.filter (fun g => decide (0 < v i g))) q, List.filter_filter,
      List.filter_filter]
    congr 2 <;> apply List.filter_congr <;> intro g _ <;> simp [Bool.and_comm]
  have hQ1 : (goods.filter (fun g => !q g)).countP (fun g => decide (0 < v i g)) ≤ 1 := by
    rw [List.countP_eq_length_filter]
    have : (relevant v i (goods.filter (fun g => !q g))).length ≤ 1 := by omega
    exact this
  cases hfav : favorite (v i) (goods.filter (fun g => !q g)) with
  | none =>
    rw [(favorite_eq_none_iff _).mp hfav, value_nil]
    exact Nat.zero_le _
  | some z =>
    obtain ⟨hz, hmax⟩ := favorite_spec _ hfav
    have hQ := value_le_of_countP_le_one v i (v i z) hmax hQ1
    have := hlt z (List.mem_filter.mp hz).1
    omega

end lemmas

/-- **The CORE theorem** (`proofs/lemmas.md`). Let `N ≥ 1`. If every core with at most `N` agents has an
EFX₀ allocation, then so does every instance with at most `N` agents in which every agent has at most three
relevant goods. -/
theorem core_reduction (v : A → G → Nat) (N : Nat)
    (hcore : ∀ (agents : List A) (goods : List G), agents.Nodup → goods.Nodup → agents.length ≤ N →
      IsCore v agents goods → ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X) :
    ∀ (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
      agents.length ≤ N → (∀ i ∈ agents, (relevant v i goods).length ≤ 3) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X := by
  suffices H : ∀ s (agents : List A) (goods : List G), agents.length + goods.length = s →
      agents ≠ [] → agents.Nodup → goods.Nodup → agents.length ≤ N →
      (∀ i ∈ agents, (relevant v i goods).length ≤ 3) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X from
    fun agents goods => H _ agents goods rfl
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
  intro agents goods hs hne hag hgd hN h3
  obtain ⟨i0, hi0⟩ := List.exists_mem_of_ne_nil agents hne
  -- no goods: nothing to allocate
  by_cases hg0 : goods = []
  · subst hg0
    exact ⟨fun _ => i0, fun g hg => by simp at hg, fun _ _ _ _ _ g hg => by simp [bundle] at hg⟩
  -- one agent: it takes everything
  by_cases h1 : agents.length ≤ 1
  · refine ⟨fun _ => i0, fun _ _ => hi0, fun x hx y hy hxy => ?_⟩
    exfalso
    have : x = y := by
      cases agents with
      | nil => simp at hx
      | cons a l =>
        cases l with
        | nil => simp at hx hy; rw [hx, hy]
        | cons b l => simp at h1
    exact hxy this
  -- 1. junk goods (L3)
  by_cases hjunk : ∃ g ∈ goods, isJunk v agents g = true
  · obtain ⟨g, hg, hgj⟩ := hjunk
    have hlt : (goods.filter (fun g => !isJunk v agents g)).length < goods.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g, hg, by simp [hgj]⟩
    obtain ⟨X', hX', hE'⟩ := ih _ (by omega) agents (goods.filter (fun g => !isJunk v agents g)) rfl hne
      hag (hgd.sublist List.filter_sublist) hN
      (fun i hi => Nat.le_trans (relevant_sublist v List.filter_sublist) (h3 i hi))
    exact junk v hne hX' hE'
  -- 2. peeling by R1
  by_cases hR1 : ∃ i ∈ agents, ∃ p ∈ goods, value v i (goods.erase p) ≤ v i p
  · obtain ⟨i, hi, p, hp, htop⟩ := hR1
    have hrest : agents.erase i ≠ [] := by
      intro h
      have := List.length_erase_of_mem hi
      rw [h] at this; simp at this; omega
    have hmeas : (agents.erase i).length + (goods.erase p).length < s := by
      rw [← hs, List.length_erase_of_mem hi, List.length_erase_of_mem hp]
      have := List.length_pos_of_mem hi
      have := List.length_pos_of_mem hp
      omega
    obtain ⟨X', hX', hE'⟩ := ih _ hmeas
      (agents.erase i) (goods.erase p) rfl hrest (hag.erase i) (hgd.erase p)
      (by rw [List.length_erase_of_mem hi]; omega)
      (fun j hj => Nat.le_trans (relevant_sublist v List.erase_sublist) (h3 j (List.mem_of_mem_erase hj)))
    obtain ⟨hX, hE⟩ := peel v (List.Nodup.not_mem_erase hag) hp hgd hX' hE' htop
    exact ⟨_, fun g hg => (mem_cons_erase hi _).mp (hX g hg), efx0L_congr v (mem_cons_erase hi) hE⟩
  -- every agent has exactly three relevant goods and is balanced
  have hbal : ∀ i ∈ agents, 3 ≤ (relevant v i goods).length ∧ ∀ g ∈ goods, 2 * v i g < value v i goods :=
    fun i hi => not_R1 v hg0 (fun ⟨p, hp, h⟩ => hR1 ⟨i, hi, p, hp, h⟩)
  -- 3. peeling by R2: an agent with at least two private goods leaves with them
  by_cases hR2 : ∃ i ∈ agents, 2 ≤ (goods.filter (isPrivate v i (agents.erase i))).length
  · obtain ⟨i, hi, h2⟩ := hR2
    have hrest : agents.erase i ≠ [] := by
      intro h
      have := List.length_erase_of_mem hi
      rw [h] at this; simp at this; omega
    have hlt : (goods.filter (fun g => !isPrivate v i (agents.erase i) g)).length < goods.length := by
      have hpos : 0 < (goods.filter (isPrivate v i (agents.erase i))).length := by omega
      obtain ⟨g, hg⟩ := List.length_pos_iff_exists_mem.mp hpos
      exact List.length_filter_lt_length_iff_exists.mpr
        ⟨g, (List.mem_filter.mp hg).1, by simp [(List.mem_filter.mp hg).2]⟩
    have hmeas : (agents.erase i).length +
        (goods.filter (fun g => !isPrivate v i (agents.erase i) g)).length < s := by
      rw [← hs, List.length_erase_of_mem hi]
      have := List.length_pos_of_mem hi
      omega
    obtain ⟨X', hX', hE'⟩ := ih _ hmeas
      (agents.erase i) (goods.filter (fun g => !isPrivate v i (agents.erase i) g)) rfl hrest (hag.erase i)
      (hgd.sublist List.filter_sublist) (by rw [List.length_erase_of_mem hi]; omega)
      (fun j hj => Nat.le_trans (relevant_sublist v List.filter_sublist) (h3 j (List.mem_of_mem_erase hj)))
    obtain ⟨hX, hE⟩ := peelR2 v (List.Nodup.not_mem_erase hag) hX' hE'
      (R2_balance v hag (Nat.le_antisymm (h3 i hi) (hbal i hi).1) (hbal i hi).2 h2)
    exact ⟨_, fun g hg => (mem_cons_erase hi _).mp (hX g hg), efx0L_congr v (mem_cons_erase hi) hE⟩
  -- 4. a core
  refine hcore agents goods hag hgd hN ⟨by omega, fun i hi => Nat.le_antisymm (h3 i hi) (hbal i hi).1,
    fun i hi => (hbal i hi).2, fun i hi => ?_, fun g hg => ?_⟩
  · have e : privateGoods v agents i goods = goods.filter (isPrivate v i (agents.erase i)) := by
      unfold privateGoods
      apply List.filter_congr
      intro g _
      rw [Bool.eq_iff_iff, decide_eq_true_eq, isPrivate_iff v hag]
    rw [e]
    exact Nat.le_of_not_lt fun h => hR2 ⟨i, hi, h⟩
  · refine Classical.byContradiction fun hno => hjunk ⟨g, hg, ?_⟩
    simp only [isJunk, List.all_eq_true, beq_iff_eq]
    intro j hj
    exact Nat.eq_zero_of_not_pos fun hpos => hno ⟨j, hj, hpos⟩

/-- **TARGET, over lists.** If every agent has at most three relevant goods, a complete EFX₀ allocation
exists. -/
theorem target_lists (v : A → G → Nat) {agents : List A} {goods : List G} (hne : agents ≠ [])
    (hag : agents.Nodup) (hgd : goods.Nodup) (h3 : ∀ i ∈ agents, (relevant v i goods).length ≤ 3) :
    ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X :=
  core_reduction v agents.length (fun agents' goods' hag' hgd' _ hc => by
      obtain ⟨hlen, hk1, hk2, -, -⟩ := hc
      have hne' : agents' ≠ [] := fun h => by rw [h] at hlen; simp at hlen
      obtain ⟨X, hX, hE, -⟩ := LB.corollaryD_lists v hag' hgd' hne' hk1
        (fun i hi g hg => Nat.le_of_lt (hk2 i hi g hg))
      exact ⟨X, hX, hE⟩)
    agents goods hne hag hgd (Nat.le_refl _) h3

/-- **TARGET** (Corollary T). Every additive instance in which every agent positively values at most three
goods (`|R_i| ≤ 3`) has a complete EFX₀ allocation. -/
theorem target (I : Inst) (hn : 0 < I.n) (h : ∀ i, numRelevant I i ≤ 3) : ∃ X : I.Alloc, I.EFX0 X := by
  obtain ⟨X, -, hE⟩ := target_lists I.v (List.ne_nil_of_mem (List.mem_finRange ⟨0, hn⟩))
    (List.nodup_finRange I.n) (List.nodup_finRange I.m) (fun i _ => (numRelevant_eq I i) ▸ h i)
  exact ⟨X, (Inst.efx0_iff I X).mpr hE⟩

end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.core_reduction
#print axioms EFX.target_lists
#print axioms EFX.target
