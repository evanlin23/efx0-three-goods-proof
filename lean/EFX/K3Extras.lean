import EFX.Peeling
import EFX.Bridge

/-!
# At most two relevant goods: serial dictatorship in any order

Corollary "two relevant goods" of the paper (`paper/k3-simple/long.tex`, `cor:k2`): serial dictatorship in any
order, each agent taking *a* favourite remaining good (any good of largest value to it), or nothing once no good is
left, and the last agent everything left, returns an EFX₀ allocation when every agent positively values at most two
goods. `EFX.SDRun` is the set of runs (any order, any favourite at every step); `EFX.sdRun_efx0` (over lists) and
`EFX.Inst.sdRun_efx0` (model) prove that every run is EFX₀. `EFX.serialDict` is one run, computable (index-order
favourite, `EFX.favorite`); `EFX.Inst.serialDict_efx0`: it is EFX₀ for every order of all agents.

In the research repository this file also held other results of the earlier paper on k = 3 (`paper/k3/`); only
serial dictatorship, which the present paper cites from here, is kept.
-/

set_option autoImplicit false

namespace EFX

section serial
variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- The runs of serial dictatorship (Corollary "two relevant goods" of the long version), over lists. The agents
of `order` take turns; each takes a favourite remaining good (any good of largest value to it among those
left), or nothing when no good is left; the last agent takes all remaining goods. `SDRun v order goods X`
says that `X` is the outcome of one run on the goods of `goods`, whatever the favourite chosen at each step. -/
inductive SDRun (v : A → G → Nat) : List A → List G → (G → A) → Prop
  | last (i : A) (goods : List G) (X : G → A) : (∀ g ∈ goods, X g = i) → SDRun v [i] goods X
  | pick (i : A) (rest : List A) (goods : List G) (p : G) (X : G → A) : rest ≠ [] → p ∈ goods →
      (∀ g ∈ goods, v i g ≤ v i p) → X p = i → SDRun v rest (goods.erase p) X → SDRun v (i :: rest) goods X
  | empty (i : A) (rest : List A) (X : G → A) : rest ≠ [] → SDRun v rest [] X → SDRun v (i :: rest) [] X

omit [DecidableEq A] in
/-- A run only depends on where it puts the goods of `goods`. -/
theorem SDRun.congr {v : A → G → Nat} {order : List A} {goods : List G} {X X' : G → A}
    (h : SDRun v order goods X) (hX : ∀ g ∈ goods, X g = X' g) : SDRun v order goods X' := by
  induction h with
  | last i goods X hall => exact SDRun.last i goods X' (fun g hg => (hX g hg) ▸ hall g hg)
  | pick i rest goods p X hne hp hmax hXp _ ih =>
    exact SDRun.pick i rest goods p X' hne hp hmax ((hX p hp) ▸ hXp)
      (ih (fun g hg => hX g (List.mem_of_mem_erase hg)))
  | empty i rest X hne _ ih => exact SDRun.empty i rest X' hne (ih (fun g hg => by simp at hg))

/-- **Corollary "two relevant goods" (over lists).** If every agent has at most two relevant goods, every run
of serial dictatorship, in any order of distinct agents and with any choice of favourites, returns an
allocation of `goods` to the agents of `order` that is EFX₀. (By induction: the first agent's favourite `p` is
worth at least all other remaining goods together, so rule R1, `peel`, applies.) -/
theorem sdRun_efx0 (v : A → G → Nat) {order : List A} {goods : List G} {X : G → A}
    (h : SDRun v order goods X) (hord : order.Nodup) (hgd : goods.Nodup)
    (h2 : ∀ i ∈ order, (relevant v i goods).length ≤ 2) :
    IsAllocation order goods X ∧ EFX0L v order goods X := by
  induction h with
  | last i goods X hall =>
    refine ⟨fun g hg => by simp [hall g hg], fun a ha b hb hab => ?_⟩
    simp only [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | pick i rest goods p X hne hp hmax hXp _ ih =>
    have hi : i ∉ rest := (List.nodup_cons.mp hord).1
    obtain ⟨hX', hE⟩ := ih (List.nodup_cons.mp hord).2 (hgd.erase p) (fun k hk =>
      Nat.le_trans ((List.erase_sublist.filter _).length_le) (h2 k (List.mem_cons_of_mem _ hk)))
    have hext : extend i p X = X := funext fun g => by
      by_cases hg : g = p
      · subst hg; simp [extend, hXp]
      · simp [extend, hg]
    rw [← hext]
    refine peel v hi hp hgd hX' hE ?_
    -- `p` is worth at least as much to `i` as all other remaining goods together
    apply value_le_of_countP_le_one v i (v i p)
    · intro g hg
      exact hmax g (List.mem_of_mem_erase hg)
    · by_cases hpos : 0 < v i p
      · have h1 := countP_erase_add_one (p := fun g => decide (0 < v i g)) hp (by simp [hpos])
        have h2i := h2 i (by simp)
        rw [relevant, ← List.countP_eq_length_filter] at h2i
        omega
      · have h0 : goods.countP (fun g => decide (0 < v i g)) = 0 := by
          rw [List.countP_eq_zero]
          intro g hg
          have := hmax g hg
          simp only [decide_eq_true_eq]
          omega
        have := (List.erase_sublist (a := p) (l := goods)).countP_le (p := fun g => decide (0 < v i g))
        omega
  | empty i rest X hne _ ih =>
    obtain ⟨-, hE⟩ := ih (List.nodup_cons.mp hord).2 hgd (fun k hk => by simp [relevant])
    exact ⟨fun g hg => by simp at hg, fun a _ b _ _ g hg => by simp [bundle] at hg⟩

/-- Serial dictatorship with a fixed choice of favourite (the first good of largest value, `favorite`); the
agent `d` only receives goods when `order` is empty. It is computable. -/
def serialDict (v : A → G → Nat) (d : A) : List A → List G → G → A
  | [], _ => fun _ => d
  | [i], _ => fun _ => i
  | i :: j :: rest, goods =>
    match favorite (v i) goods with
    | none => serialDict v d (j :: rest) goods
    | some p => extend i p (serialDict v d (j :: rest) (goods.erase p))

omit [DecidableEq A] in
/-- `serialDict` is a run of serial dictatorship. -/
theorem serialDict_run (v : A → G → Nat) (d : A) : ∀ (order : List A) (goods : List G), order ≠ [] →
    goods.Nodup → SDRun v order goods (serialDict v d order goods)
  | [], _, h, _ => absurd rfl h
  | [i], goods, _, _ => SDRun.last i goods _ (fun _ _ => rfl)
  | i :: j :: rest, goods, _, hgd => by
    have e : serialDict v d (i :: j :: rest) goods = match favorite (v i) goods with
        | none => serialDict v d (j :: rest) goods
        | some p => extend i p (serialDict v d (j :: rest) (goods.erase p)) := rfl
    cases hfav : favorite (v i) goods with
    | none =>
      have hg : goods = [] := (favorite_eq_none_iff _).mp hfav
      subst hg
      rw [e, hfav]
      exact SDRun.empty i (j :: rest) _ (by simp) (serialDict_run v d (j :: rest) [] (by simp) hgd)
    | some p =>
      obtain ⟨hp, hmax⟩ := favorite_spec _ hfav
      rw [e, hfav]
      refine SDRun.pick i (j :: rest) goods p _ (by simp) hp hmax (by simp [extend]) ?_
      refine (serialDict_run v d (j :: rest) (goods.erase p) (by simp) (hgd.erase p)).congr ?_
      intro g hg
      have hgp : g ≠ p := fun e => ((List.Nodup.mem_erase_iff hgd).mp (e ▸ hg)).1 rfl
      simp [extend, hgp]

end serial

namespace Inst

/-- Serial dictatorship on an instance of the model, in the order `order`, each agent taking its first good of
largest value among those left; computable. -/
def serialDict (I : Inst) (hn : 0 < I.n) (order : List (Fin I.n)) : I.Alloc :=
  EFX.serialDict I.v ⟨0, hn⟩ order (List.finRange I.m)

/-- **Corollary "two relevant goods".** If every agent positively values at most two goods, serial dictatorship
in any order of all agents (each agent once), with any choice of favourite at every step and the last agent
taking all remaining goods, returns an EFX₀ allocation. -/
theorem sdRun_efx0 (I : Inst) (h : ∀ i, numRelevant I i ≤ 2) {order : List (Fin I.n)} (hord : order.Nodup)
    (hall : ∀ i, i ∈ order) {X : I.Alloc} (hX : SDRun I.v order (List.finRange I.m) X) : I.EFX0 X := by
  obtain ⟨-, hE⟩ := EFX.sdRun_efx0 I.v hX hord (List.nodup_finRange _)
    (fun i _ => (numRelevant_eq I i) ▸ h i)
  exact (efx0_iff I X).mpr fun i _ j _ hij g hg => hE i (hall i) j (hall j) hij g hg

/-- **Corollary "two relevant goods", the computable procedure.** `serialDict` in any order of all agents is
EFX₀ when every agent positively values at most two goods. -/
theorem serialDict_efx0 (I : Inst) (hn : 0 < I.n) (h : ∀ i, numRelevant I i ≤ 2) {order : List (Fin I.n)}
    (hord : order.Nodup) (hall : ∀ i, i ∈ order) : I.EFX0 (I.serialDict hn order) :=
  I.sdRun_efx0 h hord hall (serialDict_run I.v ⟨0, hn⟩ order (List.finRange I.m)
    (List.ne_nil_of_mem (hall ⟨0, hn⟩)) (List.nodup_finRange _))

end Inst

end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.sdRun_efx0
#print axioms EFX.serialDict_run
#print axioms EFX.Inst.sdRun_efx0
#print axioms EFX.Inst.serialDict_efx0
