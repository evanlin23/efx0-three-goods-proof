import EFX.Peeling

/-!
# At most two relevant goods per agent (LEDGER L2c), over lists

If every agent values at most two goods positively, serial dictatorship is EFX₀: agents in order
each take their favorite remaining good, and the last agent takes everything left.

Proof: by induction on the agents, peeling the first agent with rule R1. Its favorite remaining
good `p` is worth at least as much as all other remaining goods together, because at most one of
them is relevant to it and none is worth more than `p`.

`EFX.exists_efx0_of_count` (in `EFX.Bridge`) states the result in the model's terms.
`MRD.main_theorem_L` in evanlin23/mrd-efx proves a stronger form (every bundle but one has at most
one good).
-/

set_option autoImplicit false

namespace EFX

variable {A G : Type} [DecidableEq A] [DecidableEq G]

/-- **L2c** over lists: if every agent has at most two relevant goods, serial dictatorship gives an
EFX₀ allocation. -/
theorem serialDictatorship (v : A → G → Nat) :
    ∀ (agents : List A) (goods : List G), agents ≠ [] → agents.Nodup → goods.Nodup →
      (∀ i ∈ agents, (relevant v i goods).length ≤ 2) →
      ∃ X : G → A, IsAllocation agents goods X ∧ EFX0L v agents goods X
  | [], _, h, _, _, _ => absurd rfl h
  | [i], _, _, _, _, _ => by
    refine ⟨fun _ => i, fun _ _ => by simp, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | i :: j :: rest, goods, _, hnd, hgnd, h2 => by
    cases hfav : favorite (v i) goods with
    | none =>
      have : goods = [] := (favorite_eq_none_iff _).mp hfav
      subst this
      refine ⟨fun _ => i, fun g hg => by simp at hg, ?_⟩
      intro _ _ _ _ _ g hg
      simp [bundle] at hg
    | some p =>
      obtain ⟨hp, hmax⟩ := favorite_spec _ hfav
      have hi : i ∉ j :: rest := (List.nodup_cons.mp hnd).1
      obtain ⟨X', hX', hE⟩ := serialDictatorship v (j :: rest) (goods.erase p) (by simp)
        (List.nodup_cons.mp hnd).2 (hgnd.erase p) (by
          intro k hk
          exact Nat.le_trans ((List.erase_sublist.filter _).length_le)
            (h2 k (List.mem_cons_of_mem _ hk)))
      refine ⟨extend i p X', peel v hi hp hgnd hX' hE ?_⟩
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
          have := (List.erase_sublist (a := p) (l := goods)).countP_le
            (p := fun g => decide (0 < v i g))
          omega

end EFX

/-! ## Axiom certificates (audited by `check.sh`) -/

#print axioms EFX.serialDictatorship
