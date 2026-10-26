# Lean formalization

The Lean 4 formalization of the paper `paper/k3-simple/` (EFX₀ with at most three relevant goods per agent), in core Lean 4. The conventions follow
[evanlin23/mrd-efx](https://github.com/evanlin23/mrd-efx) (the formal companion to the paper on at most two
relevant goods), whose model this library reuses verbatim.

- **Core Lean only**: no Mathlib and no other packages (`lakefile.toml` has no `require`).
- **No `sorry`**: the word may not appear in any source file, and the build must be free of errors and warnings.
- **Standard axioms only**: every declaration of the library depends only on `propext`, `Classical.choice`
  and `Quot.sound`. This rules out unfinished proofs, `native_decide` and new axioms.

Toolchain: `leanprover/lean4:v4.34.0`, pinned in `lean-toolchain` (the same as mrd-efx).

## Build and audit

    cd lean && ./check.sh

The script fails if any source file contains the word `sorry`, if any source file or `lakefile.toml` uses a
debug option, metaprogramming or unsafe code (`debug.`, `import Lean`, `run_cmd`, `run_meta`, `run_elab`,
`addDecl`, `implemented_by`, `extern`, `unsafe`), if the project has a dependency, if the build reports an error
or a warning, if any `#print axioms` certificate lists an axiom other than the three standard ones (a certificate
may also list none), if the number of certificates differs from the number of `#print axioms` commands, if any
declaration of the library (certified or not; `CheckAxioms.lean`) depends on another axiom, or if Lean's replay
checker `lake env leanchecker --fresh EFX` rejects the library (it re-checks every declaration, Init included,
in a fresh kernel; about a minute). The last two checks exist because that a declaration added under `set_option debug.skipKernelTC true` is never kernel-checked, yet builds
without warnings and has no axioms for `#print axioms` or `CheckAxioms.lean` to report; the tripwire refuses the
option and the replay checker rejects such a declaration. On success the last line is

    CHECK PASSED: 231 audited statements, 584 theorems, standard axioms only

CI runs it on every push and pull request (job `lean` in `.github/workflows/verify.yml`).

To check one theorem interactively: `lake build`, then put `import EFX` and `#print axioms EFX.peel` in a scratch
file and run `lake env lean scratch.lean`.

## Trusted base

The definitions a reader must accept, from `EFX/Model.lean` (copied from `MRD.lean` in mrd-efx `v1.2.0`, namespace
`MRD` renamed to `EFX`):

    def finSum : (k : Nat) → (Fin k → Nat) → Nat
      | 0, _ => 0
      | k+1, f => finSum k (fun i => f i.castSucc) + f (Fin.last k)

    structure Inst where
      n : Nat
      m : Nat
      v : Fin n → Fin m → Nat

    abbrev Alloc := Fin I.m → Fin I.n

    def bundleVal (X : I.Alloc) (i j : Fin I.n) (ex : Option (Fin I.m)) : Nat :=
      finSum I.m (fun g => if X g = j ∧ ex ≠ some g then I.v i g else 0)

    def EFX0 (X : I.Alloc) : Prop :=
      ∀ i j : Fin I.n, i ≠ j → ∀ g : Fin I.m, X g = j →
        I.bundleVal X i j (some g) ≤ I.bundleVal X i i none

    def numRelevant (I : Inst) (i : Fin I.n) : Nat := finSum I.m (fun g => if 0 < I.v i g then 1 else 0)

In `EFX/Model.lean` the docstring of `numRelevant` reads "The counting form of 2-relevance used in the paper:
`|R_i| ≤ 2`": it is inherited verbatim from mrd-efx, whose theorem is about two goods. The definition counts the
goods `g` with `0 < v i g` and has nothing to do with the bound 2 (`Model.lean` is left untouched, as copied).

Values are natural numbers. EFX₀ only compares sums of values, so rational instances reduce to these by scaling
each agent's values by a common denominator, and nonnegative real values (or values in any type satisfying the
axioms of the next section, rationals included) reduce to them by L12 (`proofs/real_values.md`), which is
machine-checked: see the next section.

### Values in an ordered type (`EFX/RealValues.lean`)

The paper's theorems are also stated for values in any type `V` satisfying the class `EFX.OrderedValue`
(`EFX.DE.deOrd_correct`, `EFX.DE.thmD_ordered` in `EFX/K3DEReal.lean`; Proposition limits of the shape in
`EFX/K3DELimits.lean`), and the model is mirrored for such values (`Model.lean` is unchanged):

    class OrderedValue (V : Type) extends Zero V, Add V, LE V where
      add_assoc : ∀ a b c : V, a + b + c = a + (b + c)
      add_comm : ∀ a b : V, a + b = b + a
      zero_add : ∀ a : V, 0 + a = a
      le_refl : ∀ a : V, a ≤ a
      le_trans : ∀ a b c : V, a ≤ b → b ≤ c → a ≤ c
      le_antisymm : ∀ a b : V, a ≤ b → b ≤ a → a = b
      le_total : ∀ a b : V, a ≤ b ∨ b ≤ a
      add_le_add_iff_right : ∀ a b c : V, a ≤ b ↔ a + c ≤ b + c

    def finSumO : (k : Nat) → (Fin k → V) → V            -- as finSum
    structure OInst (V : Type) where (n m : Nat) (v : Fin n → Fin m → V)
    def OInst.bundleVal, OInst.EFX0                         -- as Inst.bundleVal, Inst.EFX0, word for word
    def OInst.numRelevant (i : Fin I.n) : Nat := finSum I.m (fun g => if ¬ I.v i g ≤ 0 then 1 else 0)

These are the axioms of a linearly ordered cancellative additive commutative monoid. `ℝ≥0`, `ℚ≥0` and `ℕ` satisfy
them (so do `ℝ`, `ℚ`, `ℤ`); core Lean has no `ℝ`, so the `ℝ≥0` instance is the textbook fact, while the instances
for `Nat` and `Int` are in the file. Nonnegativity is not an axiom but a hypothesis of the theorems
(`∀ i g, 0 ≤ I.v i g`), which keeps the class to the order-and-sum axioms and lets `Int` (or `ℝ`) values with that
hypothesis in. A good is relevant iff `¬ v i g ≤ 0` (that is, `v i g > 0`). At `V = Nat` the mirrored model is
the trusted base (`EFX.efx0_nat_iff`, `EFX.numRelevant_nat`).

## Contents

The files `EFX/K3DE*.lean` are the formalization of the paper. The other files are the model (`Model.lean`) and the
part of the research repository's library (evanlin23/efx0-three-goods) that the K3DE files use. There it was
written for an earlier, longer construction of the same theorem (algorithm K3ALG, with construction LB⁺) and for
work on four relevant goods; only the declarations the K3DE files use, directly or through each other, are kept,
with their proofs unchanged, plus serial dictatorship (`K3Extras.lean`, which the paper cites) and two lemmas that
tie the ordered-value model to the trusted base (`EFX.efx0_nat_iff`, `EFX.numRelevant_nat`). Names and
namespaces are those of the research repository: `EFX.LB` for construction LB (DE's states are its rank-based
pre-allocations) and `EFX.K3` for algorithm K3ALG. Some docstrings mention that repository's ledger (`LEDGER.md`)
and notes (`proofs/…`), which are not copied here.

- `EFX/Model.lean`: the trusted base above.
- `EFX/Lists.lean`: the same notions over explicit lists of agents and goods (`value`, `bundle`, `EFX0L`), which
  suit arguments that remove agents or goods; list lemmas; `favorite`, an agent's most valued remaining good.
- `EFX/Bridge.lean`: over `List.finRange` the list notions equal the model's (`finSum_eq_sum`, `bundleVal_none`,
  `bundleVal_some`, `efx0_iff`, `numRelevant_eq`).
- `EFX/Peeling.lean`: peeling (L2). `EFX.peel`, rule R1 (agent `i` leaves with a good `p` it values at least as
  much as all other remaining goods together); `EFX.peelBundle`, the general peeling step (agent `i` leaves with a
  bundle `P` it values at least as much as all remaining goods, and `P` minus any one good is worthless to everyone
  else), with its instance `EFX.peelEmpty`, rule R1 when nothing relevant to `i` remains (`P = ∅`); `EFX.not_R1`,
  an agent to which R1 does not apply has at least three relevant goods and is strictly balanced.
- `EFX/K3Extras.lean`: Corollary "two relevant goods" (serial dictatorship in any order). `EFX.SDRun` (every run:
  any order, any favourite at every step, nothing once no good is left, the last agent takes the rest),
  `EFX.sdRun_efx0` (over lists) and `EFX.Inst.sdRun_efx0` (model): every run is EFX₀; `EFX.Inst.serialDict`, a
  computable run, and `EFX.Inst.serialDict_efx0`. (In the research repository the file also held other results of
  an earlier paper, hence its name.)
- `EFX/Rankings.lean`: ranking profiles (`EFX.LB.Profile`: rankings `a i`, `b i`, `c i`; well formed,
  `EFX.LB.WF`), consistent valuations (`Profile.Consistent`: `a ≥ b ≥ c > 0`, ties allowed, `a ≤ b + c`), ranks
  and `Profile.NA` (the goods some agent outside the pair holders ranks above its pick), and counting lemmas for
  bundles of at most two goods.
- `EFX/PreAlloc.lean`: the draft (`EFX.LB.phase1`, Phase 1 of construction LB: the agents of a list take their
  favourite remaining good in turn; `EFX.LB.phase1_spec`), the slots (`EFX.LB.fill`), and the rank-based
  pre-allocations that are DE's states: `EFX.LB.Valid` (validity), `EFX.LB.Completion` (a completion with an
  optional owner, satisfying the owner constraint), and Theorem 1′, `EFX.LB.Valid.sound` (every completion of a
  valid pre-allocation is EFX₀ for every valuation consistent with the rankings, and every bundle but the owner's
  has at most two goods; through `EFX.LB.HypNA.efx0`).
- `EFX/Timed.lean`: the cost model. `EFX.Timed` pairs a value with an operation count. It provides list operations
  with value and cost lemmas, and tables (`EFX.Timed.mkTable`: arrays filled once).
- `EFX/K3Algo.lean`: rule R1 as a search (`EFX.K3.r1Step`, `EFX.K3.findR1`) and an agent's ranking computed by
  sorting its relevant goods (`EFX.K3.sort3`, `EFX.K3.profileOf`, `EFX.K3.sort3_ranking`), with counted versions in
  `EFX.Timed` (`rankC`, `pickRankC`, `prefersC`, `favoriteC`, `valueC`, `sort3C`, `finRangeC`, with value and cost
  lemmas).
- `EFX/RealValues.lean`: L12 (`proofs/real_values.md`) over any `EFX.OrderedValue`. The value class and mirrored
  model above; `EFX.Agree` (same answer to every comparison between two subset sums);
  `EFX.OrderedValue.tri_le_iff` (for three positive values, every such comparison is decided by twelve basic
  comparisons, after cancelling common goods); `EFX.Pat.table` (every consistent pattern of those twelve answers is
  realized by one of the 31 permutations of the representatives of L12, checked by `decide +kernel`);
  `EFX.OrderedValue.tri_rep`, `EFX.OrderedValue.exists_agree`, `EFX.l12`; the transfers `EFX.efx0_iff_of_agree`,
  `EFX.numRelevant_eq_of_agree`.
- `EFX/K3Real.lean`: L12's natural-number surrogate computed in the comparison model. The program receives a
  comparison oracle `le : V → V → Bool` and inspects the values only through it (plus unit-cost addition of two of
  one agent's values; for agents with one or two relevant goods some compared sums count a good twice); the
  theorems assume `le x y = true ↔ x ≤ y`. It computes the surrogate as an `n × m` table (`EFX.K3.surrogate`,
  `EFX.K3.surrogateC`: per agent, `m` oracle calls `v_i(g) ≤ 0` find the relevant goods, twelve more give the
  pattern of the first three, and the first row of `EFX.Pat.reps` with that pattern gives the values);
  `EFX.K3.agree_surrogate`, the constructive L12. Cost: `EFX.K3.surrogateC_cost` charges `c` units per oracle call
  and bounds the surrogate by `c · n (m + 12) + 10 n m + 971 n`, so at most `n (m + 12)` calls. The oracle on `Int`,
  `EFX.K3.Examples.leZ`.
- `EFX/K3DE.lean`, `EFX/K3DEImprove.lean`, `EFX/K3DEAlgo.lean`, `EFX/K3DEExamples.lean`: the proof of the
  result and algorithm Draft and Exchange (DE) (`paper/k3-simple/main.tex` §3–§6,
  `k3/simplify/po/hall/NOTES.md`; ledger K3S.PO.LEAN), over the valid pre-allocations of `PreAlloc` (rank-based
  states: each agent holds nothing, one of its goods, or its pair `{b, c}`). The Lean names are the earlier ones of
  the paper: needs (wants), utility (score), exposed (blocker), protecting good (the blocker's leftover good `h_x`),
  valid absorber (an agent that can finish), need and exposure arcs (want and pair arrows, reversed: Lean's arcs point the way goods move, as `σ` does), need and exchange cycles
  (rings), pair chain (chain), (P) (NC).
  - `K3DE`: utilities (`EFX.DE.util`, pair 4 > a 3 > b 2 > c 1 > nothing 0), Pareto domination, free agents,
    exposure, valid absorbers (`EFX.DE.Absorber`), the paper's completion (`EFX.DE.completeDE`: the goods of `H` to
    different free agents, the rest of the junk to the absorber) and soundness (`EFX.DE.soundness`, through Theorem 1′),
    Lemma staying valid (`EFX.DE.transfer`), and one exchange lemma for chains and rings (`EFX.DE.exchange`: Lemma
    ring, with Lemma chain; `EFX.DE.exchange_scores`: every agent of the ring gets a strictly higher score, every other agent keeps
    its score).
  - `K3DEImprove`: the computable step of DE (`EFX.DE.step`, the loop's three steps: *chain*, a pair chain if (P)
    fails; *finish*, stop if every agent is a pair holder or with the first free agent `o` with `|H_o| ≤ |F| − 1`,
    which covers a free agent holding nothing, `EFX.DE.count_of_none`; *ring*, otherwise the ring of σ built from
    greedy distinct representatives), the finishing test (`EFX.DE.absorber_iff`, `EFX.DE.not_exposed_of_none`), the
    paper's rule for the distinct leftover goods (`EFX.DE.reps_first_blocker`: `q_o` is the leftover good of the
    first blocker of `o` whose good no earlier free agent took, and `σ(o)` is that blocker; `H_o` lists its goods in
    the order of their first blockers, `EFX.DE.find?_Hset`), the scores of a move (`EFX.DE.step_next_scores`), and
    the **Improvement Lemma** (`EFX.DE.improvement`) with its Corollary (`EFX.DE.completable_of_undominated`).
  - `K3DEAlgo`: the draft is valid (`EFX.DE.draft_valid`), the loop ends at a valid absorber after at most `4n`
    exchanges (`EFX.DE.loop_spec`), and DE with R1 peeling (`EFX.DE.run`, `EFX.DE.deSpec`) returns an EFX₀ allocation
    with at most one bundle of more than two goods on every instance with at most three relevant goods per agent
    (`EFX.DE.run_sound`, `EFX.DE.deSpec_correct`).
  - `K3DEExamples`: by `decide`, DE on the paper's worked example (Appendix B: one ring with two pair arrows; the paper's
    output), on its small example (§6: one ring `o → x → o`, then `z` finishes; `EFX.DE.Examples.small_spec`) and on
    three small instances (protecting goods, two pair chains, peeling).
- `EFX/K3DEPrelim.lean`, `EFX/K3DELimits.lean`, `EFX/K3DEShort.lean`, `EFX/K3DEShortExamples.lean`,
  `EFX/K3DERings.lean`, `EFX/K3DEReal.lean`, `EFX/K3DERemarks.lean`, `EFX/K3DECost*.lean`: the rest of `paper/k3-simple/` (ledger K3S.PRELIM.LEAN, K3S.LIMITS,
  K3S.SHORT, K3S.EX.LEAN, K3S.RINGS, K3S.REAL.LEAN).
  - `K3DEPrelim`: threats and safety (`EFX.DE.efx0L_iff_safe`), Lemmas threats and safety, Lemma peeling in the
    paper's form (`EFX.DE.peeling`), Lemma R1fail (`EFX.DE.R1fail`).
  - `K3DELimits`: Lemma cases of safety (`EFX.DE.Limits.safe_iff_cases`) and Proposition limits of the shape for every
    strictly balanced valuation with distinct values (`limits_a`, `limits_b`), also for ordered values, by `decide`
    over all allocations.
  - `K3DEShort`, `K3DEShortExamples`: Proposition short moves (`EFX.DE.prop_short`) with both instances attaining its
    bounds, and the worked example's facts (exactly four dominating valid states, `w_exactly_four`; all ten
    candidate completions fail, `w_completions`).
  - `K3DERings`: the ring family for every k and depth: every cycle of want and pair arrows uses exactly k pair
    arrows (`EFX.DE.Rings.nExp_eq`), and no free agent absorbs iff k ≤ 2^d (`no_free_absorber_iff`).
  - `K3DEReal`: DE on ordered values through L12's surrogate (`EFX.DE.deOrd_correct`), existence with the shape for
    ordered values (`EFX.DE.thmD_ordered`), and at most n peeling rounds (`EFX.DE.de_correct`).
  - `K3DECost`, `K3DECostStep`, `K3DECostRun`, `K3DECostBound`, `K3DECostReal` (ledger K3S.TIME): the running time.
    A counted DE (`EFX.DE.deC`, with unit-cost array writes `EFX.DE.wr`) computes exactly DE's output
    (`EFX.DE.de_eq_spec`) in at most `750 (n + 1)(n + m + 1)` counted operations (`EFX.DE.deC_cost`); on ordered
    values with a comparison oracle, `EFX.DE.deOrdC_cost`.
  - `K3DERemarks`: the instance of main.tex §1 that is EFX but not EFX₀ (`EFX.DE.Remarks.efx_not_efx0_intro`) and a
    second such example, not in the paper (`EFX.DE.Remarks.efx_not_efx0`), the remark that the protecting goods
    cannot be dropped (`pg_undominated`, `pg_only_g2`; a further remark, not in the paper), and the worked example's remaining numbers (every cycle of want and pair arrows has two pair
    arrows, `w_cycles`; DE's step, the totals 14 and 20, the completion: `w_step`, `w_totals`, `w_after`).

## Correspondence with the paper

Each row is a claim of the paper (with its row ID in the research repository's ledger) and the Lean theorems that
prove it, as `file : names`.

| Ledger | Statement | Lean (file : name) |
|---|---|---|
| K3S.PO.LEAN | The Improvement Lemma: a valid state in which no free agent is a valid absorber (can finish) and some agent is not a pair holder is Pareto-dominated by a valid state (a chain or a ring; computed by `step`), in which every agent of the ring or chain has a higher score and every other agent the same; every undominated valid state has a valid absorber, free unless every agent holds its pair; the distinct leftover goods are chosen by the paper's rule (the first blocker whose leftover good no earlier free agent took) | K3DEImprove : `EFX.DE.improvement`, `EFX.DE.completable_of_undominated`, `EFX.DE.step_stop`, `EFX.DE.step_stop_of_none`, `EFX.DE.step_next`, `EFX.DE.step_next_cycle`, `EFX.DE.step_next_scores`, `EFX.DE.cycleStep_cycle`, `EFX.DE.succ_pair`, `EFX.DE.succ_exchange`, `EFX.DE.cycleStep_spec`, `EFX.DE.reps_spec`, `EFX.DE.reps_first_blocker`, `EFX.DE.repOf_reps_append`, `EFX.DE.find?_Hset` |
| K3S.PO.LEAN | Lemmas staying valid (transfer), ring and chain (one lemma: valid, every agent of the cycle gets a strictly higher score, every other agent keeps its score), the finishing test (a)–(c) (Lean names empty and forced: under (NC) nobody is a blocker of a free agent holding nothing, which has `H_o = ∅` and passes the count); soundness of the completion (EFX₀ for every consistent valuation, only the absorber's bundle larger than two goods) | K3DE : `EFX.DE.transfer`, `EFX.DE.exchange`, `EFX.DE.exchange_scores`, `EFX.DE.completeDE_completion`, `EFX.DE.soundness`; K3DEImprove : `EFX.DE.not_exposed_of_none`, `EFX.DE.absorber_empty`, `EFX.DE.forced_hOf`, `EFX.DE.absorber_forced`, `EFX.DE.absorber_iff`, `EFX.DE.Hset_eq_nil`, `EFX.DE.count_of_none`, `EFX.DE.holds_of_count` |
| K3S.PO.LEAN | Algorithm DE is correct: on every instance with at most three relevant goods per agent it returns an EFX₀ allocation with all bundles but at most one of at most two goods, after at most `4n` exchanges; the paper's worked example and small example | K3DEAlgo : `EFX.DE.draft_valid`, `EFX.DE.loop_spec`, `EFX.DE.deCore_spec`, `EFX.DE.deStage_sound`, `EFX.DE.run_sound`, `EFX.DE.deSpec_correct`; K3DEExamples : `EFX.DE.Examples.worked_spec`, `EFX.DE.Examples.small_spec` |
| K3S.PRELIM.LEAN | Threats and safety (EFX₀ iff every agent is safe); Lemma threats (a)–(c); Lemma safety (a), (b); Lemma peeling (P of at most one good); Lemma R1fail | K3DEPrelim : `EFX.DE.efx0L_iff_safe`, `EFX.DE.threat_pair`, `EFX.DE.safe_of_pair`, `EFX.DE.safe_of_gy`, `EFX.DE.peeling`, `EFX.DE.R1fail` |
| K3S.LIMITS | Lemma cases of safety; Proposition limits of the shape (a), (b) for every valuation with distinct, strictly balanced values (natural numbers and ordered values) | K3DELimits : `EFX.DE.Limits.safe_iff_cases`, `EFX.DE.Limits.limits_a`, `EFX.DE.Limits.limits_b`, `EFX.DE.Limits.limits_a_ordered`, `EFX.DE.Limits.limits_b_ordered` |
| K3S.SHORT | Proposition short moves: without a short move, at least 2 free agents, n ≥ 6, m ≥ 8 (n ≥ 9, m ≥ 12 with 3); both bounds attained | K3DEShort : `EFX.DE.prop_short`, `EFX.DE.short_counts`; K3DEShortExamples : `EFX.DE.ShortExamples.w_attains`, `EFX.DE.ShortExamples.s8_attains`, `EFX.DE.ShortExamples.s8_remark` |
| K3S.EX.LEAN | The worked example: exactly four dominating valid states; all ten candidate completions fail EFX₀; every cycle of want and pair arrows has two pair arrows; DE's step and the completion; the EFX-versus-EFX₀ instance of main.tex §1 (`efx_not_efx0_intro`) and a second example of EFX but not EFX₀, not in the paper; the protecting goods cannot be dropped (a further remark, not in the paper) | K3DEShortExamples : `EFX.DE.ShortExamples.w_facts`, `EFX.DE.ShortExamples.w_exactly_four`, `EFX.DE.ShortExamples.w_completions`; K3DERemarks : `EFX.DE.Remarks.w_cycles`, `EFX.DE.Remarks.w_after`, `EFX.DE.Remarks.efx_not_efx0`, `EFX.DE.Remarks.efx_not_efx0_intro`, `EFX.DE.Remarks.pg_undominated`, `EFX.DE.Remarks.pg_only_g2` |
| K3S.RINGS | The ring family: every cycle of want and pair arrows uses exactly k pair arrows; no free agent absorbs iff k ≤ 2^d | K3DERings : `EFX.DE.Rings.gen_tree_ring`, `EFX.DE.Rings.nExp_eq`, `EFX.DE.Rings.no_free_absorber_iff` |
| K3S.TIME | The running time of DE: a counted program that computes exactly DE's output takes at most 750 (n + 1)(n + m + 1) operations (array reads and writes one unit each); on ordered values, plus the surrogate's n(m + 12) oracle calls and O(nm) operations | K3DECostRun : `EFX.DE.de_eq_spec`; K3DECostBound : `EFX.DE.deC_cost`, `EFX.DE.deC_cost_poly`, `EFX.DE.stepC_cost`; K3DECostReal : `EFX.DE.deOrdC_cost` |
| K3S.REAL.LEAN | DE on ordered values (comparison model through L12's surrogate); existence with the shape for ordered values; at most n peeling rounds | K3DEReal : `EFX.DE.deOrd_correct`, `EFX.DE.thmD_ordered`, `EFX.DE.de_correct`, `EFX.DE.peels_le` |
