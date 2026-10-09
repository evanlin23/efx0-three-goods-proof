# Third faithfulness audit: the running time and the remarks in Lean (paper/k3-simple)

An independent referee session (a separate AI agent of the coding assistant, Claude Code, read-only, not the author of
the files) compared `lean/EFX/K3DECost.lean`, `K3DECostStep.lean`, `K3DECostRun.lean`, `K3DECostBound.lean`,
`K3DECostReal.lean` and `K3DERemarks.lean` (branch `proof/k3-simplify`, at commit `b081b44`) with
`paper/k3-simple/long.tex` §5 (remark on protecting goods), §6.2 (paragraph Running time and the proof of the main
theorems), §6.3 (the worked example and its figure), §2 (Example EFX vs EFX₀) and §8, and with the ledger rows K3S.TIME
and K3S.EX.LEAN. Scope: definitions and statements, and whether the counted program is a faithful cost model; not the
proofs (the build passes `lean/check.sh`). Below: its findings, condensed, and what was done about each.

**Verdict.** No BLOCKING issue.
- The counted program `EFX.DE.deC` computes exactly DE's output (`de_eq_spec`, so `deC_correct` is Theorem DE for it),
  and its charges are those of a random-access machine: one unit per elementary operation, comparison, counter step,
  table or input read and array write, a new array of `k` entries charged `k`, arrays used single-threaded (a charged
  copy where an old version is still needed). Every number of the ledger row K3S.TIME is a theorem: `stepC_cost`
  (175n + 11m + 7), `loopC_cost` (4n + 1 rounds), `peelC_cost` (30n + m + 3), `deC_cost_poly`, `deC_cost` and
  `deOrdC_cost`; each has a `#print axioms` line.
- `deOrdC_cost` adds the cost of the comparison-oracle surrogate (`EFX.K3.surrogateC_cost` at one unit per call) to
  `deC_cost`; the hypothesis "at most three relevant goods" reaches the surrogate through `agree_surrogate`, which is
  what the hypotheses "correct oracle" and "nonnegative values" are for.
- `K3DERemarks.lean` matches the paper: `EFX` is the paper's EFX (only goods of positive value may be removed) and
  `efx_not_efx0` is Example EFX vs EFX₀; `pg_facts`, `pg_undominated`, `pg_only_g2` and `pg_absorbers` are the remark on
  protecting goods; `w_detail`, `w_cycles`, `w_step`, `w_totals` and `w_after` are the facts of §6.3.

**MINOR findings, and their resolution.**
1. long.tex §6.2 said "peeling takes O(n) steps per round once the relevant goods … are known", then "This count is
   machine-checked"; Lean proves O(n + m) per round (30n + m + 3: the peeled goods are erased from the list of goods).
   The total O(n(n + m)) is unaffected. Resolved: the paragraph now says that a round of peeling takes O(n + m) steps.
2. The module doc of `K3DECostBound.lean` quoted paper text that is no longer there ("We have not formalized this
   count."). Resolved: it quotes the current paragraph.
3. long.tex §8 and the ledger gave 175n + 11m + 7 per loop iteration; `loopC` charges one more unit per round for the
   exchange counter (`loopC_cost`: 175n + 11m + 8 per round). Resolved: §8 says 175n + 11m + 8 (one unit for the
   counter); the ledger and the module doc mention the extra unit.
4. Scope of two example theorems, kept as is: `w_cycles` proves that every cycle of the exchange digraph of the worked
   example has four agents and two exposure arcs (the figure caption's claim), not that there are exactly four cycles
   (the four exchange cycles are listed by `wCycles` in `K3DEShortExamples.lean`); the new holdings after the exchange
   and "o₁ and o₂ take their tops" follow from `w_step` and the definition of the exchange, and are corroborated by
   `w_exchanges`, `w_totals` and `worked_spec`, but no theorem states them one by one. "(P) holds" after the exchange
   follows from `w_after` (the step stops at x₁' with H = ∅, and the pair-chain test comes first).
5. Conventions inherited from the cost model of K3ALG (`EFX/K3CostLB.lean`), not new here: natural numbers of any size
   cost one unit (sums of values), and some reads of the profile and of the picks inside the ranking functions are
   charged through `tick` rather than `rd`. Kept as is; the charge is the same.
