# Fourth faithfulness audit: the simplified paper/k3-simple/long.tex against the Lean of DE

Independent referee session, read-only. Branch `proof/k3-simpler` at `7aea4e9` (long.tex gained the "small example"
paragraph in §6 during the audit; this report covers that version). Compared: long.tex §1 (Status, Theorem
algorithm), §3–§6 (Definitions states/scores, wants/validity/free, blockers/finishing, rings; Lemmas draft, staying
valid, ring, chain, finishing test; Theorem soundness; Improvement Lemma; Corollary Pareto-optimal states;
Algorithm 1; Theorem DE is correct; Running time; Real values), §8, with `lean/EFX/K3DE.lean`, `K3DEImprove.lean`,
`K3DEAlgo.lean`, and as needed `PreAlloc.lean`, `LBSound.lean`, `LBRun.lean`, `K3Algo.lean`, `K3DEReal.lean`,
`K3DECost*.lean`, `K3DEExamples.lean`; ledger rows K3S.PO.LEAN, K3S.PRELIM.LEAN, K3S.SHORT, K3S.EX.LEAN, K3S.RINGS,
K3S.TIME, K3S.LIMITS; `lean/README.md`. Statements and definitions only (the build passes `lean/check.sh`).
Two small Lean `#eval` scripts and one Python script were run from the scratchpad (no repository file touched).

## Verdict

Two BLOCKING items, both easy to fix. Everything else matches or is MINOR (stale names and section numbers, a
stale note, one example not checked anywhere).

## BLOCKING

**B1. Lean's DE picks different leftover goods from Algorithm 1, so "DE is a Lean function" does not hold for the
algorithm as written.**
- Paper, proof of the Improvement Lemma (long.tex l.232): "pick q_{o_i} ∈ H_{o_i} \ {q_{o_1},…}, *the first in
  index order*". By §2 (l.87), index order is the goods' numbering. Algorithm 1 l.272 uses "the ring of the proof".
  Algorithm 1 l.275 also says "give the goods of H to different free agents other than o, in index order".
  `paper/k3-simple/examples/check_examples.py` (described in §8 as "written from this paper with the loop as stated
  here") implements this as `min(g …)` and `sorted(H)`.
- Lean: `EFX.DE.reps` takes the first unused good *in the list order of* `EFX.DE.Hset`, and
  `Hset = dd ((agents.filter (expB … o)).map hOf)`. That is the blockers in agent order, and `dd` keeps the *last*
  occurrence of each good. `completeDE` hands out `H` in this same `Hset` order. K3DEImprove choice 5 documents the
  Lean order, but the paper now states a different rule.
- Concrete divergence: take the worked example and swap the c-goods of x₁ and x₁' (x₁: g₀≻g₄≻g₇, x₁': g₁≻g₄≻g₆,
  everything else as in §7). Lean: `Hset o₁ = [g₇, g₆]`, so q_{o₁} = g₇ and x_{o₁} = x₁. The step trades
  o₁→x₁→o₂→x₂→o₁, and `deSpec` returns owners `[5,1,4,3,0,2,1,0,2,1]`. The paper's rule (and `check_examples.de`)
  gives q_{o₁} = g₆, x_{o₁} = x₁', the ring o₂→x₂→o₁→x₁'→o₂, and owners `[0,5,4,3,1,2,1,3,2,3]`. Both outputs are
  EFX₀, but they are different allocations. Even under a "blocker order" reading the rules differ when two blockers
  share a leftover good, because `dd` keeps the last occurrence.
- Effect: `deSpec_correct`/`de_correct`, the 4n bound and `deC_cost` (K3S.TIME, "exactly DE's output") are about a
  variant of Algorithm 1. The written proof covers every choice, so correctness is not in doubt. But §8 ("DE is a
  Lean function, and the main theorem states … it returns …") and §1 Status ("machine-checked … together with the
  algorithm") are not literally true.
- Fix (any one of these):
  - (a) Cleanest. In Lean, let `dd` keep the *first* occurrence (`ddC` walks from the start; adjust
    `mem_dd`/`nodup_dd`/`ddC_val`). In the paper, write: "let x_{o_i} be the first blocker of o_i whose leftover good
    is not among q_{o_1},…,q_{o_{i−1}}, and q_{o_i} = h_{x_{o_i}}". At l.275, write "the goods of H, in the order of
    their first blockers, to the free agents other than o in index order". Update `check_examples.py` to match.
  - (b) Order `Hset` by `goods` in Lean, which matches the current text and the script. The counted program then
    needs a bucket pass to stay O(n+m) per iteration.
  - (c) Describe the current Lean order in the paper ("the good whose last blocker comes first"). This is awkward.

**B2. Lemmas ring and chain claim more per agent than `EFX.DE.exchange` states.**
- Lemma ring (l.189): "every agent of the ring has a higher score and every other agent the same score".
- Lemma chain (l.199): "x, j₁,…,j_k have higher scores and every other agent the same score". It also claims: "if an
  agent repeats, the agents from its first occurrence on form a ring of want arrows".
- `EFX.DE.exchange` concludes only `Valid ∧ Dominates` (all ≥, some >). The per-agent facts are proved inside the
  proof (`hlt`, `heq`) but are not exported. The docstring of `exchange` ("every agent of the cycle strictly gains")
  claims more than the statement. For the chain, `step_next_cycle` gives only "an exchange along a `Cycle`". No
  statement says the cycle is a ring of want arrows when the walk repeats.
- Nothing downstream needs more than `Dominates` (Improvement Lemma, Theorem DE), so the results stand. Still, §8
  says "the proofs of Sections 2–6 are machine-checked".
- Fix (either):
  - Add `(∀ i ∈ agents, onC i = true → util … i < util' … i) ∧ (∀ i, onC i = false → util … i = util' … i)` to the
    conclusion of `exchange` (two lines; the proof already has them).
  - Or state Lemmas ring and chain as "a valid state in which nobody's score drops and some score rises", the wording
    Theorem DE's proof already uses (l.288).

## Statement-by-statement (OK unless noted)

| Paper | Lean | Verdict |
|---|---|---|
| Def. states and scores | `IsState`/`EFX.LB.Valid` structure (holdings nothing, a, b, c, or pair via `up` with `Y u = b u`; disjoint); `util` = 4/3/2/1/0 | OK. "Higher score never means lower value" has no Lean counterpart (remark, unused). |
| Def. wants, validity, free | `Profile.NA` with U = `up` (`rank g < pickRank`; pickRank none = 3, so "holds nothing ⇒ wants all of R_i"); `Valid` (V1 + V2 + structure ⇔ every wanted good is the pick of a non-pair holder, `na_picked`); `Free` | OK, equivalent. |
| Lemma draft (any order) | `draft_valid` for any duplicate-free `agents` list (`phase1` = first of a, b, c still in the pool) | OK |
| Lemma staying valid | `transfer` (needs no validity of Y: stronger) | OK |
| Def. blockers | `Exposed o x` (x ∈ agents, x ≠ o, x ∉ up, `Y x = a x`, b x and c x each junk or `InBase o`) | OK, equal |
| "o can finish with H" | `Absorber o H`: `o ∈ up ∨ Free o`, H ⊆ junk (list), `|H| ≤ nFreeExcept o`, hits every exposed x | For free o, equal to the paper's notion: `nFreeExcept o = |F|−1` (`nFree_eq`); a duplicate-free list stands for the set. Lean is more general (it also allows a pair-holder absorber), and the paper's all-pairs case is the instance o ∈ up, H = []. Nothing claimed is missing. |
| Completion | `completeDE` (picks, c of pair holders, `fill` with one slot per free agent ≠ o in agent order, rest to o) | OK; order of H: see B1 |
| Thm soundness (incl. all pairs) | `soundness` (any `Absorber`; valuations consistent with the rankings, a ≤ b+c allowed: stronger) | OK (ℕ values; reals via K3DEReal) |
| Def. ring / trading | `Cycle` + `exchY`/`exchUp` (receiver of a free predecessor takes its pair, else the predecessor's good) | A paper ring gives a `Cycle`: need ⇐ want arrows, free ⇐ pair {y_t, h}, disj ⇐ distinct h. Lean is more general (chains, k = 1, empty holders). OK |
| Lemma ring | `exchange` | **B2** |
| Lemma chain | `succ_pair` + `cycleStep_spec`/`step_next(_cycle)`; σ = `outNb` (first listed non-up agent preferring the good = "first agent that wants it"), free agents ↦ x; the cycle through σⁿ(x) is exactly x, j₁,…,j_k closed by j_k→x, or the need cycle the walk enters | Walk matches; **B2** for per-agent claims and the "ring of want arrows" sentence |
| (NC) | `PropP` (`propP_of_find`) | OK |
| Lemma finishing test (a) | `not_exposed_of_none` | OK |
| (b) | `forced_hOf` (for any o ∉ up; hOf = h_x, the other good is Y o) | OK |
| (c) | `absorber_iff`, `absorber_forced`, `Hset_le_of_absorber`; "in particular": `absorber_empty`, `Hset_eq_nil`, `count_of_none` | OK |
| Improvement Lemma | `improvement` + `step_next_cycle` (the move is one `exchange` along a `Cycle`); `holds_of_count` (free agents hold a good) | OK |
| Corollary Pareto-optimal | `completable_of_undominated`; "in particular" via `deCore_spec`/`deStage_sound` (by DE, not via a max-score state) | OK |
| Algorithm 1 peeling | `run`: `findR1` = first agent with `r1Step` ≠ none (favourite with ties to the earliest; v(p) = 0 ⇒ ∅; v(G∖p) ≤ v(p) ⇒ {p}); `|A| ≤ 1` ⇒ all to it | OK. With G = ∅ Lean stops peeling (same allocation; documented in K3DEReal choice 2). |
| rankings / draft | `profileOf`/`sort3` (stable: ties in list = index order); `phase1` in `agents` order | OK |
| loop: chain on first x | `agents.find? pairB` | OK |
| finish: all pairs ⇒ first agent, H = ∅ | `agents.headD d` with `[]` | OK |
| finish: first free o with \|H_o\| ≤ \|F\|−1, H = H_o | `find?` with `|Hset o| + 1 ≤ |F|` | OK (H's order: B1) |
| ring | `reps` over F in agent order; x_o = first exposed agent with hOf = q; σ = `outNb` for others; start s = first agent outside up; cycle of σ through σⁿ(s) = the cycle the walk from s closes | q choice: **B1**; everything else matches |
| final distribution "in index order" | `fill` with slot1, H in `Hset` order | **B1** |
| Thm DE is correct (≤ n peels, ≤ 4n trades, shape) | `de_correct` (K3DEReal: `deSpec_correct` + `dePeels_le`); `loop_spec` (moves ≤ total increase ≤ 4n) | OK for the Lean DE (B1) |
| Running time | `deC_cost` ≤ 750(n+1)(n+m+1), `de_eq_spec`, `stepC_cost` (175n+11m+7) | OK |
| Real values | `deOrd_correct`, `thmD_ordered`, `deOrdC_cost` (surrogate, n(m+12) comparisons) | OK as §8 describes it; Thm 3's "every decision compares two sums of ≤ 2 values" is not traced (K3DEReal choice 1). See M3. |
| Small example (§6, new) | none | M2 |

## MINOR (location → fix)

Paper (`paper/k3-simple/long.tex`):
- **M1** l.365 (vocabulary sentence). Add the other old names: "(P) for (NC), junk for leftover, utility for score,
  exchange cycle / need cycle (`Cycle`, `exchange`) for ring, frozen for an agent outside U ∪ F". Add that a valid
  absorber may also be a pair holder (used only when every agent holds its pair).
- **M2** l.291 (small example). The goods named are g₀, g₁, g₂, g₃, g₅; g₄ is skipped. If goods are numbered
  consecutively, g₄ is also leftover and X_z = {g₃, g₄, g₅}. Rename g₅ → g₄ (z: g₄≻g₀≻g₁, o: g₀≻g₄≻g₁, X_z = {g₄, g₃}).
  Checked: Lean `deSpec` on the renamed instance (m = 5) returns exactly X_z = {g₃, g₄}, X_x = {g₁, g₂}, X_o = {g₀},
  with 1 trade. The example is in neither `K3DEExamples.lean` nor `check_examples.py`, so §8 l.369 ("recomputes every
  example and number of the paper") is now inaccurate. Add it to the script; a `decide` example is optional.
- **M3** l.80 (Status) "and its use on real values". Lean runs DE on a natural-number surrogate (accurately described
  in §8 l.367). Suggest "…and, through natural-number values that answer the same comparisons, its use on real
  values". Thm 3's last sentence (l.67) has no Lean counterpart; say so in §8 or leave it to the "Real values"
  paragraph.
- **M4** l.365 "The proofs of Sections 2–6 … (lean/EFX/K3DE*.lean)": Corollary 1 (§2) is `EFX.sdRun_efx0` in
  `K3Extras.lean`, and §8 also lists it under "Further files check the rest". Harmless; optionally "Sections 2–6
  (Corollary 1 in K3Extras.lean)".

Lean comments (docstrings only):
- **M5** `K3DE.lean` header: "long.tex §4–§5" → §3–§5. "Lemma transfer" → Lemma staying valid. "Lemma exchange
  cycle" → Lemma ring. In the `Absorber` docstring, "the paper's Definition of absorbers" → Definition blockers,
  finishing ("can finish"). In the `Cycle` docstring, "the paper's cycles of D⁺" → rings. The `exchange` docstring
  claims strict gain (see B2).
- **M6** `K3DEImprove.lean` header: the lemma names (Lemma P(a)/(b), noF, empty, forced, cycle) → Lemma chain,
  Lemma finishing test (a)–(c), Improvement Lemma. Choice 2 says "The paper follows σ from any agent": the paper now
  starts at the first agent outside U, so it is no longer a choice.
- **M7** `K3DEAlgo.lean` header: "The running time O(n(n+m)) of the paper is not formalized" is stale (K3DECost*,
  K3S.TIME). The same goes for `K3DEReal.lean` choice 4; its header also cites "§6.2" → §6.
- **M8** `K3DEExamples.lean` header: "worked example of long.tex §6" → §7.
- **M9** `lean/README.md` l.379 "long.tex §4–§6" → §3–§6. The K3DERemarks bullet cites "the remark that the
  protecting goods cannot be dropped", which is no longer in the paper. "every cycle of D⁺" → "every cycle of want
  and pair arrows". README table row K3S.PO.LEAN (l.552): add `EFX.DE.not_exposed_of_none`.

Ledger (`LEDGER.md`):
- **M10** K3S.PO.LEAN:
  - Add `EFX.DE.not_exposed_of_none` (finishing test (a)) and `EFX.DE.step_stop_of_none` to the Lean column.
  - Name Lemma chain in the statement ("chain: `succ_pair`, `cycleStep_spec`").
  - The note "Faithfulness audited once … (lean_audit.md): no blocking issue" predates the rewrite. Cite this audit
    once B1/B2 are resolved.
  - Sections "§3–§6" are correct.
- **M11** K3S.EX.LEAN: "the remark that the protecting goods cannot be dropped (§5: …)". The rewrite removed this
  remark from the paper. Mark it "(remark of the earlier version)" or drop it from the statement and keep the Lean.
  "every cycle of D⁺" → "every cycle of want and pair arrows". §7 and §1 references are correct.
- **M12** K3S.RINGS note: "Corrects the paper's remark, which said 'no free agent absorbs' without the condition
  k ≤ 2^d …" is stale. Appendix A (l.408) now states "if and only if k ≤ 2^d". Reword, e.g. "matches the paper's
  iff". "exchange digraph D⁺" → "want and pair arrows".
- **OK** K3S.PRELIM.LEAN (§2, Appendix B, "the soundness proof of §4 argues these cases inline"), K3S.SHORT
  (Appendix A), K3S.LIMITS (Appendix B), K3S.TIME (§6 Running time; 175n+11m+7, 750(n+1)(n+m+1)). Their section
  references and wording match the new paper.

## §8 claims checked

| Claim in §8 | Verdict |
|---|---|
| "No library beyond Lean's own, no unproved step, standard axioms" | `lean/check.sh` (not re-run; given) |
| "the main theorem states … at most n peeling rounds and 4n trades" | `EFX.DE.de_correct` |
| "One Lean lemma covers chains and rings (a chain is closed by an arrow from its last agent back to x)" | `exchange` + `succ_pair` (with k = 0, the loop x→x) |
| Ordered values with n(m+12) comparisons | `deOrd_correct`, `deOrd_eq_surrogateC` |
| Facts of §7 and Figure 1 | K3S.EX.LEAN (`w_*`) |
| Example 1 | `efx_not_efx0` |
| Appendices | K3S.SHORT, K3S.RINGS, K3S.LIMITS |
| Running time 750(n+1)(n+m+1), reading the input included, counted program = DE's output | `deC_cost`, `de_eq_spec` |
| "DE is a Lean function" | Inaccurate for Algorithm 1 as written (B1) |
| "The proofs of Sections 2–6 are machine-checked" | Overstates Lemmas ring and chain (B2) |
| Vocabulary sentence | Incomplete (M1) |

## Reproduction (scratchpad)

- `AuditEval.lean`, `AuditEval2.lean`, `AuditEval3.lean`: run with `cd lean && lake env lean <file>`. They print
  Lean's `Hset o₁ = [7, 6]`, the step and `deSpec` on the swapped instance, and the small example.
- `run_py.py`: `check_examples.de` on the swapped instance.

Not audited: `paper/k3-simple/main.tex`, which also changed in `7aea4e9`.

## Resolution (coordinating session, branch `proof/k3-simpler`)

- **B1 (choice of the leftover goods).** The paper now uses the Lean's rule, which is also the simpler one to
  state: in the proof of the Improvement Lemma, each free agent in turn takes its first blocker whose leftover good
  is not yet taken, and Algorithm 1 gives the k-th good of H, in the order of first blockers, to the k-th other free
  agent. On the Lean side `dd` now keeps the first occurrence, so `Hset o` lists the goods in the order of their
  first blockers (`EFX.DE.find?_Hset`), and `EFX.DE.reps_first_blocker` states the rule in the paper's words (q_o is
  the leftover good of o's first exposed agent whose good no earlier free agent took, and σ(o) is that agent).
  `check_examples.py` follows the same rule (0 failures). No computed example changed, no constant changed.
- **B2 (per-agent gains).** New theorems `EFX.DE.exchange_scores` (along a `Cycle`, every agent on the cycle has a
  strictly higher utility and every other agent the same) and `EFX.DE.step_next_scores` (the same for every move of
  `step`), which give Lemma ring and Lemma chain as stated.
- **M1** vocabulary sentence of §8 lists every earlier Lean name and that a valid absorber may be a pair holder.
  **M2** the small example uses goods g₀, …, g₄, and is checked in Lean (`EFX.DE.Examples.small_spec`, by `decide`)
  and by `check_examples.py`. **M3** the status sentence says that real values are covered through natural-number
  values answering the same comparisons. **M4** §8 names `K3Extras.lean` for serial dictatorship. **M5–M9** module
  headers, docstrings and `lean/README.md` follow the simplified paper's sections and names (the remark that the
  protecting goods cannot be dropped is marked as a remark of the earlier version, kept in Lean). **M10–M12** ledger
  rows K3S.PO.LEAN (new theorems, this audit), K3S.EX.LEAN (arrows, the small example, the earlier remark) and
  K3S.RINGS (the stale note) are updated.

`lean/check.sh` after these changes: CHECK PASSED, 870 audited statements, 1,938 theorems, standard axioms only.
