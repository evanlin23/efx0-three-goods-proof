# Referee report: the simplified proof of paper/k3-simple (chain / finish / ring)

An independent referee session (a separate AI agent of the coding assistant, Claude Code) read only
`paper/k3-simple/long.tex` at commit `8f30dde` (branch `proof/k3-simpler`), with no access to the repository's notes,
code, Lean files or earlier versions, and wrote its own test programs from the paper's definitions (this folder).
Below: its report, condensed, and what was done about each finding.

## Verdict

**No mathematical error.** Every definition, lemma, theorem and proof of Sections 2–6 (peeling, states, finishing,
improving, algorithm DE and its correctness) is correct and complete; so are Section 7 (the worked example) and
Appendices A–B (short moves and the ring family; cases of safety and limits of the shape). Four small gaps (G1–G4)
need one-line fixes and change no stated result.

## Line by line (Sections 2–6)

- Lemma peeling, rule R1, Corollary two relevant goods, the rankings, Lemma when nobody can leave: correct (gaps G1,
  G2 below).
- Definitions states, wants/validity/free agents and the remarks after them; Lemma draft; Lemma staying valid
  (if i wants g in Y′, then i ∉ U′, so its score in Y is at most 3, so in Y it held nothing or y with y′ = y or
  y′ ≻ y, and by transitivity it wanted g in Y): correct.
- Definition blockers/finishing: well defined (|H| ≤ |F| − 1 is the number of other free agents).
- Theorem soundness: correct and complete (sizes; wanted goods stay alone since their holders are not free; for
  T = X_j ∩ R_i: pair holders, agents holding nothing, and agents holding y with |T| ≤ 1 or T = {b_i, c_i}, where
  |X_j| ≥ 3 forces j = o and makes i a blocker, contradicting the choice of H; i = o and receivers of H are covered by
  X_i ⊇ Y_i).
- Definition rings, Lemma ring (the goods y_t distinct, each to one agent; the h's distinct and leftover; holdings
  allowed; scores rise; a wanted good on the ring sits at a non-free agent, whose arrow is a want arrow): correct.
- Lemma chain (j_t ≠ x for t ≥ 1; the repeat case gives a ring of want arrows of length ≥ 2; k = 0; the last
  agent's good unwanted; b_x, c_x unwanted): correct.
- Lemma the finishing test ((a), (b) from (NC) and o holding at most one good; (c) H meets {b_x, c_x} iff h_x ∈ H):
  correct.
- Theorem Improvement Lemma (distinct leftover goods exist as |H_{o_i}| ≥ f > i − 1; σ well defined, also with
  F = ∅; the cycle satisfies the definition of a ring): correct and complete.
- Corollary Pareto-optimal states; Algorithm 1 and Theorem DE is correct (peeling rounds are Lemma peeling; the loop
  runs in the core from a valid draft; both the chain and the ring keep validity and raise the total score; at most
  4|A| trades; at the break Lemma the finishing test and Theorem soundness apply; H_o is defined in line 12 because
  (NC) holds there): correct. Running time: plausible (gap G3); real values: 10,000 random instances with
  non-integer rational values passed.

## Gaps (no stated result affected) and their resolution

- **G1. Rule R1 when G = ∅** ("p, i's favourite good of G" is undefined; DE can reach it, e.g. n = 3, m = 1).
  Resolved: "If G = ∅ or v_i(p) = 0, so that i values no remaining good, then i may leave with P = ∅" (both papers).
  This is what the Lean definition (`EFX.K3.r1Step`: no favourite ⇒ leave with nothing) already does.
- **G2. Corollary two relevant goods: "rule R1 applies to the first agent's choice"** is not literally true (a good
  worth 0 to the agent; ties). Resolved: the proof now says the bundle satisfies conditions (i) and (ii) of Lemma
  peeling.
- **G3. Running time: "a blocker of at most one free agent"** holds only under (NC) (counterexample: rankings
  (g0, g1, g2), (g3, g5, g6), (g4, g7, g8) holding g0, g3, g4). Resolved (also found by the paper's check script):
  "once the chain test has failed, (NC) holds, and …".
- **G4. Algorithm 1, line 9** did not say that in the repeat case of Lemma chain one trades along the ring of want
  arrows. Resolved: "apply the chain of the first such x, or the ring of want arrows it runs into".

## Presentation (resolution in brackets)

- P1 the supplied PDF was older than the source (no-chain condition "(C)", clashing with case (C) of Lemma cases of
  safety) [the source already said (NC); PDFs rebuilt]. P2 R1 and rankings: say which way ties go [lower index
  first]. P3 = G2. P4 Algorithm 1: line 9 = G4; line 16: give the matching [the k-th good of H, in the order of first
  blockers, to the k-th other free agent]; line 12: (NC) holds there [stated in the proof of Theorem DE]. P5 define
  "trade" [one chain or one ring]. P6 overview: the finishing criterion is Lemma the finishing test with Theorem
  soundness [fixed]; the loop can also end with every agent holding its pair [fixed]; the abstract omits agents that
  leave with nothing ["with at most one good"]. P7 = G3. P8 Section 7: "every improvement" → every valid state
  Pareto-dominating the draft state; say that every want arrow ends at o₁ or o₂ [both fixed]. P9 Appendix A, ring
  family: o_i is the root of its tree; the leaves' leftover goods must be distinct, otherwise "iff k ≤ 2^d" fails;
  no proof is given; k = 2, d = 1 is Section 7's instance [all four fixed; the proofs are in Lean, `K3DERings.lean`].
  P10 Proposition short moves: "|H_o| ≥ |F|, hence at least |F| blockers" [fixed]. P11 Appendix B: define "threat";
  "and i is safe if" [fixed]. P12 Example EFX-but-not-EFX₀ has no good nobody values, so it does not illustrate
  that sentence [the sentence now says what the example shows]. P13 conclusion, "many more trades on the rings" was
  unclear [now: up to 12 trades from the draft at depth 4, as the paper's script prints]. P14 small points: "at most
  n peeling steps" is really n − 1 [harmless, kept]; Corollary "all bundles but one" → "but at most one" [fixed]; the
  letter x for σ's target and for agents x₁ [kept]; "Theorem (Improvement Lemma)" [kept]. P15 Section 8 not checkable
  from the text [not reviewed by this referee; see `../lean_audit4.md`].

## Tests (all with zero failures; scripts and logs in this folder)

`de.py` implements DE exactly as Algorithm 1 states it (peeling; draft; loop chain / finish / ring; for the ring, q
was taken as the first unused good in index order, the rule of the text it read; the paper now takes the first
blocker whose leftover good is unused, as the Lean does) and asserts at every step: the draft is valid with U = ∅;
every move gives a valid state in which every agent on the move strictly gains, the others keep their holdings and
the total rises; every ring satisfies the definition literally; in the ring branch every free agent holds a good and
has |H_o| ≥ |F|; Lemma the finishing test (b); at most 4|A| trades; the finishing H is allowed; the output is
complete, has at most one bundle of more than two goods, and is EFX₀ by the raw definition with exact arithmetic.
"Deep" mode also checks the finishing test (a), (c) by brute force over H ⊆ J, and soundness for every finishing
agent, up to 6 allowed H and 2 assignments of H.

| Test | Instances |
|---|---|
| Core, n = 2, m = 3..7, all 13 value patterns, deep | 294,398 |
| Core, n = 3, m = 3, 4, 5, all patterns, deep | 2,339,805 |
| Core, n = 3, m = 6 rankings, deep | 1,728,000 |
| Core, n = 3, m = 7 rankings, deep | 9,261,000 |
| Core, n = 4, m = 4 rankings, deep | 331,776 |
| General exhaustive (n ≤ 3, m ≤ 4, small values, ≤ 3 positive) | 329,221 |
| Random, n ≤ 8, six families × 100,000 (ties, unbalanced agents, goods nobody values, planted Section 7 gadgets) | 600,000 |
| Random, non-integer rational values | 10,000 |
| Ring-family instances, several agent and good orders | about 1,300 |

`allstates.py` checks every state of each profile (not only those DE reaches): exhaustive n = 2 (m ≤ 6) and n = 3
(m = 4, 5), 40,000 random profiles with n = 3..5, and the two instances of Appendix A: 30.4 million states, 1.44
million valid; Lemma staying valid on 721,600 pairs, the finishing test, soundness on 8.1 million completions, Lemma
chain for every eligible x (7,093 repeat cases), the Improvement Lemma whenever its hypotheses hold (about 200,000
states), the Corollary on every Pareto-optimal valid state, and the bounds of Proposition short moves (no state
without a short move for n ≤ 5). `example7.py` and `appendix.py` recheck every claim of Section 7 and Appendices A–B
(25 valid states, exactly 4 dominating the draft state, each with two new pairs; 33,200 allocations for Lemma cases
of safety; Proposition limits of the shape for 300 and 100 random value profiles; the ring family for k = 2..5,
d = 1, 2). The most trades in any run was 7.

Run from this folder, e.g. `python3 example7.py`, `python3 appendix.py`, `python3 random_de.py`; the logs are those
of the referee's runs.
