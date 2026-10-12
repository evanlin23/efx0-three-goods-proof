# Revision of October 2026: an external review, a referee of the revision, two prose passes, a final read

What was reviewed after the referee report of this folder (`REPORT.md`), and what was done about it. The text is
`paper/k3-simple/main.tex`; `long.tex`, which only duplicated it, was retired at the end of the round.

## 1. External review of main.pdf

A manuscript-level review (supplied by the author; it did not inspect the repository or run Lean) found no gap in
the central argument and asked for presentation changes. All were made:

1. **Scores, not welfare.** The abstract and overview said that every agent on a chain or ring "gets strictly better
   off". Ranks break ties by index, so a move from `b_i` to `a_i` with `v_i(a_i) = v_i(b_i)` raises the score but not
   the value. The text now says that every agent gets a higher-ranked holding and loses no value, and a remark after
   Definition 1 says when the value rises. The total score Φ is named and bounds the trades.
2. **The corollary on Pareto-optimal states** is renamed "score-Pareto-maximal valid states", with a note that it is
   not an efficiency guarantee.
3. **Positioning.** EFX against EFX₀ on the 4, 3, 2 example with a good of value 0 (machine-checked:
   `EFX.DE.Remarks.efx_not_efx0_intro`); the novelty claim scoped to the results of Table 1; the six-agent instance
   checked against each row (Appendix E); the 4, 1, 1, 1 instance named in the introduction.
4. **Running time.** A step-by-step derivation of O(n(n + m)) (input, peeling, each loop step, blockers under (NC),
   the sets H_o, the distinct leftover goods, the ring); Theorem 2 states the unit-cost RAM model.
5. **Verification.** Table 2 maps every result to its Lean theorem and value domain; Appendix F explains the
   natural-number encoding of real values and lists what is not formalized.
6. **Exposition.** An intuition paragraph after the definition of validity; the direction of the arrows; the open
   problems as questions.

## 2. Independent referee of the revision

A separate session checked every new statement against the definitions and against the Lean files. One blocking
finding: the novelty sentence said that every result of Table 1 bounds a quantity that the model leaves free,
which was false for the row on two relevant goods per agent; fixed. Eleven minor findings, all fixed, among them a
missing citation of `EFX.numRelevant_eq_of_agree`, the cost of the encoding (`EFX.K3.surrogateC_cost`), a
"Section" that should read "Appendix", and stray backslashes in two file names.

## 3. Two prose passes

Two separate sessions checked the text against published lists of signs of machine-written prose (Wikipedia,
"Signs of AI writing"; word-frequency studies of recent abstracts) and proposed edits: 78 in the first pass, 19 in
the second. Every edit was read, and a script checked that no mathematics, formal statement, label, reference,
citation or file path changed. The passes also found three content errors, fixed:
- the ring family (Appendix C) said that the leftover goods are distinct within each tree, which fails when the
  leaves share a pool of k < 2^d goods (a tree then has min(2^d, k) of them; `lean/EFX/K3DERings.lean`); the
  theorem is unaffected;
- the abstract said that every agent can point to another, but only agents not holding their pair do;
- Theorem 2 now counts peeling rounds rather than "steps".

## 4. Final read

A last session read the whole final text, recomputed every example with its own implementation of DE, and checked
Table 2 against the Lean files. Verdict: no error and no gap. Eight minor findings, all fixed: the stopping rule
(a free agent takes the leftover goods, handing at most one to each other free agent), comparisons with 0, the file
pointers for real values (`RealValues.lean`, `K3Real.lean`), two rows of Table 2 (`EFX.DE.r1_of_two`,
`EFX.DE.Limits.limits_a_ordered`, `limits_b_ordered`), and the description of the referee implementation of
`../README.md` (written from the proof notes, not from the paper).

The review of section 1 was supplied by the author, and its source is not recorded here. The reviews of sections 2 to 4
were by AI agents (separate sessions of Claude Code).
