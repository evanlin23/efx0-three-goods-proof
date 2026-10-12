# Paper: EFX₀ with at most three relevant goods per agent

Every instance with nonnegative additive valuations in which each agent positively values at most three goods has a
complete EFX₀ allocation, in which all bundles but at most one have at most two goods, and algorithm Draft and
Exchange (DE) computes one in O(n(n + m)) steps of a unit-cost random-access machine, with at most 4n trades. After
peeling and a draft, DE's loop has three steps: a chain (an agent holding its top takes its two other goods, both
leftover), finish (a free agent takes the leftover goods, each of its blockers' leftover goods going to another free
agent), or a ring of trades. The proof rests on the Improvement Lemma: in a valid state in which no free agent can
finish, a chain or a ring raises some agent's score (the rank of its holding, never at a loss of value) and lowers
nobody's; the ring exists because every agent can point at an agent that would gladly take its good. The novelty
claim (§1, "What is new") rests on the literature search of `proofs/novelty.md` (25 September 2026). The paper is in
Springer's LLNCS format, 11pt.

- `main.tex` → `main.pdf`: **the paper** (about 10 pages of body before the references): what is new (EFX versus
  EFX₀ on an example, and the comparison with earlier results), peeling, states, finishing (with the soundness
  proof), improving (chain, ring, the finishing test, the Improvement Lemma, all with proofs), DE with pseudocode, a
  three-agent example and the running time step by step; in the appendix the proofs of §2–§3, the corollary on
  score-Pareto-maximal valid states, the worked example with its figure, how large a ring must be, the limits of the
  shape, the related-work table with an instance that no earlier result covers (checked row by row), and the
  verification in detail (Table 2: every result and its Lean theorem; how real values are encoded; what is not
  formalized).
- `refs.bib`: the bibliography; `Repo` is this repository at tag `v1.0`, which holds the notes, tests,
  referee reports and Lean files.
- `llncs.cls` and `splncs04.bst`: Springer's LLNCS package, unmodified.
- `examples/check_examples.py`: an independent implementation of the definitions (wants, free agents, blockers,
  finishing, want and pair arrows, rings, chains) and of DE with its loop chain / finish / ring, written from the
  text, that recomputes every example and number of the paper: the instance of "What is new" that is EFX but not EFX₀ (and
  a second such example), and the remark on two relevant goods; the three-agent example; the worked example (draft state, wants, free agents, blockers, the sets
  H_o, all 10 candidate completions failing, no short move, the 4 dominating valid states, the arrows and cycles of
  its figure, DE's ring and output, raw EFX₀, also for 2,000 random valuations); both instances of Proposition short
  moves and the remark on the reused leftover good; the ring family for k ≤ 4, d ≤ 3, and DE's trades on it at depth
  4; Lemma cases of safety and Proposition limits of the shape, by listing every allocation; on all 30,507 valid
  states of the core profiles with n = 2 (m ≤ 6) and n = 3 (m ≤ 7), up to renaming goods, the finishing test,
  soundness (every completion), Lemma ring (every ring), the Improvement Lemma in the form of its proof and DE's loop
  started there; DE, peeling included, on 40,000 random instances, compared with an alternative loop (a free agent
  holding nothing finishing first) and with the earlier implementation `k3/simplify/po/hall/hall.py`; and the
  instance of "What is new" (that no earlier result's hypotheses hold for it, and DE on 2,000 random value draws).
  Run from the repository root: `python3 paper/k3-simple/examples/check_examples.py` (one process, about a minute;
  output copied to `examples/check_output.txt`; exit status 0 iff every check passes).

Build (pdflatex and bibtex; TeX Live with `texlive-pictures` and `texlive-science`; fonts are Latin Modern):

    pdflatex main && bibtex main && pdflatex main && pdflatex main

Status of the claims (section numbers are those of `main.pdf`). Every result is a written proof that is also
machine-checked in Lean, except a second, independently found proof of the Improvement Lemma (a "rainbow walk"):
- the Improvement Lemma, soundness, DE with its 3-step loop and at most 4n trades, and the shape
  (`lean/EFX/K3DE.lean`, `K3DEImprove.lean`, `K3DEAlgo.lean`, `K3DEExamples.lean`; ledger row K3S.PO.LEAN; the Lean
  files use other names for some notions: needs for wants, exposed for blocker, protecting good for leftover good, valid
  absorber for an agent that can finish);
- the lemmas of §2, Lemma cases of safety and Proposition limits of the shape (Appendix D), Proposition short moves
  with its instances and the ring family (Appendix C; every k and depth), the worked example's facts, the example of EFX
  but not EFX₀, at most n peeling rounds, and DE on ordered values such as ℝ≥0 (`lean/EFX/K3DEPrelim.lean`,
  `K3DELimits.lean`, `K3DEShort.lean`, `K3DEShortExamples.lean`, `K3DERings.lean`, `K3DEReal.lean`,
  `K3DERemarks.lean`; ledger rows K3S.PRELIM.LEAN, K3S.LIMITS, K3S.SHORT, K3S.EX.LEAN, K3S.RINGS, K3S.REAL.LEAN);
- the running time O(n(n + m)) (`lean/EFX/K3DECost*.lean`, ledger row K3S.TIME: at most 750 (n + 1)(n + m + 1)
  counted operations, array reads and writes one unit each).

Not formalized (Appendix F of `main.pdf`, "What is not formalized"): that a counted unit matches a machine step
(checked by reading the counted program); that the nonnegative reals satisfy the axioms of Lean's class of values
(core Lean has no real numbers); that DE run directly on real values makes the same decisions as on their
natural-number encoding (Lean states the theorem for the encoding); and that the Lean statements say what the text
says (compared by AI audits, not by a human).

The formal statements were written by AI assistant sessions; independent AI referee sessions compared them with the
text (`k3/simplify/po/referee/lean_audit.md`, `lean_audit2.md`, `lean_audit3.md` for earlier drafts;
`lean_audit4.md` for the current text, whose two blocking mismatches, the tie-break among leftover goods and the
per-agent gains of a ring, are resolved). The written proof was derived independently twice
(`k3/simplify/po/hall/NOTES.md`, `k3/simplify/po/potential/NOTES.md`) and refereed once with no error
(`k3/simplify/po/referee/README.md`); the current proofs were refereed once more, by a session that read only
`long.tex`, a longer exposition of the same proofs (removed from this repository after commit `ffeae05`; it is in
the history): no mathematical error, four one-line gaps fixed (`k3/simplify/po/referee/simple/REPORT.md`, with its own
implementation of DE and its tests, zero failures on about 14.9 million instances). The provers and referees were AI
agents: separate sessions of the coding assistant (Claude Code). The October 2026 revision (an external review, a
referee of the revision, two prose passes and a final read: no error, no gap) is recorded in
`k3/simplify/po/referee/simple/REVISION.md`. There has been no human peer review. Every claim is
taken from the claims ledger of the research repository evanlin23/efx0-three-goods (`LEDGER.md` at commit `31202dc`;
the rows above, and K3S.PO, K3S.SA, K3S.ST) and the notes it cites, or from the runs of `examples/check_examples.py`.
