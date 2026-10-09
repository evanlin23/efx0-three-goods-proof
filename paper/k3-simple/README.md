# Paper: EFX₀ with at most three relevant goods per agent

Every instance with nonnegative additive valuations in which each agent positively values at most three goods has a
complete EFX₀ allocation, in which all bundles but at most one have at most two goods, and algorithm Draft and
Exchange (DE) computes one in time O(n(n + m)), with at most 4n trades. After peeling and a draft, DE's loop has three
steps: a chain (an agent holding its top takes its two other goods, both leftover), finish (a free agent takes the
leftover goods, each of its blockers' leftover goods going to another free agent), or a ring of trades. The proof
rests on the Improvement Lemma: in a valid state in which no free agent can finish, a chain or a ring makes some agent
better off and nobody worse off; the ring exists because every agent can point at an agent that would gladly take its
good. The novelty claim (§1, "What is new") rests on the literature search of `proofs/novelty.md` (25 September
2026). Both documents below are in Springer's LLNCS format, 11pt, and each is self-contained.

- `main.tex` → `main.pdf`: **the paper** (about 9 pages of body before the references): what is new (with an instance
  no earlier result covers), peeling, states, finishing (with the soundness proof), improving (chain, ring, the
  finishing test, the Improvement Lemma, all with proofs), DE with pseudocode and a three-agent example; in the
  appendix the proofs of §2–§3, the corollary on Pareto-optimal states, the worked example with its figure, how
  large a ring must be, the limits of the shape, the verification in detail and the related-work table.
- `long.tex` → `long.pdf`: a detailed exposition of the same result, with every proof in the main text, an informal
  overview, the three-agent example and the worked example in the body, and appendices on how large a ring must be,
  the limits of the shape and related work.
- `refs.bib`: the bibliography of both; `Repo` is this repository at tag `v1.0`, which holds the notes, tests,
  referee reports and Lean files.
- `llncs.cls` and `splncs04.bst`: Springer's LLNCS package, unmodified.
- `examples/check_examples.py`: an independent implementation of the definitions (wants, free agents, blockers,
  finishing, want and pair arrows, rings, chains) and of DE with its loop chain / finish / ring, written from the
  text, that recomputes every example and number of both documents: Example EFX-but-not-EFX₀ and the remark on two
  relevant goods; the three-agent example; the worked example (draft state, wants, free agents, blockers, the sets
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
    pdflatex long && bibtex long && pdflatex long && pdflatex long

Status of the claims (section numbers are those of `main.pdf`). Every result is a written proof that is also
machine-checked in Lean, except a second, independently found proof of the Improvement Lemma (a "rainbow walk"):
- the Improvement Lemma, soundness, DE with its 3-step loop and at most 4n trades, and the shape
  (`lean/EFX/K3DE.lean`, `K3DEImprove.lean`, `K3DEAlgo.lean`, `K3DEExamples.lean`; ledger row K3S.PO.LEAN; the Lean
  files use other names for some notions: needs for wants, exposed for blocker, protecting good for leftover good, valid
  absorber for an agent that can finish);
- the lemmas of §2, Lemma cases of safety and Proposition limits of the shape (Appendix D), Proposition short moves
  with its instances and the ring family (Appendix C; every k and depth), the worked example's facts, Example
  EFX-but-not-EFX₀, at most n peeling rounds, and DE on ordered values such as ℝ≥0 (`lean/EFX/K3DEPrelim.lean`,
  `K3DELimits.lean`, `K3DEShort.lean`, `K3DEShortExamples.lean`, `K3DERings.lean`, `K3DEReal.lean`,
  `K3DERemarks.lean`; ledger rows K3S.PRELIM.LEAN, K3S.LIMITS, K3S.SHORT, K3S.EX.LEAN, K3S.RINGS, K3S.REAL.LEAN);
- the running time O(n(n + m)) (`lean/EFX/K3DECost*.lean`, ledger row K3S.TIME: at most 750 (n + 1)(n + m + 1)
  counted operations, array reads and writes one unit each).

The formal statements were written by AI assistant sessions; independent AI referee sessions compared them with the
text (`k3/simplify/po/referee/lean_audit.md`, `lean_audit2.md`, `lean_audit3.md` for earlier drafts;
`lean_audit4.md` for the current text, whose two blocking mismatches, the tie-break among leftover goods and the
per-agent gains of a ring, are resolved). The written proof was derived independently twice
(`k3/simplify/po/hall/NOTES.md`, `k3/simplify/po/potential/NOTES.md`) and refereed once with no error
(`k3/simplify/po/referee/README.md`); the current text was refereed once more, by a session that read only
`long.tex`: no mathematical error, four one-line gaps fixed (`k3/simplify/po/referee/simple/REPORT.md`, with its own
implementation of DE and its tests, zero failures on about 14.9 million instances). The provers and referees were AI
agents: separate sessions of the coding assistant (Claude Code). There has been no human peer review. Every claim is
taken from the claims ledger of the research repository evanlin23/efx0-three-goods (`LEDGER.md` at commit `31202dc`;
the rows above, and K3S.PO, K3S.SA, K3S.ST) and the notes it cites, or from the runs of `examples/check_examples.py`.
