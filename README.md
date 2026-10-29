# EFX₀ allocations with at most three relevant goods per agent

**Theorem.** Every instance with nonnegative additive valuations in which each agent positively values at most three
goods has a complete EFX₀ allocation, in which all bundles but at most one have at most two goods. Algorithm
*Draft and Exchange* (DE) computes one in O(n(n + m)) steps of a unit-cost random-access machine, with at most n
peeling rounds and at most 4n trades.

EFX₀ is envy-freeness up to any good in its all-goods form: v_i(X_i) ≥ v_i(X_j ∖ {h}) for all agents i ≠ j and
every good h ∈ X_j, including goods that i values at 0.

## Contents

| Path | What |
|---|---|
| `paper/k3-simple/main.pdf` | **The paper** (about 10 pages of body, with appendices). |
| `paper/k3-simple/` | LaTeX sources, bibliography, and `examples/check_examples.py`, which recomputes every example and number of the paper. |
| `lean/` | The Lean 4 formalization: the algorithm, its correctness, the bound on trades, the running time, real values, and the results of the appendices. |
| `k3/simplify/po/` | The proof notes (`hall/NOTES.md`, `potential/NOTES.md` for a second, independent proof), their test programs, and the reviews (`referee/`). |
| `proofs/novelty.md` | The literature search behind the paper's novelty claim (25 September 2026), with `proofs/citations.md` and `results/lit_search_log.md`. |
| `k4/de4/` | An attempt at four relevant goods (`NOTES.md`). DE extends to agents with a small fourth good (written proof and tests, not in Lean). A computational barrier shows how far DE's method reaches. The open problem itself is not solved. |

## How to check it

1. **Lean** (needs [elan](https://github.com/leanprover/elan); the toolchain is pinned in `lean/lean-toolchain`):

       cd lean && ./check.sh

   This builds the library, refuses `sorry`, debug options, metaprogramming and dependencies, requires a
   warning-free build, checks that every declaration uses only Lean's three standard axioms, and replays the whole
   library in a fresh kernel. It ends with `CHECK PASSED: … audited statements, … theorems, standard axioms only`.
   The main theorem is `EFX.DE.de_correct` (`lean/EFX/K3DEReal.lean`).

2. **Tests** (Python 3, no packages needed):

       python3 paper/k3-simple/examples/check_examples.py

   About a minute; exit status 0 if and only if every check passes (output in `examples/check_output.txt`).

3. **Paper** (TeX Live with `texlive-pictures` and `texlive-science`):

       cd paper/k3-simple
       pdflatex main && bibtex main && pdflatex main && pdflatex main

## What you have to trust

To believe the theorem, read the definitions in `lean/EFX/Model.lean` (about 50 lines: an instance, an allocation
as an owner map, EFX₀, the number of relevant goods) and the statement of `EFX.DE.de_correct`:

    theorem de_correct (I : Inst) (hn : 0 < I.n) (h : ∀ i, numRelevant I i ≤ 3) :
        I.EFX0 (deSpec I hn) ∧
          (∃ o, ∀ j, j ≠ o → finSum I.m (fun g => if deSpec I hn g = j then 1 else 0) ≤ 2) ∧
          dePeels I ≤ I.n ∧ deMoves I hn ≤ 4 * I.n

Everything else is checked by Lean's kernel. `lean/README.md` lists the other theorems and how they correspond to the
paper.

## Status of the review

- **Machine-checked** in Lean: every result of the paper's Sections 2–6 and appendices, the worked examples, the
  running time (a counted program equal to DE, at most 750 (n + 1)(n + m + 1) steps) and real values (through
  natural-number values that answer the same comparisons). Table 2 of the paper (Appendix F) maps every result to
  its Lean theorem. Not formalized: that a counted unit matches a machine step (checked by reading the counted
  program); that the nonnegative reals satisfy the axioms of Lean's class of values (core Lean has no real numbers);
  that DE run directly on real values makes the same decisions as on their encoding; and a second, independently
  found proof (`k3/simplify/po/potential/NOTES.md`), which the paper only mentions.
- **Reviewed by AI agents**, all separate sessions of the coding assistant (Claude Code) that helped write this work:
  the proof by a referee given only the written proof (`k3/simplify/po/referee/README.md`), the current proofs by a
  referee given only `long.tex`, a longer exposition of the same proofs (`k3/simplify/po/referee/simple/REPORT.md`,
  with its own implementation and tests; `long.tex` was removed from this repository after commit `ffeae05` and is
  in its history), and the Lean statements against the paper by four audits
  (`k3/simplify/po/referee/lean_audit*.md`). The October 2026 revision (an external review, a referee of the
  revision, two prose passes and a final read of the whole text: no error, no gap) is recorded in
  `k3/simplify/po/referee/simple/REVISION.md`. **There has been no human peer review.**
- **Tested**: three earlier implementations and the paper's script, on tens of millions of states and instances,
  without failure.
- **Novelty**: as far as the literature search of `proofs/novelty.md` (25 September 2026) found, no earlier result
  settles this case; the paper's §1 ("What is new") explains why, with an instance that no earlier theorem covers.

## Provenance

This repository was extracted from the research repository
[evanlin23/efx0-three-goods](https://github.com/evanlin23/efx0-three-goods) at commit `31202dc` (merge of PR #93),
which holds the full history, an earlier and longer construction for the same theorem, the claims ledger
(`LEDGER.md`, rows K3S.*), and work on four relevant goods. Of that repository's Lean library, `lean/` keeps only the
paper's formalization (`lean/EFX/K3DE*.lean`) and what it uses (`lean/README.md`, "Contents"). File paths are
otherwise kept as they were there, so the paper's references to files resolve here. The proofs, code, Lean
formalization and the paper were developed with the assistance of AI coding agents (Claude Code).

`lean/EFX/Model.lean` is copied from [evanlin23/mrd-efx](https://github.com/evanlin23/mrd-efx) (see `NOTICE`).
