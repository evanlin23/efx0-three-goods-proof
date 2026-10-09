# Faithfulness audit of the Lean formalization of the short proof (ledger K3S.PO.LEAN)

An independent referee session (a separate AI agent of the coding assistant, Claude Code, read-only, not the author of
the Lean files) compared `lean/EFX/K3DE.lean`, `K3DEImprove.lean`, `K3DEAlgo.lean`, `K3DEExamples.lean` (commit
`31173e2` of branch `proof/k3-simplify`) with `paper/k3-simple/long.tex` §3–§6. Its scope was the definitions and
statements, not the proofs (the build already passes `lean/check.sh`: no `sorry`, standard axioms only, kernel replay).
Below: its findings, condensed, and what was done about each.

**Verdict.** No BLOCKING issue. The definitions match the paper's definitions of states, validity, free agents,
exposure, absorbers and the completion; `EFX.LB.Valid` is equivalent to the paper's validity under `WF` (three
distinct goods per agent), which every relevant theorem assumes. Each headline theorem (`EFX.DE.improvement`,
`completable_of_undominated`, `soundness`, `absorber_iff`, `draft_valid`, `loop_spec`, `run_sound`,
`deSpec_correct`) states the paper's result with hypotheses no stronger than the paper's (Lean's are often weaker: the
Improvement Lemma needs no values; soundness holds for balanced valuations with ties); none is vacuous (`o ∈ agents` is
required of an absorber; consistent valuations exist and are used by `deStage_sound`; the examples evaluate DE in the
kernel). `deSpec` is the paper's DE with its free choices fixed (first x, first out-neighbour, greedy representatives
over F in index order, the cycle through σⁿ(s)); `deSpec_correct` is the right formal reading of existence, one large
bundle and the 4n bound, over ℕ (`EFX.Inst.EFX0` is strong EFX₀; `Alloc` is total).

**MINOR findings, and their resolution.**
1. `improvement` concludes only "some valid state dominates"; "obtained by one need cycle, pair chain or exchange
   cycle" was visible only from the definition of `step`. Resolved: new theorem `EFX.DE.step_next_cycle` (every move of
   `step` is `exchY`/`exchUp` along an `EFX.DE.Cycle`), with `EFX.DE.cycleStep_cycle`; `step_next` is now derived from
   it.
2. The goods of `H` are handed out in the order of `Hset`, not by good index; the paper's "in index order" is
   ambiguous. Resolved: listed as a choice in the module doc of `K3DEImprove.lean`.
3. Values are ℕ only; "at most n peeling steps" is structural (fuel = n), not a stated theorem. Kept, stated in the
   ledger row and the papers ("over the natural numbers").
4. `long.tex` open problem (5) still asked for a Lean proof of the Improvement Lemma. Resolved: replaced by the
   formalization of the running time and of real values.
5. `long.tex` said the files "formalize Sections 4–6", but §6 also holds Proposition "short moves" and the running
   time. Resolved: now "Sections 4 and 5, Algorithm DE and Theorem DE is correct".
6. `long.tex` said the cycle passes through σⁿ(s) "for the first agent s outside U"; for a pair chain, s is the agent
   x at which (P) fails. Resolved.
7. Table row "Lemmas facts–cycle: Lean": Lemmas P(a), noF and cycle have no standalone theorem in the paper's form.
   Resolved: the table says they are inside the theorems on DE's step. (F1) is formalized in union form
   (`EFX.DE.na_of_util`).
8. The sentence "faithfulness not reviewed independently" can be updated after this audit. Resolved in both papers and
   `paper/k3-simple/README.md`.

The module docs, the ledger row and the examples' outputs (the worked example checked by hand against §6.3) were found
accurate.
