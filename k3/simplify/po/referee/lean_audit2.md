# Second faithfulness audit: the rest of the Lean formalization of paper/k3-simple

An independent referee session (a separate AI agent of the coding assistant, Claude Code, read-only, not the author of
the files) compared `lean/EFX/K3DEPrelim.lean`, `K3DELimits.lean`, `K3DEShort.lean`, `K3DEShortExamples.lean`,
`K3DERings.lean` and `K3DEReal.lean` (branch `proof/k3-simplify`, at commit `4e849fe`) with `paper/k3-simple/long.tex`
§3, §6.2–§6.4 and §7, the ledger rows K3S.PRELIM.LEAN, K3S.LIMITS, K3S.SHORT, K3S.EX.LEAN, K3S.RINGS, K3S.REAL.LEAN,
and the new paragraphs of long.tex §8. Scope: definitions and statements, not proofs (the build passes
`lean/check.sh`). Below: its findings, condensed, and what was done about each.

**Verdict.** No BLOCKING issue. The definitions match the paper's notions (threat, safe, alone, G_y, the cases of
Lemma L5, need arcs, short moves, |F|, the exchange digraph and its cycles, the ring family, which matches `gen_tree`
of `k3/simplify/po/potential/test_exchange.py` up to an explicit renaming). All concrete rankings match the paper's
tables. The hypotheses are the paper's or weaker, none is vacuous (each has a witnessing instance), and `¬ShortMove`
is equivalent to the paper's "no short move applies" (a walk of need arcs from an exposed agent back to its free
agent is a cycle of D⁺ with one exposure arc once D is acyclic, and a need cycle is itself a short move), so
`EFX.DE.prop_short` is not weakened.

**MINOR findings, and their resolution.**
1. long.tex §7 said Lemma L5 is machine-checked "also for ordered values"; `safe_iff_cases` is over ℕ (the ordered
   forms are those of Proposition limits). Resolved: the sentence now says "Lemma L5 (over the natural numbers), and
   both parts … also for ordered values".
2. "The facts of Section 6.3" went beyond what Lean proved (the Figure's caption on the other three cycles, the
   completion paragraph's intermediate facts, the numbers 5 and 14 → 20). Resolved by proving them:
   `lean/EFX/K3DERemarks.lean` (`w_cycles`, `w_after`, `w_step`, `w_totals`, `w_detail`).
3. Ledger K3S.SHORT said "m counts distinct goods"; the bound is on `goods.length`. Resolved: reworded.
4. long.tex §1 status said "as are the other results of this paper"; DE on ordered values is the surrogate variant,
   and Example EFX-but-not-EFX₀ and the remark on protecting goods were not in Lean. Resolved: both are now proved
   (`EFX.DE.Remarks.efx_not_efx0`, `pg_undominated`, `pg_only_g2`), and the sentence points to the listed
   exceptions.
5. Cosmetic: `Rings.NeedArc` duplicates `DE.NeedArc`; the "iff k ≤ 2^d" form appears only by instantiating
   `no_free_absorber_iff`. Kept as is.

Files written after this audit (`K3DERemarks.lean`, `K3DECost*.lean`) are audited separately
(`k3/simplify/po/referee/lean_audit3.md`).
