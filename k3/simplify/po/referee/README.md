# Independent referee of the Improvement Lemma (`../hall/NOTES.md`)

The referee wrote `ref.py` from the text of `../hall/NOTES.md` alone, before reading `../hall/hall.py`. It chooses at
random wherever the proof leaves a choice, and asserts at every step:
- F1, F2, Lemma 0 (a) and (b);
- Lemmas 2 and 3, against a brute-force hitting set;
- Lemma 5's claims: each exposed agent belongs to at most one free o; the greedy representatives exist and the x_o
  are distinct; σ has no fixed point and maps into non-pair agents; every cycle agent holds a single good and is
  assigned once; every cycle agent strictly improves; the new pair holders are exactly the agents entered by an
  exposure arc;
- at most 4n steps, and EFX₀ of the output by the raw definition with values 4, 3, 2.

Verdict: no blocking issue, every lemma correct; four presentation fixes, applied in `../hall/NOTES.md`.

Results: 0 failures and 0 assert violations.

| Test set | Size | Log |
|---|---|---|
| algorithm, every ranking profile with n = 2 (m = 3..6), n = 3 (m = 4..7), n = 4 (m = 5..6) | 2,006,886 profiles | `small.log` |
| algorithm, core samples with n = 5 | 30,700 profiles | `cores.log` |
| algorithm, random with n ≤ 9 | 200,000 profiles | `random.log` |
| `improve()` on every valid state with n ≤ 3, plus samples with n = 4 | 273,805 states | `all_states.log` |
| soundness on every completion with n ≤ 3 | 1,130,775 completions | `all_states.log` |
| rejection-sampled random states (including need cycles) | 65,816 states × 3 seeds | `rstates.log` |
| rings with k = 2..9 free agents, n ≤ 304 | 3,000 instances | `ring.log` |
| peeling by R1, then the algorithm, real values | 300,000 instances | `pipeline*.log` |

The scripts were run from the session scratchpad. Their import paths may need adjusting to run from this folder.
