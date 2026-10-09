# A potential for the k = 3 core: every Pareto-optimal valid state is completable

Branch `proof/k3-simplify`, folder `k3/simplify/po/potential/`. **Status: written proof, not refereed.** Every step
of the proof is also executed, as assertions, by `exchange.py` on every valid state of the test sets of §7, with
0 failures (evidence only). Nothing here changes the ledger or `proofs/`.

## 0. Summary

- **Φ chosen:** Φ = Σ_i u_i with u = (pair 4, a 3, b 2, c 1, nothing 0). Any Φ that strictly increases under Pareto
  improvements among valid states works equally well (Σ values, leximin, …; §6).
- **Theorem PO (proved here).** Every valid state that no valid state Pareto-dominates is completable. In particular
  every valid state that maximises Φ is completable. This is Conjecture PO of `proofs/k3_simple.md` §8 and of
  `explore/reductions/NOTES.md` Idea 3.
- **The proof uses two exchanges, both Pareto improvements:**
  - an *exchange cycle* along a cycle of a digraph A, whose arcs are need arcs and "exposure arcs" o → x, each
    exposure arc labelled by the junk good of x, with pairwise distinct labels (*rainbow*);
  - a *pair chain* (P2 of the reductions notes).
- **The missing "Hall-type lemma" is a six-line walk.** If every free absorber fails, every free agent has at least
  |F| distinct junk labels. A walk that always leaves a free agent by an unused label therefore closes into a
  rainbow cycle before it runs out of labels.
- **The k = 3 theorem follows by peeling** (paper Lemmas `peel` and `R1fail`), then a Φ-maximal valid state, then
  soundness. This route uses no draft order, blocks, leaders, upgrade loop, Lemma T or Theorem B.
- **Single moves are not enough, but one rainbow cycle is.** The brief's instance (n = 6, m = 10) has no D-cycle, no
  pair chain and no cycle with a single exposure arc (the K3S rotation). It is fixed in one step by a rainbow cycle
  with two exposure arcs (§7). Lemma 3 shows that n ≥ 6 and m ≥ 8 for any such state, and an n = 6, m = 8 instance
  needs the rainbow condition itself (§3).

## 1. Definitions

Every agent i values exactly three goods R_i = {a_i, b_i, c_i}, ranked a_i ≻ b_i ≻ c_i, with
v_i(a_i) ≥ v_i(b_i) ≥ v_i(c_i) > 0 and v_i(a_i) < v_i(b_i) + v_i(c_i) (strict balance), and v_i(g) = 0 for g ∉ R_i.
The ranking is consistent with the values, and ties are broken once and for all. Goods valued by nobody may exist.

**States.**
- *Options:* a state gives each agent i a set Y_i, one of ∅, {a_i}, {b_i}, {c_i}, {b_i, c_i}, with the Y_i pairwise
  disjoint.
- U is the set of pair holders. J = M ∖ ∪_i Y_i is the junk. For i ∉ U with Y_i = {g}, write y_i = g.
- *Utility:* u(pair) = 4, u(a) = 3, u(b) = 2, u(c) = 1, u(∅) = 0. Since v(a) < v(b) + v(c), this order agrees with
  i's values (weakly, if a, b, c have ties).
- *Needs:* N_i = ∅ for i ∈ U and for a holder of its top. Otherwise N_i is the set of goods of R_i ranked strictly
  above y_i, or all of R_i if Y_i = ∅. NA = ∪_i N_i.
- *Valid:* every g ∈ NA satisfies Y_j = {g} for some j ∉ U. That j is not the agent that needs g, since nobody needs
  its own good.
- *Free:* F is the set of agents i ∉ U with Y_i = ∅ or y_i ∉ NA.
- *Exposed:* for an agent o, E_o is the set of x ≠ o with x ∉ U, Y_x = {a_x} and {b_x, c_x} ⊆ J ∪ Y_o.
- *Completable:* some o ∈ F ∪ U is a *valid absorber*: every x ∈ E_o has {b_x, c_x} ∩ J ≠ ∅, and some H ⊆ J
  meets every {b_x, c_x} ∩ J (x ∈ E_o) and has |H| ≤ |F ∖ {o}|.
- *Completion:* the goods of H go one each to distinct agents of F ∖ {o}. Every other junk good goes to o, and every
  other agent keeps Y_i.

**Need digraph D.** Its vertices are the agents not in U. It has an arc j → k when y_j ∈ N_k. Every arc joins two
distinct agents, and pair goods are never needed in a valid state, so D sees every need.

- (D1) In a valid state, the sinks of D are exactly the free agents. A non-U agent j has an out-arc iff Y_j = {g}
  with g ∈ NA, iff j ∉ F.
- (D2) A top-holder has no in-arc, because it needs nothing.

**Exchange digraph A.** It has the vertices of D, the arcs of D (*need arcs*), and one *exposure arc* o → x for
every o ∈ F with Y_o ≠ ∅ and every top-holder x ∉ U, x ≠ o, with
{b_x, c_x} = {y_o, h} for some h ∈ J. The arc's **label** is h_x := h, a function of x alone.
- A need arc never enters a top-holder (D2), and an exposure arc always does. So the type of an arc of A is
  determined by its head.
- A cycle of A is **rainbow** if its exposure arcs have pairwise distinct labels.

## 2. The two moves

**(M1) Exchange cycle.** Let C be a rainbow cycle of A. Every agent of C hands its good y to its successor on C.
- A need-arc head k now holds the received good alone.
- An exposure-arc head x, entered from o, now holds the pair {b_x, c_x} = {y_o, h_x}.
- Everyone else keeps its holding.
- A cycle of D (no exposure arc) is the special case M0, the "trading cycle" or "rotation" of the earlier notes.

**(M2) Pair chain.** Let x ∉ U be a top-holder with b_x, c_x ∈ J, and let x = p_0 → p_1 → … → p_ℓ be a path of D
(ℓ ≥ 0) ending at a free agent p_ℓ.
- x takes {b_x, c_x}.
- Each p_t (t ≥ 1) takes y_{p_{t−1}}.
- The old good of p_ℓ, if it had one, becomes junk. For ℓ = 0 this good is a_x.

**Lemma 1.** M1 and M2 turn a valid state S into a valid state S′ in which every agent on the cycle or path is
strictly better off and every other agent is unchanged. Moreover NA′ ⊆ NA and U′ ⊇ U. So S′ Pareto-dominates S, and
Φ(S′) > Φ(S).

*Proof.*
- *Distinct goods.* In M1 each y_v of the cycle moves to exactly one agent, and the labels h_x are distinct junk
  goods (rainbow). In M2, b_x and c_x are junk, and each y_{p_t} (t < ℓ) moves to exactly one agent.
- *Better off.*
  - A need-arc head k receives a good of N_k, which it ranks above its old good (or it held nothing).
  - An exposure-arc head x goes from a to pair (4 > 3).
  - In M2, x goes from a to pair, and each p_t (t ≥ 1) receives a good it needs.
- *NA′ ⊆ NA.* Agents off the cycle or path keep their needs. A head of a need arc now holds a higher-ranked good,
  so its needs shrink. The new pair holders, and the top-holders that receive a pair, need nothing before and after.
- *Validity.* Let g ∈ NA′. Then g ∈ NA, so in S g = y_w for some w ∉ U.
  - If w is not on the cycle or path, w still holds g alone.
  - If w is on it, w's out-arc there is a need arc. It is not an exposure arc, because then w ∈ F, so y_w ∉ NA.
    And w is not p_ℓ of M2, because p_ℓ ∈ F. So g goes to an agent k ∉ U′ that holds g alone.
- *U′ ⊇ U.* Nobody in U is touched. ∎

The validity argument is the one of Theorem B of `paper/k3/long.tex` and of P1–P3 in the reductions notes. What is
new is the exposure arcs and the rainbow condition.

## 3. Theorem PO

**Theorem PO.** A valid state that admits no M1 and no M2 move is completable. Hence every valid state that is
Pareto-optimal among valid states is completable, and so is every maximiser of Φ.

*Proof.* Let S be valid with no M1 or M2 move.

**Step 1 (D is acyclic).** A cycle of D is an M1 move (no labels). So from every vertex of D, following out-arcs
reaches a sink, which is a free agent by (D1).

**Step 2 (no top-holder has both b and c junk).** Otherwise M2 applies with a D-path from x to a free agent
(Step 1).

**Step 3 (an agent holding nothing absorbs).** Suppose some e ∉ U has Y_e = ∅. Then e ∈ F. An x ∈ E_e would have
b_x, c_x ∈ J ∪ ∅ = J, which Step 2 excludes. So E_e = ∅, and e is a valid absorber with H = ∅.

From now on every agent not in U holds exactly one good.

**Step 4 (no free agent).** Suppose F = ∅. Then every vertex of D has an out-arc (D1), so D has a cycle unless it
has no vertex. By Step 1 every agent is in U. Any o ∈ U then has E_o = ∅, since exposed agents are not in U. So o is
a valid absorber. (n ≥ 1.)

**Step 5 (the HitSet test is a count).** Let o ∈ F and x ∈ E_o. Then {b_x, c_x} ⊆ J ∪ {y_o}, and not both goods
are junk (Step 2). So {b_x, c_x} = {y_o, h_x} with h_x ∈ J: o → x is an exposure arc. Each set {b_x, c_x} ∩ J is
the singleton {h_x}, so H meets all of them iff H ⊇ H_o := {h_x : x ∈ E_o}. Hence

  o is a valid absorber  ⇔  |H_o| ≤ |F| − 1.

Suppose, for a contradiction, that **|H_o| ≥ |F| for every o ∈ F**.

**Step 6 (rainbow walk).** We build distinct free agents v_1, v_2, …, distinct labels c_1, c_2, … and top-holders
x_1, x_2, ….
- Let v_1 ∈ F be arbitrary.
- Suppose v_1, …, v_t are distinct and c_1, …, c_{t−1} are distinct. Then t ≤ |F| ≤ |H_{v_t}|, so some
  c_t ∈ H_{v_t} differs from c_1, …, c_{t−1}.
- Let x_t ∈ E_{v_t} have h_{x_t} = c_t, and let P_t be a D-path from x_t to a free agent v_{t+1} (Step 1).
  - If x_t is free, P_t is the trivial path and v_{t+1} = x_t.
  - v_{t+1} = v_t is allowed.
- If v_{t+1} ∈ {v_1, …, v_t}, say v_{t+1} = v_s, stop. Otherwise continue. F is finite, so the walk stops.

Then W = v_s → x_s ⇝ v_{s+1} → x_{s+1} ⇝ ⋯ → x_t ⇝ v_s is a closed walk in A. Its exposure arcs are v_i → x_i
(s ≤ i ≤ t), with the distinct labels c_s, …, c_t. Its other arcs are need arcs.

Write W = (w_0, w_1, …, w_L = w_0) and choose p < q with w_p = w_q and q − p minimal. Then w_p, …, w_{q−1} are
distinct, so they form a cycle C of A whose arcs are arcs of W. A has no loops, so C has length at least 2. The
exposure arcs of C are among those of W, so C is rainbow. This is an M1 move, a contradiction.

So some o ∈ F has |H_o| ≤ |F| − 1 and is a valid absorber.

**Pareto-optimal states.** By Lemma 1 a move gives a valid state that Pareto-dominates S. So a Pareto-optimal valid
state has no move, and the first part applies. A maximiser of Φ is Pareto-optimal. ∎

**Remarks.**
- *Variant (same strength).* Instead of the walk, pick distinct labels h_o ∈ H_o for all o ∈ F at once (greedily:
  each H_o has ≥ |F| labels). Then map each free o to the x with label h_o, and each non-free agent to one of its
  needers. This map on N ∖ U has a cycle, which is rainbow. This is the argument of `po/hall` Lemma 5 (written in
  parallel). Both need Steps 1–3 first: a top-holder with b and c both junk must be removed by M2, and an agent
  holding nothing absorbs. Otherwise the label of x is not unique, and "min hitting set ≥ |F|" no longer gives |F|
  distinct labels (for pairs of junk goods, a hitting set can exceed a matching).
- *Where the count is used.* It is used only in Step 6. "Every free absorber fails" means that each free agent
  has more labels than there are free agents other than itself, which is exactly what a walk needs to avoid reusing
  a label before it revisits a free agent.
- *Previous partial results are special cases.*
  - P1 / S1-cycles: M1 without exposure arcs.
  - P2 / S1: M2.
  - P3: M1 with one exposure arc, which is K3S's rotation.
  - P4 / S3: |F| = 1, where the walk closes at once.
  - S2: Step 3.
- *Nothing else is needed.* The proof needs no upgrade move (K3S step 2), no draft order and no choice of r or k.
  A free agent holding b with c junk is just a free agent.
- *Why rainbow.* Two exposure heads with the same label would both need the same junk good. Cycles of A that are
  not rainbow exist (632 at n = 3, m = 5, `lemma1.py`). The walk never builds one.

**When are exposure-arc cycles with two or more arcs needed?** Call a move *short* if it is a D-cycle, a pair
chain, or an M1 cycle with one exposure arc. The short moves are the moves `up`/`cycle`/`rot` of the matching notes,
up to `up`, which the proof does not need.

**Lemma 3.** Every non-completable valid state with no short move has n ≥ 6 and m ≥ 8. Both bounds are attained.

*Proof.* Run Steps 1–5. Then |F| = k ≥ 2: for k = 1 the walk closes at v_1, which is a short move.
- *Case k = 2,* F = {o_1, o_2}.
  - Each x ∈ E_{o_1} reaches o_2. If it reached o_1, the cycle o_1 → x ⇝ o_1 would be a short move.
  - So x = o_2, or a non-trivial D-path enters o_2. In the second case o_2 is not a top-holder (D2).
  - |E_{o_1}| ≥ |H_{o_1}| ≥ 2, so the second case occurs. Then o_2 is not a top-holder, so o_2 ∉ E_{o_1}. Hence
    E_{o_1} holds at least two non-free top-holders.
  - Symmetrically for E_{o_2}.
  - The sets E_o are disjoint: x ∈ E_o ∩ E_{o′} would give {b_x, c_x} = {y_o, y_{o′}} with no junk good.
  - So n ≥ 2 + 4 = 6.
  - Every agent holds at least one good (Step 3), and |H_{o_1}| ≥ 2 junk goods exist. So m ≥ n + 2 ≥ 8.
- *Case k ≥ 3.*
  - The E_o are disjoint and each has at least k agents.
  - The free agents among them are top-holders, and there are at most k of those.
  - So n ≥ k + (k² − k) = k² ≥ 9, and m ≥ n + k ≥ 12. ∎

Instances attaining the bounds:
- n = 6, m = 10: the brief's instance.
- n = 6, m = 8, with shared labels (`test_exchange.py example`, `gen_tree(2, 1, shared=True)`):
  - Rankings: o_1 (4, 5, 0), o_2 (6, 7, 1), x_1 (4, 1, 2), x_1′ (5, 3, 1), x_2 (6, 0, 2), x_2′ (7, 3, 0).
  - State: o_1 holds 0, o_2 holds 1, the x's hold their tops; junk {2, 3}.
  - Exposure: E_{o_2} = {x_1, x_1′} with labels 2, 3, and E_{o_1} = {x_2, x_2′} with labels 2, 3.
  - Of the four cycles o_2 → x_1^(′) → o_1 → x_2^(′) → o_2, only the two whose two labels differ are rainbow, so
    the rainbow condition is really used here.

## 4. Soundness (re-proved here; = `proofs/k3_simple.md` §3.3 in this setting)

**Lemma 2.** If o is a valid absorber of a valid state S with set H, the completion X is EFX₀, and only X_o can have
more than two goods.

*Proof.*
- *The bundles.*
  - X_o = Y_o ∪ (J ∖ H).
  - X_f = Y_f ∪ {h_f} for each f ∈ F ∖ {o} that receives a good h_f ∈ H.
  - X_i = Y_i for everyone else.
  - Only X_o can have three or more goods.
- *(★) Needed goods stay alone.* Every g ∈ NA is the bundle {g} of some j ∉ U. That j is not free, so j ≠ o and j
  receives nothing from H.

Fix i, j ≠ i and g ∈ X_j, and let T = X_j ∩ R_i. We show v_i(X_j ∖ {g}) ≤ v_i(X_i).
- *i ∈ U.* Then T ⊆ {a_i}, so v_i(X_j ∖ {g}) ≤ v_i(a_i) < v_i(b_i) + v_i(c_i) ≤ v_i(X_i).
- *i ∉ U and T ∩ N_i ≠ ∅.* Then X_j is a singleton by (★), so X_j ∖ {g} = ∅.
- *i ∉ U and T ∩ N_i = ∅.*
  - If Y_i = ∅, then N_i = R_i and T = ∅.
  - Otherwise every good of T is ranked below y_i, since it is not y_i and not in N_i.
    - If |T| ≤ 1, then v_i(X_j ∖ {g}) ≤ v_i(y_i) ≤ v_i(X_i).
    - If |T| = 2, then y_i = a_i and T = {b_i, c_i}. If |X_j| = 2, the bound is v_i(b_i) ≤ v_i(a_i) ≤ v_i(X_i).
    - If |X_j| ≥ 3, then j = o and b_i, c_i ∈ X_o ⊆ Y_o ∪ J, so i ∈ E_o. But H meets {b_i, c_i}, and H ∩ X_o = ∅,
      a contradiction. ∎

The lemma uses only validity, the HitSet condition, strict balance and v(c) ≥ 0. Ties among a, b, c are allowed.

## 5. The k = 3 theorem, and an algorithm

**Theorem (k = 3).** If every agent values at most three goods, an EFX₀ allocation exists, and every agent has
at most two goods except possibly one.

*Proof.* By induction on n. While rule R1 applies to some agent, peel it (`paper/k3/long.tex`, subsection "Peeling": Lemma `peel` with rule R1).
When R1 applies to nobody, every remaining agent values exactly three remaining goods and is strictly balanced
(Lemma `R1fail`).
- *Valid states exist.* Serial dictatorship in any order, each agent taking its favourite remaining good of R_i or
  nothing, is valid: every good an agent ranks above its pick was taken earlier, alone, by an agent that is not a
  pair holder.
- *Finish.* There are finitely many valid states. Take one maximising Φ. It is completable (Theorem PO), and its
  completion is EFX₀ (Lemma 2). ∎

(With one agent, or no goods, the statement is trivial. Peeled agents get at most one good, and in the core only
the absorber's bundle can have more than two goods (Lemma 2), so at most one bundle has more than two goods.)

**Algorithm LS-R** (`exchange.improve`).
1. Start from serial dictatorship.
2. Run the proof of Theorem PO as a procedure: find a D-cycle, else a pair chain, else an absorber (Steps 3–5), else
   the rainbow walk.
3. Apply the move it returns, and repeat.

Each move raises Σu by at least 1 (by at least 2 for M1). Since Σu ≤ 4n, there are at most 4n moves, and each step is
polynomial: cycle detection, path following, and the walk of at most |F| steps. On the test sets it made at most 7
moves (random profiles with n ≤ 8), and at most 5 on cores with n = 6 (§7). It applies D-cycles and pair chains
even when an absorber already works. A lazy variant that tests the absorbers first would move less. It is not simpler to run than K3S, which needs one rotation, but its proof is much shorter.

## 6. Which Φ

Theorem PO needs only that every M1 and M2 move strictly raises Φ. By Lemma 1 these moves are Pareto improvements
with NA′ ⊆ NA and U′ ⊇ U. So these work:

| Φ | covered by the proof | why |
|---|---|---|
| Σu, any weights increasing along nothing < c < b < a < pair (e.g. Σ values, pair = 5) | yes | Pareto-monotone |
| leximin of u | yes | Pareto-monotone |
| Pareto-optimality itself | yes | Theorem PO |
| (−\|NA\|, Σu) lexicographic, i.e. smallest overflow first (K3.SIZE) | yes | moves keep NA′ ⊆ NA |
| (\|U\|, Σu) lexicographic | yes | moves keep U′ ⊇ U |
| −\|NA\| alone | **no** (evidence only, see below) | a move may keep NA unchanged (e.g. an M1 cycle whose need-arc heads' old needs are still needed by others) |
| \|U\| alone | **false** | n = 2, m = 3: rankings (0, 1, 2), (1, 0, 2); no valid state has a pair, and "each holds its b" (0 holds 1, 1 holds 0) maximises \|U\| = 0 but has no free agent and no absorber |
| \|F\| alone | **false** | n = 2, m = 3: both rank (0, 1, 2); agent 0 holds 0, agent 1 holds 1: F = {1}, agent 0 is exposed for 1 with label 2 and no other free agent |

`phi_survey.py` (number of profiles where SOME maximiser is not completable):

| set | profiles | Σu | Σv | leximin | (−\|NA\|, Σu) | (\|U\|, Σu) | −\|NA\| | \|U\| | \|F\| |
|---|---|---|---|---|---|---|---|---|---|
| every profile n = 2, m = 3–6 | 210 | 0 | 0 | 0 | 0 | 0 | 0 | 4 | 40 |
| every profile n = 3, m = 4–7 | 62,676 | 0 | 0 | 0 | 0 | 0 | 0 | 2,068 | 510 |
| every profile n = 4, m = 5 | 216,000 | 0 | 0 | 0 | 0 | 0 | 0 | 54,948 | 104 |
| random profiles, 2 ≤ n ≤ 7, n + 1 ≤ m ≤ 2n + 3 | 5,000 | 0 | 0 | 0 | 0 | 0 | 0 | 235 | 204 |

So **−|NA| alone** (fewest goods needed alone, i.e. smallest overflow when nobody holds nothing) has only
completable maximisers on every test, but the proof does not cover it: its maximisers need not be Pareto-optimal,
and the moves of the proof keep |NA| when they start from a −|NA|-maximiser. A proof would need a move that strictly
shrinks NA in every non-completable state (open; no counterexample known).

**Verdict.** Σu is the cleanest. It needs no case analysis on which exchange improves Φ, and every exchange used is a
Pareto improvement. Non-Pareto Φ (exchanges that hurt an agent) were not needed.

## 7. Evidence (`test_exchange.py`, `lemma1.py`, `phi_survey.py`; logs in `logs/`)

All of this is evidence for the written proof. Values are 4, 3, 2, and goods nobody ranks are worthless. "Every
profile" fixes agent 0's ranking as 0 ≻ 1 ≻ 2 (`test_k3s.gen_small`).

**The proof, executed** (`test_exchange.py`, logs `small.log`, `small_4_6.log`, `random_cores.log`). For every valid
state of every profile, `certify` runs Steps 1–6.
- If it returns an absorber, the HitSet condition is checked and the completion is checked EFX₀ by the raw
  definition (`k3s.efx0`).
- If it returns a move, the new state is checked valid and Pareto-dominating, with NA′ ⊆ NA.
- Brute-force completability (`completable_bf`) is computed independently. Every non-completable state must get a
  move, and every Pareto-optimal state must get an absorber.
- Algorithm LS-R is run from serial dictatorship, and its output is checked EFX₀.

0 assertion failures in all sets:

| set | profiles | valid states | not completable | fixed by D-cycle / pair chain / rainbow cycle | Pareto-optimal (all completable) | max moves of LS-R | rainbow cycles used, by number of exposure arcs |
|---|---|---|---|---|---|---|---|
| every profile n=2 m=3 | 6 | 13 | 5 | 1 / 0 / 4 | 8 | 1 | 1: 4 |
| every profile n=2 m=4 | 24 | 60 | 14 | 2 / 4 / 8 | 32 | 1 | 1: 8 |
| every profile n=2 m=5 | 60 | 165 | 27 | 3 / 12 / 12 | 82 | 2 | 1: 12 |
| every profile n=2 m=6 | 120 | 352 | 44 | 4 / 24 / 16 | 164 | 2 | 1: 16 |
| every profile n=3 m=4 | 576 | 2112 | 576 | 360 / 0 / 216 | 966 | 1 | 1: 216 |
| every profile n=3 m=5 | 3600 | 12698 | 2060 | 872 / 444 / 744 | 5578 | 2 | 1: 960 |
| every profile n=3 m=6 | 14400 | 53880 | 5464 | 1720 / 2088 / 1656 | 22670 | 2 | 1: 2808 |
| every profile n=3 m=7 | 44100 | 177588 | 11988 | 2988 / 5976 / 3024 | 70794 | 3 | 1: 6624 |
| every profile n=4 m=5 | 216000 | 1446882 | 248850 | 162018 / 48432 / 38400 | 666288 | 1 | 1: 38400 |
| every profile n=4 m=6 | 1728000 | 9827184 | 1308912 | 678768 / 418176 / 211968 | 4010064 | 2 | 1: 278784 |
| random K=100000 seed=2 n<=8 | 100000 | 1552373 | 45192 | 21373 / 15733 / 8086 | 466453 | 7 | 1: 10765 |
| cores n in [5,5], 200 per core | 61400 | 652312 | 39000 | 26317 / 9463 / 3220 | 267803 | 4 | 1: 4204 |
| cores n in [6,6], 30 per core | 96210 | 1772519 | 54891 | 39390 / 12500 / 3001 | 701989 | 5 | 1: 3971, 2: 1 |

Total: about 15.5 million valid states; every Pareto-optimal state got an absorber.

**Lemma 1 on every move** (`lemma1.py`, log `lemma1.log`). Every simple cycle of A and every pair chain was
enumerated on every valid state. Every rainbow cycle and every pair chain gave a valid state with every touched agent
strictly better off: 0 failures. Rainbow cycles with up to 4 exposure arcs occurred. Non-rainbow cycles occur too
(e.g. 632 at n = 3, m = 5, 33,360 at n = 4, m = 5). No non-completable state without a short move was found at
n ≤ 4 or in 3,000 random profiles with n ≤ 7, as Lemma 3 predicts for n ≤ 5.

| set | valid states | rainbow cycles checked (by number of exposure arcs 0 / 1 / 2 / 3 / 4) | pair chains checked | non-rainbow cycles |
|---|---|---|---|---|
| every profile n = 2, m = 5–6 | 517 | 7 / 28 / 20 / 0 / 0 | 264 | 8 |
| every profile n = 3, m = 5–7 | 244,166 | 14,520 / 26,616 / 9,936 / 480 / 0 | 113,562 | 5,544 |
| every profile n = 4, m = 5 | 1,446,882 | 689,640 / 218,400 / 0 / 0 / 0 | 93,600 | 33,360 |
| 3,000 random profiles, n ≤ 7 | 31,361 | 6,930 / 3,816 / 713 / 50 / 3 | 18,419 | 482 |

**Instances** (`test_exchange.py example`, log `example.log`).
- The brief's state (n = 6, m = 10) is not completable. A has no rainbow cycle with fewer than 2 exposure arcs and
  no pair chain. `certify` returns the rainbow cycle o_1 → x_1 → o_2 → x_2 → o_1, and the new state is
  x_1, x_2 holding pairs and everyone else holding their tops. It is completable, and is the brief's dominating
  state.
- Family `gen_tree(k, d, shared)`: k free agents, each needing the two roots of a binary need tree of depth d whose
  leaves are exposed for the previous free agent, with labels private or shared (a pool of k).
  - Every such state is non-completable.
  - Every rainbow cycle of A has exactly k exposure arcs, so the improving exchange must upgrade k agents at once.
    No bounded move size suffices.
  - The walk finds one cycle, after which an absorber works. Checked for (k, d) = (2, 1), (3, 2), (4, 2), (5, 3), up
    to n = 75.

## 8. Status of each claim, and what is missing

| claim | status |
|---|---|
| Lemma 1 (M1, M2 are valid Pareto improvements, NA′ ⊆ NA, U′ ⊇ U) | proved here (written); checked on every move of the sets of §7 |
| Theorem PO (no move ⇒ completable; Pareto-optimal ⇒ completable; Φ-max ⇒ completable) | proved here (written); every step asserted on about 15.5 million valid states (§7) |
| Lemma 2 (soundness) | proved here (written; = `proofs/k3_simple.md` §3.3); raw EFX₀ check of every completion in §7 |
| k = 3 theorem via peel + Φ-max + Lemma 2 | proved here (written), using the paper's Lemmas `peel` and `R1fail` |
| Lemma 3 (exposure-arc cycles of length ≥ 2 are needed only for n ≥ 6, m ≥ 8) | proved here (written); bounds attained |
| Φ = −\|NA\| alone: every maximiser completable | **open**, 0 counterexamples (§6) |
| Φ = \|U\| alone, \|F\| alone | refuted, n = 2, m = 3 (§6) |

What is missing:
- *A referee of §§2–5.* The proof is short. The points to check are the validity argument of Lemma 1 (the same as
  Theorem B's) and Step 6.
- *A Lean formalisation.* It would need options, D and A on top of `lean/EFX/Model.lean`, then Lemma 1, the walk
  (finite, by strong induction on |F| minus the number of visited free agents) and Lemma 2. It would replace blocks,
  leaders, Lemma T and Theorem B.
- *The relation to K3S.* Theorem PO does not prove that K3S's single rotation suffices (that is still Theorem B). It
  proves a different algorithm, LS-R (§5), and the existence theorem. K3S's rotation is the special case of M1 with
  one exposure arc (r → k ⇝ r), or M2 when b_k and c_k are both junk.
- *The ledger.* If the proof survives refereeing, ledger row K3S.PO (Conjecture PO) can become PROVED with this note
  as the artifact. The ledger was not edited here, as the brief requires.

## Files

- `exchange.py`: states, need digraph, `certify` (the proof of Theorem PO as a procedure, all claims asserted),
  `check_absorber` (HitSet condition plus a raw EFX₀ check of the completion), `improve` (algorithm LS-R),
  `completable_bf` (the definition by brute force).
- `test_exchange.py`: the tests of §7. The `example` mode runs the brief's n = 6 instance and families of
  generalisations (k free agents, binary need trees, shared junk labels).
- `lemma1.py`: every rainbow cycle of A and every pair chain, on every valid state, is a valid Pareto improvement.
  It also finds states where only multi-arc exchanges help.
- `phi_survey.py`: optima of several Φ, and whether they are completable.
