# The Improvement Lemma (Conjecture PO) for k = 3: a proof

Branch `proof/k3-simplify`, workstream "po hall". Status: **written proof, refereed once with no error (the
referee's four presentation fixes are applied below), not machine-checked.** An independent proof of the same theorem
is in `../potential/NOTES.md`. The referee's own implementation and logs are in `../referee/`.
Every lemma below was tested on every state of small profiles and on random larger ones (§5); no failure.

> **Theorem (Improvement Lemma).** If a valid state is not completable, some valid state Pareto-dominates it.
> Equivalently, every Pareto-optimal valid state is completable; in fact with a *free* absorber, unless every agent
> holds its pair.

The proof is constructive: the dominating state is one of three exchanges (a need path started by a top holder whose
b and c are both junk, a cycle of the need digraph, or a cycle of an *exchange digraph* that mixes need arcs with
"x takes {b_x, c_x}" arcs). The Hall-type step that the earlier notes asked for turns out to be trivial: when every
free absorber fails, each free agent has at least |F| distinct protecting goods, so distinct representatives exist
greedily, and a functional digraph always has a cycle.

## 1. Definitions (as in the brief)

Agents have goods a_i ≻ b_i ≻ c_i. A *state* gives each agent i a holding Y_i ∈ {∅, {a_i}, {b_i}, {c_i}, {b_i, c_i}},
pairwise disjoint. U = {i : Y_i = {b_i, c_i}} (pair holders). For i ∉ U with Y_i = {g} write y_i = g. Utility order
pair ≻ a ≻ b ≻ c ≻ ∅ (u = 4, 3, 2, 1, 0). J = goods nobody holds (junk).

- *Needs* N_i: for i ∉ U holding y_i, the goods i ranks above y_i; for i holding nothing, {a_i, b_i, c_i}; for i ∈ U,
  ∅. NA = ⋃ N_i.
- *Valid*: every g ∈ NA is y_j for some j ∉ U (held alone by a non-U agent).
- *Free* agents F: i ∉ U with Y_i = ∅ or y_i ∉ NA.
- *Need digraph* D: arc j → j′ when j ∉ U holds y_j, j′ ∉ U, and y_j ∈ N_{j′}.
- *Exposed for o*: x ≠ o, x ∉ U, Y_x = {a_x}, and b_x, c_x ∈ J ∪ Y_o. E_o = the set of these agents.
- *o is a valid absorber* (o ∈ F ∪ U): every x ∈ E_o has J ∩ {b_x, c_x} ≠ ∅, and some H ⊆ J meeting every
  J ∩ {b_x, c_x} (x ∈ E_o) has |H| ≤ |F ∖ {o}|. *Completable*: some agent is a valid absorber.
- *The completion* with a valid absorber o and its set H: every good of H goes to a different free agent other than
  o; o receives Y_o ∪ (J ∖ H); every other agent keeps Y_i. Owner constraint (OC): no x ≠ o, x ∉ U, holding only
  a_x, finds both b_x and c_x in X_o. This holds: if b_x, c_x ∈ X_o = Y_o ∪ (J ∖ H), then b_x, c_x ∈ J ∪ Y_o, so
  x ∈ E_o and H holds one of them, which is then not in X_o. So the completion is EFX₀ by soundness
  (`proofs/k3s_standalone.md` §5, Theorem S). That theorem needs only the validity conditions (V1), (V2), which are
  equivalent to "valid" here, and that agents in U are balanced (every core agent is). Nothing in it depends on the
  draft.
- Y′ *Pareto-dominates* Y: u_i(Y′) ≥ u_i(Y) for all i, with strict inequality for some i.

## 2. Basic facts

**(F1) Needs shrink when an agent improves.** If u_i(Y′) ≥ u_i(Y) then N′_i ⊆ N_i. *Proof.* If Y′_i is i's pair,
N′_i = ∅. If Y′_i = {g′} then Y_i = {g} with g′ ranked at or above g, or Y_i = ∅; the goods ranked above g′ are among
those ranked above g, and N_i = {a_i, b_i, c_i} when Y_i = ∅. If Y′_i = ∅ then Y_i = ∅. ∎

**(F2) Out-arcs.** In a valid state, every non-free agent j ∉ U has an out-arc in D. *Proof.* j holds y_j ∈ NA, so
y_j ∈ N_{j′} for some j′; j′ ∉ U since pair holders need nothing, and j′ ≠ j since an agent does not need its own
good. ∎

**Lemma 0 (transfer).** Let Y be valid and Y′ a state (disjoint holdings) with (a) u_i(Y′) ≥ u_i(Y) for every i and
strict for some i, and (b) every g ∈ NA is, in Y′, the only good of some agent ∉ U′. Then Y′ is valid and
Pareto-dominates Y.
*Proof.* By (a) and (F1), NA′ ⊆ NA; by (b) every good of NA′ is held alone by a non-U′ agent. ∎

All three exchanges below are checked through Lemma 0. In each, every agent that moves receives either a good it
needed (held alone afterwards) or its pair, and passes its old good to the next agent of a path or cycle.

## 3. The proof

**Lemma 1 (P1, P2).** Let Y be valid.
(a) If D has a cycle, Y is dominated.
(b) If some x ∉ U holds a_x with b_x, c_x ∈ J, Y is dominated.

*Proof.* (a) Let j_0 → j_1 → … → j_{k−1} → j_0 be a cycle (k ≥ 2, distinct agents, all ∉ U and holding single
goods). Y′: each j_{t+1} takes y_{j_t} (indices mod k). The goods are permuted, so holdings are disjoint; each j_{t+1}
receives a good it needs, so it strictly improves; others are unchanged. (b) of Lemma 0: a needed good held by an
agent off the cycle stays put; one held by j_t moves to j_{t+1}, which holds it alone and is not in U′ = U.
(b) Walk j_0 = x, and while j_t has an out-arc in D, let j_{t+1} be an out-neighbour. If the walk repeats an agent,
D has a cycle: use (a). Otherwise it stops at j_k (k ≥ 0) with no out-arc. Y′: x takes {b_x, c_x}; for 1 ≤ t ≤ k,
j_t takes y_{j_{t−1}} (y_{j_0} = a_x); the old good of j_k (if any) becomes junk. Holdings are disjoint (b_x, c_x were
junk; the other goods shift along the path). x goes from a to its pair; each j_t (t ≥ 1) receives a good it needs.
Lemma 0 (b): b_x, c_x ∈ J are not in NA (validity); a needed good of an agent off the path stays put; y_{j_t} (t < k)
moves to j_{t+1} ∉ U′ = U ∪ {x}, alone; and y_{j_k} ∉ NA by (F2), since j_k ∉ U (j_0 = x ∉ U; for k ≥ 1, j_k needed
something) and has no out-arc. ∎

From now on Y is valid and satisfies (P2): no x ∉ U holding a_x has b_x, c_x ∈ J. (Acyclicity of D is not needed
below; Lemmas 4 and 5 find their own cycles.)

**Lemma 2.** If o ∈ F holds nothing, then E_o = ∅, so o is a valid absorber (H = ∅).
*Proof.* x ∈ E_o would have b_x, c_x ∈ J ∪ ∅, against (P2). ∎

**Lemma 3.** Let o ∈ F hold y_o = g. Every x ∈ E_o has {b_x, c_x} = {g, h_x} with h_x ∈ J. Hence, with
H_o = {h_x : x ∈ E_o}, o is a valid absorber iff |H_o| ≤ |F| − 1.
*Proof.* b_x, c_x ∈ J ∪ {g} and not both in J (P2), so one of them is g and the other, h_x, is junk. The sets to
hit are the singletons {h_x}, so the smallest hitting set is H_o itself, and |F ∖ {o}| = |F| − 1. ∎

**Lemma 4 (F = ∅).** If F = ∅, then either every agent is in U, and then any agent is a valid absorber (nobody is
exposed, since exposed agents are ∉ U; H = ∅), or D has a cycle.
*Proof.* Every agent ∉ U is non-free, so it has an out-arc to an agent ∉ U (F2); a finite digraph with minimum
out-degree ≥ 1 has a cycle. ∎

**Lemma 5 (exchange cycle; the Hall step).** Suppose F ≠ ∅, no free agent holds nothing, and |H_o| ≥ |F| for every
o ∈ F. Then Y is dominated.

*Proof.* *Distinct representatives.* List F = {o_1, …, o_f} and pick h_{o_i} ∈ H_{o_i} ∖ {h_{o_1}, …, h_{o_{i−1}}};
this is possible because |H_{o_i}| ≥ f > i − 1. (This is Hall's condition: any s of the sets have a union of size
≥ f ≥ s.) Let x_o ∈ E_o be an agent with h_{x_o} = h_o. Here h_x is well defined: under (P2), an agent x lies in
E_o for at most one free o holding a good. If x ∈ E_o ∩ E_{o′} with o ≠ o′, then {b_x, c_x} = {y_o, y_{o′}} by
Lemma 3, so neither good is junk, against (P2). The x_o are then distinct, although the argument below does not need
this: on a cycle of a functional digraph every vertex has exactly one predecessor.

*Exchange digraph.* Define σ on the agents ∉ U: σ(o) = x_o for o ∈ F, and σ(j) = an out-neighbour of j in D for
j ∉ U ∪ F (it exists by F2). Then σ(j) ∉ U and σ(j) ≠ j (x_o ∉ U, x_o ≠ o by definition of exposure; D has no loops),
and the set of agents ∉ U is non-empty (F ≠ ∅). So the functional digraph j → σ(j) has a cycle
C = (w_0, w_1, …, w_{k−1}), σ(w_t) = w_{t+1} (indices mod k), k ≥ 2, the w_t distinct. Every w_t holds a single good
(free agents hold one by hypothesis, non-free agents ∉ U hold a needed good).

*The exchange* Y′, agents off C unchanged:
- if w_t ∈ F, then w_{t+1} = x_{w_t} takes {y_{w_t}, h_{w_t}}, which is {b, c} of w_{t+1} by Lemma 3: it goes from its
  top to its pair;
- if w_t ∉ F, then w_{t+1} takes y_{w_t}, a good it needs, alone: it strictly improves.

Each w_{t+1} has exactly one predecessor on C, so Y′ is well defined. Holdings are disjoint: each y_{w_t} goes to
w_{t+1} only, and the goods h_{w_t} (w_t ∈ F ∩ C) are junk and pairwise distinct (distinct representatives). Every
agent of C strictly improves, the others are unchanged: Lemma 0 (a). Lemma 0 (b): a needed good g ∈ NA is y_j for
some j ∉ U. If j ∉ C it stays with j. If j = w_t ∈ C, then w_t ∉ F (its good is needed), so w_{t+1} took g alone; and
w_{t+1} ∉ U′, because the new pair holders are exactly the agents of C entered from a free agent, and w_{t+1} was
entered from w_t ∉ F. ∎

**Proof of the Theorem.** Let Y be valid and not completable. If (P2) fails, Lemma 1 (b). If F = ∅, Lemma 4 gives
a cycle of D (all agents in U would make Y completable), and Lemma 1 (a) dominates Y. Otherwise no o ∈ F is a valid absorber: by Lemma 2 no free agent
holds nothing, and by Lemma 3 |H_o| ≥ |F| for every o ∈ F. Lemma 5. ∎

The proof never uses the pair holders as absorbers, except when everybody holds a pair; so a Pareto-optimal valid
state is completable with a free absorber (or all agents hold pairs). It also never uses strict balance: that enters
only through the utility order (pair ≻ a) and through soundness (`proofs/k3_simple.md` §3.3–3.4).

**Corollary (algorithm).** Start from serial dictatorship (each agent in turn takes its best remaining good, or
nothing; this state is valid: the goods an agent ranks above its holding were taken earlier, alone, by agents
holding single goods). Repeat: if (P2) fails, apply Lemma 1 (b); else if every agent holds a pair, or some free o holds
nothing or has |H_o| ≤ |F| − 1, stop and complete with that o (with H = H_o); else apply Lemma 4 (if F = ∅) or
Lemma 5. Each step raises Σ u_i ≤ 4n by at least 1, so there are at most 4n steps, each polynomial (no hitting-set search is needed:
under (P2) the protecting goods of a free absorber are forced). The output is EFX₀ by soundness.

## 4. How the n = 6 instance of the brief is handled

Goods 0–9, rankings x1 (0, 4, 6), x1′ (1, 4, 7), x2 (2, 5, 8), x2′ (3, 5, 9), o1 (2, 3, 4), o2 (0, 1, 5); state: the
x's hold their tops, o1 holds 4, o2 holds 5. F = {o1, o2}, E_{o1} = {x1, x1′} with H_{o1} = {6, 7}, E_{o2} =
{x2, x2′} with H_{o2} = {8, 9}: both have |H| = 2 = |F|, so Lemma 5 applies. Greedy representatives h_{o1} = 6
(x_{o1} = x1), h_{o2} = 8 (x_{o2} = x2). σ: o1 → x1 → o2 (o2 needs 0) → x2 → o1 (o1 needs 2). The exchange: x1 takes
{4, 6}, o2 takes 0, x2 takes {5, 8}, o1 takes 2: two upgrades in one cycle, as the brief predicted
(`python3 hall.py example`). The resulting state is valid and completable.

## 5. Tests (`hall.py`, `po_check.py`, `targeted.py`; one process; logs in `logs/`)

`hall.py` re-implements the definitions of §1 (`selftest`: it agrees with `explore/matching/common.py`, completion
mode `k3s`, on validity, F, NA, J, exposure and completability for all 15,048 valid states with n = 2, m ≤ 5 and
n = 3, m ≤ 5). `improve()` is the proof of §3 as code: every case the proof excludes is an `assert`, and every output
is re-checked for validity and Pareto dominance. Every completion of a completable state is re-checked against the
raw EFX₀ definition (values 4, 3, 2). "Profiles": agent 0 ranks 0 ≻ 1 ≻ 2, all rankings of the others.

**Theorem, constructively: `improve()` on every valid, non-completable state** (`logs/small.log`,
`logs/random_algo_cores.log`):

| set | valid states | not completable = improved | P2-path | D-cycle | A-cycle (exposure arcs used) |
|---|---|---|---|---|---|
| every state, every profile n = 2, m = 3..6 | 590 | 90 | 40 | 10 | 40 (1) |
| every state, every profile n = 3, m = 4 | 2,112 | 576 | 0 | 360 | 216 (1) |
| every state, every profile n = 3, m = 5 | 12,698 | 2,060 | 444 | 872 | 744 (1) |
| every state, every profile n = 3, m = 6 | 53,880 | 5,464 | 2,088 | 1,720 | 1,656 (1) |
| every state, every profile n = 3, m = 7 | 177,588 | 11,988 | 5,976 | 2,988 | 3,024 (1) |
| every state, every profile n = 4, m = 5 (216,000 profiles) | 1,446,882 | 248,850 | 51,264 | 151,706 | 45,880 (1) |
| 3,000 random profiles n ≤ 8 (all states if n ≤ 4, else 300 sampled valid states) | 30,022 | 1,029 | 249 | 520 | 260 (1) |
| cores n = 5, 50 random profiles per core, 60 sampled valid states each | 87,891 | 1,188 | 8,166* | 0* | 274 (1)* |
| cores n = 6, 3 random profiles per core, 60 sampled valid states each | 65,571 | 207 | 4,866* | 0* | 35 (1)* |
| `targeted.py`: rings of k free agents over need trees of depth d, (k, d) ∈ {(2,1), (2,2), (3,2), (4,2), (3,3), (5,3), (8,3)}, 30 relabellings each, n up to 120 | 210 | 210 | 0 | 0 | 210 (exactly k) |

\* For the cores the move counts also include the steps of the Corollary's algorithm run on the same profiles.

No assert fired, every output was valid and dominating, and the completion built for each completable state (one per
state) was EFX₀. *Caveat (referee):* the generator `random_states` cannot produce states whose need digraph has a
cycle, because each agent may only need goods already held when it is placed. So the D-cycle counts "0\*" for the
cores hold by construction. The referee's rejection-sampled random states (`../referee/`) do include D-cycles. The 2,060 non-completable states
at n = 3, m = 5 are the same count as `explore/reductions/power.log`. (D-cycle counts include functional cycles of
Lemma 5 that happen to use no exposure arc.) In random data the exchange cycle never needs more than one exposure
arc (it is then a K3S-type rotation); on the ring constructions (the brief's instance is k = 2, d = 1) Lemma 5's
cycle runs through all k exposure arcs. (For k = 2, d = 1 the brief shows that every dominating state upgrades two
agents; that larger rings need k upgrades is plausible but not checked.)

**Pareto-optimal states** (`po_check.py`, `logs/po_check.log`; all valid states enumerated, Pareto filter): every PO
valid state is completable, completable with a free absorber (or all pairs), and satisfies P1 and P2:

| set | PO states | failures (thm / free / P1 / P2) | Q1 fails (HitSet needed) |
|---|---|---|---|
| every profile n = 2, m = 3..6 | 286 | 0 | 16 |
| every profile n = 3, m = 4..7 | 100,008 | 0 | 2,440 |
| every profile n = 4, m = 5 | 666,288 | 0 | 7,200 |
| 3,000 random profiles n ≤ 5 | 7,666 | 0 | 221 |

**Algorithm of the Corollary** (serial dictatorship, then `improve()` until the stop rule; raw EFX₀ check of the
output): 20,000 random profiles with n ≤ 10, m ≤ 2n + 3 (11,614 needed at least one step, at most 7 steps;
19,193 P2-paths, 473 exchange cycles); 15,350 core profiles n = 5 and 9,621 core profiles n = 6 (at most 4 steps).
No failure.

## 6. Remarks

- **K3S's rotation is a special case.** k (exposed for r) takes {b_k, c_k}, a_k travels along a need chain that
  ends at r: this is an exchange cycle r → k → … → r with one exposure arc (or, when b_k, c_k are both junk, the
  path of Lemma 1 (b)). Lemma 5 is the same move with several exposure arcs, chosen through distinct protecting goods;
  that is what the brief's instance needs (each of its dominating states upgrades two agents), and why the
  single-move "stuck" version (Conjecture ST) is false while the theorem holds.
- **Where the counting is used.** Only to get distinct representatives: |H_o| ≥ |F| for all o ∈ F makes the greedy
  choice possible. A weaker failure (some |H_o| < |F|) is exactly a working free absorber (Lemma 3). So the dichotomy
  is sharp: either a free absorber works or one exposure arc per free agent can be chosen with distinct junk goods.
- **The HitSet cannot be dropped (question Q1, refuted).** "Some free agent has nobody exposed" fails at Pareto-optimal
  states. Smallest (n = 2, m = 3): rankings (0, 1, 2), (1, 0, 2), both agents hold their tops; each is exposed for
  the other with the same junk good 2. The state is Pareto optimal (agent 0 taking {1, 2} leaves agent 1 at most its
  b), and completable only with H = {2} (2 goes to one agent, the other absorbs). `po_check.py` counts these states
  (`zero fails`); they are 4 of 8 PO states at n = 2, m = 3 and 248 of 5,578 at n = 3, m = 5.
- **Strict balance** is used only through pair ≻ a (the exposure arcs improve their head) and in soundness.

## 7. Sub-lemmas and status

| | statement | status | tested |
|---|---|---|---|
| F1, F2 | needs shrink on improvement; non-free non-U agents have an out-arc | proved (one line each) | implicitly in every run |
| Lemma 0 | an exchange with (a) Pareto, (b) needed goods stay single with non-pair holders is valid and dominates | proved | every exchange output is re-checked for validity and dominance |
| Lemma 1 | D-cycle ⇒ dominated; top holder with b, c junk ⇒ dominated (need path) | proved (= P1, P2 of the earlier notes) | `P2-path`, `D-cycle` counts in §5 |
| Lemma 2 | under P2, a free agent holding nothing has nobody exposed | proved | assert in `improve`, `cor_stop` |
| Lemma 3 | under P2, exposed agents of a free o holding g have {b, c} = {g, junk}; o works iff \|H_o\| ≤ \|F\| − 1 | proved | asserts in `improve`; `cor_stop` vs brute-force hitting set |
| Lemma 4 | F = ∅ ⇒ all pairs (completable) or a D-cycle | proved | `improve` |
| Lemma 5 | all free absorbers fail (P2, F ≠ ∅) ⇒ exchange cycle dominates | proved | `A-cycle` counts in §5; `targeted.py` |
| Theorem | not completable ⇒ dominated | proved | every non-completable valid state, §5 |
| Q1 | PO ⇒ some free agent has nobody exposed | **false**, n = 2, m = 3 | `po_check.py` |

## 8. What is not done

- The proof is written and tested, not refereed and not formalised in Lean.
- It uses soundness (`proofs/k3_simple.md` §3.3–3.4, "completable ⇒ EFX₀", which needs only validity) as given; the
  tests re-check every completion against the raw EFX₀ definition.
- The step from the core case to the whole k = 3 theorem (peeling) is not redone here.
