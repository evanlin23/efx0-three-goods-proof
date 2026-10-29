# Four relevant goods: Draft and Exchange, a refuted candidate DER, and the priority principle

Folder `k4/de4/`. An attempt at the first open problem of the paper (`paper/k3-simple/main.tex`, Section 6): does every
instance in which each agent positively values at most four goods have a complete EFX₀ allocation? The goal is a
clean algorithm in the style of Draft and Exchange (DE), with a proof.

**Status.** The open problem is **not** solved: nothing below is a proof for all k = 4 instances. What is here:

- **A proof attempt, and what it found** (§7). Trying to prove the candidate algorithm DER (§6) correct led to a
  counterexample. It is a six-agent, ten-good instance (`gadgets.py`, `collision12`) whose draft state is valid,
  score-Pareto-maximal and cannot be finished, and no single release helps. So **DER is false**, and so are E_DER and
  "every score-Pareto-maximal valid state can be finished". This holds even for the agents to which DE's structure
  carries over best (three-good, small-d, and big-top agents with b ≥ c + d).

  The cause is exact. A big-top agent's threat set {b, c, d} needs **two** leftover goods, and DE's counting of
  leftover goods ("labels") works only with one. A family of variants breaks DER in 51 of 200 random cases.

  What is proved along the way (§7.1, written proofs):
  - soundness of finishing on the threat ladder;
  - validity transfer;
  - the chain lemma;
  - closure of the threat ladder;
  - for the (NQ) agents, the label-free arrows and the want-ring when no agent is free.
- **E_lex, the priority principle, survives** (§5, §7.3, conjecture). For every priority order of the agents, the
  lexicographically maximal valid state of the threat ladder can be finished. It holds on everything tried, including
  every adversarial label-collision gadget, where the improving move demotes one agent inside a ring. Proving E_lex,
  or finding moves that reach its maximal states, is the open target.
- **A second proof attempt, with cheap demotions** (§9). A busy big-top blocker drops from a to b, which needs at most
  one leftover good. That restores DE's counting, at the price of a score potential instead of Pareto moves.
  - For *class D′*, an algorithm of DE's shape: Draft–Exchange–Demote. The class is three-good agents,
    small-d agents, and big-top agents with c + d ≤ b, on the threat ladder.
  - Its proof is written except for one step: rings of total gain 0 that also leave a secondary potential Ψ
    unchanged, apart from a case that is proved.
  - It has no failure on 22,930 valid states that cannot be finished.
  - A priority version for class D has no failure either, but its last step is a search.
  - For general four-good agents, maximum total score is not enough (suite instance gm4-B), so the target stays E_lex.
- **DER as specified** (§5–§6) still returns EFX₀ allocations on all 159 instances of the research repository's
  k = 4 counterexample suite and on all random instances tried. It fails on the gadgets of §7.2.
- **Theorem 1** (§2, written proof, not machine-checked, not refereed): the paper's theorem and algorithm extend
  unchanged to agents with four relevant goods whose least good is small:
  v(d) ≤ min{v(a) − v(b), v(b) − v(c), v(b) + v(c) − v(a)}. The algorithm is DE with a fifth rung. Only the soundness
  proof needs new cases. Tested by two implementations (§2).
- **Sharpness for DE** (§3, examples): each of the three inequalities is needed. Dropping any one, DE as it stands
  returns allocations that are not EFX₀.
- **A barrier for DE's own proof** (§4, computation, certificates re-checked by an independent checker). DE's proof
  needs every score-Pareto-maximal valid state to be finishable. Four-good agents fall into twelve strict order types.
  For each of the eleven types other than the small-d type, and each of the 24 natural ladders of holdings, an instance
  breaks this, even with liberal finishing. Each of the 969 stuck states is a dead end: no EFX₀ allocation contains
  its holdings. This is what forces the priority view.
- **An obstruction to value-monotone methods** (§4.3): a valid state with n = 4, m = 7 in which **every** EFX₀
  allocation gives some agent strictly less value than the state does. The research
  repository ([evanlin23/efx0-three-goods](https://github.com/evanlin23/efx0-three-goods), `k4/`, `attempts/k4-*.md`)
  reports the same phenomenon for its own spaces ("the repair lowers w′").

EFX₀ allocations exist on every instance used here; the checker verifies this by exhaustive search.

## 1. Four-good agents

An agent with four relevant goods is named a, b, c, d in decreasing order of value (ties by index). A *core* agent
(one that rule R1 does not peel) has v(a) < v(b) + v(c) + v(d). For strict values (all subset sums different) the
comparisons that are not fixed by a > b > c > d are a ⋚ b + c, a ⋚ b + d, a ⋚ c + d, b ⋚ c + d and a + d ⋚ b + c.
Only twelve of the 32 sign patterns occur (`types4.py`), with these smallest representatives:

| # | type | values (a, b, c, d) | note |
|---|---|---|---|
| 1 | a<bc a<bd a<cd b<cd ad<bc | 7, 6, 5, 3 | |
| 2 | a<bc a<bd a<cd b<cd ad>bc | 8, 6, 5, 4 | |
| 3 | a<bc a<bd a>cd b<cd ad<bc | 10, 8, 6, 3 | |
| 4 | a<bc a<bd a>cd b<cd ad>bc | 8, 6, 4, 3 | |
| 5 | a<bc a<bd a>cd b>cd ad<bc | 8, 7, 4, 2 | |
| 6 | a<bc a<bd a>cd b>cd ad>bc | 10, 8, 4, 3 | |
| 7 | a<bc a>bd a>cd b<cd ad<bc | 10, 7, 6, 2 | class C of §4.3 (with type 9) |
| 8 | a<bc a>bd a>cd b<cd ad>bc | 8, 5, 4, 2 | |
| **9** | **a<bc a>bd a>cd b>cd ad<bc** | **8, 6, 4, 1** | **small d: Theorem 1** |
| 10 | a<bc a>bd a>cd b>cd ad>bc | 10, 7, 4, 2 | |
| 11 | a>bc a>bd a>cd b<cd ad>bc | 8, 4, 3, 2 | big top |
| 12 | a>bc a>bd a>cd b>cd ad>bc | 10, 6, 3, 2 | big top |

Type 9 is the *small-d* type. Allowing ties among sums, it is condition (S) below.

## 2. Theorem 1: a small fourth good

> **(S)** An agent with four relevant goods a ≻ b ≻ c ≻ d satisfies
> v(b) + v(d) ≤ v(a),  v(c) + v(d) ≤ v(b),  v(a) + v(d) ≤ v(b) + v(c);
> equivalently, v(d) ≤ min{v(a) − v(b), v(b) − v(c), v(b) + v(c) − v(a)}.

Since v(d) > 0, (S) forces v(a) > v(b) > v(c) and v(a) < v(b) + v(c): the top three are strictly ranked and strictly
balanced. Adding the first and third inequalities gives 2v(d) ≤ v(c), so the ranking of all four goods is strict. In
words: d is no larger than any of the three gaps that DE's comparisons on a, b, c depend on.

> **Theorem 1.** Every instance with nonnegative additive valuations in which every agent positively values at most
> three goods, or exactly four goods satisfying (S), has a complete EFX₀ allocation in which all bundles but at most
> one have at most two goods. Algorithm DE₄ computes one with at most n peeling rounds and at most 4n₃ + 5n₄ ≤ 5n
> trades, in O(n(n + m)) steps. Here n₃ and n₄ count the agents left after peeling that value three and four goods.

The case n₄ = 0 is the paper's Theorems 1 and 2 (existence and shape; the algorithm).

**Algorithm DE₄** is Algorithm 1 of the paper with one change. In the draft (line 5), an agent takes the first of
a_i, b_i, c_i, d_i not yet taken, or nothing. Everything else, including the chain, finishing and ring steps, the
blockers and the completion, is the paper's word for word. Blockers involve only a_x, b_x, c_x.

### Proof

The names are the paper's. For each result we say what changes. "Verbatim" means the paper's proof applies
unchanged, word for word.

**Lemma (peeling).** Unchanged.

**Lemma (when nobody can leave), extended.** *If R1 does not apply to agent i for the set G of remaining goods, then i values
exactly three goods of G and is strictly balanced on them, or it values exactly four goods of G and they satisfy (S).*
The paper's proof shows that i values at least three goods of G, and that it is strictly balanced if it values exactly
three. If it values four, these are all of R_i, which satisfy (S) by hypothesis. ∎

So in the *core case* every agent is a strictly balanced three-good agent or a four-good (S) agent.

**Definition (states and scores), extended.** A four-good agent's holding is nothing, {a_i}, {b_i}, {c_i}, {d_i} or its pair
{b_i, c_i}, with scores 0, 4, 3, 2, 1 and 5 respectively. Three-good agents are as in the paper. Since
v(d) ≤ v(c) ≤ v(b) ≤ v(a) < v(b) + v(c), a higher score never means a lower value. The total score Φ is an integer
between 0 and 4n₃ + 5n₄.

**Definition (wants, validity, free agents)** is verbatim. An agent holding nothing wants all its relevant goods,
d included. An agent holding y wants the goods it ranks above y.

**Lemma (the draft)** and **Lemma (staying valid)** are verbatim. In the second, "its score in Y was below 4" reads
"below the score of its pair".

**Definition (blockers, finishing)** is verbatim: a blocker of o holds exactly its top a_x and has b_x, c_x ∈ J ∪ Y_o.

**Theorem (soundness).** *Let Y be a valid state, and X the completion with a free agent o that can finish with a set
H (or, if every agent holds its pair, with any agent o). Then X is EFX₀, and every bundle other than X_o has at most
two goods.*

*Proof.* The first two steps of the paper's proof are verbatim: bundles other than X_o have at most two goods, and every
good in a bundle of two or more goods is unwanted. Let i ≠ j and h ∈ X_j with |X_j| ≥ 2, and let T = X_j ∩ R_i. T
contains no good that i wants and no good of i's holding. Since goods outside R_i are worth 0 to i,
v_i(X_j ∖ {h}) ≤ v_i(T), and it suffices to show v_i(T) ≤ v_i(Y_i), except in the last case.
- *i holds its pair.* T ⊆ R_i ∖ {b_i, c_i}, which is {a_i} for three goods and {a_i, d_i} for four. Then
  v_i(T) ≤ v(a) + v(d) ≤ v(b) + v(c) by (S); for three goods v(a) < v(b) + v(c).
- *i holds nothing.* It wants all of R_i, so T = ∅.
- *Y_i = {y}.* Every good of T is ranked below y and worth at most v(y), so let |T| ≥ 2.
  - y = c_i or y = d_i: at most one relevant good is ranked below y, so this cannot happen.
  - y = b_i: then i has four goods, T = {c_i, d_i}, and v(c) + v(d) ≤ v(b) by (S).
  - y = a_i and T does not contain both b_i and c_i: T ⊆ {b_i, d_i} or T ⊆ {c_i, d_i}, worth at most
    v(b) + v(d) ≤ v(a) by (S).
  - y = a_i and b_i, c_i ∈ T: the paper's argument, verbatim. If X_j = {b_i, c_i}, removing h leaves one good, worth at
    most v(b) ≤ v(a). Otherwise |X_j| ≥ 3, so j = o and b_i, c_i ∈ X_o ⊆ Y_o ∪ J. Then i is a blocker of o, and H
    contains b_i or c_i, which went to an agent other than o: a contradiction. ∎

This is the only place where (S) is used: once in each of the three new cases.

**Definition (rings), Lemma (ring) and Lemma (chain)** are verbatim. They use only the following facts: holdings
outside U are single goods; a want arrow gives its tail a good it ranks above its own; a pair arrow takes a top-holder
to its pair; and Lemma (staying valid).

**Lemma (the finishing test)** and **Theorem (Improvement Lemma)** are verbatim. They are about blockers, which
involve only a, b, c. They also use the fact that every agent outside U ∪ F holds a single wanted good, which holds
for four-good agents too.

**Theorem (DE is correct)** is verbatim, with the bound 4n₃ + 5n₄ on Φ in place of 4n. The running-time analysis
is the paper's. The only difference is that the R1 test compares one value with a sum of up to three values of one
agent, which is still one step per test. The proofs compare only sums of values, so real values are covered. The
paper's corollary on score-Pareto-maximal valid states (all are finishable) also holds verbatim. ∎

### What is and is not checked

- Two implementations: `de4.py`, the algorithm written from the theorem statement with every claim of the proof as an
  assert; and `classc.py`, states, blockers, chains and rings written for the wider class C of §4.3, which contains (S).
  Both run without failure (§6, `test_de4.log`). Every output is checked against the raw definition of EFX₀.
- Not machine-checked. The Lean formalization in `lean/` covers only the three-good case. The changes are local
  (the states, the draft and three cases of soundness), so extending `lean/EFX/K3DE*.lean` should be routine but has
  not been done.

## 3. Each inequality of (S) is needed by DE

`test_de4.py` part [4] runs DE₄ unchanged on four-good agents that violate exactly one inequality of (S). In each case
it finds an output that is not EFX₀. The smallest instances found (agent: good:value, by value):

| dropped | instance | DE's output | envy |
|---|---|---|---|
| v(b) + v(d) ≤ v(a) | n = 3, m = 5. 0: 0:28 2:26 3:16 4:10; 1: 2:22 1:21 0:7 3:2; 2: 2:15 0:13 3:9 | {0} {2} {1, 3, 4} | agent 1 holds its top 2 (22). The owner's bundle holds its b and d: 21 + 2 = 23 > 22 |
| v(c) + v(d) ≤ v(b) | n = 3, m = 5. 0: 0:16 4:12 3:11 2:2; 1: 3:28 0:18 1:15 4:5; 2: 0:25 4:18 3:17 1:6 | {0} {1, 2, 3} {4} | agent 2 holds its b, 4 (18). The owner's bundle holds its c and d: 17 + 6 = 23 > 18 |
| v(a) + v(d) ≤ v(b) + v(c) | n = 2, m = 5. 0: 1:27 3:18 0:10 4:8; 1: 1:17 4:12 2:6 0:5 | {0, 1, 3} {2, 4} | agent 1 holds its pair {4, 2} (18). The owner's bundle holds its a and d: 17 + 5 = 22 > 18 |

Each failure is the threat that the corresponding case of the soundness proof rules out. So (S) is exactly what DE's proof
needs. Going further needs new blockers and new moves, and §4 shows that such extensions run into a barrier.

## 4. The barrier

### 4.1 What an extension of DE's proof needs

DE's proof has three parts:
1. a *ladder* of holdings for each agent, ordered by value, with wants and validity as in the paper;
2. an Improvement Lemma: every valid state that cannot be finished has a trade that keeps validity and raises some
   scores without lowering any;
3. a finishing rule of the paper's shape: one owner takes the leftover goods, minus a set H that is spread over other
   agents, at most one good each.

Parts 1 and 2 imply:

> **E(λ).** For the ladder λ, every valid state that no valid state Pareto-dominates in scores can be finished.

This is the paper's corollary on score-Pareto-maximal valid states. E(λ) is a statement about the ladder and the
finishing rule alone, so it can be tested without knowing which trades the proof would use. We test it with **liberal finishing**: any agent may own,
the goods of H may go to any agents other than the owner that hold at most one good, and the result is accepted if it
is EFX₀ by the raw definition. This is the most generous finishing rule of DE's shape. A failure of E(λ) with liberal
finishing therefore rules out every proof of the form 1–3 with ladder λ.

### 4.2 Results

Ladders for a four-good agent consist of: nothing, the four singles, some pairs, and a top rung that wants nothing and
can never be threatened. Three-good agents keep the paper's ladder. Two families:

- **natural family**: the intermediate rungs are pairs that are *not* envy-free (worth less than the other two goods),
  and the top rung is an envy-free pair. This gives 24 ladders per type, 288 in all. Theorem 1's ladder
  (nothing < d < c < b < a < {b, c}) is one of them.
- **extended family**: any pairs below the top, and a top rung that is an envy-free pair or the triple {b, c, d}
  (worth more than a in every core). Between 64 and 120 ladders per type, 1,008 in all. This family contains the
  natural one.

For each type and ladder, `barrier.py` searches random instances (all four-good agents of that type, plus three-good
agents) for a counterexample to E(λ) with liberal finishing. `barrier_deep.py` and `barrier_dense.py` search harder
on the survivors, the last with dense instances (n = 4 to 6, m = n + 1 to n + 3). Every counterexample is stored in
`barrier_certs.json`. `check_barrier.py` re-checks each one from the raw definitions; it imports nothing from this
folder. It checks the type, validity, score-Pareto-maximality against all states, that no liberal completion is
EFX₀, and that an EFX₀ allocation exists. Log: `check_barrier.log`.

| | natural family | extended family |
|---|---|---|
| types 3, 4, 7, 8, 11, 12 | all 24 ladders refuted | all ladders refuted |
| types 1, 2, 5, 6, 10 | all 24 ladders refuted | all refuted except a few *tall* ladders (below) |
| type 9 (small d) | Theorem 1's ladder satisfies E (the proof of §2); 3 more ladders not refuted, 20 refuted | 24 not refuted, 48 refuted |

**Natural family.** For every type other than the small-d type, every natural ladder is refuted. Within this family,
DE's method extends to exactly one type of four-good agent: the small-d type of Theorem 1.

**Extended family: the tall ladders, an open lead.** After the liberal-finishing searches, 17 combinations survive.
All are *tall*: they climb through envy-free pairs up to {a, b} or {a, c}, and they occur for types 1, 2, 5, 6 and 10
only. We then tested them with DE's own finishing rule in the form of the Lean formalization ("valid absorbers"): the
owner is any agent whose holding contains no wanted good, and the goods of H go to free agents. `barrier_narrow.py`
refutes 2 of them (n = 2, m = 5). The other 15 survive every search: random instances up to n = 5, dense instances
with n = 4 to 6 (`barrier_narrow_dense.log`), and the collision gadget of §4.3 built with the type's values
(`collision.py`, last part). In the gadget, a tall ladder lets z′ climb from {c, d} to {b, d} with x′'s top while x′
takes its pair, a Pareto improvement that the natural ladders do not have. `check_barrier.log` lists the 15 (section
"not refuted").

So E(λ) may hold for these ladders, with a finishing rule close to DE's. In samples (`tall_owners.py`,
`tall_owners.log`), 86% to 93% of their score-Pareto-maximal states are finished by a free agent, as in DE. The rest
need an agent on its top rung or the holder of an intermediate pair as owner. This is weak evidence: random search
also passed over the class-C collision of §4.3, which was found only by construction. A proof would also need a new
Improvement Lemma with several kinds of blockers. A top-holder is threatened by {b, c} and by {b, d} for these types,
and the holder of an intermediate pair by the other two goods.

### 4.3 The collision example: a value-monotone barrier

The natural candidate beyond (S) is **class C**: drop the middle inequality and keep b + d ≤ a and a + d ≤ b + c
(types 7 and 9). An agent of type 7 has c + d > b, so a holder of b is threatened by {c, d}. Our attempt (`classc.py`)
gives such agents the extra rung Q = {c, d} between b and a. It has a second kind of blocker (a b-holder with c, d
leftover or in the owner's bundle), a second chain (a b-holder with c, d leftover takes Q), and the move "a Q-holder
with b leftover takes {b, c}". The Q-holders join the free agents as owners and as absorbers in the rings: a
blocker of a Q-holder takes part of its Q with one leftover good, and the Q-holder takes its top in exchange. Every
step of this attempted proof is an assert in `classc.py`, and on random data none fails (`classc_random.py`: 6,000
instances, 71,985 valid states, 4,680 chains, 13,044 rings, every score-Pareto-maximal state finishable). We have not
written out a proof that the steps always succeed, and they do not. The step that fails in the example below is the
choice of *distinct* leftover goods for the pair arrows of the ring (`collision.py`):

| agent | goods (value) | holding |
|---|---|---|
| x | A′ 10, C1 7, h 6 | A′ (its top) |
| x′ | A 10, C2 7, h 6 | A (its top) |
| z (type 7) | A 10, A′ 7, C1 6, D1 2 | Q = {C1, D1}, worth 8 |
| z′ (type 7) | A′ 10, A 7, C2 6, D2 2 | Q = {C2, D2}, worth 8 |

The leftover good is h. The state is valid: z wants A and z′ wants A′, both held alone. Nobody is free. No chain
applies. The only blocker of z as owner is x, whose pair {C1, h} needs h removed; symmetrically x′ blocks z′ through
the same h. With no free agent, nothing can take h, so no owner can finish. The ring x′ → z → x → z′ → x′ would give
h to both x and x′. The state is score-Pareto-maximal, and it stays stuck, with liberal finishing, under *every*
ladder of the extended family for type 7 that contains {c, d}.

More is true, independently of any ladder: the instance has 26 EFX₀ allocations, and **each gives some agent strictly
less than its value in this state** (10, 10, 8, 8). For example, z′ falls to {C2, h} (6), or x′ falls to {C2} (7). So
no method that only raises values can reach an EFX₀ allocation from this valid state. A proof for k = 4 must
sometimes lower an agent. This matches the research repository's findings for its spaces of pre-allocations, where
every potential and every Pareto-type extremal principle tried failed at small n.

How common is this among the certificates of §4.2? Among those small enough to list every allocation
(`check_barrier.log`, last line), 175 of 969 have this property: every EFX₀ allocation lowers some agent
below its value in the stuck state. In the others, some EFX₀ allocation lowers nobody, but it lies outside DE's shape
or the ladder, for example with a holding that is not a rung or with two bundles of three goods.

## 5. Beyond the barrier: priority and the threat ladder

Two observations about the dead ends of §4 lead to a different extremal principle.

**Every certificate is a dead end.** For each of the 969 stuck states, no EFX₀ allocation gives every agent a superset
of its holding (checked by listing all allocations). So the trouble is not DE's finishing shape. These states must not
be reached, or must be left by lowering some agent.

**Priority instead of Pareto.** In the smallest dead ends, every EFX₀ allocation gives one agent an envy-free pair such
as {a, b} and lowers the other. That is the move of a *priority* potential: fix an order π of the agents and compare
score vectors lexicographically in that order, as serial dictatorship does. Earlier agents may then improve at the
expense of later ones.

**The threat ladder.** A *threat set* of a single holding y is a set S of goods ranked below y with v(S) > v(y). It is
what can threaten a holder of y in the owner's bundle. In DE the only one is {b, c}, the threat set of a, and it is
the pair. The threat ladder gives each agent:
- three goods: nothing < c < b < a < {b, c}, the paper's ladder;
- four goods: nothing, the four singles, the pairs {a, b}, {a, c}, {a, d}, and the minimal threat sets of the
  singles, ordered by value. These are the pairs among {b, c, d} worth more than a; {c, d} if worth more than b; and
  {b, c, d} for a big-top agent (a > b + c), for whom no pair among {b, c, d} beats a.

For each of the twelve types, the minimal threat sets of every rung are again rungs, higher up (`python3 lex.py`
prints the ladders and checks this; `lex.log`). So DE's principle "a threatened agent can move up to its threat set" holds
for every type. Pairs worth less than a that are not threat sets are left out on purpose. For example, the small-d
agent's {b, d} spends two goods without making the agent safe, and including it breaks the next statement (suite
instance gm4-A).

**Validity** gets one more condition, because the triple of a big-top agent is a bundle of three goods:
- (V1) every wanted good is the whole holding of some agent, as in DE;
- (V2) the holdings form a partial EFX₀ allocation. For pairs, (V2) follows from (V1).

> **E_lex** (conjecture). For every core instance with at most four relevant goods per agent (strict values) and every
> order π of the agents, the π-maximal valid state of the threat ladder can be finished. The owner is an agent whose
> holding contains no wanted good; the goods of H go to different free agents.

Evidence (`lex_test.py`, `lex_test.log` and `lex_test_scale10.log`):
- 36,000 random instances with every four-good agent of one type, 3,000 per type;
- 40,000 random instances with all types mixed;
- every priority order for n ≤ 4, six orders for n = 5;
- the 155 instances of the research repository's suite whose core has at most 6 agents;
- the 969 certificates of §4 and the collision example.

No failure. With all pairs as rungs, the statement fails (gm4-A); with only the pairs worth more than a, it fails at
n = 3; and with the triple for every four-good agent, also at n = 3.

> **E_DER** (conjecture, **refuted** in §7.2). Every score-Pareto-maximal valid state of the threat ladder can be
> finished, or can be after one agent moves to a lower rung (a *release*).

The evidence that first supported it (`der_test.py`, `der_test.log`) came from 22,903 score-Pareto-maximal states.
22,842 could be finished directly; the other 61 came from the suite and the certificates, and each needed one
release. In the collision example of §4.3, z drops d and holds {C1}: it becomes free and can absorb the leftover good
h. The counterexample of §7.2 has a structure that none of these instances contains.

## 6. DER: Draft, Exchange, Release

> **Refuted (§7.2).** DER gets stuck at the draft of the instance `collision12` of `gadgets.py` (n = 6, m = 10), and on
> 51 of 200 random variants of it. The evidence below was collected before those instances were found. It shows only
> that the failure needs a specific structure, which neither random instances nor the research repository's suite
> contain.

`der.py` (one step), `der_run.py` (the algorithm), `der_check.py` (every step on every valid state).

**Objects.** States on the threat ladder, valid by (V1) and (V2):
- *wants* and *free agents* are DE's;
- an *owner* is any agent whose holding contains no wanted good;
- a *threat set* of agent x is a minimal set T of x's unwanted goods outside its holding, with v_x(T) > v_x(holding);
- a *blocker* of an owner o is a pair (x, T) with T a threat set of x lying inside J ∪ Y_o.

Owner o *can finish* if some H ⊆ J meets every blocker's T outside Y_o (so no T lies inside Y_o) and
|H| ≤ |F ∖ {o}|. The completion is DE's: o gets Y_o ∪ (J ∖ H), and each good of H goes to a different free agent.

**Soundness (proof sketch).** Every good in a bundle of two or more goods is unwanted, by (V1). Holdings of two or
more goods do not threaten anyone, by (V2). A free agent's new pair consists of two unwanted goods. For the owner's
bundle X_o: an agent x threatened by X_o has v_x(X_o ∩ R_x) > v_x(Y_x), and X_o ∩ R_x consists of unwanted goods,
so it contains a threat set of x. That set lies in J ∪ Y_o, so x is a blocker, and H removed a good of the set from
X_o: a contradiction. Every completion found in the tests is also checked against the raw definition.

**Algorithm DER.**
1. Peel by rule R1, as in DE.
2. Draft: in index order, each agent takes its best single that is not yet taken.
3. Repeat:
   - **finish** if some owner can finish;
   - else **grab**: some agent moves to a higher rung made of its own goods and leftover goods. If it gives up a
     single wanted good, that good goes to the first agent that wants it, and so on, exactly as in DE's chain;
   - else **ring**: a cycle of *upgrade arrows* x_t → x_{t+1}. Agent x_t moves to a higher rung made of its own goods,
     goods of x_{t+1} and leftover goods. Leftover goods are used at most once, and no good is both given and kept.
     DE's want arrows and pair arrows are the special cases. `der.py` first tries DE's σ-walk, with a blocker for
     each owner and fresh leftover goods along the walk, then a depth-first search;
   - else **release**: one agent moves to a lower rung after which some owner can finish; then finish.

Grabs and rings raise the total score, which is at most the total number of rungs (at most 10 per agent). The release
is followed at once by finishing. So DER stops after at most 10n trades.

**Evidence.**
- *Every step on every valid state* (`der_check.py`, `der_check.log`): random instances with n ≤ 4 (each type, and
  mixed), the suite instances with a core of at most 5 agents, the 969 certificates and the collision example. That is
  about 32,000 valid states: 24,055 finish; 2,531 chains and 2,352 other grabs; 3,036 σ-walk rings and 84 rings found
  only by the search; 60 releases. Every completion is EFX₀ by the raw definition, and every trade gives a valid state
  that dominates in scores. Since a step exists from *every* valid state, DER succeeds from any valid starting state on
  these instances, not just from the draft.
- *End to end* (`der_run.py`, `der_run.log`): 1,800 random instances with up to 12 agents, and all 159 instances of
  the research repository's suite, including the four large ones:

  | instance | n | m | trades |
  |---|---|---|---|
  | c4-H2 | 9 | 23 | 6 |
  | lmbt-Hq3 | 14 | 34 | 6 |
  | c4-H5 | 21 | 53 | 14 |
  | lmbt-HH3 | 26 | 65 | 14 |

  Every output is EFX₀. Starting from the draft, no run needed a release.
- *Shape.* In 4,155 of 4,159 runs, at most one bundle has more than two goods. In the other 4, a big-top agent's triple
  is a second bundle of three goods. So DE's shape guarantee does not carry over as it stands.

**What is missing for a theorem.**
1. *An Improvement Lemma*: in a valid state that cannot be finished, a grab, a ring or a finishing release exists.
   This is the heart of the matter. The data says it holds, and E_lex and E_DER are its extremal forms.
2. *Polynomial time*: the ring and the hitting set H are found by search. DE finds its ring by a σ-walk and its H is
   forced. Here the σ-walk succeeds on all but 84 of about 3,100 ring states. A proof would also have to give a rule
   for choosing among blockers.
3. *Ties*: the ladders assume strict values. The research repository's tie reduction (K4.TIE) covers existence, not
   this algorithm.
4. *A machine-checked version*, as for k = 3.

## 7. A proof attempt, and the counterexample it led to

The aim was to prove DER correct. DER is correct on an instance if its loop never gets stuck: soundness and
termination are easy (§7.1). Since a non-maximal state can always be improved somehow, that reduces to an extremal
statement: every score-Pareto-maximal valid state can be finished, possibly after one release (E_DER). The plan was
to prove it as the paper proves its corollary, by an Improvement Lemma with explicit moves, writing the proof as code
with every claim an assert (`nq_proof.py`) and refining it where an assert fails. This was first done for the (NQ)
agents (below), where no release ever seemed necessary.

### 7.1 What is proved

All of this is for core instances with strict values and the threat ladder of §5. "Finite check" means a check over
the twelve strict types of `types4.py`, which is exhaustive because each statement depends only on an agent's type.

**Lemma 1 (soundness).** *Let Y be valid. Let o be an owner (its holding contains no wanted good), and let H ⊆ J meet
T ∖ Y_o for every blocker (x, T) of o, with |H| ≤ |F ∖ {o}|. Then the completion X is EFX₀.*

*Proof.* Take i ≠ j with |X_j| ≥ 2. Then v_i(X_i) ≥ v_i(Y_i), so it suffices to show θ_i(X_j) ≤ v_i(Y_i).
- *X_j = Y_j*, a holding of two or more goods: this is (V2).
- *X_j consists of a free agent's good and a good of H*: both goods are unwanted. The good of H is leftover, and by
  (V1) wanted goods are held alone. Wants are by value, so every unwanted good g of i outside Y_i has
  v_i(g) ≤ v_i(Y_i). A bundle of two goods threatens i by at most its better good.
- *j = o*: X_o ∩ R_i consists of unwanted goods of i, because o holds no wanted good and J holds none, and
  θ_i(X_o) ≤ v_i(X_o ∩ R_i). Suppose v_i(X_o ∩ R_i) > v_i(Y_i). A single unwanted good is worth at most v_i(Y_i), so
  the set has at least two goods and contains a minimal threat set T of i. Then T ⊆ X_o ⊆ Y_o ∪ J, so (i, T) is a
  blocker of o. H meets T ∖ Y_o, and that good is not in X_o: a contradiction. ∎

The top rungs of the threat ladder have no threat sets, so if every agent is on its top rung, any agent can take J.

**Lemma 2 (transfer).** *If Y is valid, and Y' is a state in which no score is lower, every good wanted in Y is held
alone, and (V2) holds, then Y' is valid.* The paper's proof of (V1) applies, because wants depend only on the value of
the holding and shrink as it rises.

**Lemma 3 (chains).** *If some agent has a threat set inside J, some agent has a valid chain.* A chain lets x take T
and passes x's old good down the agents that want it, as in the paper. (V1) holds by Lemma 2.

For (V2): a pair T threatens j only by a single good, and the goods of T were leftover, so unwanted. Suppose instead
T = {b, c, d} is the triple of a big-top agent and threatens some j. If T has a good outside R_j, then T ∩ R_j has
at most two goods and is worth more than Y_j. If T ⊆ R_j, then θ_j(T) is the value of the best pair in T. Either way,
j has a *pair* threat set inside T ⊆ J, and j's chain with that pair is valid. ∎

**Lemma 4 (closure, finite check; `python3 lex.py`).** For every type, the minimal threat sets of every rung are
higher rungs.

**Lemma 5 ((NQ) structure, finite check; `python3 nq_proof.py`).** The (NQ) types are 1, 2, 5, 6, 9, 10 and 12 of §1:
c + d ≤ b or c + d ≥ a. For them:
- (L1) every rung of two or more goods is worth more than a, so its holder wants nothing;
- (L2) a pair rung's threat sets are exactly its complement pair, when that is worth more; a triple rung has none.

Both properties fail for each of the other five types.

**Lemma 6 (G1).** *If no valid grab exists, no four-good owner has its top a leftover.* Otherwise the owner takes a
and keeps its best good: {a, y} beats a single y, a pair beats any pair without a, and {a, b} beats {b, c, d} for a
big-top agent. All its goods are unwanted, so this grab is valid by Lemma 2. ∎

**Lemma 7 (G2, (NQ)).** *If no valid grab exists, every multi-good holder x that blocks an owner o has an arrow into o
that uses no leftover good.*

*Proof.* By (L2), x holds a pair P and its threat set T is the complement of P. By Lemma 3, T ⊄ J.
- If a_x ∈ T: by Lemma 6, a_x ∈ Y_o, and x moves to {a_x, p} for either good p ∈ P.
- If P = {a_x, p}: then T = {q, q'} with v(q) + v(q') > v(a_x) + v(p), so both goods of T are worth more than p. One
  of them is in Y_o, and x moves to {a_x, that good}. ∎

**Lemma 8 ((NQ), no free agent).** *If no agent is free and some agent is busy, a ring of want arrows exists.*

*Proof.* By (L1), only agents holding at most one good want anything. With no free agent, these are busy (holding
nothing would make an agent free). So "the first agent that wants j's good" maps busy agents to busy agents, and it
has a cycle: the paper's ring of want arrows, valid by Lemma 2. ∎

With these, the proof-as-code (`nq_proof.py`) follows DE's argument: chains, then a walk that leaves each owner by an
arrow whose leftover goods are not yet used. It runs without a failed assert on random (NQ) instances
(`nq_proof.log`: about 7,000 instances, 15,000 rings). The one step it cannot justify is the counting of leftover goods
along the walk. In DE every pair arrow uses one leftover good, and a free agent that cannot finish has at least |F|
distinct ones, so a fresh one always exists. That is exactly the step that is false at k = 4.

### 7.2 The counterexample

`gadgets.py`, `collision12`: four agents of type 12 (big-top, b > c + d) and two three-good agents, with ten goods.

| agent | goods, by value | holding in the draft |
|---|---|---|
| x1 | A1 10, y1 6, h1 3, h2 2 | A1 |
| x2 | A2 10, y1 6, h3 3, h4 2 | A2 |
| x3 | A3 10, y2 6, h1 3, h3 2 | A3 |
| x4 | A4 10, y2 6, h2 3, h4 2 | A4 |
| o1 | A3 4, A4 3, y1 2 | y1 |
| o2 | A1 4, A2 3, y2 2 | y2 |

The draft state is valid, with h1, h2, h3 and h4 leftover and o1, o2 free.
- The blockers of o1 are x1 and x2, which need {h1, h2} and {h3, h4}; those of o2 are x3 and x4, which need {h1, h3}
  and {h2, h4}.
- Each free agent needs two goods in H but has only one other free agent, so neither can finish.
- o1 wants only the tops of o2's blockers, and o2 only those of o1's, so every ring passes through both. But every
  label of o1 meets every label of o2.
- The state is score-Pareto-maximal among all valid states, both of the threat ladder (54 valid states) and of DE's
  ladder with {b, c, d} as type 12's top (21 valid states). No single release finishes it.

So DER stops at the draft with no move. `gadgets.py` also builds random variants of this pattern (random values and
agent types, extra agents): DER gets stuck on 51 of 200. Purely random instances and the suite never contain the
pattern, which needs every label of one free agent's blockers to meet every label of the other's.

Consequences:
- **E_DER is false**, and so is "every score-Pareto-maximal valid state can be finished", for the threat ladder and
  for DE's ladder with triples.
- A DE-style proof by score improvements cannot cover big-top agents with b > c + d. Their pair arrows need two
  leftover goods, and two-good labels can collide where one-good labels cannot. With one-good labels and two free
  agents, a free agent whose blockers all need the same leftover good could finish by handing it to the other.

### 7.3 What survives: the priority principle

E_lex (§5) holds on `collision12` for all 720 priority orders, and on all 400 random gadgets of both families
(`gadgets.log`). The improving moves it needs are rings in which **one agent is demoted**. For example, in the order
x1, …, o2:
- x1 takes {y1, h1, h2};
- o2 takes A1;
- x4 drops from A4 to y2;
- o1 takes A4.

This is allowed because x1 comes before x4 in the order. Two observations about the maximal states:
- some owner finishes with H = ∅ in all but 1 of 2,400 sampled cases;
- the lowest-priority free agent finishes in 7,167 of 7,431. So no simple "this agent finishes" statement holds.

Open, in order of usefulness:
1. A proof of E_lex. It would settle EFX₀ existence for every instance with at most four relevant goods.
2. A move set that reaches a priority-maximal state: DE's rings plus demotions of agents of lower priority than the
   ring's best improver, with a polynomial bound on the number of moves.
3. A proof for the (NQ) agents without type 12, where no collision of two-good labels can occur. Lemmas 1–8 cover
   everything except the counting along the walk, which there involves only one-good labels. Owners that hold pairs
   still need an argument.

## 8. What this suggests

- **The small-d class is the reach of DE as it stands.** Within the natural ladders it is also the reach of any proof
  with DE's architecture (monotone trades, then one large bundle). §4 shows this.
- **Score-monotone methods fail at k = 4, whatever the ladder.**
  - §4.3: a valid state from which every EFX₀ allocation lowers some agent's value.
  - §7.2: a valid, score-Pareto-maximal draft state that no owner can finish and no release repairs, on both natural
    ladders for big-top agents.
  - The cause: pair arrows that need two leftover goods.
- **The priority principle E_lex is the surviving target.** It allows demotions inside rings, which is exactly what
  §7.2 needs, and it holds on everything tried. A proof of E_lex would answer the open problem; an efficient move set
  reaching priority-maximal states would give the algorithm.
- **A smaller target:** the (NQ) agents without type 12. Every pair arrow there needs at most one leftover good, and
  Lemmas 1–8 of §7.1 leave only the counting of leftover goods along the walk open.
- **Demotions as arcs (§9).** The total score is a potential that tolerates a demotion. For class D′ it gives a
  DE-shaped algorithm with one open step in its proof. For general four-good agents the total score fails (gm4-B), so
  demotions have to be governed by priority.

## 9. A second proof attempt: cheap demotions

§7.2 located the failure: a big-top blocker's full move needs two leftover goods, and DE's counting of labels works
only with one. This section tries the move that E_lex uses in §7.3, a **demotion**, as a regular arc. It gives an
algorithm of DE's shape for one class of agents, whose correctness proof has exactly one open step.

### 9.1 The cheap demotion

Let o be free and x a busy blocker of type T (big-top with c + d ≤ b), so that Y_x = {a_x}, P_x = {b_x, c_x, d_x} ⊆
J ∪ Y_o, and someone wants a_x. Instead of taking P_x (score +1, label P_x ∖ Y_o: two leftover goods), x drops to
b_x: score −1, label {b_x} ∩ J, at most **one** leftover good, and none if b_x = y_o. The good a_x goes on along a want
arc as before.

Each cheap label is contained in the full label of the same blocker. A free agent that cannot finish has no hitting set
of size |F| − 1 for its full labels. So any set of at most |F| − 1 used goods misses one of its full labels entirely,
and with it the cheap label. DE's counting therefore works again: a walk that leaves every free agent by a cheap arc
with a fresh label never gets stuck. The price is that rings are no longer Pareto improvements, so the potential
becomes the **total score**.

On `collision12` the priority ring of §7.3 is of this kind: x1 takes {y1, h1, h2} (+1), o2 takes A1 (+2), x4 drops
from A4 to its b, y2 (−1), and o1 takes A4 (+1). Total +3.

### 9.2 Class D with priority (`pde_proof.py`)

**Class D:** every core agent is a three-good agent, a small-d agent (type 9: b + d ≤ a < b + c, c + d ≤ b,
a + d ≤ b + c), or a type-T agent (b + c ≤ a < b + c + d, c + d ≤ b). The ladder is nothing < d < c < b < a < P, with
P = {b, c} for the first two kinds and {b, c, d} for type T. Only a holder of a is ever threatened, by a set containing
P.

The candidate **Priority Improvement Lemma**: for every order, a valid state that no free agent can finish has a chain,
a grab, or a ring of want arcs, full arcs and demoted arcs. The ring's labels must be pairwise disjoint, and its
highest-priority agent must improve. It would show that for every order the priority-maximal valid state of this
ladder can be finished, and with it EFX₀ existence for class D.

`improve_pde` constructs such a move in five steps:
1. chain;
2. grab;
3. a want ring, if no agent is free;
4. a cycle of a demoted system of distinct labels whose top agent is entered by a want arc;
5. the **PDE-3** ring: try the blockers x in priority order as the one full arc o_x → x, and search for a path back to
   o_x along want arcs and demoted arcs into blockers of lower priority than x, with all labels disjoint.

It never failed (`pde_proof.log`: 1,500 instances, every valid state that cannot be finished, 4 orders each, 11,832
cases). Two simpler versions fail:
- PDE-1, a demoted system of distinct labels with at most one upgraded arc, fails in 120 cases. In 119 the upgrade's
  label collides; in 1 the upgrade is not valid.
- PDE-2, which uses only the highest-priority blocker as the full arc, fails in 187.

Step 5 is a search, so this is evidence, not a proof.

### 9.3 Class D′ and E_sum (`sum_proof.py`)

**Class D′** has the same agents, but type T uses its threat ladder (§5):
nothing < d < c < b < a < {b, c, d} < {a, d} < {a, c} < {a, b}. Three-good and small-d agents keep the class-D ladder.
In every case only a holder of a is threatened, by a set containing P, and b lies in P.

**E_sum (conjecture for class D′):** every valid state of maximum total score can be finished. Finishing is DE's: a
free agent o and a set H ⊆ J that meets P_x ∩ J for every blocker x of o, with |H| ≤ |F| − 1.

The algorithm, Draft–Exchange–Demote, starts from the draft and applies improving moves until some free agent can
finish. Every move raises the total score, which is at most 8n, so there are at most 8n moves, each polynomial.
`improve` returns the move and asserts every claim of the proof below.

**Proved (written arguments; class D′, strict values):**
1. *Soundness.* Lemma 1 of §7.1: in class D′ the blockers are exactly the holders of a with P ⊆ Y_o ∪ J. If every
   agent holds two or more goods, any agent can take J.
2. *Grabs and chains are valid* (Lemmas 2 and 3). In particular (NC): no holder of its a has P ⊆ J.
3. *No free agent ⇒ ring of want arcs.* Every rung of two or more goods lies above a, so its holder wants nothing.
   Lemma 8's argument applies.
4. *No free type-T blocker.* A free T agent x with P_x ⊆ Y_o ∪ J has a good g ∈ P_x ∩ J by (NC). It could grab
   {a_x, g}, which is a rung of its ladder. The grab is valid: a pair threatens only by a single good, and neither a_x
   nor g is wanted. So, when no grab applies, every blocker is a busy T agent or a three-good or small-d agent.
5. *Free agents.* Each free agent holds a good and has a blocker; otherwise it finishes.
6. *Arcs.* The arcs out of a free agent o are:
   - demoted arcs, into its busy T blockers (−1, label {b_x} ∩ J);
   - full arcs, into its three-good and small-d blockers (+1). By (NC) their pair is y_o plus one leftover good, which
     is the label.

   Every label has at most one good. Out of a busy agent: a want arc to its best wanter (gain ≥ 1).
7. *Counting.* The walk never gets stuck (§9.1).
8. *Cheap rings are valid.* No new triple appears. A demoted T agent at b wants only a_x, which its wanter now holds
   alone. Two of its lower goods are worth at most c + d ≤ b. Pairs threaten only by single goods. Lemma 2 handles the
   rest.
9. *Gain.* Every demoted arc is followed by a want arc, so a cheap ring has gain at least the number of full arcs, so
   at least 0. The gain is 0 only for an **exact alternation**:
   o_1 → x_1 → o_2 → x_2 → … → o_r → x_r → o_1. Each x_i is a demoted busy T blocker of o_i, and o_{i+1} is free and
   receives a_{x_i}, exactly one rung above its holding.
10. *Upgrades.* In an exact alternation, let x take its full triple P_x instead of b_x (gain +2). The result is valid
    unless some three-good or small-d agent z off the ring holds a_z with P_z ⊆ P_x.

    *Proof.* Only the new triple P_x needs checking, because the rest is item 8. Nobody wants a good of P_x, since
    they are leftover or y_o. Take an agent z ≠ x:
    - *z holds two or more goods, or nothing.* Then z is never threatened, or has no good in P_x.
    - *z holds a single y, off the ring.* Then z ranks its goods in P_x below y. Two of them exceed y only if y = a_z
      and they are z's pair: a three-good or small-d z with P_z ⊆ P_x. A T agent at a values any two of b, c, d at
      most b + c ≤ a.
    - *z is a demoted agent at b.* It is threatened only by a bundle containing its a, which is held alone, or by its
      c and d, worth c + d ≤ b.
    - *z is a free agent other than o on the ring.* Its goods in P_x lie below its old holding, which is b or c
      (z moves up by one single). So two of them are worth at most c + d ≤ b.
    - *z = o.* Then o moves up one single: from b_o to a_o, from c_o to b_o, or from d_o to c_o. Its goods in P_x
      are y_o and goods below it.
      - From b to a is safe for type T, since b + c ≤ a. For a three-good or small-d o, {b_o, c_o} ⊆ P_x ⊆ Y_o ∪ J
        would give o a grab of its pair.
      - From c or d up is safe, since c + d ≤ b.
    The upgrade also needs P_x ∩ J to avoid the other labels on the ring. ∎

**Open: the exact-alternation step.** It remains to show that when every cheap ring has gain 0, some move still raises
the total score. The two moves that `improve` tries are:
- an upgrade with a free label (10);
- a *demotion chain*: a busy holder of a whose b is leftover drops to b, and its a goes down the want chain, with
  positive total gain.

In `sum_proof.log` (6,000 instances, a quarter each from four families: random, the collision pattern, mostly type-T
agents with shared tops, and an adversarial gadget whose two upgrades collide), 22,930 valid states cannot be
finished. In 134 of them every cheap ring has gain 0. An upgrade (30) or a demotion chain (104) always exists, and
there is no failure.

A secondary potential narrows the gap. Let Ψ be the number of type-T agents that do not hold exactly their a. Under
the pair (total score, Ψ), an exact alternation that raises Ψ is itself an improving move. It leaves Ψ unchanged only
if every o_{i+1} is a type-T agent at b_{o_{i+1}} and receives its **own** top from x_i. A ring that raises Ψ exists in
125 of the 134 states.

In the 9 states where no ring raises Ψ, every cheap ring is a "Ψ-flat" alternation of length r = 1, and there is a
single free agent. With r = 1 no label can collide, so only the agent z of (10) can block the upgrade. For r = 1 and
|F| = 1 that is impossible:
- z is not free, since o is the only free agent;
- so z is busy. Follow, from z, the agents that want the current good. None of them is o, which wants only a_x, and
  none is x, which holds its top and wants nothing. So the walk closes a ring of want arcs among busy agents, which has
  positive gain.

So under (total score, Ψ), every one of the 134 states is handled by a written argument. What is missing is the
general Ψ-flat alternation, of length r ≥ 2 or with |F| ≥ 2. Targeted searches for it (80,000 gadgets with four type-T
agents in two crossed pairs that share tops, plus extra blockers and wanters; the scripts are not kept) produced no
state in which every cheap ring has gain 0.

**General four-good agents: E_sum is false.** On the suite instance gm4-B (n = 4, m = 7), all four agents are of
Q-types (b < c + d < a). It has 25 valid states on the threat ladder, 4 of them of maximum total score. One of these,
with holdings {0, 2}, {1, 4}, {6}, {5}, cannot be finished even by the exhaustive finishing of `lex.py`. E_lex holds
on gm4-B for every order. So beyond class D′ the total score is the wrong potential, and priority (§5, §9.2) is
needed.

### 9.4 Where this leaves the problem

- **Class D′:** an algorithm of DE's shape, Draft–Exchange–Demote. With the potential (total score, Ψ), its proof is
  written except for one concrete combinatorial step (§9.3): the exact alternations that leave Ψ unchanged, other than
  those of length 1 with a single free agent. Nothing in the data contradicts that step.
- **Class D:** a priority version with the same arcs, PDE-3, with no failure on the data, but its last step is a
  search.
- **All four-good agents:** E_sum fails (gm4-B), so the goal remains E_lex. §9.2 suggests what its moves look like:
  rings of want arcs, full arcs and demotions of lower-priority blockers.

## 10. Files and how to reproduce

Python 3, no packages. Each script prints a summary; the logs are copies of its output.

| file | what |
|---|---|
| `model.py` | instances, the raw definition of EFX₀, brute-force search, random core instances |
| `types4.py` | the twelve strict types of four-good core agents |
| `de4.py` | **DE₄**, the algorithm of Theorem 1, with every claim of the proof as an assert |
| `classc.py` | states, blockers, chains, finishing and the ring of the Improvement Lemma for class C (contains (S)) |
| `test_de4.py` | the tests of Theorem 1 and §3 (`test_de4.log`, about 15 s) |
| `states.py` | generic ladders and states, DE's finishing and liberal finishing |
| `ladder_test.py` | first survey: three fixed ladders on random instances (`ladder_test.log`) |
| `barrier.py`, `barrier_deep.py`, `barrier_dense.py` | the liberal-finishing searches of §4.2; they write `barrier_certs.json` (log of the last: `barrier_dense.log`) |
| `barrier_narrow.py` | the searches with DE's own finishing (valid absorbers) on the survivors (`barrier_narrow.log`, `barrier_narrow_dense.log`) |
| `tall_owners.py` | which owners finish the maximal states of three tall ladders (`tall_owners.log`) |
| `classc_random.py` | class C on random instances (`classc_random.log`) |
| `check_barrier.py` | the independent checker of the certificates (`check_barrier.log`) |
| `collision.py` | the example of §4.3 (`collision.log`) |
| `lex.py` | the threat ladder, validity (V1) + (V2), priority-maximal states, finishing |
| `lex_test.py` | E_lex on all data (`lex_test.log`; `lex_test_scale10.log` with ten times the random instances) |
| `der_test.py` | E_DER on all data (`der_test.log`) |
| `der.py` | DER: objects and one step (finish, grab, ring, release) |
| `der_check.py` | every DER step on every valid state of the test instances (`der_check.log`) |
| `der_run.py` | DER end to end, random instances up to n = 12 and the whole suite (`der_run.log`) |
| `nq_proof.py` | the proof attempt of §7 as code (Lemmas 5–8 asserted; the walk), and the finite check of Lemma 5 (`nq_proof.log`) |
| `gadgets.py` | the counterexample `collision12` of §7.2, its random variants, and E_lex on them (`gadgets.log`) |
| `pde_proof.py` | §9.2: class D with priority, the construction PDE-3 with every step asserted, and the variants PDE-1 and PDE-2 (`pde_proof.log`) |
| `sum_proof.py` | §9.3: class D′, Draft–Exchange–Demote's improvement step with every claim asserted, and the Ψ classification (`sum_proof.log`) |

    cd k4/de4
    python3 test_de4.py          # Theorem 1 and §3; exit status 0 iff all checks pass
    python3 check_barrier.py     # re-checks every certificate of §4
    python3 collision.py         # §4.3
    python3 lex_test.py 1 SUITE  # E_lex (§5); SUITE = path to k4/suite/instances of evanlin23/efx0-three-goods
    python3 der_test.py 1 SUITE  # E_DER (§5)
    python3 der_check.py 1 SUITE # every DER step (§6)
    python3 der_run.py 1 SUITE   # DER end to end (§6)
    python3 nq_proof.py          # §7.1: the finite check of Lemma 5, and the proof attempt on random (NQ) instances
    python3 gadgets.py           # §7.2-7.3: DER fails on collision12 and on variants; E_lex holds on all of them
    python3 pde_proof.py 1500 1 --variants   # §9.2 (a few minutes)
    python3 sum_proof.py 6000 1              # §9.3 (about five minutes)

The suite argument is optional; without it, the scripts skip that part.

To regenerate the certificates, run these in order, on 4 cores:

    python3 barrier.py 400 1                    # about 2.5 minutes
    python3 barrier_deep.py 4000 2              # about 3.5 minutes
    python3 barrier_dense.py 1500 3             # about an hour
    python3 barrier_narrow.py 1500 4            # about a minute
    python3 barrier_narrow.py 1000 5 --dense    # about 70 minutes

All searches are seeded and deterministic. Only the certificates and the check log are kept as the record, not the
console output of the first two searches.

All code and text here were written with an AI coding assistant (Claude Code), like the rest of this repository. There
has been no human review.
