# Four relevant goods: Draft and Exchange, and a candidate algorithm DER

Folder `k4/de4/`. An attempt at the first open problem of the paper (`paper/k3-simple/main.tex`, Section 6): does every
instance in which each agent positively values at most four goods have a complete EFX₀ allocation? The goal is a
clean algorithm in the style of Draft and Exchange (DE).

**Status.** The open problem is **not** solved: nothing below is a proof for all k = 4 instances. What is here:

- **DER, a candidate algorithm for every instance with at most four relevant goods** (§5–§6, evidence only, no proof).
  It is DE on a different ladder of holdings:
  - the **threat ladder**: singles, pairs with the top good, and the *threat sets* of the singles (k = 3's pair {b, c}
    is the threat set of a);
  - a validity condition that also asks the holdings to be a partial EFX₀ allocation;
  - DE's finishing rule, with any agent whose holding contains no wanted good as possible owner;
  - three moves: *grab* (DE's chain, generalized), *ring* (DE's rings, with general upgrade arrows) and, at a dead
    end, one *release*.

  It returned an EFX₀ allocation on every instance tried. That includes every instance of the research repository's
  k = 4 counterexample suite (159 instances, up to n = 26, m = 65, among them the chains H_t that defeat LB₄ʳ). From
  every valid state of about 2,400 test instances, about 32,000 states, its next step is correct. Two extremal
  statements behind it hold on all data:
  - **E_lex**: for every priority order of the agents, the lexicographically maximal valid state can be finished;
  - **E_DER**: every score-Pareto-maximal valid state can be finished, or can be after one agent steps down.
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
  its holdings. This is what forces DER's two departures from DE: the priority view and the release move.
- **An obstruction to value-monotone methods** (§4.3): a valid state with n = 4, m = 7 in which **every** EFX₀
  allocation gives some agent strictly less value than the state does. DER passes it with one release. The research
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

> **E_DER** (conjecture). Every score-Pareto-maximal valid state of the threat ladder can be finished, or can be after
> one agent moves to a lower rung (a *release*).

Evidence (`der_test.py`, `der_test.log`): 22,903 score-Pareto-maximal states. 22,842 can be finished directly; the
other 61 come from the suite and the certificates, and each needs one release. In the collision example, z drops d and
holds {C1}: it becomes free and can absorb the leftover good h.

## 6. DER: Draft, Exchange, Release

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

## 7. What this suggests

- **The small-d class is the reach of DE as it stands.** Within the natural ladders it is also the reach of any proof
  with DE's architecture (monotone trades, then one large bundle).
- **Two changes get past the barrier on all data.** The ladder must be built from threat sets, and the potential must
  allow a release (or, equivalently, use priority). The collision example shows that some agent must sometimes be
  lowered.
- **Next steps.**
  - Prove the Improvement Lemma for DER: in which states does each move apply, and why does a release always finish?
  - Replace the ring search by a σ-walk with a provable choice of blockers.
  - Test DER with ties and on larger structured families.

## 8. Files and how to reproduce

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

    cd k4/de4
    python3 test_de4.py          # Theorem 1 and §3; exit status 0 iff all checks pass
    python3 check_barrier.py     # re-checks every certificate of §4
    python3 collision.py         # §4.3
    python3 lex_test.py 1 SUITE  # E_lex (§5); SUITE = path to k4/suite/instances of evanlin23/efx0-three-goods
    python3 der_test.py 1 SUITE  # E_DER (§5)
    python3 der_check.py 1 SUITE # every DER step (§6)
    python3 der_run.py 1 SUITE   # DER end to end (§6)

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
