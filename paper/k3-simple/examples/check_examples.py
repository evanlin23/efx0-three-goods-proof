#!/usr/bin/env python3
"""Recompute every example and every computed number of paper/k3-simple/long.tex, and test its lemmas and algorithm DE.

    python3 paper/k3-simple/examples/check_examples.py          (from the repository root, or from anywhere)

Exit status 0 iff every check passes. One process, no pools; about a minute. check_output.txt (same folder) is a
copy of what this script prints.

This script implements the definitions of long.tex as now written (states and scores, wants, validity, free agents,
leftover goods, blockers, finishing and completions, want arrows and pair arrows, rings, chains) and algorithm DE
(Algorithm 1: peeling by rule R1, the draft, then the loop chain / finish / ring), written from the paper's text and
not from earlier code. Every claim of the proofs that DE relies on is an assert. Allocations are checked against the
raw definition of EFX0 with exact integer arithmetic. `k3/simplify/po/hall/hall.py`, an older implementation, is used
only for cross-checks of claims that are still the same: the improving step of the Improvement Lemma, and DE's output.

Sections (as printed):
  [1] Introduction: Example "EFX, but not EFX0"; three goods break serial dictatorship; Corollary "two relevant goods".
  [2] Section 6, "A small example" (also in main.tex): three agents, one ring with one pair arrow, then a completion.
  [3] Section 7 "A Worked Example" and Figure 1: the draft state, wants, free agents, blockers, the sets H_o, the ten
      candidate completions, no small trade, the four dominating valid states, the arrows and cycles, DE's ring and
      final allocation, raw EFX0 (values 4, 3, 2 and 2,000 random strictly balanced valuations with these rankings).
  [4] Appendix A, Proposition "when short moves are not enough": both instances, and the remark that two of the four
      cycles with two pair arrows reuse a leftover good.
  [5] Appendix A, "No bounded number of pair arrows suffices": the ring family for k <= 4 and depths d <= 3, and DE
      from the draft at depth 4 (Conclusion, open problem (2)).
  [6] Appendix B: Lemma "cases of safety" and Proposition "limits of the shape", by listing every allocation.
  [7] Every valid state of every core profile with n = 2 (m <= 6) and n = 3 (m <= 7), up to renaming goods: the
      draft (Lemma "the draft", every order), the finishing test, soundness (every completion), Lemma "ring" (every
      ring), the Improvement Lemma in the form of its proof, short moves (Proposition: none missing for n <= 5), and
      the loop of DE started at every valid state.
  [8] DE, peeling included, on random instances; comparison with the loop of the previous version of the paper and
      with hall.py.
"""
import traceback
import itertools
import os
import random
import sys
import time
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
HALL = os.path.join(ROOT, 'k3', 'simplify', 'po', 'hall')

FAILS = []
LOG = []


def out(s=''):
    print(s, flush=True)
    LOG.append(s)


def check(cond, msg):
    out(('  ok    ' if cond else '  FAIL  ') + msg)
    if not cond:
        FAILS.append(msg)


# ============================================================================================ raw definitions
def val(vi, S):
    return sum(vi.get(g, 0) for g in S)


def is_efx0(v, X):
    """EFX0 (Introduction): v_i(X_i) >= v_i(X_j minus h) for all i != j and every h in X_j. v[i]: dict good -> value
    (missing = 0); X: list of sets. Exact integer arithmetic."""
    n = len(X)
    own = [val(v[i], X[i]) for i in range(n)]
    for j in range(n):
        if len(X[j]) < 2:
            continue                                        # removing the only good leaves nothing
        for i in range(n):
            if i != j:
                vi = v[i]
                tot = val(vi, X[j])
                if tot - min(vi.get(g, 0) for g in X[j]) > own[i]:
                    return False
    return True


def is_efx(v, X):
    """EFX: only goods h with v_i(h) > 0 may be removed"""
    n = len(X)
    for i in range(n):
        own = val(v[i], X[i])
        for j in range(n):
            if j != i:
                tot = val(v[i], X[j])
                if any(v[i].get(h, 0) > 0 and tot - v[i][h] > own for h in X[j]):
                    return False
    return True


def is_complete(X, m):
    return sorted(g for B in X for g in B) == list(range(m))


def values_from_ranking(rank, trip=(4, 3, 2)):
    return [dict(zip(r, trip)) for r in rank]


# ============================================================================================ peeling (Section 2)
def favourite(vi, G):
    """the favourite good of G: largest value, ties by index"""
    return min(G, key=lambda g: (-vi.get(g, 0), g))


def rule_r1(vi, G):
    """Rule R1: the set P with which the agent may leave, or None if R1 does not apply"""
    if not G:
        return frozenset()
    p = favourite(vi, G)
    vp = vi.get(p, 0)
    if vp == 0:
        return frozenset()
    if val(vi, G) - vp <= vp:
        return frozenset([p])
    return None


def ranking(vi, G):
    """the relevant goods of G, by value, ties broken by index: a_i, b_i, c_i when there are three"""
    return sorted((g for g in G if vi.get(g, 0) > 0), key=lambda g: (-vi[g], g))


# ============================================================================================ states (Section 3)
# rank[i] = (a_i, b_i, c_i); a holding is a code: 0 nothing, 1 {a}, 2 {b}, 3 {c}, 4 the pair {b, c}
NOTHING, TOP, BB, CC, PAIR = 0, 1, 2, 3, 4
SCORE = (0, 3, 2, 1, 4)                     # Definition (states and scores)
HNAME = ('-', 'a', 'b', 'c', 'pair')


def held(r, h):
    return () if h == NOTHING else ((r[h - 1],) if h != PAIR else (r[1], r[2]))


def wants_of(r, h):
    """Definition (wants): an agent outside U wants every relevant good if it holds nothing, else the goods ranked
    above the good it holds; a pair holder wants nothing"""
    return tuple(r) if h == NOTHING else (() if h in (TOP, PAIR) else tuple(r[:h - 1]))


def is_state(rank, hold):
    gs = [g for i, h in enumerate(hold) for g in held(rank[i], h)]
    return len(gs) == len(set(gs))


def all_states(rank):
    """every state (holdings pairwise disjoint)"""
    n = len(rank)
    res, cur = [], [0] * n

    def rec(i, used):
        if i == n:
            res.append(tuple(cur))
            return
        for h in range(5):
            gs = held(rank[i], h)
            if not any(g in used for g in gs):
                cur[i] = h
                rec(i + 1, used | set(gs))
    rec(0, frozenset())
    return res


class State:
    def __init__(self, rank, m, hold):
        assert is_state(rank, hold)
        n = len(rank)
        self.rank, self.m, self.hold, self.n = rank, m, tuple(hold), n
        self.Y = [held(rank[i], hold[i]) for i in range(n)]
        self.holder = {g: i for i in range(n) for g in self.Y[i]}
        self.U = frozenset(i for i in range(n) if hold[i] == PAIR)
        self.J = frozenset(g for g in range(m) if g not in self.holder)            # leftover goods
        self.W = [wants_of(rank[i], hold[i]) for i in range(n)]
        self.wanted = frozenset(g for w in self.W for g in w)
        # valid: every good that some agent wants is held alone (it is the whole holding of some agent)
        self.valid = all(g in self.holder and len(self.Y[self.holder[g]]) == 1 for g in self.wanted)
        # free: outside U, holding nothing or a good nobody wants
        self.F = [i for i in range(n) if i not in self.U and (not self.Y[i] or self.Y[i][0] not in self.wanted)]
        self.Fset = frozenset(self.F)
        self._bl = {}

    def total(self):
        return sum(SCORE[h] for h in self.hold)

    def wanters(self, g):
        """the agents that want g, in index order"""
        return [j for j in range(self.n) if g in self.W[j]]

    def blockers(self, o):
        """Definition (blockers): x != o with Y_x = {a_x} and b_x, c_x in J + Y_o (o free)"""
        if o not in self._bl:
            assert o in self.Fset
            S = self.J | set(self.Y[o])
            self._bl[o] = [x for x in range(self.n) if x != o and self.hold[x] == TOP
                           and self.rank[x][1] in S and self.rank[x][2] in S]
        return self._bl[o]

    def can_finish_with(self, o, H):
        """Definition (finishing): H subset of J, |H| <= |F| - 1, H contains b_x or c_x for every blocker x of o"""
        H = set(H)
        return (o in self.Fset and H <= self.J and len(H) <= len(self.F) - 1
                and all(H & set(self.rank[x][1:]) for x in self.blockers(o)))

    def finish_sets(self, o):
        """every H with which o can finish, by brute force over the subsets of J (the definition, no lemma)"""
        res = []
        for size in range(0, min(len(self.F) - 1, len(self.J)) + 1):
            for H in itertools.combinations(sorted(self.J), size):
                if self.can_finish_with(o, H):
                    res.append(frozenset(H))
        return res

    def can_finish(self, o):
        """the definition, by brute force; goods of J outside every {b_x, c_x} never help, so only those are tried"""
        rel = sorted({g for x in self.blockers(o) for g in self.rank[x][1:] if g in self.J})
        for size in range(0, min(len(self.F) - 1, len(rel)) + 1):
            for H in itertools.combinations(rel, size):
                if self.can_finish_with(o, H):
                    return True
        return False

    def nc_violators(self):
        """agents x with Y_x = {a_x} and b_x, c_x in J: (NC) holds iff there is none"""
        return [x for x in range(self.n) if self.hold[x] == TOP and self.rank[x][1] in self.J
                and self.rank[x][2] in self.J]

    def leftover_goods(self, o):
        """Lemma (the finishing test) under (NC): returns H_o as a dict h_x -> the first blocker x with this leftover
        good; asserts (a) and (b)"""
        bl = self.blockers(o)
        if not self.Y[o]:
            assert not bl                                                         # (a)
            return {}
        y = self.Y[o][0]
        H = {}
        for x in bl:
            b, c = self.rank[x][1], self.rank[x][2]
            assert y in (b, c)                                                    # (b): the pair of x is {y_o, h_x}
            h = c if b == y else b
            assert h in self.J                                                    # (b): h_x is leftover
            H.setdefault(h, x)
        return H

    def arrow(self, s, t):
        """Definition (rings): the arrow s -> t between agents outside U holding a single good: ('want', y_s) if t wants
        y_s; ('pair', h) if s is free, t is a blocker of s and the pair of t is {y_s, h} with h leftover; else None"""
        if s == t or s in self.U or t in self.U or len(self.Y[s]) != 1 or len(self.Y[t]) != 1:
            return None
        y = self.Y[s][0]
        want = y in self.W[t]
        pair = None
        if s in self.Fset and t in self.blockers(s):
            b, c = self.rank[t][1], self.rank[t][2]
            if y in (b, c):
                h = c if b == y else b
                if h in self.J:
                    pair = h
        assert not (want and pair is not None)          # an arrow from a free agent is never a want arrow
        return ('want', y) if want else (('pair', pair) if pair is not None else None)

    def cycle_arrows(self, cyc):
        """the arrows of a cycle of distinct agents, or None if some step is not an arrow"""
        k = len(cyc)
        if k < 2 or len(set(cyc)) != k:
            return None
        arr = [self.arrow(cyc[t], cyc[(t + 1) % k]) for t in range(k)]
        return None if any(a is None for a in arr) else arr

    def ring_arrows(self, cyc):
        """Definition (rings): the arrows if cyc is a ring (pair arrows with pairwise distinct leftover goods)"""
        arr = self.cycle_arrows(cyc)
        if arr is None:
            return None
        hs = [a[1] for a in arr if a[0] == 'pair']
        return arr if len(hs) == len(set(hs)) else None

    def raw_trade(self, cyc, arr):
        """the holdings that trading along the cycle would give (without checking that they are disjoint)"""
        new = list(self.hold)
        k = len(cyc)
        for t, (kind, _) in enumerate(arr):
            w = cyc[(t + 1) % k]
            new[w] = PAIR if kind == 'pair' else self.rank[w].index(self.Y[cyc[t]][0]) + 1
        return tuple(new)

    def trade(self, cyc):
        """trading along a ring: w_{t+1} gets y_t, with h_{t+1} for a pair arrow (its pair)"""
        arr = self.ring_arrows(cyc)
        assert arr is not None, 'not a ring'
        return self.raw_trade(cyc, arr)

    def arrow_digraph(self):
        nodes = [i for i in range(self.n) if i not in self.U and len(self.Y[i]) == 1]
        arr = {}
        for s in nodes:
            for t in nodes:
                a = self.arrow(s, t)
                if a is not None:
                    arr[(s, t)] = a
        succ = {s: sorted(t for (s2, t) in arr if s2 == s) for s in nodes}
        return nodes, succ, arr


def completion(st, o, H, receivers=None):
    """Definition (finishing): each good of H to a different free agent other than o (by default, as in Algorithm 1:
    the goods of H in the given order -- for DE, H_o in the order of the goods' first blockers; a set is taken in
    index order -- to the free agents other than o in index order), o gets Y_o + (J - H), the others keep their
    holdings"""
    Hs = list(H) if isinstance(H, (list, tuple)) else sorted(H)
    others = [f for f in st.F if f != o]
    if receivers is None:
        receivers = others[:len(Hs)]
    assert len(receivers) == len(Hs) and len(set(receivers)) == len(Hs) and set(receivers) <= set(others)
    X = [set(y) for y in st.Y]
    for g, f in zip(Hs, receivers):
        X[f].add(g)
    X[o] |= st.J - set(Hs)
    return X


def shape_ok(X, o):
    return all(len(B) <= 2 for j, B in enumerate(X) if j != o)


def simple_cycles(nodes, succ):
    """every simple cycle of a small digraph, once each (listed from its smallest vertex)"""
    res = []
    for s in nodes:
        stack = [(s, [s])]
        while stack:
            u, path = stack.pop()
            for w in succ[u]:
                if w == s:
                    res.append(path)
                elif w > s and w not in path:
                    stack.append((w, path + [w]))
    return res


def cycles_and_rings(st):
    """every cycle of want and pair arrows, with its arrows; and the rings among them"""
    nodes, succ, arr = st.arrow_digraph()
    cycles = []
    for c in simple_cycles(nodes, succ):
        ca = [arr[(c[t], c[(t + 1) % len(c)])] for t in range(len(c))]
        cycles.append((c, ca))
    rings = [(c, ca) for c, ca in cycles if st.ring_arrows(c) is not None]
    return cycles, rings


def npair(arr):
    return sum(a[0] == 'pair' for a in arr)


def dominates(h2, h1):
    """Pareto domination in scores"""
    return (all(SCORE[a] >= SCORE[b] for a, b in zip(h2, h1))
            and any(SCORE[a] > SCORE[b] for a, b in zip(h2, h1)))


def assert_step(st, new, gainers):
    """the conclusion of Lemmas (ring) and (chain): a valid state, the agents `gainers` have a higher score, every other
    agent the same score"""
    assert is_state(st.rank, new)
    st2 = State(st.rank, st.m, new)
    assert st2.valid
    g = set(gainers)
    for i in range(st.n):
        assert (SCORE[new[i]] > SCORE[st.hold[i]]) if i in g else (new[i] == st.hold[i])
    assert st2.total() > st.total()
    return st2


# ============================================================================================ moves (Section 5)
def draft(rank, order=None):
    """Lemma (the draft): in the given order (default: index order) each agent takes the first of a, b, c not yet
    taken, or nothing"""
    taken, hold = set(), [NOTHING] * len(rank)
    for i in (range(len(rank)) if order is None else order):
        for h in (TOP, BB, CC):
            if rank[i][h - 1] not in taken:
                hold[i] = h
                taken.add(rank[i][h - 1])
                break
    return tuple(hold)


def chain(st, x):
    """Lemma (chain): j_0 = x; while j_t holds a good some agent wants, j_{t+1} = the first such agent. Returns
    ('ring', cycle, None) if an agent repeats (the agents from its first occurrence on), else ('chain', [j_0..j_k],
    new holdings): x takes its pair, j_t takes the good of j_{t-1}, the old good of j_k becomes leftover."""
    assert st.hold[x] == TOP and st.rank[x][1] in st.J and st.rank[x][2] in st.J
    path = [x]
    while len(st.Y[path[-1]]) == 1 and st.wanters(st.Y[path[-1]][0]):
        nxt = st.wanters(st.Y[path[-1]][0])[0]
        assert nxt != x                                  # x holds its top and wants nothing
        if nxt in path:
            return 'ring', path[path.index(nxt):], None
        path.append(nxt)
    new = list(st.hold)
    new[x] = PAIR
    for t in range(1, len(path)):
        new[path[t]] = st.rank[path[t]].index(st.Y[path[t - 1]][0]) + 1
    return 'chain', path, tuple(new)


def apply_chain(st, x):
    """Lemma (chain), with its conclusion asserted. Returns (kind, agents, new holdings)."""
    kind, seq, new = chain(st, x)
    if kind == 'ring':
        arr = st.ring_arrows(seq)
        assert arr is not None and all(a[0] == 'want' for a in arr)          # a ring of want arrows
        new = st.trade(seq)
    assert_step(st, new, seq)
    return kind, seq, new


def blocker_owners_ok(st):
    """Running time paragraph, under (NC): an agent holding only its top is a blocker of at most one free agent that
    holds a good"""
    cnt = Counter(x for o in st.F if st.Y[o] for x in st.blockers(o))
    return all(c <= 1 for c in cnt.values())


def Ho_of(st, x, o):
    """the leftover good h_x of a blocker x of o (Lemma (the finishing test)(b))"""
    b, c = st.rank[x][1], st.rank[x][2]
    return c if b == st.Y[o][0] else b


def proof_ring(st):
    """the ring of the proof of Theorem (Improvement Lemma), under (NC) when no free agent can finish: distinct
    leftover goods (free agents in index order; x_o the first blocker of o whose leftover good is not yet picked,
    q_o = h_{x_o}); sigma(j) = x_j for free j, else the first agent that wants the good of j; follow sigma from the
    first agent outside U until an agent repeats. Returns (q, x_o, sigma, cycle)."""
    f = len(st.F)
    q, xo = {}, {}
    for o in st.F:
        Ho = st.leftover_goods(o)
        assert st.Y[o] and len(Ho) >= f                  # Lemma (the finishing test): o holds a good, |H_o| >= |F|
        xo[o] = next(x for x in st.blockers(o) if Ho_of(st, x, o) not in q.values())
        q[o] = Ho_of(st, xo[o], o)
        assert Ho[q[o]] == xo[o]                         # x_o is also the first blocker with this leftover good
    sigma = {}
    for j in range(st.n):
        if j not in st.U:
            sigma[j] = xo[j] if j in st.Fset else st.wanters(st.Y[j][0])[0]
            assert sigma[j] not in st.U and sigma[j] != j
    start = min(sigma)
    path, seen = [start], {start}
    while sigma[path[-1]] not in seen:
        path.append(sigma[path[-1]])
        seen.add(path[-1])
    cyc = path[path.index(sigma[path[-1]]):]
    assert len(cyc) >= 2 and all(len(st.Y[w]) == 1 for w in cyc)
    arr = st.ring_arrows(cyc)
    assert arr is not None                                          # the cycle is a ring
    for t, w in enumerate(cyc):
        assert arr[t] == (('pair', q[w]) if w in st.Fset else ('want', st.Y[w][0]))
    return q, xo, sigma, cyc


def improvement(st, x=None):
    """the proof of Theorem (Improvement Lemma) for a valid state in which not every agent holds its pair and no free
    agent can finish: the chain of x (default: the first agent violating (NC)) if (NC) fails, else the ring of the
    proof. Asserts the conclusion. Returns (kind, agents, new holdings, number of pair arrows)."""
    viol = st.nc_violators()
    if viol:
        kind, seq, new = apply_chain(st, viol[0] if x is None else x)
        return kind, seq, new, (1 if kind == 'chain' else 0)
    q, xo, sigma, cyc = proof_ring(st)
    new = st.trade(cyc)
    assert_step(st, new, cyc)
    return 'ring', cyc, new, sum(1 for w in cyc if w in st.Fset)


# ============================================================================================ DE (Section 6)
def de_loop(rank, m, start=None, stats=None, old_finish=False):
    """the draft (or the valid state `start`) and the loop of Algorithm 1, then its last two lines. Returns
    (X, o, H, trace, final state); trace lists the trades. With old_finish (for comparison only): the loop of the
    previous version of the paper, in which the first free agent holding nothing finishes, with H = {}, before the
    count is tried; it breaks in the same states, so only the finishing agent can differ."""
    n = len(rank)
    hold = draft(rank) if start is None else tuple(start)
    if start is None:
        assert not State(rank, m, hold).U
    trace = []
    while True:
        st = State(rank, m, hold)
        assert st.valid
        viol = st.nc_violators()
        if viol:                                                                    # chain
            kind, seq, new = apply_chain(st, viol[0])
            trace.append(dict(kind='chain' if kind == 'chain' else 'ring of want arrows (chain walk)', seq=seq,
                              state=st, new=new))
        elif len(st.U) == n:                                                        # finish: every agent its pair
            o, H = 0, frozenset()
            break
        else:
            assert blocker_owners_ok(st)
            fin = None
            if old_finish and any(not st.Y[o] for o in st.F):
                fin = (next(o for o in st.F if not st.Y[o]), frozenset())
            for o in ([] if fin else st.F):                                         # finish: |H_o| <= |F| - 1
                Ho = st.leftover_goods(o)
                if len(Ho) <= len(st.F) - 1:
                    fin = (o, tuple(Ho))                                    # H_o in the order of first blockers
                    break
            if fin is not None:
                o, H = fin
                assert st.can_finish_with(o, H)                                     # Lemma (the finishing test)(c)
                break
            q, xo, sigma, cyc = proof_ring(st)                                      # ring
            new = st.trade(cyc)
            assert_step(st, new, cyc)
            trace.append(dict(kind='ring', seq=cyc, q=q, xo=xo, sigma=sigma, state=st, new=new,
                              npair=sum(1 for w in cyc if w in st.Fset)))
        hold = new
        assert len(trace) <= 4 * n                                                  # Theorem (DE is correct)
    X = completion(st, o, H)
    assert is_complete(X, m) and shape_ok(X, o)
    if stats is not None:
        for t in trace:
            stats[t['kind'] if t['kind'] != 'ring' else 'ring with %d pair arrow(s)' % t['npair']] += 1
        stats['finish: every agent holds its pair' if len(st.U) == n else
              ('finish: free agent holding nothing' if not st.Y[o] else 'finish: free agent holding a good')] += 1
    return X, o, H, trace, st


def de(v, n, m, stats=None, core=None):
    """Algorithm 1 on an instance: v[i] dict good -> value (missing = 0), every agent valuing at most three goods.
    Returns the allocation (list of sets). If `core` is a list and the loop is reached, a dict with the core's
    rankings, its agents A and goods, the core's allocation, the finishing agent and the trades is appended."""
    A, G = list(range(n)), set(range(m))
    X = [set() for _ in range(n)]
    peeled = 0
    while len(A) >= 2:                                                              # peeling
        for i in A:
            if len(ranking(v[i], G)) <= 2:
                assert rule_r1(v[i], G) is not None        # R1 applies to every agent valuing <= 2 remaining goods
        pick = next(((i, P) for i in A for P in [rule_r1(v[i], G)] if P is not None), None)
        if pick is None:
            break
        i, P = pick
        X[i] = set(P)
        A.remove(i)
        G -= P
        peeled += 1
    assert peeled <= n
    if stats is not None:
        stats['peeled agents'] += peeled
    if len(A) == 1:
        X[A[0]] = set(G)
        return X
    goods = sorted(G)
    idx = {g: k for k, g in enumerate(goods)}
    rank = []
    for i in A:
        rel = ranking(v[i], G)
        assert len(rel) == 3 and v[i][rel[0]] < v[i][rel[1]] + v[i][rel[2]]      # Lemma (when nobody can leave)
        rank.append(tuple(idx[g] for g in rel))
    Xc, o, H, trace, _ = de_loop(rank, len(goods), stats=stats)
    if stats is not None:
        stats['runs reaching the loop'] += 1
        stats['runs with a trade'] += bool(trace)
        stats['max trades'] = max(stats['max trades'], len(trace))
        stats['max trades / n'] = max(stats['max trades / n'], len(trace) / n)
    for k, i in enumerate(A):
        X[i] = {goods[g] for g in Xc[k]}
    if core is not None:
        core.append(dict(rank=rank, m=len(goods), A=A, goods=goods, Xc=Xc, X=X, o=o, trades=len(trace)))
    return X


def with_core(c, Xc):
    """the allocation of the whole instance with the core's bundles replaced by Xc"""
    X = [set(B) for B in c['X']]
    for k, i in enumerate(c['A']):
        X[i] = {c['goods'][g] for g in Xc[k]}
    return X


# ============================================================================================ [1]
def sec_intro():
    out('[1] Introduction: Example "EFX, but not EFX0"; serial dictatorship at three goods; Corollary "two relevant '
        'goods"')
    a, b, c = 0, 1, 2
    v = [{a: 3, b: 2}, {c: 1}]
    X = [{b}, {a, c}]
    check(is_efx(v, X) and val(v[0], {c}) == 0 <= 2 and val(v[1], {b}) == 0,
          'X1 = {b}, X2 = {a, c} is EFX: agent 1 may remove only a, {c} is worth 0 <= 2; agent 2 values {b} at 0')
    check(not is_efx0(v, X) and val(v[0], {a}) == 3 > val(v[0], X[0]) == 2,
          'it is not EFX0: removing c from X2 leaves {a}, worth 3 > 2 to agent 1')
    check(is_efx0(v, [{a}, {b, c}]), 'X1 = {a}, X2 = {b, c} is EFX0')
    v = [{0: 4, 1: 3, 2: 2}, {3: 1}]
    check(not is_efx0(v, [{0}, {1, 2, 3}]) and val(v[0], {1, 2}) == 5 > 4,
          'values 4, 3, 2 on a, b, c: the agent takes a, b and c end up with a third good; without it they are worth '
          '5 > 4')
    check(is_efx0(v, de(v, 2, 4)), 'DE on the same instance is EFX0 (the second agent is peeled first)')
    # Corollary (two relevant goods): serial dictatorship in any order, a favourite remaining good each (any one of
    # them if several), the last agent taking all remaining goods
    rng = random.Random(5)
    ok, K = True, 5000
    for _ in range(K):
        n = rng.randint(1, 7)
        m = rng.randint(0, 2 * n + 2)
        v = []
        for i in range(n):
            r = min(m, rng.choice([0, 1, 2, 2, 2]))
            v.append({g: rng.randint(1, 4) for g in rng.sample(range(m), r)})
        order = rng.sample(range(n), n)
        G, X = set(range(m)), [set() for _ in range(n)]
        for i in order[:-1]:
            if G:
                best = max(v[i].get(g, 0) for g in G)
                g = rng.choice(sorted(g for g in G if v[i].get(g, 0) == best))
                X[i] = {g}
                G.discard(g)
        X[order[-1]] = set(G)
        ok &= is_complete(X, m) and is_efx0(v, X)
    check(ok, f'Corollary (two relevant goods): serial dictatorship in random orders, with random choices among '
              f'favourites, on {K} random instances with |R_i| <= 2: every output EFX0')


# ============================================================================================ [2]
def sec_small():
    out('[2] Section 6, "A small example" (agents z, x, o in this index order; goods g0, g1, g2, g3, g4)')
    gn = ['g0', 'g1', 'g2', 'g3', 'g4']                       # the goods, numbered 0..4 in index order
    G0, G1, G2, G3, G5 = range(5)
    Z, XX, O = range(3)
    names = ['z', 'x', 'o']
    rank, m = [(G5, G0, G1), (G0, G1, G2), (G0, G5, G1)], 5
    v = values_from_ranking(rank)

    def gs(S):
        return '{' + ', '.join(gn[g] for g in sorted(S)) + '}'
    check(all(G3 not in vi for vi in v) and all(rule_r1(v[i], set(range(m))) is None for i in range(3)),
          'values 4, 3, 2, nobody values g3; rule R1 applies to nobody: nobody is peeled')
    D = draft(rank)
    st = State(rank, m, D)
    check(D == (TOP, TOP, CC) and st.Y == [(G5,), (G0,), (G1,)] and st.J == {G2, G3},
          'the draft: z takes g4, x takes g0, o takes g1; leftover goods g2, g3')
    check(set(st.W[O]) == {G0, G5} and not st.W[Z] and not st.W[XX] and st.valid and st.F == [O]
          and not st.nc_violators(), 'o wants g0 and g4, held alone: valid; o is the only free agent; no chain applies')
    Xc = completion(st, O, ())
    check(st.blockers(O) == [XX] and Xc[O] == {G1, G2, G3} and val(v[XX], Xc[O] - {G3}) == 5 > val(v[XX], Xc[XX]) == 4
          and not is_efx0(v, Xc), 'x is a blocker of o: if o took {g1, g2, g3}, x would remove g3 and see g1, g2, '
                                  'worth 5 > 4 (that completion is not EFX0)')
    check(st.leftover_goods(O) == {G2: XX} and len(st.F) - 1 == 0 and not st.can_finish(O),
          'x is o\'s only blocker; H_o = {g2}, no other free agent to take it: o cannot finish (definition, all H)')
    X, o, H, trace, fst = de_loop(rank, m)
    t = trace[0] if len(trace) == 1 else {}
    sg = t.get('sigma', {})
    check(t.get('kind') == 'ring' and sg == {O: XX, XX: O, Z: O} and st.arrow(O, XX) == ('pair', G2)
          and st.arrow(XX, O) == ('want', G0) and st.arrow(Z, O) == ('want', G5),
          'sigma(o) = x, a pair arrow (x\'s pair is o\'s g1 and the leftover g2); sigma(x) = sigma(z) = o, want '
          'arrows (o wants g0, g4)')
    check(t.get('seq') == [O, XX] and t.get('npair') == 1,
          'following sigma from z (the first agent outside U) closes the ring o -> x -> o')
    new = t.get('new')
    s2 = State(rank, m, new) if new else None
    check(new == (TOP, PAIR, TOP) and s2.Y[XX] == (G1, G2) and s2.Y[O] == (G0,),
          'the trade: x takes {g1, g2}, o takes g0')
    check(s2 is not None and not s2.wanted and s2.F == [Z, O] and s2.blockers(Z) == [] and o == Z and set(H) == set(),
          'then nobody wants anything, the free agents are z and o, z has no blocker: z finishes with H = {}')
    check(X == [{G5, G3}, {G1, G2}, {G0}] and is_efx0(v, X) and de(v, 3, m) == X,
          f'DE returns X_z = {gs(X[Z])}, X_x = {gs(X[XX])}, X_o = {gs(X[O])}: EFX0 (raw definition); the same with '
          f'peeling included')


# ============================================================================================ [3]
NAMES6 = ['x1', "x1'", 'x2', "x2'", 'o1', 'o2']
X1, X1P, X2, X2P, O1, O2 = range(6)
RANK6 = [(0, 4, 6), (1, 4, 7), (2, 5, 8), (3, 5, 9), (2, 3, 4), (0, 1, 5)]


def nm(i):
    return NAMES6[i]


def sec_worked():
    out('[3] Section 7 "A Worked Example" (goods g0..g9; agents x1, x1\', x2, x2\', o1, o2 in this index order)')
    rank, m = RANK6, 10
    v = values_from_ranking(rank)
    check(all(rule_r1(v[i], set(range(m))) is None for i in range(6)) and all(4 < 3 + 2 for _ in rank),
          'values 4, 3, 2: strictly balanced, rule R1 applies to nobody, so nobody is peeled')
    D = draft(rank)
    check(D == (TOP, TOP, TOP, TOP, CC, CC),
          'the draft: the four x\'s take their tops, o1 takes g4 (its c), o2 takes g5 (its c)')
    st = State(rank, m, D)
    check([set(w) for w in st.W] == [set(), set(), set(), set(), {2, 3}, {0, 1}] and st.valid
          and all(len(st.Y[st.holder[g]]) == 1 for g in st.wanted),
          'o1 wants g2, g3; o2 wants g0, g1; the x\'s want nothing; the four wanted goods are held alone (valid)')
    check(st.J == {6, 7, 8, 9} and st.F == [O1, O2] and not st.U, 'leftover goods g6..g9; free agents o1, o2')
    check(not st.nc_violators() and all(st.holder[rank[x][1]] in (O1, O2) for x in (X1, X1P, X2, X2P)),
          'no chain applies: the b of each x is held by o1 or o2')
    H1, H2 = st.leftover_goods(O1), st.leftover_goods(O2)
    check(st.blockers(O1) == [X1, X1P] and {rank[X1][1], rank[X1][2]} == {4, 6} and {rank[X1P][1], rank[X1P][2]}
          == {4, 7} and H1 == {6: X1, 7: X1P}, 'blockers of o1: x1 (pair {g4, g6}), x1\' (pair {g4, g7}); '
          'H_o1 = {g6, g7}')
    check(st.blockers(O2) == [X2, X2P] and H2 == {8: X2, 9: X2P}, 'blockers of o2: x2, x2\'; H_o2 = {g8, g9}')
    check(len(H1) == len(H2) == 2 > len(st.F) - 1 and not st.can_finish(O1) and not st.can_finish(O2),
          '|H_o| = 2 > |F| - 1 for both: nobody can finish (also by the definition, all H)')
    check([f for f in st.F if f != O1] == [O2], 'if o1 takes the leftovers, only o2 can take one of g6, g7')
    X = completion(st, O1, {6})
    check(X[O1] == {4, 7, 8, 9} and val(v[X1P], X[X1P]) == 4 and val(v[X1P], X[O1] - {8}) == 3 + 2,
          'with H = {g6}: X_o1 = {g4, g7, g8, g9}; x1\', holding g1 (worth 4), values X_o1 without g8 at 3 + 2 = 5')
    comps = [completion(st, o, H) for o in st.F for H in [()] + [(h,) for h in sorted(st.J)]]
    check(len(comps) == 10 and all(is_complete(X, m) and not is_efx0(v, X) for X in comps),
          'all ten candidate completions (finisher o1 or o2, H empty or one leftover good) fail the EFX0 test')
    # arrows and cycles (Figure 1)
    nodes, succ, arr = st.arrow_digraph()
    fig = {(O1, X1): ('pair', 6), (O1, X1P): ('pair', 7), (O2, X2): ('pair', 8), (O2, X2P): ('pair', 9),
           (X1, O2): ('want', 0), (X1P, O2): ('want', 1), (X2, O1): ('want', 2), (X2P, O1): ('want', 3)}
    check(arr == fig, 'Figure 1: the arrows are exactly the pair arrows o1 -> x1 (g6), o1 -> x1\' (g7), o2 -> x2 '
                      '(g8), o2 -> x2\' (g9) and the want arrows x1 -> o2 (g0), x1\' -> o2 (g1), x2 -> o1 (g2), '
                      'x2\' -> o1 (g3)')
    check(not st.wanters(4) and not st.wanters(5),
          'no ring of want arrows: it would have to leave o1 or o2 by a want arrow, but nobody wants g4 or g5')
    check(succ[X1] == succ[X1P] == [O2] and all(arr[(O2, t)][0] == 'pair' for t in succ[O2]),
          'x1 and x1\' have want arrows only to o2, and the arrows from o2 are pair arrows')
    cycles, rings = cycles_and_rings(st)
    check(len(cycles) == 4 and all(len(c) == 4 and npair(ca) == 2 for c, ca in cycles) and len(rings) == 4,
          'every cycle of these arrows has four agents and two pair arrows (4 cycles, all rings)')
    check(not st.nc_violators() and not [r for r in rings if npair(r[1]) <= 1],
          'no short move: no chain, no ring with at most one pair arrow')
    dom = [s for s in all_states(rank) if dominates(s, D) and State(rank, m, s).valid]
    check(len(dom) == 4 and all(sum(h == PAIR for h in s) == 2 for s in dom),
          f'exactly four valid states Pareto-dominate the draft state (found {len(dom)}), each gives pairs to two '
          f'agents')
    for s in sorted(dom):
        out('        dominating: ' + ', '.join(f'{nm(i)}:{HNAME[h]}' for i, h in enumerate(s)))
    # DE
    X, o, H, trace, fst = de_loop(rank, m)
    t = trace[0] if trace else {}
    check(len(trace) == 1 and t['kind'] == 'ring' and t['q'] == {O1: 6, O2: 8} and t['xo'] == {O1: X1, O2: X2},
          'DE picks q_o1 = g6 (blocker x1), then q_o2 = g8 (blocker x2)')
    sg = t.get('sigma', {})
    check(sg.get(O1) == X1 and sg.get(X1) == O2 and sg.get(O2) == X2 and sg.get(X2) == O1,
          'sigma(o1) = x1, sigma(x1) = o2 (o2 wants g0), sigma(o2) = x2, sigma(x2) = o1 (o1 wants g2)')
    cyc = t.get('seq', [])
    rot = cyc[cyc.index(O1):] + cyc[:cyc.index(O1)] if O1 in cyc else []
    check(rot == [O1, X1, O2, X2], f'the ring o1 -> x1 -> o2 -> x2 -> o1 of Figure 1 (walk from x1: '
                                   f'{" -> ".join(nm(w) for w in cyc)})')
    new = t.get('new')
    check(new == (PAIR, TOP, PAIR, TOP, TOP, TOP) and State(rank, m, new).Y[O2] == (0,)
          and State(rank, m, new).Y[O1] == (2,),
          'along it x1 takes {g4, g6}, o2 takes g0, x2 takes {g5, g8}, o1 takes g2 (table: after the trade)')
    check(st.total() == 14 and State(rank, m, new).total() == 20, 'the total score rises from 14 to 20')
    s2 = State(rank, m, new)
    check(s2.valid and not s2.wanted and s2.J == {7, 9} and s2.F == [X1P, X2P, O1, O2],
          'then nobody wants anything; leftover goods g7, g9; free agents x1\', x2\', o1, o2')
    check(not s2.nc_violators() and s2.holder[rank[X1P][1]] == X1 and s2.holder[rank[X2P][1]] == X2,
          'no chain applies (b of x1\' is g4, now held by x1; b of x2\' is g5, held by x2)')
    tops = [x for x in range(6) if s2.hold[x] == TOP and x != X1P]
    check(s2.blockers(X1P) == [] and not any(set(rank[x][1:]) <= {1, 7, 9} for x in tops),
          'x1\', the first free agent, has no blocker: no other agent holding its top has b, c in {g1, g7, g9}')
    check(o == X1P and set(H) == set(), 'x1\' finishes with H = {}')
    want = [{4, 6}, {1, 7, 9}, {5, 8}, {3}, {2}, {0}]
    check(X == want, 'DE returns x1 {g4, g6}, x1\' {g1, g7, g9}, x2 {g5, g8}, x2\' {g3}, o1 {g2}, o2 {g0}')
    worth = {nm(i): val(v[i], X[X1P]) for i in range(6) if i != X1P}
    two = max(val(v[i], X[j] - {h}) for j in range(6) if len(X[j]) == 2 for i in range(6) if i != j for h in X[j])
    check(worth == {'x1': 0, 'x2': 0, "x2'": 2, 'o1': 0, 'o2': 3} and val(v[O2], X[O2]) == 4
          and val(v[X2P], X[X2P]) == 4 and two == 3 and min(val(v[i], X[i]) for i in range(6)) >= 3,
          f'directly: X_x1\' is worth 3 to o2 (holding 4), 2 to x2\' (holding 4), 0 to the others; a two-good bundle '
          f'minus a good is worth at most {two} to any other agent; every agent holds at least '
          f'{min(val(v[i], X[i]) for i in range(6))} >= 3')
    check(is_efx0(v, X) and sum(len(B) > 2 for B in X) == 1, 'the output is EFX0 (raw definition, values 4, 3, 2), '
                                                             'one bundle of more than two goods')
    rng = random.Random(1)
    same, efx = 0, 0
    K = 2000
    for _ in range(K):
        vv = []
        for r in rank:
            c = rng.randint(1, 20)
            b = rng.randint(c, 20)
            a = rng.randint(b, b + c - 1)
            vv.append({r[0]: a, r[1]: b, r[2]: c})
        assert [tuple(ranking(vi, range(m))) for vi in vv] == rank       # consistent with the rankings
        core = []
        XX = de(vv, 6, m, core=core)
        same += (len(core) == 1 and core[0]['A'] == list(range(6)) and core[0]['trades'] == 1 and XX == want)
        efx += is_efx0(vv, XX)
    check(same == K and efx == K, f'{K} random strictly balanced valuations with these rankings (ties allowed): DE '
                                  f'peels nobody and makes the same run (one trade, the same output), EFX0 (raw)')


# ============================================================================================ [4]
def short_move(st):
    """a chain applies, or a ring with at most one pair arrow exists"""
    if st.nc_violators():
        return True
    _, rings = cycles_and_rings(st)
    return any(npair(ca) <= 1 for _, ca in rings)


def hypothesis(st):
    """valid, not every agent holds its pair, no free agent can finish (by the definition)"""
    return st.valid and len(st.U) < st.n and not any(st.can_finish(o) for o in st.F)


def sec_short():
    out('[4] Appendix A, Proposition "when short moves are not enough"')
    rank, m = RANK6, 10
    st = State(rank, m, draft(rank))
    check(hypothesis(st) and not short_move(st) and len(st.F) == 2 and st.n == 6 and m == 10,
          'the draft state of Section 7: valid, not all pairs, nobody can finish, no short move; |F| = 2, n = 6 '
          '(m = 10)')
    # the m = 8 instance; agents in the order the paper lists them
    names = ['o1', 'o2', 'x1', "x1'", 'x2', "x2'"]
    o1, o2, x1, x1p, x2, x2p = range(6)
    rank = [(4, 5, 0), (6, 7, 1), (4, 1, 2), (5, 3, 1), (6, 0, 2), (7, 3, 0)]
    m, S = 8, (CC, CC, TOP, TOP, TOP, TOP)
    st = State(rank, m, S)
    check(st.Y[o1] == (0,) and st.Y[o2] == (1,) and st.valid, 'm = 8: o1 holds g0, o2 holds g1, every x its top; '
                                                              'a valid state')
    check(st.J == {2, 3} and st.F == [o1, o2], 'J = {g2, g3}, F = {o1, o2}')
    check(not st.nc_violators() and st.blockers(o2) == [x1, x1p] and st.leftover_goods(o2) == {2: x1, 3: x1p},
          'blockers of o2: x1, x1\' (leftover goods g2, g3)')
    check(st.blockers(o1) == [x2, x2p] and st.leftover_goods(o1) == {2: x2, 3: x2p},
          'blockers of o1: x2, x2\' (leftover goods g2, g3)')
    check(hypothesis(st) and not short_move(st) and st.n == 6 and m == 8,
          'nobody can finish and no short move applies: the bounds n = 6, m = 8 are attained')
    cycles, rings = cycles_and_rings(st)
    form = all(len(c) == 4 and npair(ca) == 2 and (c[0], c[2]) == (o1, o2) for c, ca in cycles)
    reuse = [(c, ca) for c, ca in cycles if st.ring_arrows(c) is None]
    gives_twice = True
    for c, ca in reuse:
        hs = [a[1] for a in ca if a[0] == 'pair']
        new = st.raw_trade(c, ca)
        owners = [i for i in range(6) if hs[0] in held(rank[i], new[i])]
        gives_twice &= len(set(hs)) == 1 and not is_state(rank, new) and len(owners) == 2
    ring_ok = True
    for c, ca in rings:
        new = st.trade(c)
        st2 = State(rank, m, new)
        ring_ok &= st2.valid and dominates(new, S) and sum(h == PAIR for h in new) == 2
    check(len(cycles) == 4 and form and len(reuse) == 2 and gives_twice and len(rings) == 2 and ring_ok,
          'remark: the cycles of arrows are the four o2 -> x -> o1 -> x\' -> o2 with two pair arrows; two use the '
          'same leftover good twice (trading would give it to two agents), the other two are rings (each trade: a '
          'valid state, two new pairs)')
    for c, ca in cycles:
        out('        cycle ' + ' -> '.join(f'{names[c[t]]} -[{ca[t][0]} g{ca[t][1]}]' for t in range(4)) + ' -> '
            + names[c[0]] + ('' if st.ring_arrows(c) else '   (reuses a leftover good: not a ring)'))
    X, o, H, trace, _ = de_loop(rank, m, start=S)
    v = values_from_ranking(rank)
    check(len(trace) == 1 and trace[0]['kind'] == 'ring' and trace[0]['npair'] == 2 and is_efx0(v, X),
          f'DE\'s loop started at this state: one ring with two pair arrows, then {names[o]} finishes; EFX0')
    X, o, H, trace, _ = de_loop(rank, m)
    check(is_efx0(v, X), f'DE from the draft on this instance: {len(trace)} trade(s), EFX0')


# ============================================================================================ [5]
def ring_family(k, d, shared):
    """Appendix A, 'No bounded number of pair arrows suffices' (as gen_tree of k3/simplify/po/potential/
    test_exchange.py): agents 0..k-1 are o_0..o_{k-1}, each holding its c and wanting the goods of the two roots of a
    binary tree (o_i and the tree have depth d); inner agents hold their c and want their children's goods; the 2^d
    leaves of the tree of o_{i+1} hold their tops and have b, c = the good of o_i and a leftover good (private, or
    leaf s takes the pool good s mod k of a pool of k goods shared by the trees). Returns (rank, holdings, m, parent,
    leaves)."""
    rank, hold, parent = [None] * k, [CC] * k, [None] * k
    g = itertools.count()
    own = [next(g) for _ in range(k)]
    pool = [next(g) for _ in range(k)] if shared else None
    leaves = {i: [] for i in range(k)}

    def build(i, depth, par):
        idx = len(rank)
        rank.append(None)
        hold.append(None)
        parent.append(par)
        if depth == 0:
            top = next(g)
            leaves[i].append(idx)
            hold[idx] = TOP
            rank[idx] = (top,)
            return top
        lft = build(i, depth - 1, idx)
        rgt = build(i, depth - 1, idx)
        c = next(g)
        rank[idx] = (lft, rgt, c)
        hold[idx] = CC
        return c
    for i in range(k):
        lft = build(i, d - 1, i)
        rgt = build(i, d - 1, i)
        rank[i] = (lft, rgt, own[i])
    for i in range(k):
        o = (i - 1) % k                                  # the leaves of the tree of o_i are blockers of o_{i-1}
        for s, idx in enumerate(leaves[i]):
            h = pool[s % k] if shared else next(g)
            top = rank[idx][0]
            rank[idx] = (top, own[o], h) if s % 2 == 0 else (top, h, own[o])
    return rank, tuple(hold), next(g), parent, leaves


def sec_rings():
    out('[5] Appendix A, the ring family: k free agents, trees of depth d (values 4, 3, 2)')
    for k in (2, 3, 4):
        for d in (1, 2, 3):
            for shared in (False, True):
                rank, hold, m, parent, leaves = ring_family(k, d, shared)
                n = len(rank)
                st = State(rank, m, hold)
                v = values_from_ranking(rank)
                ok = all(len(set(r)) == 3 for r in rank) and st.valid and not st.U and st.F == list(range(k))
                children = {j: [c for c in range(n) if parent[c] == j] for j in range(n)}
                ok &= all(set(st.W[j]) == {st.Y[c][0] for c in children[j]} for j in range(n) if children[j])
                ok &= all(len(leaves[i]) == 2 ** d for i in range(k))
                ok &= all(st.blockers(i) == sorted(leaves[(i + 1) % k]) for i in range(k))
                nofinish = not any(st.can_finish(o) for o in st.F)
                ok_iff = nofinish == (k <= 2 ** d)
                cycles, rings = cycles_and_rings(st)
                ok_k = bool(cycles) and all(npair(ca) == k for _, ca in cycles)
                X, o, H, trace, _ = de_loop(rank, m, start=hold)
                if k <= 2 ** d:
                    ok_de = (len(trace) >= 1 and trace[0]['kind'] == 'ring' and trace[0]['npair'] == k)
                else:
                    ok_de = not trace
                ok_de &= is_efx0(v, X) and shape_ok(X, o)
                Xd, od, Hd, trd, _ = de_loop(rank, m)
                ok_de &= is_efx0(v, Xd)
                check(ok and ok_iff and ok_k and ok_de,
                      f'k={k} d={d} {"shared" if shared else "private"} leftover goods: n={n} m={m}; valid, F = '
                      f'{{o_0..o_{k - 1}}}, the 2^d = {2 ** d} leaves of tree i+1 are the blockers of o_i; no free agent '
                      f'can finish: {nofinish} (k <= 2^d: {k <= 2 ** d}); {len(cycles)} cycles, all with {k} pair '
                      f'arrows, {len(rings)} rings; DE\'s loop from this state: {len(trace)} trade(s)'
                      + (f' (the first a ring with {k} pair arrows)' if trace else '')
                      + f', EFX0; DE from the draft: {len(trd)} trade(s), EFX0')
    res = {}
    for k in (2, 3, 4):
        rank, hold, m, parent, leaves = ring_family(k, 4, False)
        X, o, H, trace, _ = de_loop(rank, m)
        res[k] = len(trace)
        assert is_efx0(values_from_ranking(rank), X)
    check(max(res.values()) > 8, 'Conclusion (2), "on the rings of Appendix A many more [trades than 8]": DE from the '
                                 'draft on the family with d = 4 (private leftover goods) makes '
                                 + ', '.join(f'{t} trades for k = {k} (n = {k * 31})' for k, t in res.items())
                                 + '; outputs EFX0')


# ============================================================================================ [6]
def theta(vi, B):
    return max((val(vi, B) - vi.get(h, 0) for h in B), default=0) if len(B) else 0


def safety_cases(rank_i, X, i):
    """Lemma (cases of safety): the cases (T), (BC), (B), (C), (E) that hold for agent i"""
    a, b, c = rank_i
    where = {g: j for j, B in enumerate(X) for g in B}

    def alone(g):
        return len(X[where[g]]) == 1
    Xi = X[i]
    cs = set()
    if a in Xi and (b in Xi or c in Xi or not (where[b] == where[c] and len(X[where[b]]) >= 3)):
        cs.add('T')
    if b in Xi and c in Xi:
        cs.add('BC')
    if b in Xi and alone(a):
        cs.add('B')
    if c in Xi and alone(a) and alone(b):
        cs.add('C')
    if alone(a) and alone(b) and alone(c):
        cs.add('E')
    return cs


def safe(vi, X, i):
    return all(val(vi, X[i]) >= theta(vi, X[j]) for j in range(len(X)) if j != i)


def all_allocations(n, m):
    for a in itertools.product(range(n), repeat=m):
        X = [set() for _ in range(n)]
        for g, i in enumerate(a):
            X[i].add(g)
        yield X


def sec_limits():
    out('[6] Appendix B: Lemma "cases of safety" and Proposition "limits of the shape", by listing every allocation')
    trips = [(4, 3, 2), (5, 4, 3), (10, 9, 2), (7, 5, 3)]      # v(a) > v(b) > v(c) > 0, v(a) < v(b) + v(c)
    for t in trips:
        vi = dict(zip((0, 1, 2), t))                            # agent 0 values a, b, c = g0, g1, g2; g3..g5 at 0
        ok_th = all((theta(vi, B) == 0 if len(B) <= 1 else True) and theta(vi, B) <= val(vi, B)
                    and (theta(vi, B) == val(vi, B) if set(B) - {0, 1, 2} else True)
                    and (theta(vi, B) == max(vi.get(g, 0) for g in B) if len(B) == 2 else True)
                    for r in range(7) for B in itertools.combinations(range(6), r))
        cnt = 0
        ok = True
        for X in all_allocations(4, 6):
            ok &= safe(vi, X, 0) == bool(safety_cases((0, 1, 2), X, 0))
            cnt += 1
        check(ok and ok_th, f'values {t}: the facts on theta for every bundle of 6 goods; safe iff (T), (BC), (B), '
                            f'(C) or (E) in all {cnt} allocations of a, b, c and 3 other goods to 4 bundles')
    rank = [(0, 1, 2), (0, 1, 3), (0, 1, 4)]                    # (a): g0 = 0, g1 = 1, p_i = 2 + i
    for t in trips:
        v = values_from_ranking(rank, t)
        efx = [X for X in all_allocations(3, 5) if is_efx0(v, X)]
        small = [X for X in efx if max(len(B) for B in X) <= 2]
        ok = True
        for perm in itertools.permutations(range(3)):           # perm[j]: the agent holding bundle j
            X = [None] * 3
            for j, B in enumerate([{0}, {1}, {2, 3, 4}]):
                X[perm[j]] = B
            ok &= is_efx0(v, X) and all(cs in safety_cases(rank[perm[j]], X, perm[j])
                                        for j, cs in enumerate(['T', 'B', 'C']))
        check(efx and not small and ok, f'(a) values {t}: {len(efx)} EFX0 allocations, none with all bundles of at '
                                        f'most two goods; {{g0}}, {{g1}}, {{p0, p1, p2}} is EFX0 in every order, with '
                                        f'the agents in cases (T), (B), (C)')
    rank = [(0, 2, 3), (0, 2, 4), (1, 2, 5), (1, 2, 6)]        # (b): g0, g1, g2 = 0, 1, 2; p_i = 3 + i
    for t in trips:
        v = values_from_ranking(rank, t)
        efx = [X for X in all_allocations(4, 7) if is_efx0(v, X)]
        shapes = {tuple(sorted(len(B) for B in X)) for X in efx}
        Xs = [{0}, {2}, {1}, {3, 4, 5, 6}]
        cases = [safety_cases(rank[i], Xs, i) for i in range(4)]
        check(efx and shapes == {(1, 1, 1, 4)} and is_efx0(v, Xs)
              and all(c in cs for c, cs in zip(['T', 'B', 'T', 'C'], cases)),
              f'(b) values {t}: {len(efx)} EFX0 allocations, every one of sizes 4, 1, 1, 1; the stated one is EFX0, '
              f'cases T, B, T, C')


# ============================================================================================ [7]
def canonical_profiles(n):
    """the rankings of n agents (each an ordered triple of distinct goods), one per orbit under renaming the goods:
    goods are numbered in order of first appearance (agent 0 ranks g0 > g1 > g2). Yields (rank, number of goods used)."""
    def triples(used):
        res = []

        def rec(t, nxt):
            if len(t) == 3:
                res.append(tuple(t))
                return
            for g in range(used):
                if g not in t:
                    rec(t + [g], nxt)
            rec(t + [nxt], nxt + 1)
        rec([], used)
        return res

    def rec(rank, used):
        if len(rank) == n:
            yield list(rank), used
            return
        for t in triples(used):
            yield from rec(rank + [t], max(used, max(t) + 1))
    yield from rec([(0, 1, 2)], 3)


def check_state(st, v, cnt, hall):
    """every claim of Sections 4 and 5 on one state (asserts)"""
    n = st.n
    nc = not st.nc_violators()
    allpairs = len(st.U) == n
    fin = {o: st.finish_sets(o) for o in st.F}
    if not nc and not blocker_owners_ok(st):
        cnt['without (NC): a top holder blocks two free agents holding goods'] += 1
    if nc:                                                                  # Lemma (the finishing test)
        cnt['valid states with (NC)'] += 1
        assert blocker_owners_ok(st)                                        # running time paragraph
        for o in st.F:
            Ho = st.leftover_goods(o)                                       # (a), (b)
            lim = len(st.F) - 1
            rest = sorted(st.J - set(Ho))
            expect = {frozenset(Ho) | frozenset(E) for r in range(0, max(lim - len(Ho), -1) + 1)
                      for E in itertools.combinations(rest, r)}
            assert set(fin[o]) == expect                                    # (c): H_o <= H <= J, |H| <= |F| - 1
            assert bool(fin[o]) == (len(Ho) <= lim)
            if fin[o]:
                assert frozenset(Ho) in fin[o]
            if not st.Y[o]:
                assert fin[o]                                               # a free agent holding nothing can finish
    for o in st.F:                                                          # Theorem (soundness)
        others = [f for f in st.F if f != o]
        for H in fin[o]:
            for recv in itertools.permutations(others, len(H)):
                X = completion(st, o, H, recv)
                assert is_complete(X, st.m) and shape_ok(X, o) and is_efx0(v, X), (st.rank, st.hold, o, H, recv)
                cnt['completions (free agent that can finish)'] += 1
    if allpairs:
        for o in range(n):
            X = completion(st, o, ())
            assert is_complete(X, st.m) and shape_ok(X, o) and is_efx0(v, X)
            cnt['completions (every agent holds its pair)'] += 1
    cycles, rings = cycles_and_rings(st)                                    # Lemma (ring), every ring
    for c, ca in rings:
        assert_step(st, st.trade(c), c)
        cnt['rings traded (Lemma ring)'] += 1
    if allpairs or any(fin.values()):
        return
    cnt['states: not all pairs, no free agent can finish'] += 1             # Theorem (Improvement Lemma)
    if not nc:
        for x in st.nc_violators():                                         # Lemma (chain), for every such x
            kind, seq, new = apply_chain(st, x)
            cnt['  (NC) fails: chain of x (every x violating (NC))' if kind == 'chain' else
                '  (NC) fails: the walk from x (every x violating (NC)) closes a ring of want arrows'] += 1
    kind, seq, new, k = improvement(st)                                     # DE's step: first x, or the ring
    if nc:
        cnt[f'  (NC) holds: the ring of the proof, {k} pair arrow(s)'] += 1
    h2, hk = hall.improve(st.rank, st.m, st.hold)
    cnt['  same new state as hall.improve()'] += (h2 == new)
    cnt['  no short move (Proposition: impossible for n <= 5)'] += not (
        not nc or any(npair(ca) <= 1 for _, ca in rings))


def check_de_from(st, v, cnt):
    """the loop of DE started at a valid state (the proof of Theorem (DE is correct) starts from any valid state)"""
    X, o, H, trace, _ = de_loop(st.rank, st.m, start=st.hold)
    assert is_complete(X, st.m) and shape_ok(X, o) and is_efx0(v, X) and len(trace) <= 4 * st.n
    cnt['DE loops from a valid state'] += 1
    cnt['DE loops: trades'] += len(trace)
    cnt['DE loops: max trades'] = max(cnt['DE loops: max trades'], len(trace))


def sec_exhaustive():
    out('[7] Every valid state of every core profile, n = 2 (m <= 6) and n = 3 (m <= 7), up to renaming goods '
        '(values 4, 3, 2)')
    sys.path.insert(0, HALL)
    import hall
    for n, M in ((2, 6), (3, 7)):
        cnt = Counter()
        for rank, u in canonical_profiles(n):
            if u > M:
                continue
            for order in itertools.permutations(range(n)):                   # Lemma (the draft), every order
                s = State(rank, u, draft(rank, order))
                assert s.valid and not s.U
            v = values_from_ranking(rank)
            states = all_states(rank)
            for m in range(max(3, u), M + 1):
                cnt['profiles (with m goods)'] += 1
                for hold in states:
                    st = State(rank, m, hold)
                    cnt['states'] += 1
                    if not st.nc_violators() and not st.valid:              # the finishing test needs no validity
                        for o in st.F:
                            Ho = st.leftover_goods(o)
                            assert set(st.finish_sets(o)) == {
                                frozenset(Ho) | frozenset(E)
                                for r in range(0, max(len(st.F) - 1 - len(Ho), -1) + 1)
                                for E in itertools.combinations(sorted(st.J - set(Ho)), r)}
                        cnt['invalid states with (NC): finishing test'] += 1
                    if not st.valid:
                        continue
                    cnt['valid states'] += 1
                    check_state(st, v, cnt, hall)
                    check_de_from(st, v, cnt)
        hyp = cnt['states: not all pairs, no free agent can finish']
        check(cnt['  same new state as hall.improve()'] == hyp and cnt['  no short move (Proposition: impossible '
                                                                          'for n <= 5)'] == 0,
              f'n = {n}, m <= {M}: {cnt["profiles (with m goods)"]} profiles, {cnt["states"]} states, '
              f'{cnt["valid states"]} valid; finishing test on {cnt["valid states with (NC)"]} valid and '
              f'{cnt["invalid states with (NC): finishing test"]} invalid states with (NC) (and the running-time '
              f'remark: an agent holding only its top blocks at most one free agent holding a good; it fails in '
              f'{cnt["without (NC): a top holder blocks two free agents holding goods"]} valid states without (NC), '
              f'where DE does not use it); soundness on '
              f'{cnt["completions (free agent that can finish)"]} + {cnt["completions (every agent holds its pair)"]} '
              f'completions; Lemma ring on {cnt["rings traded (Lemma ring)"]} rings; Improvement Lemma on {hyp} '
              f'states; hall.improve() gives the same new state on {cnt["  same new state as hall.improve()"]}; '
              f'states with no short move: {cnt["  no short move (Proposition: impossible for n <= 5)"]}; DE\'s loop '
              f'from each valid state: EFX0, {cnt["DE loops: trades"]} trades in all, at most '
              f'{cnt["DE loops: max trades"]}')
        for key, c in sorted(cnt.items()):
            if key.startswith('  (NC)'):
                out(f'        Improvement Lemma, {key.strip()}: {c}')


# ============================================================================================ [8]
def sec_random(K_general=20000, K_core=20000):
    out('[8] DE, peeling included, on random instances (evidence, seed 2026)')
    sys.path.insert(0, HALL)
    import hall
    rng = random.Random(2026)
    stats = Counter()
    cores = []
    bad = []
    for kind, K in (('general', K_general), ('core', K_core)):
        for _ in range(K):
            if kind == 'general':
                n = rng.randint(1, 8)
                m = rng.randint(0, 2 * n + 3)
                v = []
                for i in range(n):
                    r = min(m, rng.choice([0, 1, 2, 3, 3, 3, 3]))
                    v.append({g: rng.randint(1, 6) for g in rng.sample(range(m), r)})
            else:
                n = rng.randint(2, 9)
                m = rng.randint(3, 2 * n + 3)
                v = []
                for i in range(n):
                    c = rng.randint(1, 9)
                    b = rng.randint(c, 9)
                    a = rng.randint(b, b + c - 1)
                    v.append(dict(zip(rng.sample(range(m), 3), (a, b, c))))
            core = []
            X = de(v, n, m, stats, core)
            ok = is_complete(X, m) and is_efx0(v, X) and sum(len(B) > 2 for B in X) <= 1
            stats[kind + ' ok'] += ok
            if not ok:
                bad.append((v, X))
            if core:
                cores.append((v, n, m, core[0]))
    check(stats['general ok'] == K_general and stats['core ok'] == K_core and stats['max trades / n'] <= 4,
          f'{K_general} instances with n <= 8, 0-3 valued goods per agent, values 1..6 (ties, unbalanced agents, '
          f'goods nobody values) and {K_core} strictly balanced cores with n <= 9: every output complete, EFX0 (raw), '
          f'at most one bundle of more than two goods, at most 4n trades')
    out(f'  stats: {stats["runs reaching the loop"]} runs reached the loop, {stats["runs with a trade"]} needed a '
        f'trade, at most {stats["max trades"]} trades; peeled agents {stats["peeled agents"]}; trades: '
        + ', '.join(f'{k} {c}' for k, c in sorted(stats.items()) if k.startswith(('chain', 'ring')))
        + '; ' + ', '.join(f'{k} {c}' for k, c in sorted(stats.items()) if k.startswith('finish')))
    # comparisons on the cores reached: the loop of the previous version of the paper (a free agent holding nothing
    # finishes first), and hall.py (whose stop rule takes the first free agent that holds nothing or has
    # |H_o| <= |F| - 1, that is, the rule of this version)
    d_old_o, d_old_X, d_hall, ok = 0, 0, 0, True
    for v, n, m, c in cores:
        Xo, oo, Ho, tro, _ = de_loop(c['rank'], c['m'], old_finish=True)
        d_old_o += oo != c['o']
        d_old_X += Xo != c['Xc']
        Xh = hall.algorithm(c['rank'], c['m'], hall.new_stats())          # good -> agent
        Bh = [{g for g in range(c['m']) if Xh[g] == i} for i in range(len(c['rank']))]
        d_hall += Bh != c['Xc']
        ok &= is_efx0(v, with_core(c, Xo)) and is_efx0(v, with_core(c, Bh)) and len(tro) == c['trades']
    check(ok, f'on the {len(cores)} cores reached: the previous paper\'s loop (a free agent holding '
                              f'nothing finishes first) picks another finishing agent in {d_old_o} run(s), another '
                              f'output in {d_old_X}; hall.py (another tie-break among the leftover goods) differs in {d_hall}; all these outputs EFX0 (raw, '
                              f'the instance\'s values)')


def sec_novel(K=2000):
    out('[9] Section 1, "What is new": an instance of the model that no earlier existence result covers')
    sets = [(0, 1, 6), (0, 1, 7), (0, 2, 8), (2, 3, 4), (3, 5, 9), (4, 5, 10)]
    n, m = len(sets), 1 + max(g for S in sets for g in S)
    valuers = {g: [i for i, S in enumerate(sets) if g in S] for g in range(m)}
    check(n == 6 and m == 11 and m == n + 5 and all(len(set(S)) == 3 for S in sets),
          'six agents, eleven goods (m = n + 5: neither m <= n + 3 nor m = n + 4), each agent values exactly three goods')
    check(len(valuers[0]) == 3, 'three agents value g0 (not at most two valuers per good)')
    check(set(sets[0]) & set(sets[1]) == {0, 1},
          'the first two agents share g0 and g1: the hypergraph of goods (edges) on agents has girth 2')
    rng = random.Random(9)
    bad = 0
    for _ in range(K):
        vals = rng.sample(range(1001, 2000), 3 * n)                # distinct values in (1, 2), scaled by 1000
        v = [{g: vals[3 * i + k] for k, g in enumerate(sorted(S))} for i, S in enumerate(sets)]
        distinct = len({tuple(sorted(vi.items())) for vi in v}) == n
        balanced = all(max(vi.values()) < sum(vi.values()) - max(vi.values()) for vi in v)
        X = de(v, n, m)
        ok = (distinct and balanced and is_complete(X, m) and is_efx0(v, X)
              and sum(1 for B in X if len(B) > 2) <= 1)
        bad += not ok
    check(bad == 0, f'{K} random draws of pairwise distinct values in (1, 2): six different valuations, every agent '
                    f'strictly balanced; DE returns a complete EFX0 allocation with at most one bundle of more than '
                    f'two goods every time')


def main():
    t0 = time.time()
    for sec in (sec_intro, sec_small, sec_worked, sec_short, sec_rings, sec_limits, sec_exhaustive, sec_random,
                sec_novel):
        try:
            sec()
        except Exception as e:                       # a failed assert is a failed check
            tb = traceback.extract_tb(e.__traceback__)[-1]
            check(False, f'{sec.__name__} stopped: {type(e).__name__} {e} (line {tb.lineno}: {tb.line})')
    out(f'{len(FAILS)} failure(s); {time.time() - t0:.0f} s')
    with open(os.path.join(HERE, 'check_output.txt'), 'w') as f:
        f.write('\n'.join(LOG[:-1]) + '\n' + f'{len(FAILS)} failure(s)\n')
    sys.exit(1 if FAILS else 0)


if __name__ == '__main__':
    main()
