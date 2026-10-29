"""Draft and Exchange for class C: every agent values three goods a > b > c with v(a) < v(b) + v(c) (as in the paper),
or four goods a > b > c > d with

    (C1) v(b) + v(d) <= v(a)    and    (C2) v(a) + v(d) <= v(b) + v(c).

Ladders (score = position):
    three goods:                 nothing, c, b, a, P              with P = {b, c} (the pair)
    four goods, c + d <= b (S):  nothing, d, c, b, a, P
    four goods, c + d >  b (M):  nothing, d, c, b, Q, a, P        with Q = {c, d} (the low pair)

Wants: the goods whose singleton is a higher rung (a Q-holder wants a; a P-holder wants nothing).
Blockers of an owner o (Y_o plus J minus H goes to o):
    top blocker: x != o holds a_x and b_x, c_x in J + Y_o;
    low blocker: x != o is an M-agent holding b_x, and c_x, d_x in J + Y_o.
A blocker's *set* is {b_x, c_x} or {c_x, d_x}. Owner o can finish with H (a subset of J) if |H| <= |F minus o| and H
meets every blocker's set; owners: free agents, Q-holders, P-holders.
"""
import itertools

from model import relevant, is_efx0

NOTHING = 'nothing'


class Agent:
    def __init__(self, vi):
        r = relevant(vi)
        self.k = len(r)
        if self.k == 3:
            self.a, self.b, self.c = r
            self.d = None
            self.kind = '3'
        else:
            self.a, self.b, self.c, self.d = r
            self.kind = 'M' if vi[self.c] + vi[self.d] > vi[self.b] else 'S'
        self.P = frozenset([self.b, self.c])
        self.Q = frozenset([self.c, self.d]) if self.kind == 'M' else None
        singles = [self.d] if self.k == 4 else []
        lad = [frozenset()] + [frozenset([g]) for g in singles + [self.c, self.b]]
        if self.kind == 'M':
            lad.append(self.Q)
        lad += [frozenset([self.a]), self.P]
        self.ladder = lad

    def wants(self, B):
        s = self.ladder.index(B)
        return frozenset(g for g in [self.a, self.b, self.c, self.d] if g is not None and frozenset([g]) in self.ladder[s + 1:])


def class_c_ok(vi):
    r = relevant(vi)
    if len(r) == 3:
        a, b, c = (vi[g] for g in r)
        return a < b + c
    if len(r) != 4:
        return False
    a, b, c, d = (vi[g] for g in r)
    return b + d <= a and a + d <= b + c and a > b > c > d > 0


class State:
    def __init__(self, ags, m, Y):
        self.ags, self.m, self.Y = ags, m, [frozenset(B) for B in Y]
        n = len(ags)
        held = frozenset().union(*self.Y)
        assert sum(len(B) for B in self.Y) == len(held), 'holdings overlap'
        self.J = frozenset(range(m)) - held
        self.W = [ags[i].wants(self.Y[i]) for i in range(n)]
        self.wanted = frozenset().union(*self.W)
        alone = frozenset(next(iter(B)) for B in self.Y if len(B) == 1)
        self.valid = self.wanted <= alone
        self.U = [i for i in range(n) if self.Y[i] == ags[i].P]
        self.L = [i for i in range(n) if ags[i].Q is not None and self.Y[i] == ags[i].Q]
        self.F = [i for i in range(n) if len(self.Y[i]) <= 1 and not (self.Y[i] & self.wanted)]

    def blocker_sets(self, o):
        """(x, set) for every blocker x of owner o"""
        S = self.J | self.Y[o]
        out = []
        for x, ag in enumerate(self.ags):
            if x == o:
                continue
            if self.Y[x] == frozenset([ag.a]) and ag.P <= S:
                out.append((x, ag.P))
            elif ag.kind == 'M' and self.Y[x] == frozenset([ag.b]) and ag.Q <= S:
                out.append((x, ag.Q))
        return out

    def can_finish(self, o):
        """a smallest H (a tuple) with which o can finish, or None"""
        if o not in self.F and o not in self.L and o not in self.U:
            return None
        sets = [s & self.J for x, s in self.blocker_sets(o)]
        if any(not s for s in sets):
            return None
        cap = len([f for f in self.F if f != o])
        Jl = sorted(self.J)
        for k in range(cap + 1):
            for H in itertools.combinations(Jl, k):
                if all(set(H) & s for s in sets):
                    return H
        return None

    def completion(self, o, H):
        X = [set(B) for B in self.Y]
        X[o] |= self.J - set(H)
        for h, f in zip(H, [f for f in self.F if f != o]):
            X[f].add(h)
        return X

    def scores(self):
        return tuple(self.ags[i].ladder.index(self.Y[i]) for i in range(len(self.ags)))


def all_states(ags, m):
    n = len(ags)
    res, cur = [], [None] * n

    def rec(i, used):
        if i == n:
            res.append(State(ags, m, list(cur)))
            return
        for B in ags[i].ladder:
            if not (B & used):
                cur[i] = B
                rec(i + 1, used | B)
    rec(0, frozenset())
    return res


def check_every_form(v, m):
    """returns (number of valid states, list of score-Pareto-maximal valid states that no owner can finish);
    asserts that every completion found is EFX0 (soundness)"""
    ags = [Agent(vi) for vi in v]
    sts = [s for s in all_states(ags, m) if s.valid]
    sc = [s.scores() for s in sts]
    bad = []
    for s, t in zip(sts, sc):
        for o in range(len(ags)):
            H = s.can_finish(o)
            if H is not None:
                assert is_efx0(v, s.completion(o, H)), 'unsound completion'
        if any(u != t and all(x >= y for x, y in zip(u, t)) for u in sc):
            continue
        if all(s.can_finish(o) is None for o in range(len(ags))):
            bad.append(s)
    return len(sts), bad


# ---------------------------------------------------------------------------------------------------- moves
def first_wanter(st, g, avoid=()):
    for z in range(len(st.ags)):
        if z not in avoid and g in st.W[z]:
            return z
    return None


def chain_candidates(st):
    """(x, new holding) for every agent to which a chain applies: a top-holder with b, c leftover (takes P), an
    M-agent holding b with c, d leftover (takes Q), or a Q-holder with b leftover (takes P, d becomes leftover; its
    old goods are unwanted, so the chain stops at once)"""
    out = []
    for x, ag in enumerate(st.ags):
        if st.Y[x] == frozenset([ag.a]) and ag.P <= st.J:
            out.append((x, ag.P))
        elif ag.kind == 'M' and st.Y[x] == frozenset([ag.b]) and ag.Q <= st.J:
            out.append((x, ag.Q))
        elif ag.kind == 'M' and st.Y[x] == ag.Q and ag.b in st.J:
            out.append((x, ag.P))
    return out


def apply_chain(st, x, newB):
    """the chain of x: x takes newB, its old good goes to the first agent that wants it, and so on; returns the new
    holdings, or ('ring', cycle) if the walk repeats an agent"""
    Y = list(st.Y)
    path = [x]
    while True:
        j = path[-1]
        if len(st.Y[j]) != 1:
            break
        g = next(iter(st.Y[j]))
        if g not in st.wanted:
            break
        z = first_wanter(st, g)
        if z in path:
            return ('ring', path[path.index(z):])
        path.append(z)
    Y[x] = newB
    for t in range(1, len(path)):
        Y[path[t]] = st.Y[path[t - 1]]
    return Y


def improve(st, label_order='free-first'):
    """the improving trade of the Improvement Lemma (class C), when no chain applies and no owner can finish.
    Returns (kind, new holdings, cycle) or raises AssertionError with a reason."""
    n = len(st.ags)
    assert not chain_candidates(st)
    assert all(st.Y[o] for o in st.F), 'a free agent holds nothing (it could finish)'
    absorbers = list(st.F) + list(st.L)
    if label_order == 'free-first':
        absorbers = sorted(st.F) + sorted(st.L)
    used = set()
    rep = {}                                    # absorber -> (blocker, its set, label or None)
    for o in absorbers:
        cands = []
        for x, S in st.blocker_sets(o):
            lab = S & st.J
            assert len(lab) <= 1 and S - st.J <= st.Y[o]
            cands.append((x, S, next(iter(lab)) if lab else None))
        assert cands, 'an absorber without blockers (it could finish)'
        pick = next((c for c in cands if c[2] is None), None)
        if pick is None:
            pick = next((c for c in cands if c[2] not in used), None)
        assert pick is not None, 'no unused label for absorber %d' % o
        if pick[2] is not None:
            used.add(pick[2])
        rep[o] = pick
    sigma = {}
    for j in range(n):
        if j in rep:
            sigma[j] = rep[j][0]
        elif len(st.Y[j]) == 1 and st.Y[j] <= st.wanted:
            sigma[j] = first_wanter(st, next(iter(st.Y[j])))
    start = min(sigma)
    seen = []
    j = start
    while j not in seen:
        seen.append(j)
        assert j in sigma, 'walk left the domain at %d' % j
        j = sigma[j]
    cyc = seen[seen.index(j):]                   # cyc[t+1] = sigma(cyc[t]): cyc[t+1] receives cyc[t]'s goods
    Y = list(st.Y)
    for t, w in enumerate(cyc):
        r = cyc[(t + 1) % len(cyc)]
        if w in rep:
            Y[r] = rep[w][1]
        else:
            Y[r] = st.Y[w]
    return Y, cyc


def check_improvement(v, m):
    """for every valid state of the instance: if a chain applies, check it; else if no owner can finish and not every
    agent holds its pair, run improve() and check that the result is a valid state that dominates in scores.
    Returns counts."""
    ags = [Agent(vi) for vi in v]
    cnt = {'states': 0, 'chain': 0, 'finish': 0, 'ring': 0, 'allpairs': 0}
    for st in all_states(ags, m):
        if not st.valid:
            continue
        cnt['states'] += 1
        ch = chain_candidates(st)
        if ch:
            res = apply_chain(st, *ch[0])
            if isinstance(res, tuple):
                cyc = res[1]                       # ring of want arrows: each agent takes the next one's good
                Y = list(st.Y)
                for t, w in enumerate(cyc):
                    Y[cyc[(t + 1) % len(cyc)]] = st.Y[w]
            else:
                Y = res
            new = State(ags, m, Y)
            assert new.valid and all(x >= y for x, y in zip(new.scores(), st.scores())) and new.scores() != st.scores()
            cnt['chain'] += 1
            continue
        if all(i in st.U for i in range(len(ags))):
            cnt['allpairs'] += 1
            continue
        if any(st.can_finish(o) is not None for o in range(len(ags))):
            cnt['finish'] += 1
            continue
        Y, cyc = improve(st)
        new = State(ags, m, Y)
        assert new.valid, 'ring result not valid'
        assert all(x >= y for x, y in zip(new.scores(), st.scores())) and new.scores() != st.scores(), 'no domination'
        cnt['ring'] += 1
    return cnt
