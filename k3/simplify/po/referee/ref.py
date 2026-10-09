"""Referee's independent implementation of NOTES.md (po/hall) sections 1-3, written from the text only.
Holding codes: -1 nothing, 0 a, 1 b, 2 c, 3 pair {b,c}.  Utility 0,3,2,1,4."""
import itertools, random, sys
from collections import Counter

UT = (3, 2, 1, 4, 0)  # index by h (h=-1 -> UT[-1] = 0)
VAL = (4, 3, 2)
STATS = Counter()


class Inst:
    def __init__(self, rank, m):
        self.n = len(rank); self.m = m
        self.rank = [tuple(r) for r in rank]
        self.pos = [{g: k for k, g in enumerate(r)} for r in self.rank]


def goods(I, i, h):
    if h == -1: return ()
    if h == 3: return (I.rank[i][1], I.rank[i][2])
    return (I.rank[i][h],)


def needs(I, i, h):
    if h == -1: return set(I.rank[i])
    if h == 3: return set()
    return set(I.rank[i][:h])


class St:
    def __init__(self, I, H):
        self.I = I; self.H = tuple(H); n = I.n
        held = []
        for i in range(n): held += goods(I, i, H[i])
        self.disjoint = len(held) == len(set(held))
        self.U = {i for i in range(n) if H[i] == 3}
        self.y = {i: I.rank[i][H[i]] for i in range(n) if 0 <= H[i] <= 2}
        self.N = [needs(I, i, H[i]) for i in range(n)]
        self.NA = set().union(*self.N)
        self.J = set(range(I.m)) - set(held)
        self.single = {g: i for i, g in self.y.items()}  # held alone by a non-U agent
        self.F = {i for i in range(n) if i not in self.U and (H[i] == -1 or self.y[i] not in self.NA)}
        self.valid = self.disjoint and all(g in self.single for g in self.NA)

    def outn(self, j):
        """out-neighbours of j in the need digraph D"""
        if j in self.U or j not in self.y: return []
        g = self.y[j]
        return [k for k in range(self.I.n) if k not in self.U and g in self.N[k]]

    def base(self, o):
        return set(goods(self.I, o, self.H[o]))

    def exposed(self, o):
        I = self.I; B = self.J | self.base(o)
        return [x for x in range(I.n) if x != o and x not in self.U and self.H[x] == 0
                and I.rank[x][1] in B and I.rank[x][2] in B]

    def min_hit(self, sets):
        """size of a smallest hitting set (brute force); sets nonempty"""
        if not sets: return 0, set()
        univ = sorted(set().union(*sets))
        for s in range(len(univ) + 1):
            for H in itertools.combinations(univ, s):
                Hs = set(H)
                if all(Hs & S for S in sets): return s, Hs
        raise AssertionError

    def absorber_bf(self, o):
        """definition of valid absorber in section 1 (brute force); returns H or None"""
        if not (o in self.F or o in self.U): return None
        I = self.I
        sets = [self.J & {I.rank[x][1], I.rank[x][2]} for x in self.exposed(o)]
        if any(not S for S in sets): return None
        s, H = self.min_hit(sets)
        return H if s <= len(self.F - {o}) else None

    def completable_bf(self):
        return [o for o in range(self.I.n) if self.absorber_bf(o) is not None]


def util(H, i): return UT[H[i]]


def efx0(I, X):
    n = I.n
    v = [{g: VAL[k] for k, g in enumerate(I.rank[i])} for i in range(n)]
    for i in range(n):
        vi = sum(v[i].get(g, 0) for g in X[i])
        for j in range(n):
            if j == i or not X[j]: continue
            vals = [v[i].get(g, 0) for g in X[j]]
            if vi < sum(vals) - min(vals): return False
    return True


def complete(S, o, Hs):
    I = S.I; n = I.n
    X = [set(goods(I, i, S.H[i])) for i in range(n)]
    frees = sorted(S.F - {o})
    Hl = sorted(Hs)
    assert len(Hl) <= len(frees)
    for g, f in zip(Hl, frees): X[f].add(g)
    X[o] |= (S.J - set(Hl))
    allg = [g for x in X for g in x]
    assert sorted(allg) == list(range(I.m))
    return X


def check_transition(S, H2, strict_agents=None, tag=''):
    """Lemma 0 hypotheses (a), (b) + F1, then validity and Pareto dominance of the result"""
    I = S.I; n = I.n
    S2 = St(I, H2)
    assert S2.disjoint, ('disjoint', tag)
    ups = [util(H2, i) - util(S.H, i) for i in range(n)]
    assert all(d >= 0 for d in ups) and any(d > 0 for d in ups), ('lemma0a', tag, S.H, H2)
    if strict_agents is not None:
        for i in range(n):
            if i in strict_agents: assert ups[i] > 0, ('cycle agent not strict', tag)
            else: assert H2[i] == S.H[i], ('off-cycle moved', tag)
    for i in range(n):  # F1
        assert S2.N[i] <= S.N[i], ('F1', tag)
    for g in S.NA:  # Lemma 0 (b)
        assert g in S2.single, ('lemma0b', tag, g, S.H, H2)
    assert S2.NA <= S.NA
    assert S2.valid, ('valid', tag)
    return S2


def f2_check(S):
    for j in range(S.I.n):
        if j not in S.U and j not in S.F:
            assert S.outn(j), 'F2'


def lemma1a(S, cyc, tag='D-cycle'):
    I = S.I; H2 = list(S.H); k = len(cyc)
    assert k >= 2 and len(set(cyc)) == k
    for t in range(k):
        a, b = cyc[t], cyc[(t + 1) % k]
        assert a not in S.U and b not in S.U and a in S.y and S.y[a] in S.N[b]
        H2[b] = I.pos[b][S.y[a]]
    STATS[tag] += 1
    return check_transition(S, H2, set(cyc), tag)


def find_walk(S, start, rng):
    path = [start]; idx = {start: 0}
    while True:
        out = S.outn(path[-1])
        if not out: return path, None
        nx = rng.choice(out)
        if nx in idx: return path, path[idx[nx]:]
        idx[nx] = len(path); path.append(nx)


def lemma1b(S, x, rng):
    I = S.I
    assert x not in S.U and S.H[x] == 0 and I.rank[x][1] in S.J and I.rank[x][2] in S.J
    path, cyc = find_walk(S, x, rng)
    if cyc is not None:
        return lemma1a(S, cyc, 'P2-walk-cycle')
    k = len(path) - 1
    jk = path[-1]
    assert jk not in S.U
    if jk in S.y: assert S.y[jk] not in S.NA, 'end of path holds needed good'
    H2 = list(S.H); H2[x] = 3
    for t in range(1, k + 1):
        g = S.y[path[t - 1]]
        assert g in S.N[path[t]]
        H2[path[t]] = I.pos[path[t]][g]
    STATS['P2-path'] += 1
    return check_transition(S, H2, set(path), 'P2-path')


def lemma3_H(S, o):
    """free o holding g: returns dict x -> h_x, asserting Lemma 3's structure"""
    I = S.I; g = S.y[o]; hx = {}
    for x in S.exposed(o):
        bc = {I.rank[x][1], I.rank[x][2]}
        assert g in bc, ('lemma3: g not in bc', S.H, o, x)
        (h,) = bc - {g}
        assert h in S.J, 'lemma3: h not junk'
        hx[x] = h
    return hx


def p2_violators(S):
    I = S.I
    return [x for x in range(I.n) if x not in S.U and S.H[x] == 0 and I.rank[x][1] in S.J and I.rank[x][2] in S.J]


def stop_rule(S):
    """Corollary's stop rule under P2; returns (o, H) or None; cross-checks Lemmas 2,3 vs brute force"""
    n = S.I.n
    if len(S.U) == n:
        for o in range(n): assert S.absorber_bf(o) is not None
        return 0, set()
    res = None
    for o in sorted(S.F):
        bf = S.absorber_bf(o)
        if S.H[o] == -1:
            assert not S.exposed(o), 'lemma2'
            assert bf is not None
            if res is None: res = (o, set())
            continue
        hx = lemma3_H(S, o)
        Ho = set(hx.values())
        mine = len(Ho) <= len(S.F) - 1
        assert mine == (bf is not None), ('lemma3 iff', S.H, o)
        if mine:
            s, _ = S.min_hit([{h} for h in hx.values()])
            assert s == len(Ho)
            if res is None: res = (o, Ho)
    return res


def lemma4(S, rng):
    assert not S.F and len(S.U) < S.I.n
    f2_check(S)
    start = rng.choice([i for i in range(S.I.n) if i not in S.U])
    path, cyc = find_walk(S, start, rng)
    assert cyc is not None, 'lemma4: no cycle'
    return lemma1a(S, cyc, 'L4-cycle')


def lemma5(S, rng):
    I = S.I; n = I.n
    F = sorted(S.F); f = len(F)
    assert f > 0 and all(S.H[o] != -1 for o in F)
    hx = {o: lemma3_H(S, o) for o in F}
    Hs = {o: set(hx[o].values()) for o in F}
    for o in F: assert len(Hs[o]) >= f
    # each x exposed for at most one free o
    cnt = Counter(x for o in F for x in hx[o])
    assert all(c == 1 for c in cnt.values()), 'x exposed for two free agents'
    order = F[:]; rng.shuffle(order)
    chosen = set(); h = {}; xo = {}
    for o in order:
        cand = sorted(Hs[o] - chosen)
        assert cand, 'greedy SDR fails'
        h[o] = rng.choice(cand); chosen.add(h[o])
        xo[o] = rng.choice([x for x, hh in hx[o].items() if hh == h[o]])
    assert len(set(xo.values())) == f, 'x_o not distinct'
    sigma = {}
    nonU = [i for i in range(n) if i not in S.U]
    for j in nonU:
        if j in S.F: sigma[j] = xo[j]
        else:
            out = S.outn(j); assert out, 'F2'
            sigma[j] = rng.choice(out)
        assert sigma[j] not in S.U and sigma[j] != j
    # find a cycle
    cur = rng.choice(nonU); seen = {}
    while cur not in seen:
        seen[cur] = len(seen); cur = sigma[cur]
    cyc = [cur]; nx = sigma[cur]
    while nx != cur: cyc.append(nx); nx = sigma[nx]
    k = len(cyc); assert k >= 2
    for w in cyc: assert w in S.y, 'cycle agent holds no single good'
    H2 = list(S.H); assigned = Counter(); used = []
    nexp = 0
    for t in range(k):
        w, w2 = cyc[t], cyc[(t + 1) % k]
        if w in S.F:
            assert w2 == xo[w]
            assert {I.rank[w2][1], I.rank[w2][2]} == {S.y[w], h[w]}
            assert S.H[w2] == 0
            H2[w2] = 3; used += [S.y[w], h[w]]; nexp += 1
        else:
            assert S.y[w] in S.N[w2]
            H2[w2] = I.pos[w2][S.y[w]]; used.append(S.y[w])
        assigned[w2] += 1
    assert all(assigned[w] == 1 for w in cyc)
    assert len(used) == len(set(used))
    STATS['L5-cycle'] += 1; STATS['L5-exposure-arcs-%d' % nexp] += 1
    S2 = check_transition(S, H2, set(cyc), 'L5')
    newU = S2.U - S.U
    assert newU == {cyc[(t + 1) % k] for t in range(k) if cyc[t] in S.F}
    return S2


def improve(S, rng):
    """one step of the Theorem's proof on a valid state; returns ('stop', o, H) or ('move', S2)"""
    assert S.valid
    f2_check(S)
    v = p2_violators(S)
    if v:
        return 'move', lemma1b(S, rng.choice(v), rng)
    st = stop_rule(S)
    if st is not None: return 'stop', st
    # not stopping: no free agent is a valid absorber (brute force)
    for o in S.F: assert S.absorber_bf(o) is None
    if not S.F: return 'move', lemma4(S, rng)
    return 'move', lemma5(S, rng)


def serial_dictatorship(I, order=None):
    taken = set(); H = [-1] * I.n
    for i in (order or range(I.n)):
        for k, g in enumerate(I.rank[i]):
            if g not in taken:
                H[i] = k; taken.add(g); break
    return H


def algorithm(rank, m, rng, order=None):
    I = Inst(rank, m)
    S = St(I, serial_dictatorship(I, order))
    assert S.valid, 'SD not valid'
    steps = 0; tot = sum(util(S.H, i) for i in range(I.n))
    while True:
        r = improve(S, rng)
        if r[0] == 'stop':
            o, Hs = r[1]
            X = complete(S, o, Hs)
            assert efx0(I, X), ('NOT EFX0', rank, m, S.H, o, Hs, X)
            STATS['steps-%d' % steps] += 1
            return X, steps
        S2 = r[1]
        t2 = sum(util(S2.H, i) for i in range(I.n))
        assert t2 > tot; tot = t2
        steps += 1; S = S2
        assert steps <= 4 * I.n
