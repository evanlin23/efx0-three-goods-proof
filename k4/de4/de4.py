"""Algorithm DE (Draft and Exchange, paper/k3-simple/main.tex, Algorithm 1) extended to agents with a small fourth good.

Admissible instances: every agent positively values at most three goods, or exactly four goods a > b > c > d (by value,
ties by index) with

    (S)   v(b) + v(d) <= v(a),    v(c) + v(d) <= v(b),    v(a) + v(d) <= v(b) + v(c),

that is, v(d) <= min(v(a) - v(b), v(b) - v(c), v(b) + v(c) - v(a)). The only change to DE is a fifth rung: a
four-good agent's holdings are nothing, d, c, b, a and the pair {b, c} (scores 0..5), and the draft takes the first of
a, b, c, d not yet taken. Blockers, wants, chains, rings, finishing and the completion are word for word the paper's.

Written from the statement of the theorem in NOTES.md, independently of classc.py. Every claim of the proof that the
algorithm relies on is an assert.
"""
from model import val


def favourite(vi, G):
    return min(G, key=lambda g: (-vi.get(g, 0), g))


def rule_r1(vi, G):
    if not G:
        return frozenset()
    p = favourite(vi, G)
    if vi.get(p, 0) == 0:
        return frozenset()
    if val(vi, G) - vi[p] <= vi[p]:
        return frozenset([p])
    return None


def ranking(vi, G):
    return sorted((g for g in G if vi.get(g, 0) > 0), key=lambda g: (-vi[g], g))


def small_d(vals):
    a, b, c, d = vals
    return b + d <= a and c + d <= b and a + d <= b + c


def admissible(v):
    for vi in v:
        r = ranking(vi, list(vi))
        if len(r) > 4 or (len(r) == 4 and not small_d([vi[g] for g in r])):
            return False
    return True


class Run:
    """one run of DE; after run(), X is the allocation and peels, trades the counts"""

    def __init__(self, n, m, v, check=True):
        """check=False runs DE on any instance with at most four relevant goods per agent (used to show that each
        condition of (S) is needed); the asserts on (S) are then skipped"""
        assert not check or admissible(v)
        self.n, self.m, self.v, self.check = n, m, v, check
        self.peels = self.trades = 0
        self.log = []

    # ---------------------------------------------------------------------------- state helpers (core agents A)
    def setup_core(self, A, G):
        self.A, self.G = A, G
        self.rank = {}
        for i in A:
            r = ranking(self.v[i], G)
            assert len(r) in (3, 4), 'Lemma R1fail: a remaining agent values three or four goods'
            vals = [self.v[i][g] for g in r]
            if len(r) == 3:
                assert vals[0] < vals[1] + vals[2], 'Lemma R1fail: strictly balanced'
            else:
                assert vals[0] < vals[1] + vals[2] + vals[3]
                assert small_d(vals) or not self.check
            self.rank[i] = r
        self.pair = {i: frozenset(self.rank[i][1:3]) for i in A}

    def holding(self, i):
        return self.Y[i]

    def score(self, i):
        r, B = self.rank[i], self.Y[i]
        if B == self.pair[i]:
            return len(r) + 1
        if not B:
            return 0
        return len(r) - r.index(next(iter(B)))

    def wants(self, i):
        B = self.Y[i]
        if B == self.pair[i]:
            return []
        r = self.rank[i]
        if not B:
            return list(r)
        return r[:r.index(next(iter(B)))]

    def refresh(self):
        A = self.A
        self.holder = {g: i for i in A for g in self.Y[i]}
        self.J = sorted(g for g in self.G if g not in self.holder)
        self.U = [i for i in A if self.Y[i] == self.pair[i]]
        self.W = {i: self.wants(i) for i in A}
        self.wanted = set(g for i in A for g in self.W[i])
        for g in self.wanted:                                   # validity
            assert g in self.holder and len(self.Y[self.holder[g]]) == 1, 'state not valid'
        self.F = [i for i in A if i not in self.U and (not self.Y[i] or next(iter(self.Y[i])) not in self.wanted)]

    def first_wanter(self, g):
        return next(i for i in self.A if g in self.W[i])

    def blockers(self, o):
        """x != o holding exactly its top, with b_x, c_x in J + Y_o (in index order)"""
        S = set(self.J) | set(self.Y[o])
        return [x for x in self.A if x != o and self.Y[x] == frozenset([self.rank[x][0]]) and self.pair[x] <= S]

    # ---------------------------------------------------------------------------- the algorithm
    def run(self):
        n, v = self.n, self.v
        X = [set() for _ in range(n)]
        A, G = list(range(n)), set(range(self.m))
        while len(A) >= 2:                                      # peeling
            i = next((i for i in A if rule_r1(v[i], G) is not None), None)
            if i is None:
                break
            P = rule_r1(v[i], G)
            X[i] = set(P)
            A.remove(i)
            G -= P
            self.peels += 1
        if len(A) == 1:
            X[A[0]] = set(G)
            self.X = X
            return X
        self.setup_core(A, G)
        self.Y = {}
        taken = set()
        for i in A:                                             # the draft
            g = next((g for g in self.rank[i] if g not in taken), None)
            self.Y[i] = frozenset([g]) if g is not None else frozenset()
            taken |= self.Y[i]
        self.refresh()
        assert not self.U
        bound = sum(len(self.rank[i]) + 1 for i in A)           # largest total score
        while True:
            phi = sum(self.score(i) for i in A)
            old = {i: self.score(i) for i in A}
            x = next((x for x in A if self.Y[x] == frozenset([self.rank[x][0]]) and self.pair[x] <= set(self.J)), None)
            if x is not None:
                self.chain(x)
            elif all(i in self.U for i in A):
                o, H = A[0], []
                break
            else:
                o, H = self.finisher()
                if o is not None:
                    break
                self.ring()
            self.refresh()
            self.trades += 1
            assert all(self.score(i) >= old[i] for i in A) and sum(self.score(i) for i in A) > phi
            assert self.trades <= bound
        others = [f for f in self.F if f != o]
        for i in A:
            X[i] = set(self.Y[i])
        X[o] |= set(self.J) - set(H)
        for h, f in zip(H, others):
            X[f].add(h)
        self.X = X
        return X

    def chain(self, x):
        path = [x]
        while True:
            j = path[-1]
            if len(self.Y[j]) != 1 or next(iter(self.Y[j])) not in self.wanted:
                break
            z = self.first_wanter(next(iter(self.Y[j])))
            if z in path:
                cyc = path[path.index(z):]                      # a ring of want arrows: each takes the previous good
                assert len(cyc) >= 2
                new = {cyc[(t + 1) % len(cyc)]: self.Y[cyc[t]] for t in range(len(cyc))}
                self.Y.update(new)
                self.log.append(('chain-ring', cyc))
                return
            path.append(z)
        new = {x: self.pair[x]}
        for t in range(1, len(path)):
            new[path[t]] = self.Y[path[t - 1]]
        self.Y.update(new)
        self.log.append(('chain', path))

    def finisher(self):
        """the first free agent o with |H_o| <= |F| - 1, and H_o in the order of first blockers (Lemma test)"""
        for o in self.F:
            if not self.Y[o]:
                assert not self.blockers(o), 'Lemma test (a)'
                return o, []
            H = []
            for x in self.blockers(o):
                assert next(iter(self.Y[o])) in self.pair[x], 'Lemma test (b)'
                (h,) = self.pair[x] - self.Y[o]
                assert h in self.J
                if h not in H:
                    H.append(h)
            if len(H) <= len(self.F) - 1:
                return o, H
        return None, None

    def ring(self):
        """the ring of the proof of the Improvement Lemma"""
        A, F = self.A, self.F
        assert all(self.Y[o] for o in F)
        q, xo = {}, {}
        for o in F:                                             # distinct leftover goods, greedily
            for x in self.blockers(o):
                (h,) = self.pair[x] - self.Y[o]
                if h not in q.values():
                    q[o], xo[o] = h, x
                    break
            assert o in q, 'Improvement Lemma: |H_o| >= |F| gives a fresh leftover good'
        sigma = {}
        for j in A:
            if j in self.U:
                continue
            sigma[j] = xo[j] if j in F else self.first_wanter(next(iter(self.Y[j])))
        start = next(j for j in A if j not in self.U)
        seen = []
        j = start
        while j not in seen:
            seen.append(j)
            j = sigma[j]
        cyc = seen[seen.index(j):]                              # sigma(cyc[t]) = cyc[t + 1]
        assert len(cyc) >= 2
        new = {}
        for t, w in enumerate(cyc):
            r = cyc[(t + 1) % len(cyc)]
            new[r] = (self.Y[w] | {q[w]}) if w in F else self.Y[w]
            if w in F:
                assert new[r] == self.pair[r]
        self.Y.update(new)
        self.log.append(('ring', cyc))
