"""Independent implementation of algorithm DE written from long.tex alone.

Values are Python ints (exact).  Agents are 0..n-1, goods 0..m-1, and
"index order" is the natural order of these integers.

Every claim the paper makes along a run can be asserted (checks=True), and
optional deep checks (deep=True) brute-force the finishing test, the
soundness theorem for every allowed completion, and the Lemma-test facts.
"""
from itertools import combinations


class CheckError(Exception):
    pass


def check(cond, msg):
    if not cond:
        raise CheckError(msg)


# ---------------------------------------------------------------- raw EFX0
def efx0_violations(v, X):
    """Raw definition: v_i(X_i) >= v_i(X_j minus {h}) for all i != j, h in X_j."""
    n = len(v)
    bad = []
    for i in range(n):
        vi = v[i]
        own = sum(vi[g] for g in X[i])
        for j in range(n):
            if i == j:
                continue
            tot = sum(vi[g] for g in X[j])
            for h in X[j]:
                if tot - vi[h] > own:
                    bad.append((i, j, h))
    return bad


def is_efx0(v, X):
    return not efx0_violations(v, X)


# ---------------------------------------------------------------- rule R1
def rule_r1(vi, G):
    """Return P (tuple) if rule R1 applies to an agent with values vi on the
    set G of remaining goods, else None.  For G empty we take the convention
    that the agent may leave with nothing (the paper leaves this implicit)."""
    if not G:
        return ()
    p = min(G, key=lambda g: (-vi[g], g))
    if vi[p] == 0:
        return ()
    rest = sum(vi[g] for g in G if g != p)
    if rest <= vi[p]:
        return (p,)
    return None


# ---------------------------------------------------------------- core
class Core:
    """The core case on agents A and goods G (Sections 3-5)."""

    def __init__(self, v, A, G):
        self.v = v
        self.A = sorted(A)
        self.G = frozenset(G)
        self.rank = {}
        self.pos = {}
        for i in self.A:
            R = [g for g in sorted(G) if v[i][g] > 0]
            check(len(R) == 3, f"core: agent {i} values {len(R)} goods")
            R.sort(key=lambda g: (-v[i][g], g))
            a, b, c = R
            check(v[i][a] < v[i][b] + v[i][c], f"core: agent {i} not strictly balanced")
            self.rank[i] = (a, b, c)
            self.pos[i] = {a: 0, b: 1, c: 2}
        self.pairs = {i: frozenset(self.rank[i][1:]) for i in self.A}
        self.tops = {i: frozenset([self.rank[i][0]]) for i in self.A}

    # -- basic notions
    def score(self, i, h):
        if h == self.pairs[i]:
            return 4
        if len(h) == 0:
            return 0
        check(len(h) == 1, "holding of size other than 0,1,2(pair)")
        (g,) = h
        return 3 - self.pos[i][g]

    def is_state(self, Y):
        seen = set()
        for i in self.A:
            h = Y[i]
            if not (len(h) == 0 or h == self.pairs[i] or (len(h) == 1 and next(iter(h)) in self.pos[i])):
                return False
            if seen & h:
                return False
            seen |= h
        return True

    def U(self, Y):
        return {i for i in self.A if Y[i] == self.pairs[i]}

    def holder(self, Y):
        hd = {}
        for i in self.A:
            for g in Y[i]:
                hd[g] = i
        return hd

    def J(self, Y):
        held = set()
        for i in self.A:
            held |= Y[i]
        return self.G - held

    def wants(self, Y, i, g):
        if Y[i] == self.pairs[i]:
            return False
        if g not in self.pos[i]:
            return False
        if len(Y[i]) == 0:
            return True
        (y,) = Y[i]
        return self.pos[i][g] < self.pos[i][y]

    def wanters(self, Y, g):
        return [i for i in self.A if self.wants(Y, i, g)]

    def wanted_goods(self, Y):
        return {g for i in self.A for g in self.pos[i] if self.wants(Y, i, g)}

    def valid(self, Y):
        hd = self.holder(Y)
        for g in self.wanted_goods(Y):
            if g not in hd or Y[hd[g]] != frozenset([g]):
                return False
        return True

    def free(self, Y):
        Uset = self.U(Y)
        F = []
        for i in self.A:
            if i in Uset:
                continue
            if len(Y[i]) == 0:
                F.append(i)
            else:
                (y,) = Y[i]
                if not self.wanters(Y, y):
                    F.append(i)
        return F

    def blockers(self, Y, o, J=None):
        if J is None:
            J = self.J(Y)
        S = J | Y[o]
        return [x for x in self.A if x != o and Y[x] == self.tops[x]
                and self.rank[x][1] in S and self.rank[x][2] in S]

    def nc(self, Y, J=None):
        if J is None:
            J = self.J(Y)
        for x in self.A:
            if Y[x] == self.tops[x] and self.rank[x][1] in J and self.rank[x][2] in J:
                return False
        return True

    # -- finishing, brute force from Definition 3
    def can_finish_sets(self, Y, o, F, J, limit=None):
        """All H subset of J allowed by Definition 3 (|H|<=|F|-1, hits every blocker)."""
        bl = self.blockers(Y, o, J)
        need = [self.pairs[x] for x in bl]
        Jl = sorted(J)
        out = []
        for s in range(0, min(len(F) - 1, len(Jl)) + 1):
            for H in combinations(Jl, s):
                Hs = set(H)
                if all(Hs & p for p in need):
                    out.append(frozenset(H))
                    if limit and len(out) >= limit:
                        return out
        return out

    def completion(self, Y, o, H, F, order=None):
        """Definition 3 completion; goods of H (index order) to free agents
        other than o (index order, or the given order)."""
        J = self.J(Y)
        recv = [f for f in F if f != o] if order is None else order
        check(len(H) <= len(recv), "completion: not enough free agents")
        X = {i: set(Y[i]) for i in self.A}
        for g, f in zip(sorted(H), recv):
            X[f].add(g)
        X[o] = set(Y[o]) | (J - set(H))
        return X

    def H_o(self, Y, o, J):
        """Set of goods h_x of the blockers of o (Lemma 6(b)), with the map x -> h_x."""
        hx = {}
        for x in self.blockers(Y, o, J):
            other = self.pairs[x] - Y[o]
            check(len(other) == 1, f"Lemma test(b): pair of blocker {x} is not {{y_o, h}}")
            (h,) = other
            check(h in J, "Lemma test(b): h_x not leftover")
            check(len(Y[o]) == 1 and Y[o] <= self.pairs[x], "Lemma test(b): y_o not in pair")
            hx[x] = h
        return set(hx.values()), hx

    # -- rings (Definition 4)
    def check_ring(self, Y, ring):
        k = len(ring)
        check(k >= 2, "ring: k < 2")
        check(len(set(ring)) == k, "ring: agents not distinct")
        Uset = self.U(Y)
        J = self.J(Y)
        F = set(self.free(Y))
        hs = []
        for t in range(k):
            w, w2 = ring[t], ring[(t + 1) % k]
            check(w not in Uset, "ring: agent in U")
            check(len(Y[w]) == 1, "ring: agent not holding a single good")
            (y,) = Y[w]
            is_want = self.wants(Y, w2, y)
            is_pair = (w in F and w2 in self.blockers(Y, w, J) and y in self.pairs[w2]
                       and len(self.pairs[w2] - {y}) == 1 and next(iter(self.pairs[w2] - {y})) in J)
            check(is_want or is_pair, f"ring: arrow {w}->{w2} is neither want nor pair arrow")
            check(not (is_want and w in F), "ring: free agent's good wanted")
            if w in F:
                check(is_pair, "ring: arrow from free agent is not a pair arrow")
                hs.append(next(iter(self.pairs[w2] - {y})))
            else:
                check(is_want, "ring: arrow from non-free agent is not a want arrow")
        check(len(hs) == len(set(hs)), "ring: h's of pair arrows not distinct")
        return sum(1 for t in range(k) if ring[t] in F)

    def trade_ring(self, Y, ring):
        F = set(self.free(Y))
        k = len(ring)
        Z = dict(Y)
        for t in range(k):
            w, w2 = ring[t], ring[(t + 1) % k]
            (y,) = Y[w]
            if w in F:
                Z[w2] = self.pairs[w2]
            else:
                Z[w2] = frozenset([y])
        return Z

    # -- chain (Lemma 5)
    def chain(self, Y, x):
        seq = [x]
        seen = {x: 0}
        while True:
            j = seq[-1]
            h = Y[j]
            check(len(h) <= 1, "chain: agent on path holds two goods")
            if len(h) == 0:
                break
            (g,) = h
            W = self.wanters(Y, g)
            if not W:
                break
            nxt = W[0]
            if nxt in seen:
                check(seen[nxt] >= 1, "chain: x repeats")
                return ('ring', seq[seen[nxt]:], None)
            seen[nxt] = len(seq)
            seq.append(nxt)
        Z = dict(Y)
        Z[x] = self.pairs[x]
        for t in range(1, len(seq)):
            Z[seq[t]] = Y[seq[t - 1]]
        return ('chain', seq, Z)

    # -- ring of Theorem 3's proof
    def improvement_ring(self, Y):
        J = self.J(Y)
        F = self.free(Y)
        Uset = self.U(Y)
        q, xo, used = {}, {}, set()
        f = len(F)
        for o in F:
            check(len(Y[o]) == 1, "improve: free agent holds nothing")
            Ho, hx = self.H_o(Y, o, J)
            check(len(Ho) >= f, "improve: |H_o| < |F|")
            cand = sorted(Ho - used)
            check(cand, "improve: no distinct leftover good")
            q[o] = cand[0]
            used.add(q[o])
            xo[o] = min(x for x in hx if hx[x] == q[o])
        Fs = set(F)

        def sigma(j):
            if j in Fs:
                return xo[j]
            (y,) = Y[j]
            W = self.wanters(Y, y)
            check(W, "improve: non-free agent's good not wanted")
            return W[0]
        start = min(i for i in self.A if i not in Uset)
        seq, seen = [start], {start: 0}
        while True:
            nxt = sigma(seq[-1])
            check(nxt not in Uset and nxt != seq[-1], "improve: sigma into U or fixed point")
            if nxt in seen:
                return seq[seen[nxt]:], q, xo
            seen[nxt] = len(seq)
            seq.append(nxt)


def de(v, checks=True, deep=False, stats=None):
    """Algorithm 1 (DE).  Returns the allocation X as a list of sets."""
    n = len(v)
    m = len(v[0]) if n else 0
    for i in range(n):
        check(sum(1 for g in range(m) if v[i][g] > 0) <= 3, "input: agent values > 3 goods")
        check(all(x >= 0 for x in v[i]), "input: negative value")
    A = list(range(n))
    G = set(range(m))
    X = [set() for _ in range(n)]
    peel = 0
    # peeling
    while len(A) >= 2:
        chosen = None
        for i in A:
            P = rule_r1(v[i], G)
            if P is not None:
                chosen = (i, P)
                break
        if chosen is None:
            break
        i, P = chosen
        if checks:
            # Lemma 1 conditions (i), (ii)
            check(len(P) <= 1, "peel: |P|>1")
            check(sum(v[i][g] for g in P) >= sum(v[i][g] for g in G if g not in P), "peel: (i) fails")
        X[i] = set(P)
        A.remove(i)
        G -= set(P)
        peel += 1
    if stats is not None:
        stats['peel'] = peel
        stats['core_n'] = len(A)
        stats['trades'] = 0
    if len(A) == 1:
        X[A[0]] = set(G)
        return X
    C = Core(v, A, G)  # asserts the core case (Lemma 2)
    # draft
    Y = {}
    taken = set()
    for i in C.A:
        Y[i] = frozenset()
        for g in C.rank[i]:
            if g not in taken:
                Y[i] = frozenset([g])
                taken.add(g)
                break
    if checks:
        check(C.is_state(Y) and C.valid(Y) and not C.U(Y), "draft: not a valid state with U empty")
    trades = 0
    kinds = []
    while True:
        J = C.J(Y)
        Uset = C.U(Y)
        old_scores = {i: C.score(i, Y[i]) for i in C.A}
        # 1. chain
        xs = [x for x in C.A if Y[x] == C.tops[x] and C.rank[x][1] in J and C.rank[x][2] in J]
        if xs:
            x = xs[0]
            kind, seq, Z = C.chain(Y, x)
            if kind == 'ring':
                if checks:
                    npair = C.check_ring(Y, seq)
                    check(npair == 0, "chain-ring has a pair arrow")
                Z = C.trade_ring(Y, seq)
                raised = set(seq)
                kinds.append('chain-ring')
            else:
                raised = set(seq)
                kinds.append('chain')
            trades += 1
        elif len(Uset) == len(C.A):
            o, H = C.A[0], frozenset()
            break
        else:
            F = C.free(Y)
            fin = None
            for o in F:
                Ho, _ = C.H_o(Y, o, J)
                if len(Ho) <= len(F) - 1:
                    fin = (o, frozenset(Ho))
                    break
            if checks and deep:
                deep_finish_checks(C, Y, F, J)
            if fin is not None:
                o, H = fin
                break
            ring, q, xo = C.improvement_ring(Y)
            if checks:
                npair = C.check_ring(Y, ring)
                if stats is not None:
                    stats.setdefault('ring_pairs', []).append(npair)
            Z = C.trade_ring(Y, ring)
            raised = set(ring)
            kinds.append('ring')
            trades += 1
        if checks:
            check(C.is_state(Z), "move: result is not a state")
            check(C.valid(Z), "move: result not valid")
            for i in C.A:
                s = C.score(i, Z[i])
                if i in raised:
                    check(s > old_scores[i], f"move: agent {i} on move did not gain")
                else:
                    check(s == old_scores[i], f"move: agent {i} off move changed score")
                    check(Z[i] == Y[i], f"move: agent {i} off move changed holding")
            check(sum(C.score(i, Z[i]) for i in C.A) > sum(old_scores.values()), "move: total did not rise")
        Y = Z
        check(trades <= 4 * len(C.A), "more than 4|A| trades")
    # finish
    F = C.free(Y)
    if checks:
        check(C.nc(Y), "finish without (NC)")
        if len(Uset) < len(C.A):
            check(o in F, "finisher not free")
            bl = C.blockers(Y, o, J)
            check(H <= J and len(H) <= len(F) - 1 and all(H & C.pairs[x] for x in bl),
                  "finish: H not allowed by Definition 3")
    Xc = C.completion(Y, o, H, F if o in F else [])
    for i in C.A:
        X[i] = set(Xc[i])
    if stats is not None:
        stats['trades'] = trades
        stats['kinds'] = kinds
        stats['finisher_holds_nothing'] = (len(Y[o]) == 0)
    return X


def deep_finish_checks(C, Y, F, J):
    """Lemma 6 (a)-(c) by brute force, and Theorem 1 for every allowed completion."""
    check(C.nc(Y, J), "deep: (NC) fails where expected")
    for o in F:
        bl = C.blockers(Y, o, J)
        if len(Y[o]) == 0:
            check(not bl, "Lemma 6(a): free agent holding nothing has a blocker")
        Ho, _ = C.H_o(Y, o, J)
        allowed = C.can_finish_sets(Y, o, F, J)
        check(bool(allowed) == (len(Ho) <= len(F) - 1), "Lemma 6(c): equivalence fails")
        if allowed:
            check(frozenset(Ho) in allowed, "Lemma 6(c): H_o not allowed")
            for H in allowed[:6]:
                for order in ([f for f in F if f != o], [f for f in F if f != o][::-1]):
                    Xc = C.completion(Y, o, H, F, order)
                    check_core_alloc(C, Xc, o)


def check_core_alloc(C, Xc, o):
    """EFX0 among core agents for a core allocation, + shape + completeness."""
    allg = set()
    for i in C.A:
        check(not (allg & Xc[i]), "core alloc: overlap")
        allg |= Xc[i]
    check(allg == set(C.G), "core alloc: incomplete")
    for i in C.A:
        if i != o:
            check(len(Xc[i]) <= 2, "core alloc: bundle other than X_o has > 2 goods")
    v = C.v
    for i in C.A:
        own = sum(v[i][g] for g in Xc[i])
        for j in C.A:
            if i == j:
                continue
            tot = sum(v[i][g] for g in Xc[j])
            for h in Xc[j]:
                check(tot - v[i][h] <= own, f"Theorem 1: {i} envies X_{j} minus {h}")


def check_output(v, X, stats=None):
    n = len(v)
    m = len(v[0]) if n else 0
    allg = set()
    for i in range(n):
        check(not (allg & X[i]), "output: goods given twice")
        allg |= X[i]
    check(allg == set(range(m)), "output: incomplete")
    big = sum(1 for i in range(n) if len(X[i]) > 2)
    check(big <= 1, "output: more than one bundle with > 2 goods")
    bad = efx0_violations(v, X)
    check(not bad, f"output: not EFX0 {bad[:3]}")
    if stats is not None:
        check(stats['peel'] <= n, "more than n peeling rounds")
        check(stats['trades'] <= 4 * n, "more than 4n trades")
