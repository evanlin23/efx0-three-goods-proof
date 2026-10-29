#!/usr/bin/env python3
"""Priority DE (PDE) for class D: the Priority Improvement Lemma as code.

Class D: every core agent is
    a three-good agent a > b > c with v(a) < v(b) + v(c)                       (pair P = {b, c});
    a small-d agent: v(b) + v(d) <= v(a) < v(b) + v(c), v(c) + v(d) <= v(b), v(a) + v(d) <= v(b) + v(c)   (P = {b, c});
    a type-T agent (type 12 of types4.py, with ties allowed in the proof): v(b) + v(c) <= v(a) < v(b) + v(c) + v(d)
        and v(c) + v(d) <= v(b)                                                 (P = {b, c, d}).
Ladder: nothing < d < c < b < a < P (no d for three goods). Only a holder of a is ever threatened, by sets containing
P; a holder of P wants nothing and is never threatened. Validity: (V1) + (V2) (lex.py).

Arcs of the exchange digraph (goods move along the arc, from tail to head):
    want arc     j -> w     j busy (holds a single good y_j that someone wants), w wants y_j: w takes y_j;
    full arc     o -> x     o free (holds y_o, unwanted), x holds a_x and is a blocker of o (P_x inside J + {y_o}):
                            x takes P_x (label P_x minus y_o, inside J);
    demoted arc  o -> x     the same x, but x takes only b_x (b_x = y_o, or b_x leftover: label {b_x} or nothing).
A *priority ring* is a cycle of such arcs with pairwise disjoint labels whose result is valid and better in the
priority order: its highest-priority agent improves (every arc's head improves, except the head of a demoted arc).

Priority Improvement Lemma (candidate): for every order pi, a valid state of a class-D instance that no free agent can
finish (and in which not every agent holds P) has a valid chain or grab, or a priority ring.
It implies that for every order the priority-maximal valid state of this ladder can be finished, and so EFX0 existence
for class D instances. improve_pde is the construction (PDE-3); every step is an assert, and check_all runs it on every
valid state that cannot be finished, for four orders.

    python3 pde_proof.py [instances] [seed] [--variants]
"""
import random
import sys
from collections import Counter

from model import relevant, describe
from lex import LexSpace
from gadgets import type_vals, bal3, TYPES


def agent_kind(vi):
    r = relevant(vi)
    x = [vi[g] for g in r]
    if len(r) == 3:
        return '3' if x[0] < x[1] + x[2] else None
    a, b, c, d = x
    if b + d <= a < b + c and c + d <= b and a + d <= b + c:
        return 'S'
    if b + c <= a < b + c + d and c + d <= b:
        return 'T'
    return None


def ladder_d(vi):
    r = relevant(vi)
    kind = agent_kind(vi)
    assert kind is not None, 'not a class-D agent'
    if kind == '3':
        a, b, c = r
        return [frozenset(), frozenset([c]), frozenset([b]), frozenset([a]), frozenset([b, c])]
    a, b, c, d = r
    P = frozenset([b, c]) if kind == 'S' else frozenset([b, c, d])
    return [frozenset()] + [frozenset([g]) for g in (d, c, b, a)] + [P]


class D:
    def __init__(self, n, m, v):
        self.n, self.m, self.v = n, m, v
        self.sp = LexSpace(n, m, v, ladder_d)
        self.R = [relevant(vi) for vi in v]          # a, b, c(, d)

    def setup(self, st):
        sp = self.sp
        self.st = tuple(st)
        self.Y = sp.holdings(st)
        self.J = frozenset(range(self.m)) - frozenset().union(*self.Y)
        self.W = [sp.wants(i, s) for i, s in enumerate(st)]
        self.wanted = frozenset().union(*self.W)
        self.top = [s == len(sp.lad[i]) - 1 for i, s in enumerate(st)]
        self.F = [i for i in range(self.n) if not self.top[i] and len(self.Y[i]) <= 1 and not (self.Y[i] & self.wanted)]
        self.P = [sp.lad[i][-1] for i in range(self.n)]

    def a(self, i):
        return self.R[i][0]

    def b(self, i):
        return self.R[i][1]

    def blockers(self, o):
        S = self.J | self.Y[o]
        return [x for x in range(self.n) if x != o and self.Y[x] == frozenset([self.a(x)]) and self.P[x] <= S]

    def can_finish(self, o):
        """DE's test: H meets P_x minus Y_o for every blocker x, |H| <= |F| - 1"""
        sets = [self.P[x] & self.J for x in self.blockers(o)]
        if any(not s for s in sets):
            return None
        from der import hitting_set
        return hitting_set(sets, len([f for f in self.F if f != o]))

    def chain(self):
        """DE's chain (a top-holder with P inside J), valid; None if there is none"""
        for x in range(self.n):
            if self.Y[x] == frozenset([self.a(x)]) and self.P[x] <= self.J:
                Y = list(self.Y)
                path = [x]
                while True:
                    j = path[-1]
                    if len(self.Y[j]) != 1 or not (self.Y[j] & self.wanted):
                        break
                    z = next(z for z in range(self.n) if self.Y[j] <= self.W[z])
                    if z in path:
                        cyc = path[path.index(z):]
                        for t, w in enumerate(cyc):
                            Y[cyc[(t + 1) % len(cyc)]] = self.Y[w]
                        st = self.as_state(Y)
                        if st:
                            return st
                        break
                    path.append(z)
                else:
                    pass
                Y = list(self.Y)
                Y[x] = self.P[x]
                for t in range(1, len(path)):
                    Y[path[t]] = self.Y[path[t - 1]]
                st = self.as_state(Y)
                if st:
                    return st
        return None

    def grab(self):
        """some agent moves to a higher rung made of its own goods and leftover goods; a single wanted good it gives up
        goes down the want chain (as in a chain); returns a valid new state or None"""
        for x in range(self.n):
            lad = self.sp.lad[x]
            for s in range(len(lad) - 1, self.st[x], -1):
                B = lad[s]
                if not B <= self.Y[x] | self.J:
                    continue
                Y = list(self.Y)
                if self.Y[x] <= B or not (self.Y[x] & self.wanted):
                    Y[x] = B
                else:
                    path = [x]
                    ok = True
                    while True:
                        j = path[-1]
                        if len(self.Y[j]) != 1 or not (self.Y[j] & self.wanted):
                            break
                        z = next(z for z in range(self.n) if self.Y[j] <= self.W[z])
                        if z in path:
                            ok = False
                            break
                        path.append(z)
                    if not ok:
                        continue
                    Y[x] = B
                    for t in range(1, len(path)):
                        Y[path[t]] = self.Y[path[t - 1]]
                st = self.as_state(Y)
                if st:
                    return st
        return None

    def as_state(self, Y):
        try:
            st = tuple(self.sp.lad[i].index(frozenset(B)) for i, B in enumerate(Y))
        except ValueError:
            return None
        return st if self.sp.is_valid(st) else None


def class_d_instance(rng, collision=False):
    if collision:
        A1, A2, A3, A4, y1, y2, h1, h2, h3, h4 = range(10)
        labels = [(A1, y1, (h1, h2)), (A2, y1, (h3, h4)), (A3, y2, (h1, h3)), (A4, y2, (h2, h4))]
        v = []
        for A, yy, (c, d) in labels:
            a, b, cc, dd = type_vals(rng, TYPES[11])
            trio = [yy, c, d]
            rng.shuffle(trio)
            v.append({A: a, trio[0]: b, trio[1]: cc, trio[2]: dd})
        for want, yy in (((A3, A4), y1), ((A1, A2), y2)):
            a, b, c = bal3(rng)
            v.append({want[0]: a, want[1]: b, yy: c})
        return 6, 10, v
    n = rng.choice([2, 3, 3, 4, 4, 5])
    m = rng.randint(4, 3 + n)
    v = []
    for _ in range(n):
        r = rng.random()
        if r < 0.45:
            vals = type_vals(rng, TYPES[11])
        elif r < 0.6:
            vals = type_vals(rng, TYPES[8])
        else:
            vals = bal3(rng)
        v.append(dict(zip(rng.sample(range(m), len(vals)), vals)))
    return n, m, v


# ---------------------------------------------------------------------------------------------------- PDE-1
def pde1(d, order):
    """the deterministic construction: returns (kind, new state) or raises AssertionError with the failing step"""
    rank = {a: k for k, a in enumerate(order)}
    n = d.n
    # 1. demoted SDR: free agents in priority order, each takes its lowest-priority blocker with a fresh demoted label
    rep, used = {}, set()
    for o in sorted(d.F, key=lambda i: rank[i]):
        cand = []
        for x in d.blockers(o):
            bx = d.b(x)
            if bx in d.Y[o] or bx in d.J:
                D = frozenset([bx]) & d.J
                if not (D & used):
                    cand.append((rank[x], x, D))
        assert cand, 'demoted SDR: no fresh demoted label'
        cand.sort(reverse=True)                          # lowest priority first
        r, x, D = cand[0]
        rep[o] = (x, frozenset([d.b(x)]), D)
        used |= D
    # 2. sigma: busy -> highest-priority wanter
    sigma = {}
    for j in range(n):
        if j in rep:
            sigma[j] = rep[j][0]
        elif d.Y[j] & d.wanted:
            ws = [w for w in range(n) if d.Y[j] <= d.W[w]]
            sigma[j] = min(ws, key=lambda w: rank[w])
    # 3. the cycles of sigma
    cycles, seen = [], set()
    for s in sigma:
        walk, j = [], s
        while j in sigma and j not in walk and j not in seen:
            walk.append(j)
            j = sigma[j]
        if j in walk:
            cycles.append(walk[walk.index(j):])
        seen |= set(walk)
    assert cycles, 'sigma has no cycle'
    tried = []
    for cyc in sorted(cycles, key=lambda c: min(rank[i] for i in c)):
        top = min(cyc, key=lambda i: rank[i])
        prev = cyc[(cyc.index(top) - 1) % len(cyc)]
        Y = list(d.Y)
        for t, w in enumerate(cyc):
            r = cyc[(t + 1) % len(cyc)]
            Y[r] = rep[w][1] if w in rep else d.Y[w]
        if prev not in rep:                              # the top is entered by a want arc: it improves
            st = d.as_state(Y)
            assert st is not None, 'demoted ring not valid'
            return 'demoted ring', st
        # 4. the top is a demoted blocker: upgrade it to its full arc
        x = top
        Y[x] = d.P[x]
        labels = [rep[w][2] for w in cyc if w in rep and w != prev] + [d.P[x] & d.J]
        if sum(len(L) for L in labels) == len(frozenset().union(*labels)):
            st = d.as_state(Y)
            if st is not None:
                return 'ring with one full arc', st
            tried.append('full upgrade not valid')
        else:
            tried.append('full upgrade: label conflict')
    raise AssertionError('no cycle works: ' + ', '.join(tried))


def check_pde1(N, seed):
    rng = random.Random(seed)
    out, ex = Counter(), {}
    for t in range(N):
        n, m, v = class_d_instance(rng, collision=(t % 5 == 4))
        d = D(n, m, v)
        orders = [tuple(range(n)), tuple(reversed(range(n)))] + [tuple(rng.sample(range(n), n)) for _ in range(2)]
        for st in d.sp.valid_states():
            d.setup(st)
            if all(d.top) or any(d.can_finish(o) is not None for o in d.F):
                continue
            if d.chain() is not None:
                out['chain'] += 1
                continue
            if d.grab() is not None:
                out['grab'] += 1
                continue
            for order in orders:
                try:
                    kind, new = pde1(d, order)
                    rank = {a: k for k, a in enumerate(order)}
                    ch = [i for i in range(n) if new[i] != st[i]]
                    topc = min(ch, key=lambda i: rank[i])
                    assert new[topc] > st[topc], 'not better in the priority order'
                    out[kind] += 1
                except AssertionError as e:
                    out['FAIL: ' + str(e)] += 1
                    ex.setdefault(str(e), (describe(v), order, [sorted(B) for B in d.Y]))
    return out, ex


# ---------------------------------------------------------------------------------------------------- PDE-2
def pde2(d, order, return_path=False):
    """x* = the highest-priority blocker, o* its free agent. A path from x* back to o* along want arcs and demoted
    arcs with pairwise disjoint labels avoiding x*'s full label, closed by the full arc o* -> x*. Depth-first search
    over paths. Returns the new state, or raises AssertionError."""
    rank = {a: k for k, a in enumerate(order)}
    blockers = {o: d.blockers(o) for o in d.F}
    allb = [(rank[x], x, o) for o in d.F for x in blockers[o]]
    assert allb, 'no blocker at all'
    r, xs, os_ = min(allb)
    Lstar = d.P[xs] & d.J

    def out(j):
        if d.Y[j] & d.wanted:
            return [(w, d.Y[j], frozenset()) for w in sorted(range(d.n), key=lambda w: rank[w]) if d.Y[j] <= d.W[w]]
        if j in d.F:
            res = []
            for x in sorted(blockers[j], key=lambda x: -rank[x]):
                bx = d.b(x)
                if bx in d.Y[j] or bx in d.J:
                    res.append((x, frozenset([bx]), frozenset([bx]) & d.J))
            return res
        return []

    def close(path):
        Y = list(d.Y)
        Y[xs] = d.P[xs]
        for j, (x, B, L) in path:
            Y[x] = B
        return d.as_state(Y)

    def dfs(j, path, seen, used):
        for x, B, L in out(j):
            if L & used:
                continue
            if x == xs:
                continue
            step = path + [(j, (x, B, L))]
            if x == os_:
                st = close(step)
                if st is not None:
                    return st, step
                continue
            if x in seen:
                continue
            r = dfs(x, step, seen | {x}, used | L)
            if r is not None:
                return r
        return None

    res = dfs(xs, [], {xs, os_}, set(Lstar))
    assert res is not None, 'no valid path from x* back to o*'
    return res if return_path else res[0]


def check_pde2(N, seed):
    rng = random.Random(seed)
    out, ex = Counter(), {}
    for t in range(N):
        n, m, v = class_d_instance(rng, collision=(t % 5 == 4))
        d = D(n, m, v)
        orders = [tuple(range(n)), tuple(reversed(range(n)))] + [tuple(rng.sample(range(n), n)) for _ in range(2)]
        for st in d.sp.valid_states():
            d.setup(st)
            if all(d.top) or any(d.can_finish(o) is not None for o in d.F):
                continue
            if d.chain() is not None:
                out['chain'] += 1
                continue
            if d.grab() is not None:
                out['grab'] += 1
                continue
            if not d.F:
                out['want ring (no free agent)'] += 1
                continue
            for order in orders:
                try:
                    new = pde2(d, order)
                    rank = {a: k for k, a in enumerate(order)}
                    ch = [i for i in range(n) if new[i] != st[i]]
                    topc = min(ch, key=lambda i: rank[i])
                    assert new[topc] > st[topc], 'not better in the priority order'
                    out['PDE-2 ring'] += 1
                except AssertionError as e:
                    out['FAIL: ' + str(e)] += 1
                    ex.setdefault(str(e), (describe(v), order, [sorted(B) for B in d.Y]))
    return out, ex


# ---------------------------------------------------------------------------------------------------- combined
def want_ring(d):
    """no free agent: every agent off its top rung is busy; follow the first wanter (DE's ring of want arrows)"""
    j = next(i for i in range(d.n) if not d.top[i])
    walk = []
    while j not in walk:
        walk.append(j)
        assert d.Y[j] & d.wanted, 'an agent off its top rung that is not busy'
        j = next(w for w in range(d.n) if d.Y[j] <= d.W[w])
    cyc = walk[walk.index(j):]
    Y = list(d.Y)
    for t, w in enumerate(cyc):
        Y[cyc[(t + 1) % len(cyc)]] = d.Y[w]
    st = d.as_state(Y)
    assert st is not None, 'want ring not valid'
    return st


def demoted_ring_improving(d, order):
    """PDE-1 steps 1-3 only: a cycle of the demoted SDR whose top is entered by a want arc"""
    rank = {a: k for k, a in enumerate(order)}
    rep, used = {}, set()
    for o in sorted(d.F, key=lambda i: rank[i]):
        cand = []
        for x in d.blockers(o):
            bx = d.b(x)
            if bx in d.Y[o] or bx in d.J:
                D_ = frozenset([bx]) & d.J
                if not (D_ & used):
                    cand.append((rank[x], x, D_))
        if not cand:
            return None
        cand.sort(reverse=True)
        r, x, D_ = cand[0]
        rep[o] = (x, frozenset([d.b(x)]), D_)
        used |= D_
    sigma = {}
    for j in range(d.n):
        if j in rep:
            sigma[j] = rep[j][0]
        elif d.Y[j] & d.wanted:
            sigma[j] = min((w for w in range(d.n) if d.Y[j] <= d.W[w]), key=lambda w: rank[w])
    seen = set()
    for s in sigma:
        walk, j = [], s
        while j in sigma and j not in walk and j not in seen:
            walk.append(j)
            j = sigma[j]
        seen |= set(walk)
        if j not in walk:
            continue
        cyc = walk[walk.index(j):]
        top = min(cyc, key=lambda i: rank[i])
        prev = cyc[(cyc.index(top) - 1) % len(cyc)]
        if prev in rep:
            continue
        Y = list(d.Y)
        for t, w in enumerate(cyc):
            Y[cyc[(t + 1) % len(cyc)]] = rep[w][1] if w in rep else d.Y[w]
        st = d.as_state(Y)
        if st is not None:
            return st
    return None


def pde3(d, order):
    """try the blockers x in priority order as the full arc o_x -> x; a path from x back to o_x along want arcs and
    demoted arcs into blockers of lower priority than x, labels pairwise disjoint and disjoint from x's full label"""
    rank = {a: k for k, a in enumerate(order)}
    pairs = sorted((rank[x], x, o) for o in d.F for x in d.blockers(o))
    for r, xs, os_ in pairs:
        Lstar = d.P[xs] & d.J

        def out(j):
            if d.Y[j] & d.wanted:
                return [(w, d.Y[j], frozenset()) for w in range(d.n) if d.Y[j] <= d.W[w]]
            if j in d.F:
                res = []
                for x in d.blockers(j):
                    bx = d.b(x)
                    if rank[x] > r and (bx in d.Y[j] or bx in d.J):
                        res.append((x, frozenset([bx]), frozenset([bx]) & d.J))
                return res
            return []

        def close(path):
            Y = list(d.Y)
            Y[xs] = d.P[xs]
            for j, (x, B, L) in path:
                Y[x] = B
            return d.as_state(Y)

        def dfs(j, path, seen, used):
            for x, B, L in out(j):
                if L & used or x == xs:
                    continue
                step = path + [(j, (x, B, L))]
                if x == os_:
                    st = close(step)
                    if st is not None:
                        return st
                    continue
                if x in seen:
                    continue
                res = dfs(x, step, seen | {x}, used | L)
                if res is not None:
                    return res
            return None

        st = dfs(xs, [], {xs, os_}, set(Lstar))
        if st is not None:
            return st
    raise AssertionError('no blocker gives a ring')


def improve_pde(d, order):
    """the construction: chain, grab, want ring (no free agent), demoted ring with improving top, PDE-2"""
    st = d.chain()
    if st is not None:
        return 'chain', st
    st = d.grab()
    if st is not None:
        return 'grab', st
    if not d.F:
        return 'want ring', want_ring(d)
    st = demoted_ring_improving(d, order)
    if st is not None:
        return 'demoted ring', st
    return 'PDE-3 ring', pde3(d, order)


def check_all(N, seed, orders_per=4):
    rng = random.Random(seed)
    out, ex = Counter(), {}
    for t in range(N):
        n, m, v = class_d_instance(rng, collision=(t % 5 == 4))
        d = D(n, m, v)
        orders = [tuple(range(n)), tuple(reversed(range(n)))] + [tuple(rng.sample(range(n), n))
                                                                  for _ in range(orders_per - 2)]
        for st in d.sp.valid_states():
            d.setup(st)
            if all(d.top) or any(d.can_finish(o) is not None for o in d.F):
                continue
            for order in orders:
                d.setup(st)
                try:
                    kind, new = improve_pde(d, order)
                    rank = {a: k for k, a in enumerate(order)}
                    ch = [i for i in range(n) if new[i] != st[i]]
                    topc = min(ch, key=lambda i: rank[i])
                    assert new[topc] > st[topc], 'not better in the priority order'
                    out[kind] += 1
                except AssertionError as e:
                    out['FAIL: ' + str(e)] += 1
                    ex.setdefault(str(e), (describe(v), order, [sorted(B) for B in d.Y]))
    return out, ex


def report(name, out, ex):
    print(name)
    for k in sorted(out):
        print('    %-50s %d' % (k, out[k]))
    for k, e in list(ex.items())[:3]:
        print('    example, %s: %s' % (k, e))
    return sum(c for k, c in out.items() if k.startswith('FAIL'))


if __name__ == '__main__':
    args = [x for x in sys.argv[1:] if not x.startswith('--')]
    N = int(args[0]) if args else 300
    seed = int(args[1]) if len(args) > 1 else 1
    fails = report('PDE-3 (the construction): chain, grab, want ring, demoted ring, PDE-3 ring', *check_all(N, seed))
    if '--variants' in sys.argv:          # the two simpler constructions, which fail (NOTES.md, section 9.2)
        report('PDE-1: demoted SDR, at most one upgraded arc', *check_pde1(N, seed))
        report('PDE-2: only the highest-priority blocker as the full arc', *check_pde2(N, seed))
    sys.exit(1 if fails else 0)
