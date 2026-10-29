#!/usr/bin/env python3
"""E_sum for class D': every valid state of maximum total score can be finished. The improvement step as code.

Class D' (pde_proof.agent_kind): three-good agents (ladder nothing < c < b < a < {b, c}); small-d agents (nothing < d <
c < b < a < {b, c}); type-T agents (b + c <= a < b + c + d, c + d <= b) on the threat ladder
nothing < d < c < b < a < {b, c, d} < {a, d} < {a, c} < {a, b}. In every case only a holder of a is threatened, by a set
containing the pair P ({b, c} or {b, c, d}), and b lies in P.

Cheap arcs (goods move from tail to head):
    want      busy j -> w (w wants y_j): w takes y_j, gain >= 1
    demoted   free o -> x, x a busy type-T blocker of o: x takes b_x (from Y_o or J): gain -1 (a to b), label {b_x} & J
    full      free o -> x, x a three-good or small-d blocker of o: x takes P_x: gain 1, label of one good
A free type-T blocker would grab {a, g} for a leftover g of its triple, so when no grab applies there is none (asserted).
improve(d) returns a valid state of larger total score, following the attempted proof; every step is an assert.

Psi = the number of type-T agents not holding exactly their a. A cheap ring of total gain 0 is an exact alternation
(free agent, demoted busy type-T blocker, free agent one rung up, ...); it leaves Psi unchanged exactly when every free
agent on it is a type-T agent that receives its own a. main() reports, for the states where every cheap ring has gain 0,
whether one of them raises Psi (then the pair (total score, Psi) rises without an upgrade or a demotion chain).

    python3 sum_proof.py [instances] [seed]
"""
import random
import sys
from collections import Counter

from model import relevant, describe
from lex import LexSpace, pair_ladder
from pde_proof import agent_kind, class_d_instance
from gadgets import type_vals, bal3, TYPES
from der import hitting_set


def ladder_dp(vi):
    k = agent_kind(vi)
    r = relevant(vi)
    assert k is not None, 'not a class-D agent'
    if k == '3':
        a, b, c = r
        return [frozenset(), frozenset([c]), frozenset([b]), frozenset([a]), frozenset([b, c])]
    a, b, c, d = r
    if k == 'S':
        return [frozenset()] + [frozenset([g]) for g in (d, c, b, a)] + [frozenset([b, c])]
    return pair_ladder(vi, 'threat')


class Fail(Exception):
    pass


def need(c, msg):
    if not c:
        raise Fail(msg)


class DP:
    def __init__(self, n, m, v):
        self.n, self.m, self.v = n, m, v
        self.sp = LexSpace(n, m, v, ladder_dp)
        self.R = [relevant(vi) for vi in v]
        self.kind = [agent_kind(vi) for vi in v]
        self.P = []
        for i, vi in enumerate(v):
            r = self.R[i]
            self.P.append(frozenset(r[1:3]) if self.kind[i] in '3S' else frozenset(r[1:4]))

    def setup(self, st):
        sp = self.sp
        self.st = tuple(st)
        self.Y = sp.holdings(st)
        self.J = frozenset(range(self.m)) - frozenset().union(*self.Y)
        self.W = [sp.wants(i, s) for i, s in enumerate(st)]
        self.wanted = frozenset().union(*self.W)
        self.top = [s == len(sp.lad[i]) - 1 for i, s in enumerate(st)]
        self.busy = [bool(self.Y[i] & self.wanted) for i in range(self.n)]
        self.F = [i for i in range(self.n) if not self.top[i] and len(self.Y[i]) <= 1 and not self.busy[i]]
        # inert agents: holding two or more goods (all such rungs are worth more than a: they want nothing and,
        # except a type-T agent's own pairs, which are envy-free, they are never threatened)
        self.U = [i for i in range(self.n) if len(self.Y[i]) >= 2]

    def score(self, i, B):
        return self.sp.lad[i].index(frozenset(B))

    def a(self, i):
        return self.R[i][0]

    def b(self, i):
        return self.R[i][1]

    def blockers(self, o):
        S = self.J | self.Y[o]
        return [x for x in range(self.n) if x != o and self.Y[x] == frozenset([self.a(x)]) and self.P[x] <= S]

    def can_finish(self, o):
        sets = [self.P[x] & self.J for x in self.blockers(o)]
        if any(not s for s in sets):
            return None
        return hitting_set(sets, len([f for f in self.F if f != o]))

    def finishable(self):
        if len(self.U) == self.n:
            return True                    # nobody can be threatened: any agent takes J
        return any(self.can_finish(o) is not None for o in self.F)

    def as_state(self, Y):
        try:
            st = tuple(self.sp.lad[i].index(frozenset(B)) for i, B in enumerate(Y))
        except ValueError:
            return None
        return st if self.sp.is_valid(st) else None

    # ------------------------------------------------------------------------------------------- Pareto moves
    def grab(self):
        for x in range(self.n):
            lad = self.sp.lad[x]
            for s in range(len(lad) - 1, self.st[x], -1):
                B = lad[s]
                if not B <= self.Y[x] | self.J:
                    continue
                Y = list(self.Y)
                if self.Y[x] <= B or not self.busy[x]:
                    Y[x] = B
                else:
                    path = [x]
                    ring = None
                    while True:
                        j = path[-1]
                        if not self.busy[j]:
                            break
                        z = next(z for z in range(self.n) if self.Y[j] <= self.W[z])
                        if z in path:
                            ring = path[path.index(z):]
                            break
                        path.append(z)
                    if ring is not None:            # a ring of want arrows: trade along it (DE's chain lemma)
                        for t, w in enumerate(ring):
                            Y[ring[(t + 1) % len(ring)]] = self.Y[w]
                        st = self.as_state(Y)
                        if st:
                            return st
                        continue
                    Y[x] = B
                    for t in range(1, len(path)):
                        Y[path[t]] = self.Y[path[t - 1]]
                st = self.as_state(Y)
                if st:
                    return st
        return None

    def want_ring(self):
        j = next(i for i in range(self.n) if i not in self.U)
        walk = []
        while j not in walk:
            walk.append(j)
            need(self.busy[j], 'no free agent, but an agent holding at most one good is not busy')
            j = next(w for w in range(self.n) if self.Y[j] <= self.W[w])
        cyc = walk[walk.index(j):]
        Y = list(self.Y)
        for t, w in enumerate(cyc):
            Y[cyc[(t + 1) % len(cyc)]] = self.Y[w]
        st = self.as_state(Y)
        need(st is not None, 'want ring not valid')
        return st

    # ------------------------------------------------------------------------------------------- cheap arcs
    def cheap_arcs(self, o):
        """(gain, x, new holding of x, label, kind) for the cheap arcs out of the free agent o"""
        out = []
        for x in self.blockers(o):
            sx = self.st[x]
            if self.busy[x] and self.kind[x] == 'T':
                bx = self.b(x)
                need(bx in self.Y[o] | self.J, 'b of a blocker outside Y_o + J')
                B = frozenset([bx])
                out.append((self.score(x, B) - sx, x, B, B & self.J, 'demoted'))
            elif self.kind[x] == 'T':
                need(False, 'a free type-T blocker, but no grab applies')
            else:                          # a three-good or small-d blocker: its pair needs one leftover good
                B = self.P[x]
                L = B & self.J
                need(len(L) == 1, 'a three-good or small-d blocker whose pair needs %d leftover goods' % len(L))
                out.append((self.score(x, B) - sx, x, B, L, 'full'))
        return out

    def wanters(self, j):
        y = self.Y[j]
        return [(self.score(w, y) - self.st[w], w) for w in range(self.n) if y <= self.W[w]]


def cheap_rings(d):
    """the cheap walk from every start outside U: at a busy agent the wanter with the largest gain; at a free agent the
    cheap arc with a fresh label, largest gain first. Yields (arcs of the cycle, holdings after trading, total gain)."""
    for start in range(d.n):
        if start in d.U:
            continue
        walk, arcs, used, j = [], [], set(), start
        ok = True
        while j not in walk:
            walk.append(j)
            if d.busy[j]:
                ws = sorted(d.wanters(j), reverse=True)
                need(ws, 'a busy agent with no wanter')
                g, w = ws[0]
                arcs.append((j, w, d.Y[j], frozenset(), g, 'want'))
                j = w
            elif j in d.F:
                cand = [c for c in d.cheap_arcs(j) if not (c[3] & used)]
                if not cand:
                    ok = False
                    break
                cand.sort(key=lambda c: -c[0])
                g, x, B, L, kind = cand[0]
                arcs.append((j, x, B, L, g, kind))
                used |= L
                j = x
            else:
                ok = False
                break
        need(ok, 'the cheap walk is stuck')
        cyc_arcs = arcs[walk.index(j):]
        gain = sum(a[4] for a in cyc_arcs)
        need(gain >= 0, 'a cheap ring with negative total gain')
        Y = list(d.Y)
        for (t, h, B, L, g, kind) in cyc_arcs:
            Y[h] = B
        yield cyc_arcs, Y, gain


def psi(d, Y):
    return sum(1 for i in range(d.n) if d.kind[i] == 'T' and Y[i] != frozenset([d.a(i)]))


def demotion_chain(d):
    """a busy agent x whose b is leftover drops to b (gain -1); a_x goes to its wanter with the largest gain, whose old
    good goes on to its best wanter if it is wanted, and so on (DE's chain); positive total gain; or None"""
    best = None
    for x in range(d.n):
        if not d.busy[x] or d.Y[x] != frozenset([d.a(x)]) or d.b(x) not in d.J:
            continue
        Y = list(d.Y)
        Y[x] = frozenset([d.b(x)])
        gain = d.score(x, Y[x]) - d.st[x]
        path, j = [x], x
        ok = True
        while d.busy[j]:
            ws = sorted(d.wanters(j), reverse=True)
            g, w = ws[0]
            if w in path:
                ok = False
                break
            Y[w] = d.Y[j]
            gain += g
            path.append(w)
            j = w
        if not ok or gain <= 0:
            continue
        new = d.as_state(Y)
        if new is not None and (best is None or gain > best[0]):
            best = (gain, new)
    return None if best is None else best[1]


def improve(d, st):
    """a valid state of larger total score, or Fail"""
    d.setup(st)
    s = d.grab()
    if s is not None:
        return 'grab', s
    for x in range(d.n):
        if d.Y[x] == frozenset([d.a(x)]):
            need(not d.P[x] <= d.J, '(NC) fails but no grab')
    if not d.F:
        need(len(d.U) < d.n, 'every agent inert but not finishable')
        return 'want ring', d.want_ring()
    for o in d.F:
        need(d.Y[o], 'a free agent holds nothing')
        need(d.blockers(o), 'a free agent without blockers')
    for cyc_arcs, Y, gain in cheap_rings(d):
        new = d.as_state(Y)
        need(new is not None, 'a cheap ring is not valid')
        if gain > 0:
            return 'cheap ring', new
        # gain 0: an exact alternation (free agent, demoted busy type-T blocker, free agent up one rung, ...).
        # Upgrade one demoted arc to the full arc (x takes P_x: gain +2 over the demoted arc) if its leftover goods
        # are not used elsewhere on the ring.
        for i, (t, h, B, L, g, kind) in enumerate(cyc_arcs):
            if kind != 'demoted':
                continue
            other = frozenset().union(*[a[3] for k2, a in enumerate(cyc_arcs) if k2 != i])
            if d.P[h] & d.J & other:
                continue
            Y2 = list(Y)
            Y2[h] = d.P[h]
            new2 = d.as_state(Y2)
            if new2 is not None:
                return 'exact alternation, one arc upgraded', new2
    new = demotion_chain(d)
    if new is not None:
        return 'demotion chain', new
    raise Fail('every cheap ring has total gain 0, no upgrade, no demotion chain')


def t_heavy_instance(rng):
    """mostly type-T agents whose tops come from a small pool of goods: shared tops, where Psi can stay flat"""
    n = rng.choice([3, 4, 4, 5, 5, 6])
    m = rng.randint(n + 1, n + 4)
    tops = rng.sample(range(m), rng.randint(1, max(1, n - 2)))
    v = []
    for _ in range(n):
        r = rng.random()
        vals = type_vals(rng, TYPES[11]) if r < 0.75 else type_vals(rng, TYPES[8]) if r < 0.85 else bal3(rng)
        A = rng.choice(tops)
        v.append(dict(zip([A] + rng.sample([g for g in range(m) if g != A], len(vals) - 1), vals)))
    return n, m, v


def alternation_gadget(rng):
    """two free three-good agents o1, o2 and busy type-T blockers x1, x2 whose triples contain each other's b, so that
    the cheap rings are exact alternations whose upgrades collide; x3 and x4 are further blockers, so that neither free
    agent can finish (12 goods)"""
    A1, A2, A3, A4, y1, y2, b1, b2, h3, h4, P, Q = range(12)

    def T(a, b, c, d):
        x = type_vals(rng, TYPES[11])
        return {a: x[0], b: x[1], c: x[2], d: x[3]}
    v = [T(A1, b1, y1, b2) if rng.random() < 0.5 else T(A1, b1, b2, y1),
         T(A2, b2, y2, b1) if rng.random() < 0.5 else T(A2, b2, b1, y2),
         T(A3, h3, y1, P) if rng.random() < 0.5 else dict(zip((A3, y1, h3), bal3(rng))),
         T(A4, h4, y2, Q) if rng.random() < 0.5 else dict(zip((A4, y2, h4), bal3(rng)))]
    for (w0, w1), y in (((A2, A4), y1), ((A1, A3), y2)):
        a, b, c = bal3(rng)
        w = [w0, w1]
        rng.shuffle(w)
        v.append({w[0]: a, w[1]: b, y: c})
    return 6, 12, v


FAMILIES = {
    'random': lambda rng: class_d_instance(rng),
    'collision': lambda rng: class_d_instance(rng, collision=True),
    'shared tops': t_heavy_instance,
    'alternation gadget': alternation_gadget,
}


def main(N, seed):
    rng = random.Random(seed)
    out, ex = Counter(), {}
    names = sorted(FAMILIES)
    for t in range(N):
        fam = names[t % len(names)]
        n, m, v = FAMILIES[fam](rng)
        if any(agent_kind(vi) is None for vi in v):
            continue
        d = DP(n, m, v)
        out['instances, ' + fam] += 1
        for st in d.sp.valid_states():
            d.setup(st)
            if d.finishable():
                continue
            try:
                kind, new = improve(d, st)
                need(sum(new) > sum(st), 'no increase')
                out['step: ' + kind] += 1
                if kind in ('exact alternation, one arc upgraded', 'demotion chain'):
                    d.setup(st)
                    up = any(psi(d, Y) > psi(d, d.Y) for c, Y, g in cheap_rings(d))
                    out['  (every cheap ring has gain 0; one raises Psi: %s)' % ('yes' if up else 'no')] += 1
            except Fail as e:
                out['FAIL: ' + str(e)] += 1
                ex.setdefault(str(e), (describe(v), [sorted(B) for B in d.Y]))
    for k in sorted(out, key=lambda k: (not k.startswith('instances'), k.startswith('  '), k)):
        print('%-62s %d' % (k, out[k]))
    for k, e in list(ex.items())[:6]:
        print('  %s: %s' % (k, e))
    return 1 if any(k.startswith('FAIL') for k in out) else 0


if __name__ == '__main__':
    sys.exit(main(int(sys.argv[1]) if len(sys.argv) > 1 else 1200, int(sys.argv[2]) if len(sys.argv) > 2 else 1))
