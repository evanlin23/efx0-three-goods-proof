"""DER (Draft, Exchange, Release): a DE-style procedure for agents with at most four relevant goods, on the threat
ladder of lex.py. Experimental: the steps are defined here and checked on data (der_check.py); there is no proof.

Objects (for one core instance; agents have three or four relevant goods, strict values):
  ladder      lex.pair_ladder(rule='threat'): singles, pairs with a, and the minimal threat sets of the singles;
              the threat sets of every rung are again rungs, higher up (python3 lex.py checks this);
  state       a rung per agent, holdings pairwise disjoint; J = the leftover goods;
  wants       goods whose singleton is a higher rung than the holding;
  valid       (V1) wanted goods are held alone, (V2) the holdings form a partial EFX0 allocation;
  threat set  of agent x: a minimal set T of x's unwanted goods outside its holding with v_x(T) > v_x(holding), |T| >= 2;
  free        holds at most one good, which nobody wants (and is not on its top rung);
  owner       an agent whose holding contains no wanted good;
  blocker     of an owner o: (x, T) with x != o and T a threat set of x inside J + Y_o;
  finishing   o can finish with H (a subset of J) if H meets T minus Y_o for every blocker (x, T) of o (so no T lies
              inside Y_o) and |H| <= |F minus o|; completion: X_o = Y_o + J - H, the goods of H to free agents other
              than o, one each.

Moves, tried in this order by step() (DER also starts with peeling by R1 and the draft; see der_run.py):
  finish  some owner can finish.
  grab    some agent x moves to a higher rung B made of its own goods and leftover goods (chain() tries x's threat sets
          inside J first, as DE's chain). If x gives up a single wanted good, it goes to the first agent that wants it,
          whose old good goes on in the same way; the last released holding becomes leftover. If an agent repeats, the
          agents from its first occurrence form a ring of want arrows: trade along it.
  ring    first ring(): sigma(o) = a blocker x_o of the owner o (chosen along the walk so that the leftover goods it
          uses are fresh), sigma(j) = the first agent that wants j's good for an agent j holding a single wanted good;
          follow sigma from agent 0 and trade along the cycle. Then general_ring(): a depth-first search for a cycle of
          upgrade arrows (x_t moves to a higher rung made of its own goods, goods of x_{t+1} and leftover goods).
  release (release_finishes()) one agent moves to a lower rung after which some owner can finish.
"""
import itertools

from model import val, threat, is_efx0, relevant
from lex import LexSpace


def hitting_set(sets, cap):
    """a smallest set H (a sorted tuple) meeting every set of `sets` (each of at most three goods), if |H| <= cap;
    else None. Branches on an unmet set; the sets are small, so this is fast in practice."""
    sets = [frozenset(s) for s in sets]
    best = [None]

    def rec(H, k):
        if best[0] is not None and len(H) >= len(best[0]):
            return
        unmet = [s for s in sets if not (s & H)]
        if not unmet:
            best[0] = tuple(sorted(H))
            return
        if len(H) >= cap:
            return
        s = min(unmet, key=len)
        for g in sorted(s):
            rec(H | {g}, k + 1)
    rec(frozenset(), 0)
    return best[0]


class DER:
    def __init__(self, n, m, v):
        self.sp = LexSpace(n, m, v, 'threat')
        self.n, self.m, self.v = n, m, v

    # ------------------------------------------------------------------------------------------------ basic objects
    def setup(self, st):
        sp, n = self.sp, self.n
        self.st = tuple(st)
        self.Y = sp.holdings(st)
        held = set().union(*self.Y)
        self.J = frozenset(range(self.m)) - held
        self.W = [sp.wants(i, s) for i, s in enumerate(st)]
        self.wanted = frozenset().union(*self.W)
        self.top = [s == len(sp.lad[i]) - 1 for i, s in enumerate(st)]
        self.F = [i for i in range(n) if not self.top[i] and len(self.Y[i]) <= 1 and not (self.Y[i] & self.wanted)]
        self.owners = [i for i in range(n) if not (self.Y[i] & self.wanted)]

    def threat_sets(self, x):
        vi, B = self.v[x], self.Y[x]
        hv = val(vi, B)
        unw = [g for g in relevant(vi) if g not in B and g not in self.W[x]]
        out = []
        for size in range(2, len(unw) + 1):
            for T in itertools.combinations(unw, size):
                if val(vi, T) > hv and not any(set(S) < set(T) for S in out):
                    out.append(frozenset(T))
        return out

    def blockers(self, o):
        S = self.J | self.Y[o]
        return [(x, T) for x in range(self.n) if x != o for T in self.threat_sets(x) if T <= S]

    def can_finish(self, o):
        if o not in self.owners:
            return None
        sets = []
        for x, T in self.blockers(o):
            rest = T & self.J
            if not rest:
                return None
            sets.append(rest)
        cap = len([f for f in self.F if f != o])
        return hitting_set(sets, cap)

    def completion(self, o, H):
        X = [set(B) for B in self.Y]
        X[o] |= self.J - set(H)
        for h, f in zip(H, [f for f in self.F if f != o]):
            X[f].add(h)
        return X

    def rung(self, i, B):
        return self.sp.lad[i].index(frozenset(B))

    def first_wanter(self, g):
        return next(z for z in range(self.n) if g in self.W[z])

    # ------------------------------------------------------------------------------------------------ moves
    def chain(self, x, T):
        """the state after x's chain with new holding T (a higher rung inside Y_x + J), or None if it is not valid.
        If x gives up a single wanted good, it goes down the want chain as in DE; if x keeps its good, nothing
        moves but x."""
        Y = list(self.Y)
        if self.Y[x] <= T:
            Y[x] = T
            return self.as_state(Y)
        path = [x]
        while True:
            j = path[-1]
            if len(self.Y[j]) != 1 or not (self.Y[j] & self.wanted):
                break
            z = self.first_wanter(next(iter(self.Y[j])))
            if z in path:
                cyc = path[path.index(z):]
                for t, w in enumerate(cyc):
                    Y[cyc[(t + 1) % len(cyc)]] = self.Y[w]
                return self.as_state(Y)
            path.append(z)
        Y[x] = T
        for t in range(1, len(path)):
            Y[path[t]] = self.Y[path[t - 1]]
        return self.as_state(Y)

    def as_state(self, Y):
        try:
            st = tuple(self.rung(i, B) for i, B in enumerate(Y))
        except ValueError:
            return None
        return st if self.sp.is_valid(st) else None

    def ring(self):
        """the ring of the walk construction; returns (state or None, reason)"""
        walk, used, choice = [], set(), {}
        j = 0
        while j not in walk:
            walk.append(j)
            if self.Y[j] & self.wanted:                 # busy: a single wanted good (V1)
                j = self.first_wanter(next(iter(self.Y[j])))
            else:                                       # an owner that cannot finish: it has a blocker
                cand = [(x, T) for x, T in self.blockers(j) if not ((T & self.J) & used)]
                if not cand:
                    return None, 'no blocker with fresh leftover goods at owner %d' % j
                x, T = cand[0]
                choice[j] = (x, T)
                used |= T & self.J
                j = x
        cyc = walk[walk.index(j):]
        Y = list(self.Y)
        for t, w in enumerate(cyc):
            r = cyc[(t + 1) % len(cyc)]
            Y[r] = choice[w][1] if w in choice else self.Y[w]
        st = self.as_state(Y)
        return st, None if st else 'ring result not valid'

    def upgrade_arrows(self, x):
        """(w, B): x can move to the higher rung B made of its own goods, goods of w's holding (at least one) and
        leftover goods"""
        out = []
        lad = self.sp.lad[x]
        for w in range(self.n):
            if w == x or not self.Y[w]:
                continue
            pool = self.Y[x] | self.Y[w] | self.J
            for s in range(len(lad) - 1, self.st[x], -1):
                B = lad[s]
                if B <= pool and B & self.Y[w]:
                    out.append((w, B))
        return out

    def general_ring(self):
        """a cycle of upgrade arrows x_0 -> x_1 -> ... -> x_0 (x_t moves to a rung B_t that takes goods of x_{t+1})
        whose result is a valid state: each agent of the cycle moves to its new rung; a good of x_{t+1} goes only to
        x_t, and x_{t+1} does not keep it; leftover goods are used at most once; goods of a cycle agent that nobody
        takes become leftover. Depth-first search; returns the new state or None."""
        n = self.n
        arrows = {x: self.upgrade_arrows(x) for x in range(n)}

        def result(path):
            Y = list(self.Y)
            fromJ = set()
            for t, (x, B, w) in enumerate(path):
                if (B & self.J) & fromJ:
                    return None
                fromJ |= B & self.J
                keep_w = path[(t + 1) % len(path)][1] & self.Y[w]
                if (B & self.Y[w]) & keep_w:
                    return None
            for x, B, w in path:
                Y[x] = B
            return self.as_state(Y)

        def dfs(path, agents):
            x, B, w = path[-1]
            if w == path[0][0]:
                return result(path)
            if w in agents or len(path) >= n:
                return None
            for w2, B2 in arrows[w]:
                r = dfs(path + [(w, B2, w2)], agents | {w})
                if r is not None:
                    return r
            return None

        for x in range(n):
            for w, B in arrows[x]:
                r = dfs([(x, B, w)], {x})
                if r is not None:
                    return r
        return None

    # ------------------------------------------------------------------------------------------------ one step
    def step(self, st):
        """('finish', o, H) | ('chain', new) | ('ring', new) | ('stuck', reason)"""
        self.setup(st)
        if all(self.top):
            return ('finish', 0, ())
        for o in self.owners:
            H = self.can_finish(o)
            if H is not None:
                return ('finish', o, H)
        for x in range(self.n):
            for T in self.threat_sets(x):
                if T <= self.J:
                    new = self.chain(x, T)
                    if new is not None:
                        return ('chain', new)
        for x in range(self.n):                         # grab: a higher rung made of x's goods and leftover goods
            for s in range(len(self.sp.lad[x]) - 1, self.st[x], -1):
                B = self.sp.lad[x][s]
                if B <= self.Y[x] | self.J:
                    new = self.chain(x, B)
                    if new is not None:
                        return ('grab', new)
        new, why = self.ring()
        if new is not None:
            return ('ring', new)
        new = self.general_ring()
        if new is not None:
            return ('general ring', new)
        return ('stuck', why)

    def release_finishes(self, st):
        """a lower rung for one agent after which some owner can finish"""
        for i in range(self.n):
            for r in range(st[i] - 1, -1, -1):
                t = st[:i] + (r,) + st[i + 1:]
                if self.sp.is_valid(t):
                    self.setup(t)
                    for o in self.owners:
                        if self.can_finish(o) is not None:
                            return i, r, o
        return None
