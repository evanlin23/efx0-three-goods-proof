"""Candidate for k = 4: priority-maximal valid states over the pair ladder.

Ladder (score = position; rungs in increasing order of value, strict values assumed):
    three goods a > b > c:   nothing, c, b, a, {b, c}                             (the paper's ladder)
    four goods a > b > c > d: nothing, the four singles and the pairs worth more than a, by value; plus the triple
                              {b, c, d} if the agent is big-top (v(a) > v(b) + v(c))

A state gives each agent a rung, the holdings pairwise disjoint. It is *valid* if
    (V1) every wanted good (a good whose singleton is a higher rung than the holding) is the whole holding of an agent;
    (V2) the holdings form a partial EFX0 allocation: no agent EFX0-envies another agent's holding.
For pairs (V2) follows from (V1) (a pair threatens j only by a single good worth more than j's holding, which j then
wants); it matters for the triples of big-top agents.

Priority: for an order pi of the agents, a state is pi-better than another if the score vectors, read in the order pi,
are lexicographically larger. The candidate statement:

    E_lex: for every order pi, the pi-maximal valid state can be finished:
           some agent o whose holding contains no wanted good takes its holding plus the leftover goods minus H, and
           the goods of H go to different free agents other than o (free: holding at most one good, nobody wants it,
           not on the top rung); the result is EFX0 (raw check).
"""
import itertools

from model import val, threat, is_efx0, relevant

PAIRS = ['ab', 'ac', 'ad', 'bc', 'bd', 'cd']


def threat_sets(vals):
    """the minimal threat sets of an agent's single holdings: for each single y, the minimal sets S of goods ranked
    below y with v(S) > v(y) (names over 'abcd')"""
    names = 'abcd'[:len(vals)]
    v = dict(zip(names, vals))
    out = set()
    for k, y in enumerate(names):
        below = names[k + 1:]
        for size in range(2, len(below) + 1):
            for S in itertools.combinations(below, size):
                if sum(v[x] for x in S) > v[y] and not any(set(T) < set(S) for T in out if sum(v[x] for x in T) > v[y]
                                                           and set(T) <= set(below)):
                    out.add(''.join(S))
    return out


def pair_ladder(vi, rule='threat'):
    """rule 'all': every pair; 'above-top': the pairs worth more than a; 'threat' (the default): the pairs with a and
    the minimal threat sets of the singles"""
    r = relevant(vi)
    if len(r) == 3:
        a, b, c = r
        return [frozenset(), frozenset([c]), frozenset([b]), frozenset([a]), frozenset([b, c])]
    g = dict(zip('abcd', r))
    if rule == 'threat':
        names = sorted(set(['ab', 'ac', 'ad']) | threat_sets([vi[x] for x in r]))
    else:
        names = [p for p in PAIRS if rule == 'all' or vi[g[p[0]]] + vi[g[p[1]]] > vi[g['a']]]
        if vi[g['a']] > vi[g['b']] + vi[g['c']]:
            names.append('bcd')
    hs = [frozenset([x]) for x in r] + [frozenset(g[ch] for ch in s) for s in names]
    hs.sort(key=lambda B: (val(vi, B), sorted(B)))
    return [frozenset()] + hs


class LexSpace:
    def __init__(self, n, m, v, ladder=pair_ladder):
        """ladder: a function of an agent's values, or 'all' / 'above-top' for pair_ladder's rules"""
        if isinstance(ladder, str):
            rule = ladder
            ladder = lambda vi: pair_ladder(vi, rule)
        self.n, self.m, self.v = n, m, v
        self.lad = [ladder(v[i]) for i in range(n)]
        self.R = [frozenset(relevant(v[i])) for i in range(n)]
        self._valid = None

    def wants(self, i, s):
        lad = self.lad[i]
        higher = lad[s + 1:]
        return frozenset(g for g in self.R[i] if g not in lad[s] and frozenset([g]) in higher)

    def holdings(self, st):
        return [self.lad[i][s] for i, s in enumerate(st)]

    def is_valid(self, st):
        Y = self.holdings(st)
        alone = set(next(iter(B)) for B in Y if len(B) == 1)
        for i, s in enumerate(st):
            if not self.wants(i, s) <= alone:
                return False
        own = [val(self.v[i], Y[i]) for i in range(self.n)]
        for j, B in enumerate(Y):
            if len(B) >= 2:
                for i in range(self.n):
                    if i != j and threat(self.v[i], B) > own[i]:
                        return False
        return True

    def all_states(self):
        res, cur = [], [0] * self.n

        def rec(i, used):
            if i == self.n:
                res.append(tuple(cur))
                return
            for s, B in enumerate(self.lad[i]):
                if not (B & used):
                    cur[i] = s
                    rec(i + 1, used | B)
        rec(0, frozenset())
        return res

    def valid_states(self):
        if self._valid is None:
            self._valid = [s for s in self.all_states() if self.is_valid(s)]
        return self._valid

    def lex_max(self, order):
        return max(self.valid_states(), key=lambda s: tuple(s[i] for i in order))

    def draft_rest(self, order, k, st, used):
        """the agents order[k:] each take, in order, their highest single not yet taken (or nothing)"""
        st, used = list(st), set(used)
        for i in order[k:]:
            best = 0
            for s, B in enumerate(self.lad[i]):
                if len(B) == 1 and not (B & used):
                    best = s
            st[i] = best
            used |= self.lad[i][best]
        return tuple(st)

    def priority_draft(self, order):
        """Priority Draft: in the order, each agent takes the highest rung (disjoint from the goods taken) such that the
        choices so far, completed by the draft of the remaining agents, form a valid state"""
        st, used = [0] * self.n, set()
        for k, i in enumerate(order):
            for s in range(len(self.lad[i]) - 1, -1, -1):
                B = self.lad[i][s]
                if B & used:
                    continue
                cand = list(st)
                cand[i] = s
                if self.is_valid(self.draft_rest(order, k + 1, cand, used | B)):
                    st[i] = s
                    used |= B
                    break
            else:
                raise AssertionError('no rung keeps the state valid')
        return tuple(st)

    def free(self, st):
        Y = self.holdings(st)
        wanted = set().union(*[self.wants(i, s) for i, s in enumerate(st)])
        top = [s == len(self.lad[i]) - 1 for i, s in enumerate(st)]
        F = [i for i in range(self.n) if not top[i] and len(Y[i]) <= 1 and not (Y[i] & wanted)]
        owners = [i for i in range(self.n) if not (Y[i] & wanted)]
        return Y, F, owners

    def finish(self, st):
        """a completion (owner, H, receivers, X) that is EFX0, or None"""
        Y, F, owners = self.free(st)
        J = sorted(set(range(self.m)) - set().union(*Y))
        for o in owners:
            rec = [f for f in F if f != o]
            for k in range(len(rec) + 1):
                for H in itertools.combinations(J, k):
                    for to in itertools.permutations(rec, k):
                        X = [set(B) for B in Y]
                        X[o] |= set(J) - set(H)
                        for h, f in zip(H, to):
                            X[f].add(h)
                        if is_efx0(self.v, X):
                            return o, H, to, X
        return None


def rung_threat_sets(vi, B):
    """the minimal threat sets of holding B: sets T of unwanted goods outside B, |T| >= 2, v(T) > v(B)"""
    hv = val(vi, B)
    unw = [g for g in relevant(vi) if g not in B and vi[g] <= hv]
    out = []
    for size in range(2, len(unw) + 1):
        for T in itertools.combinations(unw, size):
            if val(vi, T) > hv and not any(set(S) < set(T) for S in out):
                out.append(frozenset(T))
    return out


if __name__ == '__main__':
    from types4 import all_types
    print('The threat ladder of each strict type, and the minimal threat sets of each rung (all are higher rungs).')
    for t, vals in sorted(all_types().items()):
        vi = dict(zip('abcd', vals))
        lad = pair_ladder(vi, 'threat')
        name = lambda B: ''.join(sorted(B))
        rows = []
        for k, B in enumerate(lad):
            ts = rung_threat_sets(vi, B) if B else []
            for T in ts:
                assert T in lad[k + 1:], 'a threat set that is not a higher rung'
            if ts:
                rows.append('%s: %s' % (name(B), ', '.join(name(T) for T in ts)))
        print('%-28s %-14s %s' % (t, vals, ' < '.join(name(B) for B in lad[1:])))
        print('%44s threats  %s' % ('', '; '.join(rows)))
    print('closure holds for every type')
