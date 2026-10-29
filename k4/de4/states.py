"""Generalized Draft-and-Exchange states for agents with three or four relevant goods (core agents: top worth less than
the other relevant goods together).

A *ladder* gives each agent a list of holdings (frozensets of its relevant goods), from score 0 (nothing) upwards; the
score of a holding is its position. An agent wants a good g if g is relevant to it, not in its holding, and the
holding {g} is a higher rung than its current holding (for the ladders here this is the same as v(g) > v(holding)).
A state is valid if every wanted good is held alone. Free agents hold nothing or a single good nobody wants, and are
not on their top rung. Finishing (as in the paper): a free agent o takes Y_o plus J minus H, with |H| <= |F| - 1 and
each good of H given to a different free agent other than o. Here finishing is tested exactly: the completion must be
EFX0 by the raw definition (model.is_efx0), trying every H and every assignment of H.
"""
import itertools

from model import val, is_efx0, relevant


# ---------------------------------------------------------------------------------------------------- ladders
def ladder_k3(vi):
    """the paper's ladder: nothing, c, b, a, {b, c}"""
    a, b, c = relevant(vi)
    return [frozenset(), frozenset([c]), frozenset([b]), frozenset([a]), frozenset([b, c])]


def ladder_singles_T(vi):
    """4 goods: nothing, d, c, b, a, T with T the larger of {a, d} and {b, c} (an envy-free pair)"""
    r = relevant(vi)
    if len(r) == 3:
        return ladder_k3(vi)
    a, b, c, d = r
    T = frozenset([a, d]) if vi[a] + vi[d] >= vi[b] + vi[c] else frozenset([b, c])
    return [frozenset()] + [frozenset([g]) for g in (d, c, b, a)] + [T]


def ladder_singles_triple(vi):
    """4 goods: nothing, d, c, b, a, {b, c, d}"""
    r = relevant(vi)
    if len(r) == 3:
        return ladder_k3(vi)
    a, b, c, d = r
    return [frozenset()] + [frozenset([g]) for g in (d, c, b, a)] + [frozenset([b, c, d])]


def ladder_all_pairs(vi):
    """4 goods: nothing, every single and every pair, by value (strict values assumed), up to the first envy-free
    pair (holdings above it are never needed: it already wants nothing and fears nothing)"""
    r = relevant(vi)
    if len(r) == 3:
        return ladder_k3(vi)
    tot = val(vi, r)
    hs = [frozenset([g]) for g in r] + [frozenset(p) for p in itertools.combinations(r, 2)]
    hs.sort(key=lambda B: (val(vi, B), sorted(B)))
    out = [frozenset()]
    for B in hs:
        out.append(B)
        if len(B) == 2 and 2 * val(vi, B) >= tot:
            break
    return out


LADDERS = {'k3': ladder_k3, 'T': ladder_singles_T, 'triple': ladder_singles_triple, 'pairs': ladder_all_pairs}


# ---------------------------------------------------------------------------------------------------- states
class Space:
    """the states of one instance for one ladder"""

    def __init__(self, n, m, v, ladder):
        self.n, self.m, self.v = n, m, v
        self.lad = [ladder(v[i]) for i in range(n)]
        self.R = [frozenset(relevant(v[i])) for i in range(n)]

    def wants(self, i, s):
        """goods agent i wants at rung s"""
        lad = self.lad[i]
        if s == len(lad) - 1:
            return frozenset()
        higher = lad[s + 1:]
        return frozenset(g for g in self.R[i] if g not in lad[s] and frozenset([g]) in higher)

    def all_states(self):
        n = self.n
        res, cur = [], [0] * n

        def rec(i, used):
            if i == n:
                res.append(tuple(cur))
                return
            for s, B in enumerate(self.lad[i]):
                if not (B & used):
                    cur[i] = s
                    rec(i + 1, used | B)
        rec(0, frozenset())
        return res

    def info(self, st):
        """holdings, leftover goods, wanted goods, validity, free agents"""
        Y = [self.lad[i][s] for i, s in enumerate(st)]
        held = frozenset().union(*Y)
        J = frozenset(range(self.m)) - held
        W = [self.wants(i, s) for i, s in enumerate(st)]
        wanted = frozenset().union(*W)
        alone = frozenset(next(iter(B)) for B in Y if len(B) == 1)
        valid = wanted <= alone
        top = [s == len(self.lad[i]) - 1 for i, s in enumerate(st)]
        F = [i for i in range(self.n) if not top[i] and len(Y[i]) <= 1 and not (Y[i] & wanted)]
        return Y, J, W, wanted, valid, F, top

    def completions(self, st, maxH=None):
        """every completion of the paper's form (owner o free, or any agent if all are on the top rung)"""
        Y, J, W, wanted, valid, F, top = self.info(st)
        Jl = sorted(J)
        owners = F if not all(top) else list(range(self.n))
        for o in owners:
            others = [f for f in F if f != o]
            lim = len(others) if maxH is None else min(len(others), maxH)
            for k in range(lim + 1):
                for H in itertools.combinations(Jl, k):
                    rest = J - frozenset(H)
                    for recv in itertools.permutations(others, k):
                        X = [set(B) for B in Y]
                        X[o] |= rest
                        for h, f in zip(H, recv):
                            X[f].add(h)
                        yield o, H, recv, X

    def finishable(self, st, maxH=None):
        for o, H, recv, X in self.completions(st, maxH):
            if is_efx0(self.v, X):
                return (o, H, recv, X)
        return None

    def dominated_by(self, st, valid_states):
        """valid states that Pareto-dominate st in scores"""
        return [t for t in valid_states if t != st and all(a >= b for a, b in zip(t, st))]

    def pareto_max(self, valid_states):
        """the valid states that no valid state Pareto-dominates in scores. In decreasing order of total score, a
        state is dominated iff some maximal state found before it dominates it."""
        out = []
        for st in sorted(set(valid_states), key=lambda s: -sum(s)):
            if not any(all(a >= b for a, b in zip(t, st)) for t in out):
                out.append(st)
        return out

    def draft(self, order=None):
        """each agent in turn takes its highest single rung whose good is not taken"""
        order = range(self.n) if order is None else order
        st = [0] * self.n
        used = set()
        for i in order:
            lad = self.lad[i]
            best = 0
            for s, B in enumerate(lad):
                if len(B) == 1 and not (B & used):
                    best = s
            st[i] = best
            used |= lad[best]
        return tuple(st)


# ---------------------------------------------------------------------------------------------------- liberal finishing
def liberal_finishable(sp, st):
    """the most liberal completion of DE's shape: any owner o, each good of H to a different agent other than o that
    holds at most one good; raw EFX0 check. A state with J empty is finishable iff it is EFX0 itself."""
    Y, J, W, wanted, valid, F, top = sp.info(st)
    Jl = sorted(J)
    if not J:
        return is_efx0(sp.v, [set(B) for B in Y])
    small = [i for i in range(sp.n) if len(Y[i]) <= 1]
    for o in range(sp.n):
        others = [f for f in small if f != o]
        for k in range(len(others) + 1):
            for H in itertools.combinations(Jl, k):
                rest = J - frozenset(H)
                for recv in itertools.permutations(others, k):
                    X = [set(B) for B in Y]
                    X[o] |= rest
                    for h, f in zip(H, recv):
                        X[f].add(h)
                    if is_efx0(sp.v, X):
                        return True
    return False
