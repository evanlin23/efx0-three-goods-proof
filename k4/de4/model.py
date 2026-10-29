"""Raw definitions for the k = 4 experiments: instances, EFX0, brute-force search for EFX0 allocations, and random
core instances with at most four relevant goods per agent.

An instance is (n, m, v) with v[i] a dict good -> positive integer value (missing goods are worth 0). Allocations are
lists of frozensets. Exact integer arithmetic throughout.
"""
import itertools
import random


def val(vi, S):
    return sum(vi.get(g, 0) for g in S)


def threat(vi, B):
    """theta_i(B): the largest value of v_i(B minus h) over h in B (0 if |B| <= 1)"""
    if len(B) <= 1:
        return 0
    return val(vi, B) - min(vi.get(g, 0) for g in B)


def is_efx0(v, X):
    n = len(X)
    own = [val(v[i], X[i]) for i in range(n)]
    for j in range(n):
        if len(X[j]) < 2:
            continue
        for i in range(n):
            if i != j and threat(v[i], X[j]) > own[i]:
                return False
    return True


def envious(v, X):
    """pairs (i, j) with i EFX0-envying X_j"""
    n = len(X)
    own = [val(v[i], X[i]) for i in range(n)]
    return [(i, j) for j in range(n) for i in range(n) if i != j and threat(v[i], X[j]) > own[i]]


def all_efx0(n, m, v, shape=None):
    """every EFX0 allocation (owner map tuple); shape='D': all bundles but at most one have <= 2 goods"""
    res = []
    for owner in itertools.product(range(n), repeat=m):
        X = [set() for _ in range(n)]
        for g, i in enumerate(owner):
            X[i].add(g)
        if shape == 'D' and sum(1 for B in X if len(B) > 2) > 1:
            continue
        if is_efx0(v, X):
            res.append(owner)
    return res


def bundles(n, owner):
    X = [set() for _ in range(n)]
    for g, i in enumerate(owner):
        X[i].add(g)
    return [frozenset(B) for B in X]


def relevant(vi):
    """relevant goods in decreasing order of value (ties by index)"""
    return sorted((g for g in vi if vi[g] > 0), key=lambda g: (-vi[g], g))


def is_core_agent(vi):
    r = relevant(vi)
    if len(r) < 3:
        return False
    return vi[r[0]] < sum(vi[g] for g in r[1:])


# ---------------------------------------------------------------------------------------------- random instances
def subset_sums_distinct(vals):
    s = set()
    for k in range(1, len(vals) + 1):
        for c in itertools.combinations(vals, k):
            t = sum(c)
            if t in s:
                return False
            s.add(t)
    return True


def random_core_values(rng, k, lo=1, hi=30, strict=True):
    """values of one core agent with k in {3, 4} goods, decreasing: top < sum of the others; strict = all subset sums
    distinct (the strict types of the research repo, enough by its tie reduction)"""
    while True:
        vals = sorted((rng.randint(lo, hi) for _ in range(k)), reverse=True)
        if vals[0] >= sum(vals[1:]):
            continue
        if strict and not subset_sums_distinct(vals):
            continue
        return vals


def random_core(rng, n, m, p4=0.7, strict=True, hi=30):
    """a random core: every agent values 3 or 4 of the m goods (4 with probability p4), core values"""
    v = []
    for _ in range(n):
        k = 4 if (rng.random() < p4 and m >= 4) else 3
        goods = rng.sample(range(m), k)
        vals = random_core_values(rng, k, hi=hi, strict=strict)
        rng.shuffle(goods)
        v.append(dict(zip(goods, vals)))
    return v


def describe(v):
    return '; '.join('%d: %s' % (i, ' '.join('%d:%d' % (g, vi[g]) for g in relevant(vi))) for i, vi in enumerate(v))
