"""Strict order types of a four-good core agent: values a > b > c > d > 0, a < b + c + d, all subset sums distinct.
The type is the sign pattern of the comparisons between disjoint subsets that are not decided by a > b > c > d alone."""
import itertools
import random

FEATS = [('a', 'bc'), ('a', 'bd'), ('a', 'cd'), ('b', 'cd'), ('ad', 'bc')]


def sums(vals, s):
    return sum(vals['abcd'.index(ch)] for ch in s)


def type_of(vals):
    """vals = (a, b, c, d) decreasing; returns a string such as 'a<bc a>bd ...'"""
    return ' '.join('%s%s%s' % (x, '<' if sums(vals, x) < sums(vals, y) else '>', y) for x, y in FEATS)


def all_types(trials=200000, hi=40, seed=0):
    rng = random.Random(seed)
    seen = {}
    for _ in range(trials):
        vals = tuple(sorted(rng.sample(range(1, hi), 4), reverse=True))
        if vals[0] >= sum(vals[1:]):
            continue
        ss = [sum(c) for k in range(1, 5) for c in itertools.combinations(vals, k)]
        if len(set(ss)) < len(ss):
            continue
        t = type_of(vals)
        if t not in seen or sum(vals) < sum(seen[t]):
            seen[t] = vals
    return seen


if __name__ == '__main__':
    for t, vals in sorted(all_types().items()):
        print(t, vals)
