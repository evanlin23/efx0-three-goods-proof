#!/usr/bin/env python3
"""Adversarial label-collision gadgets (NOTES.md, section 9).

The counterexample to DER (collision12): free agents o_1..o_k hold goods y_1..y_k; each o_i has blockers whose pair
arrows need leftover goods ("labels") from a small common pool, so that labels collide; and o_i wants only the tops of
blockers of o_{i+1}, so that every ring must pass through several free agents. Random variants: blockers of type 12
(label of two leftover goods) or three-good blockers (label of one), random label choices, wants along a random cycle,
random values within the types.

For each gadget: is the draft state (agents in index order) stuck for DER? Is E_lex true (every priority order's
maximal valid state of the threat ladder finishable)?

    python3 gadgets.py [instances per worker and family] [seed]      (default 50, 2: 200 gadgets per family)
"""
import itertools
import random
import sys
from collections import Counter
from multiprocessing import Pool

from model import describe, all_efx0
from lex import LexSpace
from der_run import run
from types4 import all_types, type_of

TYPES = sorted(all_types())


def collision12():
    """the counterexample to DER and E_DER: n = 6, m = 10"""
    A1, A2, A3, A4, y1, y2, h1, h2, h3, h4 = range(10)
    v = [{A1: 10, y1: 6, h1: 3, h2: 2}, {A2: 10, y1: 6, h3: 3, h4: 2}, {A3: 10, y2: 6, h1: 3, h3: 2},
         {A4: 10, y2: 6, h2: 3, h4: 2}, {A3: 4, A4: 3, y1: 2}, {A1: 4, A2: 3, y2: 2}]
    return 6, 10, v


def type_vals(rng, typ):
    while True:
        a, b, c, d = sorted(rng.sample(range(1, 40), 4), reverse=True)
        if a < b + c + d and type_of((a, b, c, d)) == typ:
            return a, b, c, d


def bal3(rng):
    while True:
        a, b, c = sorted(rng.sample(range(1, 40), 3), reverse=True)
        if a < b + c:
            return a, b, c


def gadget(rng):
    """k = 2 or 3 free three-good agents, each with 2 blockers; labels from a pool of 3 or 4 leftover goods"""
    k = rng.choice([2, 2, 3])
    nb = 2
    goods = itertools.count()
    y = [next(goods) for _ in range(k)]
    pool = [next(goods) for _ in range(rng.choice([3, 4]))]
    tops = [[next(goods) for _ in range(nb)] for _ in range(k)]
    v = []
    for i in range(k):
        for t in range(nb):
            if rng.random() < 0.6:                       # type-12 blocker: a = top, b = y_i, c, d = two pool goods
                a, b, c, d = type_vals(rng, TYPES[11])
                h = rng.sample(pool, 2)
                v.append({tops[i][t]: a, y[i]: b, h[0]: c, h[1]: d})
            else:                                        # three-good blocker: a = top, {b, c} = {y_i, a pool good}
                a, b, c = bal3(rng)
                h = rng.choice(pool)
                pair = [y[i], h]
                rng.shuffle(pair)
                v.append({tops[i][t]: a, pair[0]: b, pair[1]: c})
    perm = list(range(k))
    rng.shuffle(perm)
    for i in range(k):                                   # o_i wants the tops of the blockers of o_{next(i)}
        j = perm[(perm.index(i) + 1) % k]
        a, b, c = bal3(rng)
        wanted = tops[j][:2]
        v.append({wanted[0]: a, wanted[1]: b, y[i]: c})
    m = next(goods)
    return len(v), m, v


def perfect_gadget(rng):
    """collision12's pattern with random values: blockers' labels {h1, h2}, {h3, h4} for o1 and {h1, h3}, {h2, h4} for
    o2 (type 12 blockers); o1, o2 of random core types (three goods, or four with their third/fourth good elsewhere);
    plus 0 to 2 extra random core agents on the same goods and fresh ones"""
    A1, A2, A3, A4, y1, y2, h1, h2, h3, h4 = range(10)
    labels = [(y1, (h1, h2)), (y1, (h3, h4)), (y2, (h1, h3)), (y2, (h2, h4))]
    v = []
    for (A, (yy, (c, d))) in zip((A1, A2, A3, A4), labels):
        a, b, cc, dd = type_vals(rng, TYPES[11])
        v.append({A: a, yy: b, c: cc, d: dd})
    m = 10
    for (want, yy) in (((A3, A4), y1), ((A1, A2), y2)):
        if rng.random() < 0.5:
            a, b, c = bal3(rng)
            v.append({want[0]: a, want[1]: b, yy: c})
        else:                                           # a four-good agent: its d is a fresh good
            typ = rng.choice(TYPES)
            a, b, c, d = type_vals(rng, typ)
            v.append({want[0]: a, want[1]: b, yy: c, m: d})
            m += 1
    for _ in range(rng.choice([0, 0, 1, 2])):
        k = rng.choice([3, 4])
        vals = bal3(rng) if k == 3 else type_vals(rng, rng.choice(TYPES))
        extra = rng.randint(0, 1)
        goods = rng.sample(range(m + extra), k)
        m += extra
        v.append(dict(zip(goods, vals)))
    return len(v), m, v


def check(args):
    trials, seed = args[:2]
    family = args[2] if len(args) > 2 else 'random'
    rng = random.Random(seed)
    out, ex = Counter(), {}
    for t in range(trials):
        n, m, v = gadget(rng) if family == 'random' else perfect_gadget(rng)
        try:
            run(n, m, v)
            out['DER succeeds'] += 1
        except AssertionError:
            out['DER stuck'] += 1
            ex.setdefault('DER stuck', (n, m, describe(v)))
        sp = LexSpace(n, m, v, 'threat')
        if len(sp.valid_states()) > 60000:
            out['E_lex skipped (too many states)'] += 1
            continue
        orders = [tuple(range(n))] + [tuple(rng.sample(range(n), n)) for _ in range(5)]
        bad = [o for o in orders if sp.finish(sp.lex_max(o)) is None]
        out['E_lex fails' if bad else 'E_lex holds'] += 1
        if bad:
            ex.setdefault('E_lex fails', (n, m, describe(v), bad[0]))
    return out, ex


def main(trials, seed):
    n, m, v = collision12()
    try:
        run(n, m, v)
        print('collision12: DER succeeds')
    except AssertionError as e:
        print('collision12: DER fails (%s)' % e)
    sp = LexSpace(n, m, v, 'threat')
    bad = sum(1 for o in itertools.permutations(range(n)) if sp.finish(sp.lex_max(o)) is None)
    print('collision12: orders whose priority-maximal state is not finishable: %d of 720' % bad)
    fails = 0
    for family in ('random', 'perfect'):
        with Pool(4) as pool:
            res = pool.map(check, [(trials, seed * 100 + s, family) for s in range(4)])
        tot, ex = Counter(), {}
        for c, e in res:
            tot += c
            for k, x in e.items():
                ex.setdefault(k, x)
        print('%s gadgets: %s' % (family, dict(tot)))
        for k, x in ex.items():
            print('  example, %s: %s' % (k, x))
        fails += tot['E_lex fails']
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main(int(sys.argv[1]) if len(sys.argv) > 1 else 50, int(sys.argv[2]) if len(sys.argv) > 2 else 2))
