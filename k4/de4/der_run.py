#!/usr/bin/env python3
"""DER end to end: peel by rule R1, draft (each agent in index order takes its best single not taken), then repeat
der.DER.step (finish / chain / grab / ring / general ring) and, when stuck, one release followed by finishing. Every
output is checked against the raw definition of EFX0; the run reports the number of trades and releases.

Runs on random instances (no state enumeration: only the current state is used, so n can be large) and on every
instance of the research repository's suite, the large ones included.

    python3 der_run.py [scale] [suite_dir]
"""
import glob
import json
import os
import random
import sys
from collections import Counter
from multiprocessing import Pool

from model import random_core_values, describe, is_efx0
from der import DER
from lex_test import peel

HERE = os.path.dirname(os.path.abspath(__file__))


def run(n0, m0, v0):
    """returns (allocation of the core, stats) for the instance after peeling; raises AssertionError on failure"""
    n, m, v = peel(n0, m0, v0)
    stats = Counter()
    if n <= 1:
        return None, stats
    d = DER(n, m, v)
    st, used = [0] * n, set()
    for i in range(n):                                      # the draft
        best = 0
        for s, B in enumerate(d.sp.lad[i]):
            if len(B) == 1 and not (B & used):
                best = s
        st[i] = best
        used |= d.sp.lad[i][best]
    st = tuple(st)
    assert d.sp.is_valid(st), 'draft not valid'
    bound = sum(len(l) for l in d.sp.lad)
    while True:
        res = d.step(st)
        if res[0] == 'finish':
            d.setup(st)
            if all(d.top):
                X = [set(B) for B in d.Y]
                X[0] |= d.J
            else:
                X = d.completion(res[1], res[2])
            break
        if res[0] == 'stuck':
            r = d.release_finishes(st)
            assert r is not None, 'stuck and no release finishes'
            i, rung, o = r
            st = st[:i] + (rung,) + st[i + 1:]
            stats['releases'] += 1
            continue
        assert all(a >= b for a, b in zip(res[1], st)) and res[1] != st
        st = res[1]
        stats[res[0]] += 1
        stats['trades'] += 1
        assert stats['trades'] <= bound, 'too many trades'
    assert sorted(g for B in X for g in B) == list(range(m)), 'not complete'
    assert is_efx0(v, X), 'not EFX0'
    stats['bundles > 2'] = sum(1 for B in X if len(B) > 2)
    return X, stats


def job(args):
    trials, seed, nmax = args
    rng = random.Random(seed)
    tot = Counter()
    worst = 0
    for t in range(trials):
        n = rng.randint(2, nmax)
        m = rng.randint(max(n + 1, 4), 2 * n + 3)
        v = []
        for _ in range(n):
            k = rng.choice([3, 4, 4, 4]) if rng.random() < 0.9 else rng.choice([1, 2])
            vals = random_core_values(rng, k, hi=rng.choice([10, 20, 40])) if k >= 3 else \
                [rng.randint(1, 20) for _ in range(k)]
            v.append(dict(zip(rng.sample(range(m), len(vals)), vals)))
        try:
            X, s = run(n, m, v)
        except AssertionError as e:
            return seed, tot, '%s: %s' % (describe(v), e)
        tot += s
        tot['runs'] += 1
        worst = max(worst, s['trades'])
    tot['max trades in a run'] = worst
    return seed, tot, None


def main(scale, suite_dir):
    fails = 0
    for nmax in (5, 8, 12):
        with Pool(4) as pool:
            res = pool.map(job, [(150 * scale, 100 * nmax + s, nmax) for s in range(4)])
        tot = Counter()
        for seed, t, err in res:
            mx = max(tot['max trades in a run'], t['max trades in a run'])
            tot += t
            tot['max trades in a run'] = mx
            if err:
                fails += 1
                print('  FAIL (seed %d): %s' % (seed, err))
        print('random instances, n up to %2d: %s' % (nmax, dict(tot)), flush=True)
    if suite_dir:
        tot = Counter()
        for f in sorted(glob.glob(os.path.join(suite_dir, '*.json'))):
            d = json.load(open(f))
            if 'kind' in d:
                continue
            v = [dict(zip(s, x)) for s, x in zip(d['sets'], d['vals'])]
            try:
                X, s = run(d['n'], d['m'], v)
            except AssertionError as e:
                fails += 1
                print('  FAIL suite %s (n = %d): %s' % (d['id'], d['n'], e))
                continue
            tot += s
            tot['instances'] += 1
            if d['n'] >= 9:
                print('   suite %s (n = %d, m = %d): EFX0, %d trades, %d releases' %
                      (d['id'], d['n'], d['m'], s['trades'], s['releases']), flush=True)
        print('suite: %s' % dict(tot))
    print('ALL RUNS PASSED' if not fails else '%d FAILURES' % fails)
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main(int(sys.argv[1]) if len(sys.argv) > 1 else 1, sys.argv[2] if len(sys.argv) > 2 else None))
