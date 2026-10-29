#!/usr/bin/env python3
"""Check the steps of der.py on every valid state of test instances. For each valid state: a finishing owner (its
completion checked against the raw definition of EFX0), or a chain or ring whose result is a valid state that
dominates in scores, or else (stuck) a single release after which an owner can finish. Reports the counts and every
kind of failure.

    python3 der_check.py [scale] [suite_dir]
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
from lex_test import type_values, peel
from types4 import all_types

HERE = os.path.dirname(os.path.abspath(__file__))


def check(n, m, v, limit_states=20000):
    d = DER(n, m, v)
    V = d.sp.valid_states()
    out = Counter()
    if len(V) > limit_states:
        out['skipped (too many states)'] += 1
        return out, None
    for st in V:
        res = d.step(st)
        kind = res[0]
        if kind == 'finish':
            d.setup(st)
            X = d.completion(res[1], res[2]) if not all(d.top) else [set(B) for B in d.Y]
            if all(d.top):
                X[0] |= d.J
            if not is_efx0(v, X):
                return out, 'unsound completion at %s' % (st,)
            out['finish'] += 1
        elif kind in ('chain', 'ring', 'grab', 'general ring'):
            new = res[1]
            if not (all(a >= b for a, b in zip(new, st)) and new != st):
                return out, '%s does not dominate at %s' % (kind, st)
            out[kind] += 1
        else:
            r = d.release_finishes(st)
            if r is None:
                return out, 'stuck (%s) and no release finishes, state %s' % (res[1], [sorted(B) for B in d.sp.holdings(st)])
            out['release (%s)' % res[1].split(' at ')[0]] += 1
    return out, None


def job(args):
    kind, trials, seed = args
    rng = random.Random(seed)
    tot = Counter()
    for t in range(trials):
        n = rng.choice([2, 3, 3, 4, 4])
        m = rng.randint(4, 3 + n)
        v = []
        for _ in range(n):
            if kind == 'mixed':
                vals = random_core_values(rng, 4 if rng.random() < 0.75 else 3, hi=rng.choice([10, 20, 40]))
            else:
                vals = type_values(rng, kind) if rng.random() < 0.8 else random_core_values(rng, 3)
            v.append(dict(zip(rng.sample(range(m), len(vals)), vals)))
        c, err = check(n, m, v)
        tot += c
        if err:
            return kind, tot, '%s: %s' % (describe(v), err)
    return kind, tot, None


def main(scale, suite_dir):
    jobs = [(t, 60 * scale, 31) for t in sorted(all_types())] + [('mixed', 150 * scale, s) for s in range(4)]
    grand = Counter()
    fails = 0
    with Pool(4) as pool:
        for kind, tot, err in pool.imap(job, jobs):
            grand += tot
            fails += bool(err)
            print('%-28s %s%s' % (kind, dict(tot), '' if not err else '\n      FAIL ' + err), flush=True)
    others = []
    if suite_dir:
        for f in sorted(glob.glob(os.path.join(suite_dir, '*.json'))):
            d = json.load(open(f))
            if 'kind' in d:
                continue
            v = [dict(zip(s, x)) for s, x in zip(d['sets'], d['vals'])]
            n, m, v = peel(d['n'], d['m'], v)
            if 2 <= n <= 5:
                others.append(('suite ' + d['id'], n, m, v))
    cd = json.load(open(os.path.join(HERE, 'barrier_certs.json')))
    for c in cd['certificates']:
        others.append(('certificate', c['n'], c['m'], [{int(g): x for g, x in vi.items()} for vi in c['v']]))
    from collision import V
    others.append(('collision', 4, 7, V))
    tot = Counter()
    for name, n, m, v in others:
        c, err = check(n, m, v)
        tot += c
        if err:
            fails += 1
            print('      FAIL %s %s: %s' % (name, describe(v), err))
    print('%-28s %s' % ('suite, certificates, collision', dict(tot)))
    grand += tot
    print('total', dict(grand))
    print('ALL CHECKS PASSED' if not fails else '%d FAILURES' % fails)
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main(int(sys.argv[1]) if len(sys.argv) > 1 else 1, sys.argv[2] if len(sys.argv) > 2 else None))
