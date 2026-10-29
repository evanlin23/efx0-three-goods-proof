#!/usr/bin/env python3
"""E_DER on data: every score-Pareto-maximal valid state of the threat ladder (lex.py) is finishable, or becomes
finishable after one agent steps down to a lower rung (a *release*). Random instances (each type, and mixed), the
research repository's suite (after peeling), the barrier certificates and the collision example.

    python3 der_test.py [scale] [suite_dir]
"""
import glob
import json
import os
import random
import sys
from collections import Counter
from multiprocessing import Pool

from model import random_core_values, describe
from lex import LexSpace
from lex_test import type_values, peel
from types4 import all_types

HERE = os.path.dirname(os.path.abspath(__file__))


def analyze(n, m, v):
    """Counter over the score-Pareto-maximal valid states: finishable / release / FAIL"""
    sp = LexSpace(n, m, v, 'threat')
    V = sp.valid_states()
    Vs = set(V)
    out = Counter()
    pm = sp_pareto_max(V)
    for s in pm:
        if sp.finish(s) is not None:
            out['finishable'] += 1
            continue
        ok = False
        for i in range(n):
            for r in range(s[i]):
                t = s[:i] + (r,) + s[i + 1:]
                if t in Vs and sp.finish(t) is not None:
                    ok = True
                    break
            if ok:
                break
        out['one release finishes' if ok else 'FAIL'] += 1
    return out


def sp_pareto_max(V):
    out = []
    for s in sorted(set(V), key=lambda s: -sum(s)):
        if not any(all(a >= b for a, b in zip(t, s)) for t in out):
            out.append(s)
    return out


def job(args):
    kind, trials, seed = args
    rng = random.Random(seed)
    tot = Counter()
    for t in range(trials):
        n = rng.choice([2, 3, 3, 4, 4, 5])
        m = rng.randint(4, 3 + n)
        v = []
        for _ in range(n):
            if kind == 'mixed':
                vals = random_core_values(rng, 4 if rng.random() < 0.75 else 3, hi=rng.choice([10, 20, 40]))
            else:
                vals = type_values(rng, kind) if rng.random() < 0.8 else random_core_values(rng, 3)
            v.append(dict(zip(rng.sample(range(m), len(vals)), vals)))
        c = analyze(n, m, v)
        tot += c
        if c['FAIL']:
            return kind, tot, describe(v)
    return kind, tot, None


def main(scale, suite_dir):
    jobs = [(t, 200 * scale, 21) for t in sorted(all_types())] + [('mixed', 500 * scale, s) for s in range(4)]
    grand = Counter()
    with Pool(4) as pool:
        for kind, tot, fail in pool.imap(job, jobs):
            grand += tot
            print('%-28s %s%s' % (kind, dict(tot), '' if fail is None else '  FAIL on ' + fail), flush=True)
    if suite_dir:
        tot = Counter()
        for f in sorted(glob.glob(os.path.join(suite_dir, '*.json'))):
            d = json.load(open(f))
            if 'kind' in d:
                continue
            v = [dict(zip(s, x)) for s, x in zip(d['sets'], d['vals'])]
            n, m, v = peel(d['n'], d['m'], v)
            if 2 <= n <= 6:
                tot += analyze(n, m, v)
        print('%-28s %s' % ('suite', dict(tot)))
        grand += tot
    d = json.load(open(os.path.join(HERE, 'barrier_certs.json')))
    tot = Counter()
    for c in d['certificates']:
        tot += analyze(c['n'], c['m'], [{int(g): x for g, x in vi.items()} for vi in c['v']])
    from collision import V
    tot += analyze(4, 7, V)
    print('%-28s %s' % ('certificates and collision', dict(tot)))
    grand += tot
    print('total', dict(grand))
    return 1 if grand['FAIL'] else 0


if __name__ == '__main__':
    sys.exit(main(int(sys.argv[1]) if len(sys.argv) > 1 else 1, sys.argv[2] if len(sys.argv) > 2 else None))
