#!/usr/bin/env python3
"""Stress test of E_lex (lex.py): for every priority order, the priority-maximal valid state of the pair ladder can be
finished by DE's rule (an owner whose holding has no wanted good; H to free agents), with a raw EFX0 check.

  [1] random instances in which every four-good agent has one given strict type (all twelve types), plus three-good
      agents, n = 2 to 5; every order for n <= 4, six random orders for n = 5;
  [2] random instances with agents of all types mixed;
  [3] the research repository's counterexample suite (k4/suite/instances of evanlin23/efx0-three-goods; pass its path),
      after peeling by rule R1, for the instances whose core has at most 6 agents;
  [4] the instances of every certificate in barrier_certs.json (dead ends for Pareto-maximal states);
  [5] the collision example (collision.py).

    python3 lex_test.py [scale] [suite_dir]
"""
import glob
import itertools
import json
import os
import random
import sys
from multiprocessing import Pool

from model import random_core_values, describe, relevant, val
from lex import LexSpace
from types4 import all_types, type_of

HERE = os.path.dirname(os.path.abspath(__file__))
FAILS = []


def report(ok, msg):
    print(('  ok    ' if ok else '  FAIL  ') + msg, flush=True)
    if not ok:
        FAILS.append(msg)


def orders_for(n, rng, k=6):
    if n <= 4:
        return list(itertools.permutations(range(n)))
    return [tuple(range(n))] + [tuple(rng.sample(range(n), n)) for _ in range(k - 1)]


RULE = os.environ.get('LADDER', 'threat')
MODE = os.environ.get('MODE', 'lexmax')


def check_instance(n, m, v, rng):
    """None if every tested order's maximal state finishes, else a description of the failure"""
    sp = LexSpace(n, m, v, RULE)
    if not sp.valid_states():
        return 'no valid state'
    for order in orders_for(n, rng):
        st = sp.lex_max(order) if MODE == 'lexmax' else sp.priority_draft(order)
        if not sp.is_valid(st):
            return 'order %s: the state is not valid' % (order,)
        if sp.finish(st) is None:
            return 'order %s, state %s' % (order, [sorted(B) for B in sp.holdings(st)])
    return None


def type_values(rng, typ):
    while True:
        vals = random_core_values(rng, 4, hi=rng.choice([12, 25, 40]))
        if type_of(vals) == typ:
            return vals


def typed_job(args):
    typ, trials, seed = args
    rng = random.Random(seed)
    for t in range(trials):
        n = rng.choice([2, 3, 3, 4, 4, 5])
        m = rng.randint(4, 3 + n)
        p4 = rng.choice([0.5, 1.0])
        v = []
        for _ in range(n):
            vals = type_values(rng, typ) if rng.random() < p4 else random_core_values(rng, 3)
            v.append(dict(zip(rng.sample(range(m), len(vals)), vals)))
        w = check_instance(n, m, v, rng)
        if w:
            return typ, t, '%s: %s' % (describe(v), w)
    return typ, trials, None


def mixed_job(args):
    trials, seed = args
    rng = random.Random(seed)
    for t in range(trials):
        n = rng.choice([2, 3, 3, 4, 4, 5, 5])
        m = rng.randint(4, 3 + n)
        v = []
        for _ in range(n):
            vals = random_core_values(rng, 4 if rng.random() < 0.7 else 3, hi=rng.choice([10, 20, 40]))
            v.append(dict(zip(rng.sample(range(m), len(vals)), vals)))
        w = check_instance(n, m, v, rng)
        if w:
            return seed, t, '%s: %s' % (describe(v), w)
    return seed, trials, None


def peel(n, m, v):
    """rule R1 as in the paper; returns the remaining agents and goods, renumbered"""
    A, G = list(range(n)), set(range(m))
    while len(A) >= 2:
        hit = None
        for i in A:
            rel = sorted((g for g in G if v[i].get(g, 0) > 0), key=lambda g: (-v[i][g], g))
            if not rel:
                hit = (i, set())
                break
            p = rel[0]
            if sum(v[i][g] for g in rel[1:]) <= v[i][p]:
                hit = (i, {p})
                break
        if hit is None:
            break
        A.remove(hit[0])
        G -= hit[1]
    gl = sorted(G)
    idx = {g: k for k, g in enumerate(gl)}
    return len(A), len(gl), [{idx[g]: x for g, x in v[i].items() if g in G} for i in A]


def strict(vi):
    x = list(vi.values())
    sums = [sum(c) for k in range(1, len(x) + 1) for c in itertools.combinations(x, k)]
    return len(set(sums)) == len(sums)


def part3(suite_dir, rng):
    files = sorted(glob.glob(os.path.join(suite_dir, '*.json')))
    done = skipped = nonstrict = 0
    for f in files:
        d = json.load(open(f))
        if 'kind' in d:
            continue
        v = [dict(zip(s, x)) for s, x in zip(d['sets'], d['vals'])]
        n, m, v = peel(d['n'], d['m'], v)
        if n > 6 or n < 2:
            skipped += 1
            continue
        if not all(strict(vi) for vi in v):
            nonstrict += 1
        w = check_instance(n, m, v, rng)
        if w:
            report(False, 'suite %s: %s' % (d['id'], w))
            return
        done += 1
    report(True, 'suite: %d instances checked after peeling (%d with ties), %d skipped (core with more than 6 agents '
           'or fewer than 2)' % (done, nonstrict, skipped))


def main(scale, suite_dir):
    rng = random.Random(1)
    print('[1] random instances, one type of four-good agent at a time')
    with Pool(4) as pool:
        for typ, t, w in pool.imap(typed_job, [(typ, 300 * scale, 11) for typ in sorted(all_types())]):
            report(w is None, '%-28s %d instances%s' % (typ, t, '' if w is None else ': ' + w))
    print('[2] random instances, all types mixed')
    with Pool(4) as pool:
        res = pool.map(mixed_job, [(500 * scale, s) for s in range(8)])
    bad = [r for r in res if r[2]]
    report(not bad, '%d instances%s' % (sum(r[1] for r in res), '' if not bad else ': ' + bad[0][2]))
    if suite_dir:
        print('[3] the research repository\'s counterexample suite')
        part3(suite_dir, rng)
    print('[4] the instances of the barrier certificates')
    d = json.load(open(os.path.join(HERE, 'barrier_certs.json')))
    for c in d['certificates']:
        v = [{int(g): x for g, x in vi.items()} for vi in c['v']]
        w = check_instance(c['n'], c['m'], v, rng)
        if w:
            report(False, 'certificate %s %s: %s' % (c['type'], c['ladder'], w))
            break
    else:
        report(True, '%d certificate instances' % len(d['certificates']))
    print('[5] the collision example')
    from collision import V
    w = check_instance(4, 7, V, rng)
    report(w is None, 'collision example%s' % ('' if w is None else ': ' + w))
    print('\n%s' % ('ALL CHECKS PASSED' if not FAILS else '%d FAILURES' % len(FAILS)))
    return 1 if FAILS else 0


if __name__ == '__main__':
    scale = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    suite = sys.argv[2] if len(sys.argv) > 2 else None
    sys.exit(main(scale, suite))
