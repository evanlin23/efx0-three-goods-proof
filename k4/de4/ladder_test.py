#!/usr/bin/env python3
"""Test, for each candidate ladder, the statement behind the paper's Corollary (score-Pareto-maximal valid states):

    every-form: every valid state that no valid state Pareto-dominates in scores is finishable;
    some-form:  some valid state is finishable.

The every-form is what a Draft-and-Exchange proof (an improving trade from every unfinishable valid state) needs. Random
core instances with three and four relevant goods per agent, strict values; prints the first failures found.

    python3 ladder_test.py [trials] [seed]
"""
import random
import sys

from model import random_core, describe, all_efx0
from states import Space, LADDERS


def run(trials, seed):
    rng = random.Random(seed)
    fails = {name: {'every': [], 'some': []} for name in LADDERS if name != 'k3'}
    counts = {name: [0, 0, 0] for name in fails}
    for t in range(trials):
        n = rng.choice([2, 3, 3, 4])
        m = rng.randint(4, 4 + n)
        v = random_core(rng, n, m)
        for name in fails:
            sp = Space(n, m, v, LADDERS[name])
            states = sp.all_states()
            valid = [s for s in states if sp.info(s)[4]]
            pm = sp.pareto_max(valid)
            counts[name][0] += 1
            bad = [s for s in pm if sp.finishable(s) is None]
            if bad:
                counts[name][1] += 1
                if len(fails[name]['every']) < 3:
                    fails[name]['every'].append((n, m, v, bad[0]))
                if not any(sp.finishable(s) is not None for s in valid):
                    counts[name][2] += 1
                    if len(fails[name]['some']) < 3:
                        fails[name]['some'].append((n, m, v, None))
    for name in fails:
        c = counts[name]
        print('ladder %-7s instances %d  every-form fails %d  some-form fails %d' % (name, c[0], c[1], c[2]))
        for kind in ('every', 'some'):
            for n, m, v, st in fails[name][kind]:
                sp = Space(n, m, v, LADDERS[name])
                print('   %s-form failure: n=%d m=%d  %s' % (kind, n, m, describe(v)))
                if st is not None:
                    Y = sp.info(st)[0]
                    print('      stuck Pareto-maximal state:', [sorted(B) for B in Y])
                print('      EFX0 allocations exist: %s' % bool(all_efx0(n, m, v)))


if __name__ == '__main__':
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    run(trials, seed)
