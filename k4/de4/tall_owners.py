#!/usr/bin/env python3
"""Which owners finish the score-Pareto-maximal valid states of three tall ladders that no search refuted (NOTES.md,
section 4.2)? For each such state: 'free' if a free agent can finish (DE's rule), else 'top' if an agent on its top
rung can, else the intermediate pairs whose holders can (owner: an agent whose holding contains no wanted good; H to
free agents; raw EFX0). Random instances as in barrier.py.

    python3 tall_owners.py [instances per ladder] [seed]
"""
import itertools
import random
import sys
from collections import Counter

from model import is_efx0, relevant
from states import Space
from barrier import make_ladder, random_instance

COMBOS = [('a<bc a<bd a>cd b>cd ad<bc', ('bd', 'bc', 'ab')),
          ('a<bc a<bd a<cd b<cd ad<bc', ('cd', 'bd', 'bc', 'ac', 'ab')),
          ('a<bc a>bd a>cd b>cd ad>bc', ('bc', 'ad', 'ac', 'ab'))]


def owner_kinds(sp, s):
    Y, J, W, wanted, ok, F, top = sp.info(s)
    kinds = set()
    for o in range(sp.n):
        if Y[o] & wanted:
            continue
        rec = [f for f in F if f != o]
        found = False
        for k in range(len(rec) + 1):
            for H in itertools.combinations(sorted(J), k):
                for to in itertools.permutations(rec, k):
                    X = [set(B) for B in Y]
                    X[o] |= J - set(H)
                    for h, f in zip(H, to):
                        X[f].add(h)
                    if is_efx0(sp.v, X):
                        found = True
                        break
                if found:
                    break
            if found:
                break
        if found:
            if o in F:
                kinds.add('free')
            elif top[o]:
                kinds.add('top')
            else:
                name = dict(zip(relevant(sp.v[o]), 'abcd'))
                kinds.add('pair ' + ''.join(sorted(name[g] for g in Y[o])))
    if 'free' in kinds:
        return 'free'
    if 'top' in kinds:
        return 'top'
    return ', '.join(sorted(kinds)) or 'none'


def main(N, seed):
    for typ, spec in COMBOS:
        rng = random.Random(seed)
        lad = make_ladder(spec)
        cnt = Counter()
        for t in range(N):
            n, m, v = random_instance(rng, typ)
            sp = Space(n, m, v, lad)
            valid = [s for s in sp.all_states() if sp.info(s)[4]]
            for s in sp.pareto_max(valid):
                cnt[owner_kinds(sp, s)] += 1
        tot = sum(cnt.values())
        print('%-28s %-28s %d score-Pareto-maximal states: %s' %
              (typ, ' < '.join(spec), tot, ', '.join('%s %d' % kv for kv in cnt.most_common())))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 400, int(sys.argv[2]) if len(sys.argv) > 2 else 9)
