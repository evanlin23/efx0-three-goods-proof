#!/usr/bin/env python3
"""For the (type, ladder) pairs that no search refuted with liberal finishing (the survivors in barrier_certs.json,
small-d type excluded), search for a counterexample to E(lambda) with DE's own finishing rule, in the form of the Lean
formalization: the owner is any agent whose holding contains no wanted good (a free agent or a pair holder: a "valid
absorber"), and the goods of H go to different free agents other than the owner. Adds the certificates found to
barrier_certs.json with "finishing": "absorber".

    python3 barrier_narrow.py [instances per ladder] [seed] [--dense]

With --dense, the instances are those of barrier_dense.py (n = 4 to 6, m = n + 1 to n + 3, mostly four-good agents),
and only the pairs not yet refuted with this rule are searched.
"""
import json
import random
import sys
from multiprocessing import Pool

from barrier import make_ladder, random_instance, type_values, SMALL_D
from model import random_core_values
import itertools

from model import is_efx0
from states import Space


def absorber_finishable(sp, st):
    Y, J, W, wanted, valid, F, top = sp.info(st)
    owners = [i for i in range(sp.n) if not (Y[i] & wanted)]
    for o in owners:
        rec = [f for f in F if f != o]
        for k in range(len(rec) + 1):
            for H in itertools.combinations(sorted(J), k):
                for to in itertools.permutations(rec, k):
                    X = [set(B) for B in Y]
                    X[o] |= J - set(H)
                    for h, f in zip(H, to):
                        X[f].add(h)
                    if is_efx0(sp.v, X):
                        return True
    return False


def dense_instance(rng, typ):
    n = rng.choice([4, 4, 5, 5, 6])
    m = rng.randint(n + 1, n + 3)
    v = []
    for _ in range(n):
        vals = type_values(rng, typ) if rng.random() < 0.8 else random_core_values(rng, 3)
        v.append(dict(zip(rng.sample(range(m), len(vals)), vals)))
    return n, m, v


def narrow_search(args):
    typ, spec, trials, seed, dense = args
    rng = random.Random(seed)
    lad = make_ladder(spec)
    best = None
    for t in range(trials):
        n, m, v = dense_instance(rng, typ) if dense else random_instance(rng, typ)
        if best is not None and (n, m) >= (best['n'], best['m']):
            continue
        sp = Space(n, m, v, lad)
        valid = [s for s in sp.all_states() if sp.info(s)[4]]
        for s in sp.pareto_max(valid):
            if not absorber_finishable(sp, s):
                best = {'type': typ, 'ladder': list(spec), 'n': n, 'm': m, 'finishing': 'absorber',
                        'v': [{str(g): x for g, x in vi.items()} for vi in v],
                        'state': [sorted(B) for B in sp.info(s)[0]]}
                break
    return typ, spec, best


def main(trials, seed, dense):
    d = json.load(open('barrier_certs.json'))
    done = set((c['type'], tuple(c['ladder'])) for c in d['certificates'] if c.get('finishing') == 'absorber')
    jobs = [(t, tuple(s), trials, seed, dense) for t, s in d['survivors'] if t != SMALL_D and (t, tuple(s)) not in done]
    with Pool(4) as pool:
        for typ, spec, best in pool.imap_unordered(narrow_search, jobs):
            if best is None:
                print('   no counterexample: %-30s %s' % (typ, ' < '.join(spec)), flush=True)
            else:
                print('   counterexample: %-30s %-30s n=%d m=%d' % (typ, ' < '.join(spec), best['n'], best['m']),
                      flush=True)
                d['certificates'].append(best)
    json.dump(d, open('barrier_certs.json', 'w'), indent=0)


if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    main(int(args[0]) if args else 400, int(args[1]) if len(args) > 1 else 4, '--dense' in sys.argv)
