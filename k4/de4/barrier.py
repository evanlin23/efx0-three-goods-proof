#!/usr/bin/env python3
"""The barrier: for every strict type of four-good core agent other than the small-d type, and every ladder of the
family below, find an instance (every four-good agent of that type, the others three-good core agents with the paper's
ladder) with a valid state that no valid state Pareto-dominates in scores and that has no EFX0 completion of DE's shape,
even with liberal finishing (any owner; each good of H to a different agent holding at most one good).

Ladder family for a four-good agent (rungs in order of value): nothing, the four singles, any set of pairs worth less
than the top rung, and a top rung that is an envy-free pair (worth at least the other two goods) or the triple
{b, c, d} (worth more than a in a core). These top rungs are exactly the holdings that want nothing and can never be
threatened.

Writes certificates to barrier_certs.json (re-checked independently by check_barrier.py).

    python3 barrier.py [instances per ladder] [seed]
"""
import itertools
import json
import random
import sys
from multiprocessing import Pool

from model import random_core_values, relevant, val
from states import Space, ladder_k3, liberal_finishable
from types4 import all_types, type_of

PAIRS = ['ab', 'ac', 'ad', 'bc', 'bd', 'cd']
SMALL_D = 'a<bc a>bd a>cd b>cd ad<bc'


def rung_value(vals, name):
    return sum(vals['abcd'.index(ch)] for ch in name)


def ladders_for(vals):
    tot = sum(vals)
    ef = [p for p in PAIRS if 2 * rung_value(vals, p) >= tot]
    out = []
    for top in ef + ['bcd']:
        lower = [p for p in PAIRS if rung_value(vals, p) < rung_value(vals, top)]
        for k in range(len(lower) + 1):
            for sub in itertools.combinations(lower, k):
                out.append(tuple(sorted(sub, key=lambda p: rung_value(vals, p))) + (top,))
    return out


def make_ladder(spec):
    def lad(vi):
        r = relevant(vi)
        if len(r) == 3:
            return ladder_k3(vi)
        g = dict(zip('abcd', r))
        hs = [frozenset([x]) for x in r] + [frozenset(g[ch] for ch in name) for name in spec]
        hs.sort(key=lambda B: val(vi, B))
        return [frozenset()] + hs
    return lad


def type_values(rng, typ):
    while True:
        vals = random_core_values(rng, 4, hi=rng.choice([12, 25, 40]))
        if type_of(vals) == typ:
            return vals


def collision_gadget(rng, typ):
    """the n = 4, m = 7 pattern of NOTES.md: two four-good agents z, z' holding {c, d}, each with b equal to the
    other's top; two three-good agents x, x' holding those tops, with pairs {c_z, h} and {c_z', h}"""
    A, Ap, C1, D1, C2, D2, h = range(7)
    vz, vz2 = type_values(rng, typ), type_values(rng, typ)
    x = random_core_values(rng, 3)
    x2 = random_core_values(rng, 3)
    v = [dict(zip((Ap, C1, h), x)), dict(zip((A, C2, h), x2)),
         dict(zip((A, Ap, C1, D1), vz)), dict(zip((Ap, A, C2, D2), vz2))]
    return 4, 7, v


def random_instance(rng, typ):
    n = rng.choice([2, 2, 3, 3, 4, 4, 5])
    m = rng.randint(4, 3 + n)
    p4 = rng.choice([0.5, 1.0])
    v = []
    for _ in range(n):
        vals = type_values(rng, typ) if rng.random() < p4 else random_core_values(rng, 3)
        v.append(dict(zip(rng.sample(range(m), len(vals)), vals)))
    return n, m, v


def stuck(n, m, v, spec):
    sp = Space(n, m, v, make_ladder(spec))
    valid = [s for s in sp.all_states() if sp.info(s)[4]]
    for s in sp.pareto_max(valid):
        if not liberal_finishable(sp, s):
            return [sorted(B) for B in sp.info(s)[0]]
    return None


def search(args):
    typ, spec, trials, seed = args
    rng = random.Random(seed)
    best = None
    for t in range(trials):
        n, m, v = collision_gadget(rng, typ) if t % 4 == 3 else random_instance(rng, typ)
        if best is not None and (n, m) >= (best['n'], best['m']):
            continue
        st = stuck(n, m, v, spec)
        if st is not None:
            best = {'type': typ, 'ladder': list(spec), 'n': n, 'm': m,
                    'v': [{str(g): x for g, x in vi.items()} for vi in v], 'state': st}
            if n <= 2:
                break
    return typ, spec, best


def main(trials, seed):
    types = all_types()
    jobs = [(typ, spec, trials, seed) for typ, rep in sorted(types.items()) for spec in ladders_for(rep)]
    certs, survivors = [], []
    with Pool(4) as pool:
        for typ, spec, best in pool.imap(search, jobs):
            if best is None:
                survivors.append((typ, spec))
            else:
                certs.append(best)
    print('ladders tested: %d (%d types)' % (len(jobs), len(types)))
    print('refuted: %d; survivors: %d' % (len(certs), len(survivors)))
    for typ, spec in survivors:
        print('   survives: %-30s %s' % (typ, ' < '.join(spec)))
    sizes = {}
    for c in certs:
        sizes[(c['n'], c['m'])] = sizes.get((c['n'], c['m']), 0) + 1
    print('sizes of the certificates (n, m): count', sorted(sizes.items()))
    with open('barrier_certs.json', 'w') as f:
        json.dump({'small_d': SMALL_D, 'certificates': certs,
                   'survivors': [[t, list(s)] for t, s in survivors]}, f, indent=0)


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 400, int(sys.argv[2]) if len(sys.argv) > 2 else 1)
