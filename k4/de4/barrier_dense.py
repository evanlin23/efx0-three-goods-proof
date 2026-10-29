#!/usr/bin/env python3
"""Dense search on the survivors of barrier.py / barrier_deep.py that are not of the small-d type: larger instances
(n = 4 to 6) with few goods per agent (m = n + 1 to n + 3), mostly four-good agents of the type; adds the certificates
found to barrier_certs.json.

    python3 barrier_dense.py [instances per ladder] [seed]
"""
import json
import random
import sys
from multiprocessing import Pool

from barrier import stuck, type_values, SMALL_D
from model import random_core_values


def dense_search(args):
    typ, spec, trials, seed = args
    rng = random.Random(seed)
    for t in range(trials):
        n = rng.choice([4, 4, 5, 5, 6])
        m = rng.randint(n + 1, n + 3)
        v = []
        for _ in range(n):
            vals = type_values(rng, typ) if rng.random() < 0.8 else random_core_values(rng, 3)
            v.append(dict(zip(rng.sample(range(m), len(vals)), vals)))
        st = stuck(n, m, v, spec)
        if st is not None:
            return typ, spec, {'type': typ, 'ladder': list(spec), 'n': n, 'm': m,
                               'v': [{str(g): x for g, x in vi.items()} for vi in v], 'state': st}
    return typ, spec, None


def main(trials, seed):
    d = json.load(open('barrier_certs.json'))
    jobs = [(t, tuple(s), trials, seed) for t, s in d['survivors'] if t != SMALL_D]
    left = [[t, s] for t, s in d['survivors'] if t == SMALL_D]
    with Pool(4) as pool:
        for typ, spec, best in pool.imap_unordered(dense_search, jobs):
            if best is None:
                left.append([typ, list(spec)])
                print('   still survives: %-30s %s' % (typ, ' < '.join(spec)), flush=True)
            else:
                print('   refuted: %-30s %-28s n=%d m=%d' % (typ, ' < '.join(spec), best['n'], best['m']), flush=True)
                d['certificates'].append(best)
    d['survivors'] = left
    json.dump(d, open('barrier_certs.json', 'w'), indent=0)
    print('survivors left %d (%d of them small-d)' % (len(left), sum(1 for t, s in left if t == SMALL_D)))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 1500, int(sys.argv[2]) if len(sys.argv) > 2 else 3)
