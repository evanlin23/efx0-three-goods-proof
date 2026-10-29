#!/usr/bin/env python3
"""Search the survivors of barrier.py harder (more instances, other seeds); adds the certificates found to
barrier_certs.json.

    python3 barrier_deep.py [instances per ladder] [seed]
"""
import json
import sys
from multiprocessing import Pool

from barrier import search, SMALL_D


def main(trials, seed):
    d = json.load(open('barrier_certs.json'))
    jobs = [(t, tuple(s), trials, seed) for t, s in d['survivors'] if t != SMALL_D]
    left = [[t, s] for t, s in d['survivors'] if t == SMALL_D]
    found = 0
    with Pool(4) as pool:
        for typ, spec, best in pool.imap(search, jobs):
            if best is None:
                left.append([typ, list(spec)])
                print('   still survives: %-30s %s' % (typ, ' < '.join(spec)), flush=True)
            else:
                d['certificates'].append(best)
                found += 1
    d['survivors'] = left
    json.dump(d, open('barrier_certs.json', 'w'), indent=0)
    print('searched %d, refuted now %d, survivors left %d (%d of them small-d)' %
          (len(jobs), found, len(left), sum(1 for t, s in left if t == SMALL_D)))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 4000, int(sys.argv[2]) if len(sys.argv) > 2 else 2)
