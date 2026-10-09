"""Exhaustive DE tests on general (non-core) profiles: every value vector with
entries in {0..maxv} and at most three positive entries, for every agent."""
import sys
import time
from itertools import product
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '.')
from de import de, check_output, CheckError


def rows(m, maxv):
    return [r for r in product(range(maxv + 1), repeat=m) if sum(1 for x in r if x > 0) <= 3]


def work(args):
    n, m, maxv, first = args
    R = rows(m, maxv)
    res = Counter()
    fails = []
    for rest in product(R, repeat=n - 1):
        v = [list(first)] + [list(r) for r in rest]
        st = {}
        try:
            X = de(v, checks=True, deep=False, stats=st)
            check_output(v, X, st)
        except CheckError as e:
            fails.append((v, str(e)))
            continue
        res['ok'] += 1
        res['core'] += st['core_n'] >= 2
        res['trades_max'] = max(res['trades_max'], st['trades'])
    return res, fails


if __name__ == '__main__':
    n, m, maxv = map(int, sys.argv[1:4])
    t0 = time.time()
    R = rows(m, maxv)
    tot = Counter()
    fails = []
    with Pool(4) as pool:
        for res, fl in pool.imap_unordered(work, [(n, m, maxv, r) for r in R], chunksize=4):
            tm = max(tot['trades_max'], res.pop('trades_max', 0))
            tot.update(res)
            tot['trades_max'] = tm
            fails.extend(fl)
    print(f"general n={n} m={m} values 0..{maxv}: profiles={tot['ok'] + len(fails)} ok={tot['ok']} fail={len(fails)} "
          f"reaching core={tot['core']} max trades={tot['trades_max']} time={time.time() - t0:.1f}s")
    for v, e in fails[:5]:
        print('  FAIL', e, v)
