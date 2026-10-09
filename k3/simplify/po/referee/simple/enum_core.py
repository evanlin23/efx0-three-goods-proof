"""Exhaustive tests of DE on core profiles.

usage: python enum_core.py n m patterns [deep] [workers]
patterns: 'rank'  -> values (4,3,2) in all 6 orders on each 3-subset
          'all'   -> 13 value patterns: perms of (4,3,2),(3,3,2),(3,2,2),(1,1,1)
"""
import sys
import time
from itertools import combinations, permutations, product
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '.')
from de import de, check_output, CheckError


def patterns(kind):
    base = [(4, 3, 2)] if kind == 'rank' else [(4, 3, 2), (3, 3, 2), (3, 2, 2), (1, 1, 1)]
    out = set()
    for b in base:
        for p in permutations(b):
            out.add(p)
    return sorted(out)


def agent_rows(m, kind):
    rows = []
    for S in combinations(range(m), 3):
        for p in patterns(kind):
            row = [0] * m
            for g, x in zip(S, p):
                row[g] = x
            rows.append(tuple(row))
    return rows


def work(args):
    n, m, kind, deep, first = args
    rows = agent_rows(m, kind)
    cnt = 0
    trades = Counter()
    kinds = Counter()
    pairs = Counter()
    fails = []
    for rest in product(rows, repeat=n - 1):
        v = [list(first)] + [list(r) for r in rest]
        st = {}
        try:
            X = de(v, checks=True, deep=deep, stats=st)
            check_output(v, X, st)
        except CheckError as e:
            fails.append((v, str(e)))
            continue
        cnt += 1
        trades[st['trades']] += 1
        for k in st.get('kinds', []):
            kinds[k] += 1
        for p in st.get('ring_pairs', []):
            pairs[p] += 1
    return cnt, trades, kinds, pairs, fails


if __name__ == '__main__':
    n, m, kind = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    deep = len(sys.argv) > 4 and sys.argv[4] == 'deep'
    workers = int(sys.argv[5]) if len(sys.argv) > 5 else 4
    rows = agent_rows(m, kind)
    t0 = time.time()
    tasks = [(n, m, kind, deep, r) for r in rows]
    tot = 0
    T, K, P = Counter(), Counter(), Counter()
    fails = []
    with Pool(workers) as pool:
        for cnt, trades, kinds, pairs, fl in pool.imap_unordered(work, tasks, chunksize=1):
            tot += cnt
            T.update(trades); K.update(kinds); P.update(pairs)
            fails.extend(fl)
    print(f"n={n} m={m} patterns={kind} deep={deep}: profiles={tot + len(fails)} ok={tot} fail={len(fails)} "
          f"time={time.time() - t0:.1f}s")
    print('  trades distribution', dict(sorted(T.items())))
    print('  move kinds', dict(K), ' pair arrows per DE ring', dict(sorted(P.items())))
    for v, e in fails[:5]:
        print('  FAIL', e, v)
