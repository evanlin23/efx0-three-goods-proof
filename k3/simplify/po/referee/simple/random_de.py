"""Random tests of DE (peeling included) on general instances, n <= 8."""
import sys
import random
import time
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '.')
from de import de, check_output, CheckError


def balanced_vals(rng):
    while True:
        if rng.random() < 0.4:
            vals = [rng.choice([1, 2, 3]) for _ in range(3)]
        else:
            vals = [rng.randint(1, 12) for _ in range(3)]
        s = sorted(vals, reverse=True)
        if s[0] < s[1] + s[2]:
            return s  # descending, so the listed order is the ranking up to ties


def gen_planted(rng):
    """Plant Section-7-like gadgets: k free agents o, each with blockers x whose
    b is o's drafted good and whose c is leftover; o's a and b are tops of x's."""
    k = rng.choice([2, 2, 2, 3])
    nb = [rng.randint(max(1, k - 1), k + 1) for _ in range(k)]
    goods = 0
    def new():
        nonlocal goods
        goods += 1
        return goods - 1
    oc = [new() for _ in range(k)]  # o's drafted (c) goods
    xs = []  # (top, b, c, group)
    pool = [new() for _ in range(rng.randint(2, sum(nb) + 1))]
    distinct = rng.random() < 0.6
    grp = []
    for gi in range(k):
        fresh = rng.sample(pool, nb[gi]) if (distinct and nb[gi] <= len(pool)) else [rng.choice(pool) for _ in range(nb[gi])]
        for t in range(nb[gi]):
            xs.append([new(), oc[gi], fresh[t]])
            grp.append(gi)
    n_x = len(xs)
    os_ = []
    cyc = rng.random() < 0.7
    for gi in range(k):
        if cyc:
            cand = [t for t in range(n_x) if grp[t] == (gi - 1) % k]
            if len(cand) < 2:
                cand = list(range(n_x))
        else:
            cand = list(range(n_x))
        a, b = rng.sample(cand, 2)
        os_.append([xs[a][0], xs[b][0], oc[gi]])
    agents = xs + os_
    extra = rng.randint(0, 2)
    for _ in range(extra):
        agents.append(rng.sample(range(goods + 2), 3))
    if rng.random() < 0.2:
        rng.shuffle(agents)
    m = max(max(r) for r in agents) + 1 + rng.randint(0, 2)
    perm = list(range(m))
    rng.shuffle(perm)
    v = [[0] * m for _ in agents]
    for i, r in enumerate(agents):
        vals = balanced_vals(rng)
        for g, x in zip(r, vals):
            v[i][perm[g]] = x
    return v


def gen(rng, kind):
    if kind == 'planted':
        return gen_planted(rng)
    n = rng.randint(1, 8)
    if kind == 'general':
        m = rng.randint(0, 14)
    elif kind == 'core':
        m = rng.randint(3, n + 5)
    elif kind == 'tight':
        m = rng.randint(3, max(3, n + 2))
    else:  # mid / skew
        m = rng.randint(max(3, n + 1), 2 * n + 3)
    v = [[0] * m for _ in range(n)]
    for i in range(n):
        if kind == 'general':
            k = rng.choices([0, 1, 2, 3], weights=[1, 1, 2, 6])[0]
        else:
            k = 3
        k = min(k, m)
        if kind == 'skew':
            wts = [1.0 / (g + 1) ** 1.2 for g in range(m)]
            S = []
            while len(S) < k:
                g = rng.choices(range(m), weights=wts)[0]
                if g not in S:
                    S.append(g)
        else:
            S = rng.sample(range(m), k)
        while True:
            if rng.random() < 0.4:
                vals = [rng.choice([1, 2, 3]) for _ in range(k)]
            else:
                vals = [rng.randint(1, 12) for _ in range(k)]
            if kind == 'general' or k < 3:
                break
            s = sorted(vals, reverse=True)
            balanced = s[0] < s[1] + s[2]
            if kind == 'core' and (balanced or rng.random() < 0.2):
                break
            if kind in ('tight', 'mid', 'skew') and balanced:
                break
        for g, x in zip(S, vals):
            v[i][g] = x
    return v


def work(args):
    seed, N, kind, deep_every = args
    rng = random.Random(seed)
    res = Counter()
    trades = Counter()
    pairs = Counter()
    fails = []
    for t in range(N):
        v = gen(rng, kind)
        st = {}
        try:
            X = de(v, checks=True, deep=(t % deep_every == 0), stats=st)
            check_output(v, X, st)
        except CheckError as e:
            fails.append((v, str(e)))
            continue
        res['ok'] += 1
        res['core'] += (st['core_n'] >= 2)
        res['peeled'] += st['peel']
        trades[st['trades']] += 1
        for k in st.get('kinds', []):
            res['kind_' + k] += 1
        for p in st.get('ring_pairs', []):
            pairs[p] += 1
        if st.get('finisher_holds_nothing'):
            res['finisher_holds_nothing'] += 1
    return res, trades, pairs, fails


if __name__ == '__main__':
    kind = sys.argv[1]
    N = int(sys.argv[2])
    chunks = 40
    t0 = time.time()
    R, T, P = Counter(), Counter(), Counter()
    fails = []
    with Pool(4) as pool:
        for res, trades, pairs, fl in pool.imap_unordered(work, [({"general": 1, "core": 2, "tight": 3, "mid": 4, "skew": 5, "planted": 6}[kind] * 100000 + s, N // chunks, kind, 5) for s in range(chunks)]):
            R.update(res); T.update(trades); P.update(pairs); fails.extend(fl)
    print(f"random {kind}: runs={R['ok'] + len(fails)} ok={R['ok']} fail={len(fails)} time={time.time() - t0:.1f}s")
    print('  ', dict(R))
    print('   trades', dict(sorted(T.items())), ' pair arrows per DE ring', dict(sorted(P.items())))
    for v, e in fails[:5]:
        print('  FAIL', e, v)
