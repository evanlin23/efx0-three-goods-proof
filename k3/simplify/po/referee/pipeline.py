"""Whole k = 3 pipeline: R1 peeling until no agent can be peeled, then the Corollary's algorithm on the residual
core case; raw EFX0 check with the REAL values (ties, top-heavy, a = b + c, fewer than three goods, zero goods)."""
import sys, random, time
from collections import Counter
sys.path.insert(0, '/tmp/claude-0/-home-user-efx0-three-goods/891575f8-e905-5025-9feb-2c6293ea3e11/scratchpad')
import ref

def efx0_real(n, v, X):
    for i in range(n):
        vi = sum(v[i].get(g, 0) for g in X[i])
        for j in range(n):
            if j == i or not X[j]: continue
            vals = [v[i].get(g, 0) for g in X[j]]
            if vi < sum(vals) - min(vals): return False
    return True

def ranking(vi, G):
    return sorted([g for g in vi if g in G and vi[g] > 0], key=lambda g: (-vi[g], g))

def pipeline(n, m, v, rng):
    G = set(range(m)); A = list(range(n)); X = [set() for _ in range(n)]
    while len(A) >= 2:
        peel = []
        for i in A:
            r = ranking(v[i], G)
            if len(r) <= 2 or v[i][r[0]] >= v[i][r[1]] + v[i][r[2]]: peel.append(i)
        if not peel: break
        i = rng.choice(peel); r = ranking(v[i], G)
        if r: X[i].add(r[0]); G.discard(r[0])
        A.remove(i)
    if len(A) == 1:
        X[A[0]] |= G; return X, 'single'
    if not A:
        return X, 'none'
    # residual core: every agent of A has three goods in G with a < b + c
    gl = sorted(G); gi = {g: k for k, g in enumerate(gl)}
    rank = []
    for i in A:
        r = ranking(v[i], G); assert len(r) == 3 and v[i][r[0]] < v[i][r[1]] + v[i][r[2]]
        rank.append(tuple(gi[g] for g in r))
    Xc, steps = ref.algorithm(rank, len(gl), rng)
    for k, i in enumerate(A): X[i] |= {gl[g] for g in Xc[k]}
    return X, 'core%d' % len(A)

if __name__ == '__main__':
    K = int(sys.argv[1]); rng = random.Random(int(sys.argv[2])); C = Counter(); t = time.time()
    for _ in range(K):
        n = rng.randint(1, 9); m = rng.randint(0, 2 * n + 4)
        v = []
        for i in range(n):
            k = rng.randint(0, min(3, m)) if rng.random() < 0.2 else min(3, m)
            gs = rng.sample(range(m), k)
            v.append({g: rng.choice([rng.randint(1, 6), rng.randint(1, 3)]) for g in gs})
        X, tag = pipeline(n, m, v, rng)
        assert sorted(g for x in X for g in x) == list(range(m))
        assert efx0_real(n, v, X), (n, m, v, X)
        C[tag if not tag.startswith('core') else 'core'] += 1
    print(f'pipeline: {K} random instances, all EFX0 with real values; {dict(C)}; {time.time()-t:.0f}s')
    print(dict(sorted(ref.STATS.items())))
