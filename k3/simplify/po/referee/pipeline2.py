import sys, random, time
from collections import Counter
sys.path.insert(0, '.')
import ref, pipeline
K = int(sys.argv[1]); rng = random.Random(int(sys.argv[2])); C = Counter(); t = time.time()
for _ in range(K):
    n = rng.randint(2, 9); m = rng.randint(3, 2 * n + 4); v = []
    for i in range(n):
        u = rng.random(); gs = rng.sample(range(m), 3)
        if u < 0.08: gs = gs[:rng.randint(0, 2)]
        if u < 0.85 and len(gs) == 3:
            vals = rng.choice([(4,3,2),(10,9,2),(10,6,5),(5,5,1),(3,3,3),(5,3,3),(6,4,3)])
        else:
            vals = tuple(rng.randint(1, 6) for _ in gs)
        v.append(dict(zip(gs, vals)))
    X, tag = pipeline.pipeline(n, m, v, rng)
    assert sorted(g for x in X for g in x) == list(range(m))
    assert pipeline.efx0_real(n, v, X), (n, m, v, X)
    C[tag] += 1
print(f'pipeline (mostly balanced agents, ties): {K} instances, all EFX0 with real values; residual sizes {dict(sorted(C.items()))}; {time.time()-t:.0f}s')
print(dict(sorted(ref.STATS.items())))
