"""Theorem on every valid state (not only those the algorithm visits) + soundness on general valid states."""
import sys, time, random, itertools
from collections import Counter
sys.path.insert(0, '/home/user/efx0-three-goods/k3/simplify')
sys.path.insert(0, '/tmp/claude-0/-home-user-efx0-three-goods/891575f8-e905-5025-9feb-2c6293ea3e11/scratchpad')
from test_k3s import gen_small
import ref

C = Counter()

def completions(S, o, allperm):
    """every hitting set H (subset of the union, |H| <= |F-o|) and assignments of H to free agents != o"""
    I = S.I
    sets = [S.J & {I.rank[x][1], I.rank[x][2]} for x in S.exposed(o)]
    if any(not s for s in sets): return
    univ = sorted(set().union(*sets)) if sets else []
    frees = sorted(S.F - {o})
    for s in range(len(frees) + 1):
        for H in itertools.combinations(univ, s):
            if not all(set(H) & st for st in sets): continue
            perms = itertools.permutations(frees, s) if allperm else [tuple(frees[:s])]
            for tgt in perms:
                X = [set(ref.goods(I, i, S.H[i])) for i in range(I.n)]
                for g, f in zip(H, tgt): X[f].add(g)
                X[o] |= S.J - set(H)
                yield X

def one_profile(rank, m, rng, allperm=True):
    I = ref.Inst(rank, m); n = I.n
    for H in itertools.product(range(-1, 4), repeat=n):
        S = ref.St(I, H)
        if not S.valid: continue
        C['valid'] += 1
        comp = S.completable_bf()
        if comp:
            C['completable'] += 1
            if not (set(comp) & S.F) and len(S.U) < n: C['completable only via U'] += 1
            for o in comp:
                for X in completions(S, o, allperm):
                    C['completions checked'] += 1
                    assert ref.efx0(I, X), ('SOUNDNESS', rank, m, H, o, X)
        else:
            C['not completable'] += 1
        r = ref.improve(S, rng)
        if r[0] == 'stop':
            assert comp
            o, Hs = r[1]
            assert ref.efx0(I, ref.complete(S, o, Hs))
        else:
            C['improved'] += 1
            if not comp: C['not completable -> improved'] += 1

if __name__ == '__main__':
    t = time.time(); rng = random.Random(7)
    for n, ms in ((2, range(3, 7)), (3, range(4, 8))):
        for m in ms:
            for _, _, rank in gen_small(n, m):
                one_profile(rank, m, rng, allperm=True)
            print(f'n={n} m={m} done {time.time()-t:.0f}s', dict(C), flush=True)
    # n = 4: sampled profiles, every state
    for m in (5, 6, 7):
        prng = random.Random(m)
        for _ in range(int(sys.argv[1]) if len(sys.argv) > 1 else 1500):
            rank = [(0, 1, 2)] + [tuple(prng.sample(range(m), 3)) for _ in range(3)]
            one_profile(rank, m, rng, allperm=False)
        print(f'n=4 m={m} sampled done {time.time()-t:.0f}s', dict(C), flush=True)
    print(dict(sorted(ref.STATS.items())))
