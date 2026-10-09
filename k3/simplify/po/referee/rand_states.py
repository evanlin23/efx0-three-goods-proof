"""Random profiles n <= 9: improve() on random valid states (rejection sampling), several seeds each."""
import sys, random, time
from collections import Counter
sys.path.insert(0, '/tmp/claude-0/-home-user-efx0-three-goods/891575f8-e905-5025-9feb-2c6293ea3e11/scratchpad')
import ref

def rand_valid_states(I, rng, tries):
    n = I.n; out = set()
    for _ in range(tries):
        order = list(range(n)); rng.shuffle(order); taken = set(); H = [-1] * n
        for i in order:
            opts = [h for h in range(-1, 4) if not (set(ref.goods(I, i, h)) & taken)]
            w = [1 if h == -1 else (3 if h == 3 else 4) for h in opts]
            h = rng.choices(opts, w)[0]; H[i] = h; taken |= set(ref.goods(I, i, h))
        S = ref.St(I, H)
        if S.valid: out.add(tuple(H))
    return out

if __name__ == '__main__':
    K = int(sys.argv[1]); rng = random.Random(int(sys.argv[2])); C = Counter(); t = time.time()
    for _ in range(K):
        n = rng.randint(2, 9); m = rng.randint(3, 2 * n + 3)
        rank = [tuple(rng.sample(range(m), 3)) for _ in range(n)]
        I = ref.Inst(rank, m)
        for H in rand_valid_states(I, rng, 300):
            S = ref.St(I, H); C['valid states'] += 1
            comp = bool(S.completable_bf()) if n <= 7 else None
            for s in range(3):
                r = ref.improve(S, random.Random(s))
                if r[0] == 'stop':
                    o, Hs = r[1]; assert ref.efx0(I, ref.complete(S, o, Hs)); C['stop'] += 1
                    if comp is not None: assert comp
                else:
                    C['improved'] += 1
                    if comp is False: C['not completable -> improved'] += 1
    print(f'random states: {K} profiles n<=9, {dict(C)}, {time.time()-t:.0f}s')
    print(dict(sorted(ref.STATS.items())))
