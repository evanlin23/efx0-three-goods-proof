import sys, time, random, itertools
sys.path.insert(0, '/home/user/efx0-three-goods/k3/simplify')
sys.path.insert(0, '/tmp/claude-0/-home-user-efx0-three-goods/891575f8-e905-5025-9feb-2c6293ea3e11/scratchpad')
from test_k3s import gen_small
from lbx import core_profiles
import ref

def run(label, gen, seed=0, orders=False):
    rng = random.Random(seed); t = time.time(); cnt = 0; mx = 0; nstep = 0
    for n, m, rank in gen:
        order = None
        if orders:
            order = list(range(n)); rng.shuffle(order)
        X, s = ref.algorithm(rank, m, rng, order)
        cnt += 1; mx = max(mx, s); nstep += (s > 0)
    print(f'{label}: {cnt} profiles, {nstep} needed >=1 step, max steps {mx}, {time.time()-t:.0f}s', flush=True)

def rand_gen(K, seed, maxn=9):
    rng = random.Random(seed)
    for _ in range(K):
        n = rng.randint(1, maxn); m = rng.randint(3, 2 * n + 3)
        yield n, m, [tuple(rng.sample(range(m), 3)) for _ in range(n)]

if __name__ == '__main__':
    which = sys.argv[1]
    if which == 'small':
        for n, ms in ((2, range(3, 7)), (3, range(4, 8)), (4, range(5, 7))):
            for m in ms:
                run(f'all profiles n={n} m={m}', gen_small(n, m), seed=n * 100 + m)
    elif which == 'cores':
        run('core_profiles(5, sample=100, minn=5)', core_profiles(5, sample=100, minn=5), seed=5)
    elif which == 'random':
        run('random n<=9 (SD order 0..n-1)', rand_gen(int(sys.argv[2]), 11), seed=12)
        run('random n<=9 (random SD order)', rand_gen(int(sys.argv[2]), 13), seed=14, orders=True)
    print(dict(sorted(ref.STATS.items())), flush=True)
