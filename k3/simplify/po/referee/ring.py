"""Referee's own ring constructions: k free agents o_i, each blocking >= k exposed top holders (distinct-ish junk,
junk goods shared across blocks allowed), need trees of random shape from exposed tops of block i to o_{i+1}.
Lemma 5 must fire with up to k exposure arcs; then the improvement loop is run to a stop and the completion checked."""
import sys, random, time
from collections import Counter
sys.path.insert(0, '/tmp/claude-0/-home-user-efx0-three-goods/891575f8-e905-5025-9feb-2c6293ea3e11/scratchpad')
import ref

def build(k, rng, extra=0, share=0.3):
    goods = [0]
    def new():
        goods[0] += 1; return goods[0] - 1
    rank = []; hold = []
    p = [new() for _ in range(k)]
    junk_pool = []
    roots = []
    for i in range(k):
        # tree under o_i; its leaves are exposed for o_{i-1}
        prev = p[(i - 1) % k]
        need_leaves = k + rng.randint(0, extra)
        # build tree top-down: list of (agent_slot) frontier "needs" to be satisfied by a good
        # each node: holds own good q, needs 1 or 2 goods (children)
        frontier = []  # goods that must be held by children (requested)
        r = rng.choice([1, 2])
        o_needs = [new() for _ in range(r)]
        roots.append((o_needs, p[i], r))
        frontier = o_needs[:]
        leaves = []
        while len(frontier) + len(leaves) < need_leaves or not frontier:
            if not frontier: break
            g = frontier.pop(rng.randrange(len(frontier)))
            # internal node holding g, needing 1 or 2 new goods
            r2 = rng.choice([1, 2])
            ns = [new() for _ in range(r2)]
            if r2 == 2: rank.append((ns[0], ns[1], g)); hold.append(2)
            else: rank.append((ns[0], g, new())); hold.append(1)  # holds b, c is a fresh good... make it junk-free:
            frontier += ns
        # remaining frontier goods are tops of exposed agents
        hs = []
        for A in frontier:
            if junk_pool and rng.random() < share: h = rng.choice(junk_pool)
            else: h = new(); junk_pool.append(h)
            hs.append(h)
            bc = [prev, h]; rng.shuffle(bc)
            rank.append((A, bc[0], bc[1])); hold.append(0)
    for i, (ns, pi, r) in enumerate(roots):
        if r == 2: rank.append((ns[0], ns[1], pi)); hold.append(2)
        else: rank.append((ns[0], pi, new())); hold.append(1)
    m = goods[0]
    # random relabelling of goods and agents
    gp = list(range(m)); rng.shuffle(gp)
    ap = list(range(len(rank))); rng.shuffle(ap)
    rank2 = [None] * len(rank); hold2 = [None] * len(rank)
    for a, b in enumerate(ap):
        rank2[b] = tuple(gp[g] for g in rank[a]); hold2[b] = hold[a]
    return rank2, m, hold2

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[2])); K = int(sys.argv[1]); C = Counter(); t = time.time()
    for it in range(K):
        k = rng.randint(2, 9)
        rank, m, H = build(k, rng, extra=rng.randint(0, 3), share=rng.choice([0, 0.3, 0.7]))
        I = ref.Inst(rank, m); S = ref.St(I, H)
        if not S.valid: C['invalid build'] += 1; continue
        comp = S.completable_bf() if len(rank) <= 40 else None
        before = dict(ref.STATS)
        steps = 0; tot = sum(ref.util(S.H, i) for i in range(I.n)); first = True
        while True:
            r = ref.improve(S, random.Random(it))
            if r[0] == 'stop':
                o, Hs = r[1]; assert ref.efx0(I, ref.complete(S, o, Hs)); break
            if first:
                C['first move ' + ('L5' if ref.STATS['L5-cycle'] > before.get('L5-cycle', 0) else 'other')] += 1
                arcs = [kk for kk in ref.STATS if kk.startswith('L5-exposure-arcs') and ref.STATS[kk] > before.get(kk, 0)]
                C['first ' + (arcs[0] if arcs else 'no-L5') + ' (k=%d)' % k] += 1
                first = False
            S = r[1]; steps += 1
            t2 = sum(ref.util(S.H, i) for i in range(I.n)); assert t2 > tot; tot = t2
            assert steps <= 4 * I.n
        C['runs'] += 1; C['n max'] = max(C['n max'], I.n)
        # also the algorithm from serial dictatorship on the same profile
        ref.algorithm(rank, m, random.Random(it)); C['algo'] += 1
    print(f'rings: {dict(sorted(C.items()))} {time.time()-t:.0f}s')
    print(dict(sorted(ref.STATS.items())))
