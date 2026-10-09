"""Targeted constructions for Lemma 5 (generalisations of the n = 6, m = 10 instance of the brief). Evidence only.

ring(k, d): k free agents o_0..o_{k-1}. o_i holds p_i (its c) and needs two goods; these are the roots of a binary
in-tree of depth d of agents holding their c (each needs the goods of its two children). The 2^d leaves of the tree
of o_{i+1} are top holders: the first k of them are exposed for o_i (ranking (A, p_i, h) with h a fresh junk good),
the others rank (A, p_{i}', h') with p_i' the good of an internal tree agent (not exposed). So F = {o_i}, every
|H_o| = k = |F|: no free absorber works, and no pair holders exist, so the state is not completable.
For every k, d with 2^d >= k: build, check validity and non-completability, run improve(), check the result.
Also: random relabellings of the agents (the greedy SDR and the cycle then differ).

  python3 targeted.py
"""
import sys, os, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hall import St, improve, dominates


def ring(k, d):
    rank, opt = [], []
    goods = iter(range(10 ** 6))
    p = [next(goods) for _ in range(k)]                       # o_i's held good (its c)
    o_idx = []
    trees = []
    for i in range(k):
        # tree of depth d below o_{i}: level 0 = the 2 goods o_i needs
        level = [next(goods), next(goods)]                    # goods needed by o_i (held by its 2 children)
        o_idx.append(len(rank)); rank.append((level[0], level[1], p[i])); opt.append(3)
        internal = []
        for depth in range(1, d):
            nxt = []
            for g in level:
                c1, c2 = next(goods), next(goods)
                rank.append((c1, c2, g)); opt.append(3); internal.append(g)
                nxt += [c1, c2]
            level = nxt
        trees.append((level, internal))
    for i in range(k):
        leaves, internal = trees[(i + 1) % k]                 # leaves below o_{i+1}
        for t, A in enumerate(leaves):
            if t < k:
                h = next(goods)
                rank.append((A, p[i], h)); opt.append(1)       # exposed for o_i
            else:
                q = internal[0] if internal else p[(i + 1) % k]
                h = next(goods)
                rank.append((A, q, h)); opt.append(1)          # not exposed: q is held by a tree agent / o_{i+1}
    m = max(g for r in rank for g in r) + 1
    return rank, m, tuple(opt)


def relabel(rank, m, opt, rng):
    n = len(rank); perm = list(range(n)); rng.shuffle(perm)
    gperm = list(range(m)); rng.shuffle(gperm)
    rank2 = [None] * n; opt2 = [None] * n
    for i in range(n):
        rank2[perm[i]] = tuple(gperm[g] for g in rank[i]); opt2[perm[i]] = opt[i]
    return rank2, m, tuple(opt2)


if __name__ == '__main__':
    rng = random.Random(5)
    for k, d in [(2, 1), (2, 2), (3, 2), (4, 2), (3, 3), (5, 3), (8, 3)]:
        rank, m, opt = ring(k, d)
        hist = {}
        for rep in range(30):
            r2, m2, o2 = (rank, m, opt) if rep == 0 else relabel(rank, m, opt, rng)
            st = St(r2, m2, o2)
            assert st.valid and len(st.F) == k and st.completable() is None, (k, d)
            stats = collections.Counter(); stats['A-cycle len'] = collections.Counter()
            stats['A-cycle exposure arcs'] = collections.Counter()
            new, kind = improve(r2, m2, o2, stats)
            assert St(r2, m2, new).valid and dominates(new, o2)
            e = max(stats['A-cycle exposure arcs']) if stats['A-cycle exposure arcs'] else 0
            hist[(kind, e)] = hist.get((kind, e), 0) + 1
        print(f"ring k={k} d={d}: n={len(rank)} m={m}, 30 relabellings, all improved; (kind, exposure arcs used): {hist}",
              flush=True)
