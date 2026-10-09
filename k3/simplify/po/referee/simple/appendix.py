"""Brute-force checks of Appendix B (Lemma 'cases of safety', Proposition
'limits of the shape') and of the tree construction at the end of Appendix A."""
import sys
import random
from itertools import product
from collections import Counter
sys.path.insert(0, '.')
from de import is_efx0, Core, check
from allstates import short_ring_exists


def bundles(assign, nag):
    B = [set() for _ in range(nag)]
    for g, i in enumerate(assign):
        B[i].add(g)
    return B


def safe(v, B, i):
    own = sum(v[i][g] for g in B[i])
    for j in range(len(B)):
        if j == i:
            continue
        tot = sum(v[i][g] for g in B[j])
        for h in B[j]:
            if tot - v[i][h] > own:
                return False
    return True


def lemma_cases(B, i, a, b, c):
    Xi = B[i]
    def alone(g):
        return any(Bk == {g} for Bk in B)
    def bc_together_big():
        return any(b in Bk and c in Bk and len(Bk) >= 3 for Bk in B)
    T = a in Xi and (b in Xi or c in Xi or not bc_together_big())
    BC = b in Xi and c in Xi
    Bc = b in Xi and alone(a)
    Cc = c in Xi and alone(a) and alone(b)
    E = alone(a) and alone(b) and alone(c)
    return T or BC or Bc or Cc or E


# Lemma L5: agent 0 values goods 0,1,2 (a,b,c); goods 3,4,5 extra; 4 agents
rng = random.Random(7)
tested = 0
for vals in [(4, 3, 2), (10, 7, 5), (5, 4, 2), (100, 99, 2), (7, 6, 5)]:
    assert vals[0] > vals[1] > vals[2] > 0 and vals[0] < vals[1] + vals[2]
    for nag in (2, 3, 4):
        for mg in (3, 4, 5, 6):
            v = [[0] * mg for _ in range(nag)]
            v[0][0], v[0][1], v[0][2] = vals
            for assign in product(range(nag), repeat=mg):
                B = bundles(assign, nag)
                s = safe(v, B, 0)
                lc = lemma_cases(B, 0, 0, 1, 2)
                assert s == lc, (vals, B, s, lc)
                tested += 1
print('Lemma cases of safety: allocations tested', tested, 'all agree')

# Proposition (a)
def prop_a(valsets):
    # goods g0=0, g1=1, p0=2, p1=3, p2=4
    v = []
    for i in range(3):
        row = [0] * 5
        row[0], row[1], row[2 + i] = valsets[i]
        v.append(row)
    sizes_efx = Counter()
    for assign in product(range(3), repeat=5):
        B = bundles(assign, 3)
        if is_efx0(v, B):
            sizes_efx[tuple(sorted(len(x) for x in B))] += 1
            assert max(len(x) for x in B) >= 3, B
    from itertools import permutations
    for perm in permutations(range(3)):
        B = [None] * 3
        B[perm[0]], B[perm[1]], B[perm[2]] = {0}, {1}, {2, 3, 4}
        assert is_efx0(v, B), B
    return sizes_efx


def rand_vals(rng):
    while True:
        a, b, c = sorted(rng.sample(range(1, 60), 3), reverse=True)
        if a < b + c:
            return (a, b, c)


print('Prop (a), values 4,3,2: EFX0 bundle-size multisets', dict(prop_a([(4, 3, 2)] * 3)))
for t in range(300):
    prop_a([rand_vals(rng) for _ in range(3)])
print('Prop (a): 300 random strict balanced value profiles ok')


def prop_b(valsets):
    # g0=0, g1=1, g2=2, p0..p3 = 3..6
    ranks = [(0, 2, 3), (0, 2, 4), (1, 2, 5), (1, 2, 6)]
    v = []
    for i in range(4):
        row = [0] * 7
        for g, x in zip(ranks[i], valsets[i]):
            row[g] = x
        v.append(row)
    sizes = Counter()
    for assign in product(range(4), repeat=7):
        B = bundles(assign, 4)
        if is_efx0(v, B):
            sizes[tuple(sorted(len(x) for x in B))] += 1
    assert set(sizes) == {(1, 1, 1, 4)}, sizes
    B = [{0}, {2}, {1}, {3, 4, 5, 6}]
    assert is_efx0(v, B)
    return sizes


print('Prop (b), values 4,3,2: EFX0 bundle-size multisets', dict(prop_b([(4, 3, 2)] * 4)))
for t in range(100):
    prop_b([rand_vals(rng) for _ in range(4)])
print('Prop (b): 100 random strict balanced value profiles ok')


# Appendix A tree construction
def tree_state(k, d):
    """o_i is the root of a binary tree of depth d; internal agents hold their c and
    want their a,b held by their two children; leaves of tree i+1 hold their tops and
    have pair {y_{o_i}, h} with distinct leftover h."""
    agents = []  # (a,b,c) and held good
    holding = []
    goods = [0]

    def new():
        goods[0] += 1
        return goods[0] - 1
    yo = [new() for _ in range(k)]
    leaves_of = {}
    roots = []
    for i in range(k):
        # build tree for o_i
        # level 0: o_i itself with held good yo[i]
        level = [None]  # placeholder for root
        root_idx = len(agents)
        agents.append(None)
        holding.append(yo[i])
        frontier = [(root_idx, yo[i])]
        for depth in range(1, d + 1):
            nxt = []
            for (p, pc) in frontier:
                kid_goods = []
                for _ in range(2):
                    idx = len(agents)
                    if depth < d:
                        g = new()  # child's c, held by child
                        agents.append(None)
                        holding.append(g)
                        nxt.append((idx, g))
                        kid_goods.append(g)
                    else:
                        g = new()  # leaf top
                        agents.append(('leaf', g, i))
                        holding.append(g)
                        kid_goods.append(g)
                        leaves_of.setdefault(i, []).append(idx)
                # parent's a, b are the children's goods, its c is pc
                agents[p] = (kid_goods[0], kid_goods[1], pc)
            frontier = nxt
        roots.append(root_idx)
    # leaves of tree (i+1) are blockers of o_i: pair {yo[i], h}
    for i in range(k):
        for idx in leaves_of[(i + 1) % k]:
            _, top, _ = agents[idx]
            agents[idx] = (top, yo[i], new())
    m = goods[0]
    v = []
    for r in agents:
        row = [0] * m
        for g, x in zip(r, (4, 3, 2)):
            row[g] = x
        v.append(row)
    Y = {i: frozenset([holding[i]]) for i in range(len(agents))}
    return v, Y, roots


def cycles_pair_counts(C, Y, F, J, limit=10 ** 6):
    nodes = list(C.A)
    adj = {u: [] for u in nodes}
    for w in nodes:
        (y,) = Y[w]
        if w in F:
            for x in C.blockers(Y, w, J):
                adj[w].append((x, 1))
        else:
            for w2 in C.wanters(Y, y):
                adj[w].append((w2, 0))
    counts = Counter()

    def dfs(start, u, onpath, npair):
        for b, t in adj[u]:
            if b == start:
                counts[npair + t] += 1
            elif b > start and b not in onpath:
                onpath.add(b)
                dfs(start, b, onpath, npair + t)
                onpath.remove(b)
    for s in nodes:
        dfs(s, s, {s}, 0)
    return counts


for k in (2, 3, 4, 5):
    for d in (1, 2):
        v, Y, roots = tree_state(k, d)
        C = Core(v, range(len(v)), range(len(v[0])))
        assert C.is_state(Y) and C.valid(Y) and C.nc(Y)
        J = C.J(Y)
        F = C.free(Y)
        assert sorted(F) == sorted(roots), (F, roots)
        can = [bool(C.can_finish_sets(Y, o, F, J, limit=1)) for o in F] if k <= 3 else None
        Ho = [len(C.H_o(Y, o, J)[0]) for o in F]
        nofinish = all(h > len(F) - 1 for h in Ho)
        assert nofinish == (k <= 2 ** d)
        if can is not None:
            assert (not any(can)) == nofinish
        cc = cycles_pair_counts(C, Y, set(F), J) if len(v) <= 40 else None
        short = short_ring_exists(C, Y, F, J)
        res = ''
        if nofinish:
            ring, q, xo = C.improvement_ring(Y)
            npair = C.check_ring(Y, ring)
            Z = C.trade_ring(Y, ring)
            assert C.valid(Z)
            res = f'DE ring has {npair} pair arrows'
        print(f'tree k={k} d={d}: n={len(v)} m={len(v[0])} |H_o|={Ho[0]} no-finish={nofinish} '
              f'cycle pair counts={dict(cc) if cc else "skipped"} short move={short} {res}')
