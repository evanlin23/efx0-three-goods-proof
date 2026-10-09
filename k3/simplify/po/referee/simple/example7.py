"""Check every claim of Section 7 and of Appendix A's second instance."""
import sys
from itertools import product, combinations
sys.path.insert(0, '.')
from de import Core, de, is_efx0, efx0_violations, check, check_output

names = ['x1', "x1'", 'x2', "x2'", 'o1', 'o2']
ranks = [(0, 4, 6), (1, 4, 7), (2, 5, 8), (3, 5, 9), (2, 3, 4), (0, 1, 5)]
m = 10


def make_v(ranks, m, vals=(4, 3, 2)):
    v = []
    for r in ranks:
        row = [0] * m
        for g, x in zip(r, vals):
            row[g] = x
        v.append(row)
    return v


v = make_v(ranks, m)
C = Core(v, range(6), range(m))
# draft
Y = {}
taken = set()
for i in C.A:
    Y[i] = frozenset()
    for g in C.rank[i]:
        if g not in taken:
            Y[i] = frozenset([g]); taken.add(g); break
print('draft', {names[i]: sorted(Y[i]) for i in C.A})
assert [sorted(Y[i]) for i in C.A] == [[0], [1], [2], [3], [4], [5]]
print('wanted goods', sorted(C.wanted_goods(Y)), 'valid', C.valid(Y))
for i in C.A:
    print(' ', names[i], 'wants', [g for g in C.pos[i] if C.wants(Y, i, g)])
J = C.J(Y)
F = C.free(Y)
print('J', sorted(J), 'F', [names[i] for i in F], 'NC', C.nc(Y))
for o in F:
    bl = C.blockers(Y, o, J)
    Ho, hx = C.H_o(Y, o, J)
    print('blockers of', names[o], [names[x] for x in bl], 'H', sorted(Ho), {names[x]: h for x, h in hx.items()})
# ten candidate completions
cnt = 0
fails = 0
for o in F:
    other = [f for f in F if f != o]
    for H in [()] + [(h,) for h in sorted(J)]:
        Xc = C.completion(Y, o, set(H), F)
        X = [Xc[i] for i in range(6)]
        cnt += 1
        if not is_efx0(v, X):
            fails += 1
        else:
            print('completion EFX0!', names[o], H)
print('candidate completions', cnt, 'fail', fails)
# the concrete one
Xc = C.completion(Y, 4, {6}, F)
print('X_o1 with H={g6}:', sorted(Xc[4]), "x1' value of X_o1 minus g8:", sum(v[1][g] for g in Xc[4] if g != 8))

# all states Pareto-dominating the draft
opts = {i: [frozenset(), frozenset([C.rank[i][0]]), frozenset([C.rank[i][1]]), frozenset([C.rank[i][2]]), C.pairs[i]] for i in C.A}
base = {i: C.score(i, Y[i]) for i in C.A}
dom = []
nvalid = 0
for choice in product(*[opts[i] for i in C.A]):
    Z = dict(zip(C.A, choice))
    if not C.is_state(Z) or not C.valid(Z):
        continue
    nvalid += 1
    sc = {i: C.score(i, Z[i]) for i in C.A}
    if all(sc[i] >= base[i] for i in C.A) and any(sc[i] > base[i] for i in C.A):
        dom.append(Z)
print('valid states', nvalid, 'dominating draft:', len(dom))
for Z in dom:
    print('  ', {names[i]: sorted(Z[i]) for i in C.A}, 'pairs:', [names[i] for i in C.A if Z[i] == C.pairs[i]])

# arrows and cycles
arrows = []
for w in C.A:
    (y,) = Y[w]
    if w in F:
        for x in C.blockers(Y, w, J):
            arrows.append((w, x, 'pair'))
    else:
        for w2 in C.wanters(Y, y):
            arrows.append((w, w2, 'want'))
print('arrows', [(names[a], names[b], t) for a, b, t in arrows])


def simple_cycles(nodes, arrows):
    adj = {u: [] for u in nodes}
    for a, b, t in arrows:
        adj[a].append((b, t))
    cyc = []

    def dfs(start, u, path, types):
        for b, t in adj[u]:
            if b == start:
                cyc.append((list(path), types + [t]))
            elif b > start and b not in path:
                dfs(start, b, path + [b], types + [t])
    for s in nodes:
        dfs(s, s, [s], [])
    return cyc


cyc = simple_cycles(C.A, arrows)
print('cycles', len(cyc), [(len(p), t.count('pair')) for p, t in cyc])

# DE run
st = {}
X = de(v, checks=True, deep=True, stats=st)
print('DE output', {names[i]: sorted(X[i]) for i in range(6)}, st)
check_output(v, X, st)
print('EFX0', is_efx0(v, X))
assert [sorted(X[i]) for i in range(6)] == [[4, 6], [1, 7, 9], [5, 8], [3], [2], [0]]

# the ring DE picks
ring, q, xo = C.improvement_ring(Y)
print('ring', [names[i] for i in ring], 'q', {names[o]: q[o] for o in q}, 'x', {names[o]: names[xo[o]] for o in xo})
Z = C.trade_ring(Y, ring)
print('after trade', {names[i]: sorted(Z[i]) for i in C.A}, 'total', sum(C.score(i, Y[i]) for i in C.A), '->', sum(C.score(i, Z[i]) for i in C.A))
J2 = C.J(Z)
F2 = C.free(Z)
print('after trade: wanted', C.wanted_goods(Z), 'J', sorted(J2), 'F', [names[i] for i in F2], 'NC', C.nc(Z))
for o in F2:
    print('  blockers of', names[o], [names[x] for x in C.blockers(Z, o, J2)])

# Other value choices with the same rankings: same run?
import random
random.seed(1)
for trial in range(2000):
    vals = []
    for r in ranks:
        while True:
            a, b, c = sorted([random.randint(1, 30) for _ in range(3)], reverse=True)
            if a < b + c:
                break
        vals.append((a, b, c))
    vv = [[0] * m for _ in range(6)]
    for i, (r, val) in enumerate(zip(ranks, vals)):
        for g, x in zip(r, val):
            vv[i][g] = x
    # ties broken by index must give the same rankings
    Cc = Core(vv, range(6), range(m))
    if any(Cc.rank[i] != ranks[i] for i in range(6)):
        continue
    X2 = de(vv, checks=True)
    assert [sorted(X2[i]) for i in range(6)] == [[4, 6], [1, 7, 9], [5, 8], [3], [2], [0]], X2
print('same run for random strictly balanced values with these rankings: ok')

# ---------------- Appendix A, second instance (m = 8)
print('\n--- Appendix A, m=8 instance')
names2 = ['o1', 'o2', 'x1', "x1'", 'x2', "x2'"]
ranks2 = [(4, 5, 0), (6, 7, 1), (4, 1, 2), (5, 3, 1), (6, 0, 2), (7, 3, 0)]
v2 = make_v(ranks2, 8)
C2 = Core(v2, range(6), range(8))
Y2 = {0: frozenset([0]), 1: frozenset([1]), 2: frozenset([4]), 3: frozenset([5]), 4: frozenset([6]), 5: frozenset([7])}
print('state', C2.is_state(Y2), 'valid', C2.valid(Y2), 'NC', C2.nc(Y2))
J2 = C2.J(Y2)
F2 = C2.free(Y2)
print('J', sorted(J2), 'F', [names2[i] for i in F2])
for o in F2:
    Ho, hx = C2.H_o(Y2, o, J2)
    print(' blockers of', names2[o], {names2[x]: h for x, h in hx.items()}, 'can finish (brute)', bool(C2.can_finish_sets(Y2, o, F2, J2)))
arrows2 = []
for w in C2.A:
    (y,) = Y2[w]
    if w in F2:
        for x in C2.blockers(Y2, w, J2):
            h = next(iter(C2.pairs[x] - {y}))
            arrows2.append((w, x, 'pair', h))
    else:
        for w2 in C2.wanters(Y2, y):
            arrows2.append((w, w2, 'want', None))
print('arrows', [(names2[a], names2[b], t, h) for a, b, t, h in arrows2])
cyc2 = simple_cycles(C2.A, [(a, b, t) for a, b, t, h in arrows2])
hmap = {(a, b): h for a, b, t, h in arrows2}
for p, t in cyc2:
    hs = [hmap[(p[k], p[(k + 1) % len(p)])] for k in range(len(p)) if t[k] == 'pair']
    ring_ok = True
    try:
        C2.check_ring(Y2, p)
    except Exception as e:
        ring_ok = False
    print('  cycle', [names2[i] for i in p], 'pair arrows', t.count('pair'), 'hs', hs, 'is ring', ring_ok)
print('n', len(C2.A), 'm', len(C2.G))
