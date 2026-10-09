"""Theorem PO (NOTES.md): every valid state that is Pareto-optimal among valid states is completable.

This file is the proof, executed. `certify(st)` follows the proof of NOTES.md §3 step by step on a valid state and
returns either
    ('absorber', o, H)            o is an absorber that passes the HitSet test (H = the protecting goods), or
    ('move', kind, new_opt)       an improving exchange: kind 'D-cycle' (M0), 'pair-chain' (M2) or 'rainbow' (M1).
Every claim the proof makes is an `assert`:
  - an absorber result really is a K3S completion (|H| <= |F \\ {o}|, H meets every exposed pair in junk), and the
    allocation it gives is EFX0 by the raw definition (values 4, 3, 2; `k3s.efx0`);
  - a move result is a valid state in which every agent is at least as well off and the agents it touches are
    strictly better off (so sum u strictly grows; u = nothing 0, c 1, b 2, a 3, pair 4);
  - in the walk of Step 4 an unused colour always exists, and the walk closes into a rainbow cycle.
`completable_bf(st)` is an independent brute-force test of the definition (every absorber, smallest hitting set).

Model (k = 3 core case, ranking profiles): rank[i] = (a_i, b_i, c_i); option of an agent: 0 nothing, 1 a, 2 b, 3 c,
4 pair {b, c}. Evidence only; run `python3 test_exchange.py` for the tests.
"""
import itertools, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..'))
from k3s import efx0 as efx0_raw  # noqa: E402

UT = (0, 3, 2, 1, 4)          # utility of an option: nothing 0, a 3, b 2, c 1, pair 4
VAL = (4, 3, 2)


def held(r, o):
    return () if o == 0 else ((r[o - 1],) if o < 4 else (r[1], r[2]))


def need(r, o):
    return tuple(r) if o == 0 else (() if o in (1, 4) else tuple(r[:o - 1]))


class St:
    """a state with its derived data"""

    def __init__(self, rank, m, opt):
        n = len(rank)
        self.rank, self.m, self.opt, self.n = rank, m, tuple(opt), n
        self.Y = [held(rank[i], opt[i]) for i in range(n)]
        goods = [g for y in self.Y for g in y]
        self.distinct = len(goods) == len(set(goods))
        self.holder = {g: i for i in range(n) for g in self.Y[i]}
        self.NA = set()
        for i in range(n):
            self.NA.update(need(rank[i], opt[i]))
        self.valid = self.distinct and all(g in self.holder and opt[self.holder[g]] in (1, 2, 3) for g in self.NA)
        self.J = set(range(m)) - set(self.holder)
        self.U = [i for i in range(n) if opt[i] == 4]
        self.F = [i for i in range(n) if opt[i] != 4 and (opt[i] == 0 or self.Y[i][0] not in self.NA)]

    def needers(self, j):
        """D out-neighbours of j: non-U agents that need j's (single) good"""
        if self.opt[j] not in (1, 2, 3):
            return []
        g = self.Y[j][0]
        return [k for k in range(self.n) if k != j and g in need(self.rank[k], self.opt[k])]

    def exposed(self, o):
        W = self.J | set(self.Y[o])
        return [x for x in range(self.n) if x != o and self.opt[x] == 1
                and self.rank[x][1] in W and self.rank[x][2] in W]


def min_hitting(sets, limit):
    if not sets:
        return []
    univ = sorted({g for s in sets for g in s})
    for k in range(0, min(limit, len(univ)) + 1):
        for H in itertools.combinations(univ, k):
            if all(s & set(H) for s in sets):
                return list(H)
    return None


def completable_bf(st):
    """the definition, by brute force: some absorber o in F or U, every exposed pair meets J, and a hitting set of
    junk goods with at most |F \\ {o}| goods exists. Returns (o, H) or None."""
    for o in sorted(set(st.F) | set(st.U)):
        sets = [set(st.rank[x][1:]) & st.J for x in st.exposed(o)]
        if any(not s for s in sets):
            continue
        H = min_hitting(sets, len([f for f in st.F if f != o]))
        if H is not None:
            return o, H
    return None


def allocation(st, o, H):
    """K3S completion: H one good each to distinct free agents other than o, the rest of J to o"""
    X = [None] * st.m
    for g, i in st.holder.items():
        X[g] = i
    others = [f for f in st.F if f != o]
    assert len(H) <= len(others)
    for g, f in zip(sorted(H), others):
        X[g] = f
    for g in st.J:
        if X[g] is None:
            X[g] = o
    return X


def is_efx0(st, X):
    return efx0_raw(st.n, st.m, [dict(zip(r, VAL)) for r in st.rank], X)


def d_cycle(st):
    """a cycle of the need digraph D, as a list of agents [j0, j1, ...] with j_{t+1} needing j_t's good"""
    color = {}
    for s in range(st.n):
        if s in color:
            continue
        stack = [(s, iter(st.needers(s)))]; color[s] = 1; path = [s]
        while stack:
            v, it = stack[-1]
            w = next(it, None)
            if w is None:
                color[v] = 2; stack.pop(); path.pop(); continue
            if color.get(w) == 1:
                return path[path.index(w):]
            if w not in color:
                color[w] = 1; stack.append((w, iter(st.needers(w)))); path.append(w)
    return None


def d_path_to_sink(st, x):
    """follow D from x (first needer each time) to a sink; D must be acyclic. Sinks of D among non-U agents are
    exactly the free agents."""
    path = [x]
    while True:
        nx = st.needers(path[-1])
        if not nx:
            return path
        path.append(nx[0])
        assert len(path) <= st.n, "D has a cycle"


def apply_arcs(st, arcs, pair_heads):
    """exchange along arcs (u, v): v receives u's good; v in pair_heads takes its pair (the received good plus a
    junk good), the others hold the received good alone"""
    opt = list(st.opt)
    for u, v in arcs:
        if v in pair_heads:
            opt[v] = 4
        else:
            g = st.Y[u][0]
            opt[v] = st.rank[v].index(g) + 1
    return tuple(opt)


def check_move(st, new_opt, touched):
    nt = St(st.rank, st.m, new_opt)
    assert nt.valid, ("move gives an invalid state", st.rank, st.m, st.opt, new_opt)
    for i in range(st.n):
        if i in touched:
            assert UT[new_opt[i]] > UT[st.opt[i]], ("touched agent not better", st.opt, new_opt, i)
        else:
            assert new_opt[i] == st.opt[i]
    # NA only shrinks (used in the proof of validity)
    assert nt.NA <= st.NA
    return nt


def certify(st, stats=None):
    """the proof of Theorem PO, executed (NOTES.md §3)"""
    assert st.valid
    S = stats if stats is not None else {}
    bump = lambda k: S.__setitem__(k, S.get(k, 0) + 1)
    # Step 0 (M0): a cycle of D. Rotate it.
    cyc = d_cycle(st)
    if cyc is not None:
        arcs = [(cyc[t], cyc[(t + 1) % len(cyc)]) for t in range(len(cyc))]
        new = apply_arcs(st, arcs, set())
        check_move(st, new, set(cyc)); bump('move_D_cycle')
        return ('move', 'D-cycle', new)
    # Step 1 (M2): a top-holder x with b_x and c_x both junk takes them; a_x goes down a D-path to a sink f.
    for x in range(st.n):
        if st.opt[x] == 1 and st.rank[x][1] in st.J and st.rank[x][2] in st.J:
            path = d_path_to_sink(st, x)
            arcs = [(path[t], path[t + 1]) for t in range(len(path) - 1)]
            new = list(apply_arcs(st, arcs, set())); new[x] = 4; new = tuple(new)
            check_move(st, new, set(path)); bump('move_pair_chain')
            return ('move', 'pair-chain', new)
    # Step 2: an agent holding nothing absorbs; nobody is exposed for it.
    e = next((i for i in range(st.n) if st.opt[i] == 0), None)
    if e is not None:
        assert st.exposed(e) == [], "S2 fails"
        bump('absorber_nothing')
        return ('absorber', e, [])
    # Step 3: no free agent: everybody holds a pair (else D would have a cycle).
    if not st.F:
        assert len(st.U) == st.n, "no free agent but D acyclic and some non-U agent"
        bump('absorber_all_pairs')
        return ('absorber', 0, [])
    # Step 4: for a free o, every exposed x has exactly one junk good h_x (the other good is o's).
    nF = len(st.F); col = {}
    for o in st.F:
        E = st.exposed(o); col[o] = {}
        for x in E:
            hs = [g for g in st.rank[x][1:] if g in st.J]
            assert len(hs) == 1 and set(st.rank[x][1:]) == {hs[0], st.Y[o][0]}, "exposure shape"
            col[o].setdefault(hs[0], x)
        if len(col[o]) <= nF - 1:
            bump('absorber_free')
            return ('absorber', o, sorted(col[o]))
    # Step 5: every free o has >= |F| colours. Rainbow walk.
    used = []; seq = [st.F[0]]; arcs = []          # arcs of the walk in A: (u, v, colour or None)
    visited = {st.F[0]: 0}
    while True:
        o = seq[-1]
        free_cols = [h for h in col[o] if h not in used]
        assert free_cols, "no unused colour (counting step fails)"
        h = free_cols[0]; x = col[o][h]; used.append(h)
        arcs.append((o, x, h))
        path = d_path_to_sink(st, x)
        for t in range(len(path) - 1):
            arcs.append((path[t], path[t + 1], None))
        f = path[-1]
        assert f in st.F
        if f in visited:
            break
        visited[f] = len(arcs); seq.append(f)
    # the closed walk starts at the first arc out of f
    start = next(k for k, a in enumerate(arcs) if a[0] == f)
    walk = arcs[start:]
    assert walk[-1][1] == walk[0][0]
    # extract a simple cycle: first repeated vertex along the walk
    verts = [walk[0][0]] + [a[1] for a in walk]
    pos = {}
    for k, v in enumerate(verts):
        if v in pos:
            cyc_arcs = walk[pos[v]:k]; break
        pos[v] = k
    heads = {v for _, v, c in cyc_arcs if c is not None}
    cols = [c for _, _, c in cyc_arcs if c is not None]
    assert len(cols) == len(set(cols)), "not rainbow"
    new = apply_arcs(st, [(u, v) for u, v, _ in cyc_arcs], heads)
    check_move(st, new, {u for u, _, _ in cyc_arcs}); bump('move_rainbow')
    bump(f'rainbow_len_{len(heads)}')
    return ('move', 'rainbow', new)


def check_absorber(st, o, H):
    """an absorber result satisfies the definition and gives an EFX0 allocation"""
    others = [f for f in st.F if f != o]
    assert o in st.F or o in st.U
    assert set(H) <= st.J and len(H) <= len(others)
    for x in st.exposed(o):
        assert set(st.rank[x][1:]) & set(H), ("exposed pair not hit", st.opt, o, x, H)
    X = allocation(st, o, H)
    assert is_efx0(st, X), ("completion not EFX0", st.rank, st.m, st.opt, o, H, X)
    return X


def improve(rank, m, opt, stats=None, maxsteps=None):
    """from a valid state, apply the moves of `certify` until an absorber is found; returns (state, o, H, #moves)"""
    st = St(rank, m, opt); k = 0; su = sum(UT[o] for o in opt)
    while True:
        r = certify(st, stats)
        if r[0] == 'absorber':
            return st, r[1], r[2], k
        st = St(rank, m, r[2]); k += 1
        su2 = sum(UT[o] for o in st.opt); assert su2 > su; su = su2
        assert maxsteps is None or k <= maxsteps


def serial_dictatorship(rank, m):
    """each agent in index order takes its favourite remaining good, or nothing (a valid state)"""
    used = set(); opt = []
    for r in rank:
        t = next((t for t in range(3) if r[t] not in used), None)
        if t is None:
            opt.append(0)
        else:
            opt.append(t + 1); used.add(r[t])
    return tuple(opt)
