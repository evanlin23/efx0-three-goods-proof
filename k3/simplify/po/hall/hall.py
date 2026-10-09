"""Improvement Lemma (Conjecture PO) for the k = 3 core case: the constructive proof of NOTES.md, as code, and its
tests. One process, no pools.

Model (independent re-implementation of the definitions in NOTES.md §1; cross-checked against
`explore/matching/common.py` by `selftest`): ranking profile `rank` (rank[i] = (a_i, b_i, c_i)), m goods, a state is a
tuple `opt` of options 0 = nothing, 1 = a, 2 = b, 3 = c, 4 = pair {b, c} with distinct held goods.

`improve(rank, m, opt)` takes a valid state that is not completable and returns (opt', kind): a valid state that
Pareto-dominates it, built exactly as in the proof (Theorem, NOTES.md §3):
  kind 'P2-path'  a top holder x with b_x, c_x both junk takes {b_x, c_x}; a_x moves along a need path (Lemma 1);
  kind 'D-cycle'  a cycle of the need digraph (Lemma 1, or the case F = {} of Lemma 4 in NOTES.md);
  kind 'A-cycle'  a cycle of the exchange digraph A (need arcs + one exposure arc o -> x_o per free o; Lemma 5 of NOTES.md).
Every step the proof calls impossible is an assert.

  python3 hall.py selftest                 definitions agree with common.py on every state of small profiles
  python3 hall.py small N M                every valid, non-completable state of every profile: improve() works
  python3 hall.py random K SEED MAXN       same on random profiles (states sampled when there are too many)
  python3 hall.py algo K SEED MAXN         algorithm SD + improve until completable, raw EFX0 check, <= 4n steps
  python3 hall.py cores MAXN SAMPLE        algorithm and improve() on random profiles of every certified core
  python3 hall.py example                  the n = 6, m = 10 instance of NOTES.md §5
"""
import sys, os, itertools, random, time, collections

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'explore', 'matching'))
sys.path.insert(0, os.path.join(HERE, '..', '..'))

UT = {0: 0, 3: 1, 2: 2, 1: 3, 4: 4}          # utility order: nothing < c < b < a < pair


def held(r, o):
    return () if o == 0 else ((r[o - 1],) if o < 4 else (r[1], r[2]))


def needs_of(r, o):
    return tuple(r) if o == 0 else (() if o in (1, 4) else tuple(r[:o - 1]))


class St:
    """a state with its derived data (definitions of NOTES.md §1)"""

    def __init__(self, rank, m, opt):
        self.rank, self.m, self.opt, self.n = rank, m, tuple(opt), len(rank)
        n = self.n
        self.Y = [held(rank[i], opt[i]) for i in range(n)]
        allg = [g for y in self.Y for g in y]
        self.distinct = len(allg) == len(set(allg))
        self.holder = {g: i for i in range(n) for g in self.Y[i]}
        self.U = {i for i in range(n) if opt[i] == 4}
        self.NA = set()
        for i in range(n):
            self.NA.update(needs_of(rank[i], opt[i]))
        self.J = [g for g in range(m) if g not in self.holder]
        self.Jset = set(self.J)
        # valid: every needed good is held, as the only good, by a non-U agent
        self.valid = self.distinct and all(g in self.holder and opt[self.holder[g]] in (1, 2, 3) for g in self.NA)
        self.F = [i for i in range(n) if i not in self.U and (opt[i] == 0 or self.Y[i][0] not in self.NA)]

    def exposed(self, o):
        W = self.Jset | set(self.Y[o])
        return [x for x in range(self.n) if x != o and self.opt[x] == 1
                and self.rank[x][1] in W and self.rank[x][2] in W]

    def absorber_ok(self, o):
        """None if o fails; else a smallest hitting set H (junk goods meeting every {b_x, c_x} & J, x exposed)"""
        if not (o in self.F or o in self.U):
            return None
        sets = []
        for x in self.exposed(o):
            s = frozenset(g for g in self.rank[x][1:] if g in self.Jset)
            if not s:
                return None
            sets.append(s)
        lim = len(self.F) - (1 if o in self.F else 0)
        univ = sorted({g for s in sets for g in s})
        for k in range(0, min(lim, len(univ)) + 1):
            for H in itertools.combinations(univ, k):
                if all(s & set(H) for s in sets):
                    return list(H)
        return None

    def completable(self):
        for o in range(self.n):
            H = self.absorber_ok(o)
            if H is not None:
                return o, H
        return None

    def allocation(self, o, H):
        """the completion of NOTES.md §1: H one good each into distinct free agents other than o, the rest of J to o"""
        X = [None] * self.m
        for g, i in self.holder.items():
            X[g] = i
        others = [f for f in self.F if f != o]
        assert len(H) <= len(others)
        for g, f in zip(H, others):
            X[g] = f
        for g in self.J:
            if X[g] is None:
                X[g] = o
        return X


def dominates(s2, s1):
    return all(UT[a] >= UT[b] for a, b in zip(s2, s1)) and any(UT[a] > UT[b] for a, b in zip(s2, s1))


def needers(st, g):
    """non-U agents that need good g (in index order)"""
    return [j for j in range(st.n) if st.opt[j] in (0, 2, 3) and g in needs_of(st.rank[j], st.opt[j])]


def apply_chain(st, arcs, pair_agents):
    """arcs: list of (u, v) meaning v takes u's single good (v != pair agent) or v is a pair agent.
    pair_agents: agents that take their pair. Returns the new option tuple."""
    o2 = list(st.opt)
    for u, v in arcs:
        if v in pair_agents:
            continue
        g = st.Y[u][0]
        o2[v] = st.rank[v].index(g) + 1
    for x in pair_agents:
        o2[x] = 4
    return tuple(o2)


def d_cycle_from(st, path):
    """path closed into a D-cycle: path[k] -> path[k+1] -> ... -> path[-1] -> path[k]"""
    arcs = [(path[t], path[t + 1]) for t in range(len(path) - 1)] + [(path[-1], path[0])]
    return apply_chain(st, arcs, set())


def p2_fails(st):
    return [x for x in range(st.n) if st.opt[x] == 1 and st.rank[x][1] in st.Jset and st.rank[x][2] in st.Jset]


def cor_stop(st):
    """the Corollary's stop rule: if (P2) holds and every agent holds a pair, or some free o holds nothing, or some
    free o has |H_o| <= |F| - 1, return (o, H_o); else None. H_o = forced protecting goods (Lemma 3)."""
    if p2_fails(st):
        return None
    if len(st.U) == st.n:
        return 0, []
    for o in st.F:
        if st.opt[o] == 0:
            assert not st.exposed(o)                     # Lemma 2
            return o, []
        g = st.Y[o][0]
        H = sorted({st.rank[x][2] if st.rank[x][1] == g else st.rank[x][1] for x in st.exposed(o)})
        if len(H) <= len(st.F) - 1:
            return o, H
    return None


def improve(rank, m, opt, stats=None):
    """requires: valid, and either (P2) fails or no free agent is a valid absorber and not every agent holds a pair
    (implied by "not completable")"""
    st = St(rank, m, opt)
    assert st.valid
    assert p2_fails(st) or (len(st.U) < st.n and all(st.absorber_ok(o) is None for o in st.F))
    n = st.n
    # ---- Lemma 1 (P2): a top holder x with b_x, c_x both junk
    for x in range(n):
        if st.opt[x] == 1 and st.rank[x][1] in st.Jset and st.rank[x][2] in st.Jset:
            path = [x]
            while True:
                last = path[-1]
                if st.opt[last] == 0 or st.Y[last][0] not in st.NA:
                    break                          # the path ends at a free agent (or x itself if a_x is not needed)
                w = needers(st, st.Y[last][0])[0]
                assert w != last
                if w in path:                       # a cycle of D
                    k = path.index(w)
                    return d_cycle_from(st, path[k:]), 'D-cycle'
                path.append(w)
            arcs = [(path[t], path[t + 1]) for t in range(len(path) - 1)]
            return apply_chain(st, arcs, {x}), 'P2-path'
    # from here on P2 holds
    nonU = [i for i in range(n) if i not in st.U]
    assert nonU, "all agents hold pairs: completable"
    F = st.F
    if not F:
        # every non-U agent holds a needed good: follow need arcs until a repeat
        path = [nonU[0]]
        while True:
            w = needers(st, st.Y[path[-1]][0])[0]
            if w in path:
                return d_cycle_from(st, path[path.index(w):]), 'D-cycle'
            path.append(w)
    # Lemma 2: a free agent holding nothing has no exposed agent (so it would be a valid absorber)
    for o in F:
        assert st.opt[o] != 0, "free agent holding nothing: valid absorber"
    # Lemma 3: for free o holding g, every x exposed for o has {b_x, c_x} = {g, h_x}, h_x junk
    E, H = {}, {}
    for o in F:
        g = st.Y[o][0]
        E[o] = st.exposed(o)
        H[o] = {}
        for x in E[o]:
            bx, cx = st.rank[x][1], st.rank[x][2]
            assert g in (bx, cx)
            h = cx if bx == g else bx
            assert h in st.Jset
            H[o].setdefault(h, x)
        # o fails  <=>  |H_o| >= |F|
        assert len(H[o]) >= len(F), "free absorber with |H_o| <= |F| - 1"
    # Lemma 5 of NOTES.md: distinct representatives h_o in H_o, greedily
    used, xo = set(), {}
    for o in F:
        h = next(h for h in sorted(H[o]) if h not in used)
        used.add(h)
        xo[o] = H[o][h]
    # exchange digraph A restricted to one out-arc per non-U agent
    succ = {}
    for v in nonU:
        if v in xo:
            succ[v] = xo[v]
        else:
            succ[v] = needers(st, st.Y[v][0])[0]
        assert succ[v] != v and succ[v] in nonU
    path, seen = [nonU[0]], {nonU[0]}
    while succ[path[-1]] not in seen:
        path.append(succ[path[-1]])
        seen.add(path[-1])
    cyc = path[path.index(succ[path[-1]]):]
    arcs = [(cyc[t], cyc[(t + 1) % len(cyc)]) for t in range(len(cyc))]
    pairs = {v for u, v in arcs if u in xo}           # entered by an exposure arc u -> x_u
    o2 = apply_chain(st, arcs, pairs)
    if stats is not None:
        stats['A-cycle len'][len(cyc)] += 1
        stats['A-cycle exposure arcs'][len(pairs)] += 1
    kind = 'A-cycle' if pairs else 'D-cycle'
    return o2, kind


def check_improve(rank, m, opt, stats):
    o2, kind = improve(rank, m, opt, stats)
    s2 = St(rank, m, o2)
    assert s2.valid, (rank, m, opt, o2, kind)
    assert dominates(o2, opt), (rank, m, opt, o2, kind)
    stats[kind] += 1
    return o2


# ---------------------------------------------------------------------------------------------------- enumeration
def all_states(rank, m):
    n = len(rank); out = []; cur = [0] * n

    def rec(i, used):
        if i == n:
            out.append(tuple(cur)); return
        for o in range(5):
            h = held(rank[i], o)
            if any(g in used for g in h):
                continue
            cur[i] = o; rec(i + 1, used | set(h))
    rec(0, frozenset())
    return out


def run_profile(rank, m, stats, states=None):
    for s in (states if states is not None else all_states(rank, m)):
        st = St(rank, m, s)
        if not st.valid:
            continue
        stats['valid'] += 1
        c = st.completable()
        if c is None:
            stats['not completable'] += 1
            check_improve(rank, m, s, stats)
        else:
            o, H = c
            stats['completable'] += 1
            # soundness check of the completion against the raw EFX0 definition
            if stats.get('raw') is not None:
                X = st.allocation(o, H)
                assert efx0(rank, m, X), (rank, m, s, o, H, X)


def efx0(rank, m, X):
    n = len(rank)
    v = [dict(zip(r, (4, 3, 2))) for r in rank]
    B = [[g for g in range(m) if X[g] == i] for i in range(n)]
    for i in range(n):
        own = sum(v[i].get(g, 0) for g in B[i])
        for j in range(n):
            if i == j or not B[j]:
                continue
            s = sum(v[i].get(g, 0) for g in B[j]); mn = min(v[i].get(g, 0) for g in B[j])
            if s - mn > own:
                return False
    return True


def gen_small(n, m):
    tri = list(itertools.permutations(range(m), 3))
    for rest in itertools.product(tri, repeat=n - 1):
        yield [(0, 1, 2)] + list(rest)


def new_stats():
    s = collections.Counter()
    s['A-cycle len'] = collections.Counter(); s['A-cycle exposure arcs'] = collections.Counter()
    return s


def show(stats, label, t0):
    d = {k: v for k, v in stats.items() if not isinstance(v, collections.Counter) and k != 'raw'}
    print(f"{label}: {d}; A-cycle lengths {dict(sorted(stats['A-cycle len'].items()))}; "
          f"exposure arcs per A-cycle {dict(sorted(stats['A-cycle exposure arcs'].items()))}  [{time.time() - t0:.0f}s]",
          flush=True)


# ---------------------------------------------------------------------------------------------------- algorithm
def serial_dictatorship(rank, m):
    used = set(); opt = []
    for r in rank:
        o = next((t + 1 for t, g in enumerate(r) if g not in used), 0)
        if o:
            used.add(r[o - 1])
        opt.append(o)
    return tuple(opt)


def algorithm(rank, m, stats):
    """the Corollary: serial dictatorship, then improve() until the stop rule `cor_stop` holds; returns the
    allocation (checked against the raw EFX0 definition)"""
    opt = serial_dictatorship(rank, m)
    steps = 0
    while True:
        st = St(rank, m, opt)
        assert st.valid
        c = cor_stop(st)
        if c is not None:
            assert st.absorber_ok(c[0]) is not None and len(st.absorber_ok(c[0])) == len(c[1])
            break
        opt = check_improve(rank, m, opt, stats)
        steps += 1
        assert steps <= 4 * len(rank)
    stats['algo steps'] = max(stats['algo steps'], steps)
    stats['algo runs'] += 1
    stats['algo improved'] += steps > 0
    X = st.allocation(*c)
    assert efx0(rank, m, X), (rank, m, opt, c, X)
    return X


def random_states(rank, m, rng, K):
    """K random valid states (duplicates removed): agents in random order; each picks a random option whose goods are
    unused and whose needs are already held as single goods (so every state with an acyclic need digraph can occur)"""
    n = len(rank); out = set()
    for _ in range(K):
        used = set(); singles = set(); opt = [0] * n; ok = True
        for i in rng.sample(range(n), n):
            choices = [o for o in range(5) if not any(g in used for g in held(rank[i], o))
                       and all(g in singles for g in needs_of(rank[i], o))]
            if not choices:                      # dead end (e.g. a_i went into a pair): drop this sample
                ok = False; break
            o = rng.choice(choices)
            opt[i] = o; used.update(held(rank[i], o))
            if o in (1, 2, 3):
                singles.add(rank[i][o - 1])
        if ok:
            out.add(tuple(opt))
    return list(out)


# ---------------------------------------------------------------------------------------------------- self-test
def selftest():
    from common import Base, completes
    t0 = time.time(); cnt = 0
    for n, m in [(2, 3), (2, 4), (2, 5), (3, 4), (3, 5)]:
        for rank in gen_small(n, m):
            for s in all_states(rank, m):
                st = St(rank, m, s); b = Base(rank, m, s)
                assert st.valid == b.valid
                if not st.valid:
                    continue
                assert sorted(st.F) == sorted(b.free) and sorted(st.NA) == sorted(b.NA) and st.J == b.J
                for o in range(n):
                    assert st.exposed(o) == b.exposed(o)
                mine = st.completable() is not None
                theirs = completes(b, how='k3s') is not None
                assert mine == theirs, (rank, m, s)
                cnt += 1
    print(f"selftest: {cnt} valid states agree with common.py (validity, F, NA, J, exposure, completability)  "
          f"[{time.time() - t0:.0f}s]", flush=True)


def example():
    rank = [(0, 4, 6), (1, 4, 7), (2, 5, 8), (3, 5, 9), (2, 3, 4), (0, 1, 5)]
    m = 10
    opt = (1, 1, 1, 1, 3, 3)
    st = St(rank, m, opt)
    print('example: valid', st.valid, 'NA', sorted(st.NA), 'J', st.J, 'F', st.F, 'completable', st.completable())
    stats = new_stats()
    o2, kind = improve(rank, m, opt, stats)
    s2 = St(rank, m, o2)
    print('  improve ->', o2, kind, 'valid', s2.valid, 'dominates', dominates(o2, opt), 'completable', s2.completable())


if __name__ == '__main__':
    mode = sys.argv[1]
    t0 = time.time()
    if mode == 'selftest':
        selftest()
    elif mode == 'example':
        example()
    elif mode == 'small':
        n, m = int(sys.argv[2]), int(sys.argv[3])
        stats = new_stats(); stats['raw'] = True; P = 0
        for rank in gen_small(n, m):
            run_profile(rank, m, stats); P += 1
        show(stats, f"every state of every profile n={n} m={m} ({P} profiles)", t0)
    elif mode == 'random':
        K, seed, N = map(int, sys.argv[2:5]); rng = random.Random(seed)
        stats = new_stats(); stats['raw'] = True
        for _ in range(K):
            n = rng.randint(2, N); m = rng.randint(max(3, n), 2 * n + 2)
            rank = [tuple(rng.sample(range(m), 3)) for _ in range(n)]
            S = all_states(rank, m) if n <= 4 else random_states(rank, m, rng, 300)
            run_profile(rank, m, stats, S)
        show(stats, f"{K} random profiles n<={N} (seed {seed})", t0)
    elif mode == 'algo':
        K, seed, N = map(int, sys.argv[2:5]); rng = random.Random(seed)
        stats = new_stats()
        for _ in range(K):
            n = rng.randint(2, N); m = rng.randint(max(3, n), 2 * n + 3)
            rank = [tuple(rng.sample(range(m), 3)) for _ in range(n)]
            algorithm(rank, m, stats)
        show(stats, f"algorithm on {K} random profiles n<={N} (seed {seed})", t0)
    elif mode == 'cores':
        from lbx import core_profiles
        N, S = int(sys.argv[2]), int(sys.argv[3])
        stats = new_stats(); stats['raw'] = True; rng = random.Random(7)
        os.chdir(os.path.join(HERE, '..', '..', '..', '..'))
        for n, m, rank in core_profiles(N, sample=S, minn=N):
            rank = [tuple(r) for r in rank]
            algorithm(rank, m, stats)
            run_profile(rank, m, stats, random_states(rank, m, rng, 60))
        show(stats, f"cores n={N}, {S} random profiles per core (algorithm + 60 random states each)", t0)
