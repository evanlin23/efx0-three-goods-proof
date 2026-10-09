"""Tests of Theorem PO and of its proof (exchange.certify) on every valid state of many profiles. Evidence only;
one process, no pools.

  python3 test_exchange.py example                 the n = 6, m = 10 instance of the brief, and its generalisations
  python3 test_exchange.py small N M               every ranking profile (agent 0 ranks 0 > 1 > 2), every valid state
  python3 test_exchange.py random K SEED MAXN      K random profiles, 2 <= n <= MAXN, m in n+1..2n+3, every valid state
  python3 test_exchange.py cores MAXN SAMPLE MINN  SAMPLE random profiles of every certified core, every valid state

For every valid state: certify() must return an absorber whose K3S completion is EFX0 (raw check), or an improving
move (valid, Pareto-dominating). Also counted: valid states that are not completable (brute force over the
definition), each of which must get a move; Pareto-optimal states (all must get an absorber); and the algorithm
"serial dictatorship, then moves until an absorber" (EFX0 raw check, number of moves).
"""
import sys, os, random, collections, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'explore', 'matching'))
from exchange import St, certify, check_absorber, completable_bf, improve, serial_dictatorship, UT  # noqa: E402
from exp_fast import valid_states  # noqa: E402


def pareto_set(opts):
    us = [tuple(UT[o] for o in opt) for opt in opts]
    order = sorted(range(len(us)), key=lambda k: -sum(us[k])); keep = []
    for k in order:
        if not any(all(a >= b for a, b in zip(us[j], us[k])) and us[j] != us[k] for j in keep):
            keep.append(k)
    return {opts[k] for k in keep}


def run_profile(rank, m, S, first):
    opts = [s[0] for s in valid_states(rank, m)]
    po = pareto_set(opts)
    for opt in opts:
        st = St(rank, m, opt)
        r = certify(st, S)
        S['states'] += 1
        bf = completable_bf(st)
        if r[0] == 'absorber':
            check_absorber(st, r[1], r[2])
            assert bf is not None
        if bf is None:
            S['not_completable'] += 1
            assert r[0] == 'move'
            S['not_completable_' + r[1]] += 1
            if r[1] == 'rainbow' and 'rainbow' not in first:
                first['rainbow'] = (rank, m, opt, r[2])
        if opt in po:
            S['pareto_optimal'] += 1
            assert r[0] == 'absorber', ("PO state got a move", rank, m, opt, r)
    # algorithm: serial dictatorship then moves
    st, o, H, k = improve(rank, m, serial_dictatorship(rank, m))
    check_absorber(st, o, H)
    S['alg_moves_%d' % k] += 1


def example():
    rank = [(0, 4, 6), (1, 4, 7), (2, 5, 8), (3, 5, 9), (2, 3, 4), (0, 1, 5)]
    m = 10
    opt = (1, 1, 1, 1, 3, 3)       # the x's hold their tops, o1 holds 4 (its c), o2 holds 5 (its c)
    st = St(rank, m, opt)
    print("example: valid", st.valid, "F", st.F, "J", sorted(st.J), "completable", completable_bf(st))
    print("  " + cycle_profile(st))
    r = certify(st)
    print("certify ->", r)
    nt = St(rank, m, r[2]); print("new state", nt.opt, "valid", nt.valid, "F", nt.F, "completable", completable_bf(nt))
    print("certify(new) ->", certify(nt))
    # generalisations: k free agents o_0..o_{k-1}; o_i holds its c and needs the goods of the two roots of a binary
    # tree T_i of depth d (internal agents hold their c and need their children's goods; leaves hold their tops).
    # The leaves of T_{i+1} are exposed for o_i: their (b, c) = (o_i's good, a junk good). With shared=True the junk
    # goods come from one pool of k goods, so colours repeat across the o's and the walk must avoid them.
    for k, d, shared in ((2, 1, False), (2, 1, True), (3, 2, False), (3, 2, True), (4, 2, True), (5, 3, True)):
        rank, opt, m = gen_tree(k, d, shared)
        st = St(rank, m, opt)
        seq = []
        while True:
            r = certify(st)
            if r[0] == 'absorber':
                break
            seq.append(r[1]); st = St(rank, m, r[2])
        check_absorber(st, r[1], r[2])
        st0 = St(rank, m, opt)
        print(f"tree family k={k} d={d} shared={shared}: n={len(rank)} m={m} valid={st0.valid} "
              f"completable={completable_bf(st0) is not None}; moves {seq}; then absorber {r[1]}, H={r[2]}; "
              f"{cycle_profile(st0)}")


def cycle_profile(st):
    """cycles of the exchange digraph A of st: fewest exposure arcs on a rainbow cycle, number of rainbow and of
    non-rainbow cycles, and whether a pair chain exists"""
    import networkx as nx
    from lemma1 import exchange_digraph
    G, col = exchange_digraph(st); best = None; nr = bad = 0
    for cyc in nx.simple_cycles(G):
        cs = [col[(cyc[t], cyc[(t + 1) % len(cyc)])] for t in range(len(cyc)) if (cyc[t], cyc[(t + 1) % len(cyc)]) in col]
        if len(cs) == len(set(cs)):
            nr += 1; best = len(cs) if best is None else min(best, len(cs))
        else:
            bad += 1
    chain = any(st.opt[x] == 1 and st.rank[x][1] in st.J and st.rank[x][2] in st.J for x in range(st.n))
    return f"A: {nr} rainbow cycles (fewest exposure arcs {best}), {bad} non-rainbow cycles, pair chain {chain}"


def gen_tree(k, d, shared):
    rank = [None] * k; opt = [3] * k; g = [0]
    def new():
        g[0] += 1; return g[0] - 1
    own = [new() for _ in range(k)]
    pool = [new() for _ in range(k)] if shared else None
    leaves = {i: [] for i in range(k)}
    def build(i, depth):
        """returns the good held by the root of a subtree; appends agents"""
        idx = len(rank); rank.append(None); opt.append(None)
        if depth == 0:
            top = new(); leaves[i].append(idx); opt[idx] = 1; rank[idx] = (top,); return top
        l, r = build(i, depth - 1), build(i, depth - 1)
        c = new(); rank[idx] = (l, r, c); opt[idx] = 3; return c
    for i in range(k):
        x, y = build(i, d - 1), build(i, d - 1)
        rank[i] = (x, y, own[i])
    for i in range(k):
        o = (i - 1) % k                      # leaves of T_i are exposed for o_{i-1}
        for s, idx in enumerate(leaves[i]):
            h = pool[s % k] if shared else new()
            top = rank[idx][0]
            rank[idx] = (top, own[o], h) if s % 2 == 0 else (top, h, own[o])
    return rank, tuple(opt), g[0]


def main():
    mode = sys.argv[1]
    if mode == 'example':
        example(); return
    S = collections.Counter(); first = {}; t0 = time.time(); tot = 0
    if mode == 'small':
        from test_k3s import gen_small
        n, m = int(sys.argv[2]), int(sys.argv[3])
        src = ((r, m) for _, _, r in gen_small(n, m)); title = f"every profile n={n} m={m}"
    elif mode == 'random':
        K, seed, N = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]); rng = random.Random(seed)
        def gen():
            for _ in range(K):
                n = rng.randint(2, N); m = rng.randint(n + 1, 2 * n + 3)
                yield [tuple(rng.sample(range(m), 3)) for _ in range(n)], m
        src = gen(); title = f"random K={K} seed={seed} n<={N}"
    elif mode == 'cores':
        from lbx import core_profiles
        N, SAMP, lo = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        src = ((list(r), m) for _, m, r in core_profiles(N, sample=SAMP, minn=lo)); title = f"cores n in [{lo},{N}], {SAMP} per core"
    for rank, m in src:
        run_profile(rank, m, S, first); tot += 1
    print(f"{title}: {tot} profiles, {time.time() - t0:.0f}s; " + ", ".join(f"{k}={v}" for k, v in sorted(S.items())), flush=True)
    for k, v in first.items():
        print(f"  first {k}: {v}")


if __name__ == '__main__':
    main()
