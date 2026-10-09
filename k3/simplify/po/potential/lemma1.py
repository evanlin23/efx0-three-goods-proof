"""Lemma 1 (NOTES.md §2), tested on EVERY move, not only those the proof picks. Evidence only; one process.

For every valid state of every profile in the set: build the exchange digraph A (D-arcs and coloured X-arcs),
enumerate all its simple cycles (networkx) and all pair chains (M2: a top-holder with b, c junk and any D-path from
it to a free agent). Every rainbow cycle and every pair chain must give a valid state with every touched agent
strictly better off. Also counted: non-completable states whose only moves are rainbow cycles with >= 2 X-arcs (no D-cycle,
no pair chain, no cycle with one X-arc: the K3S rotation and the moves of explore/matching do not apply); and cycles that are NOT rainbow (two X-heads with the same junk good); the exchange
is then not even defined (one junk good would go to two agents), which is why the proof needs rainbow cycles.

  python3 lemma1.py small N M | random K SEED MAXN
"""
import sys, os, random, collections, time
import networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'explore', 'matching'))
from exchange import St, apply_arcs, check_move, completable_bf  # noqa: E402
from exp_fast import valid_states  # noqa: E402


def exchange_digraph(st):
    """A: vertices = non-U agents; D-arcs j -> k (k needs j's good), X-arcs o -> x (o free holding y_o, x holds its
    top, {b_x, c_x} = {y_o, h_x} with h_x junk), colour h_x"""
    G = nx.DiGraph(); col = {}
    for j in range(st.n):
        if st.opt[j] == 4:
            continue
        G.add_node(j)
        for k in st.needers(j):
            G.add_edge(j, k)
    for o in st.F:
        if st.opt[o] == 0:
            continue
        y = st.Y[o][0]
        for x in range(st.n):
            if x == o or st.opt[x] != 1:
                continue
            bc = set(st.rank[x][1:])
            if y in bc and len(bc & st.J) == 1:
                assert not G.has_edge(o, x)
                G.add_edge(o, x); col[(o, x)] = next(iter(bc & st.J))
    return G, col


def d_paths(st, x):
    """all D-paths from x ending at a free agent"""
    out = []
    def rec(path):
        if path[-1] in st.F:
            out.append(list(path))
        for k in st.needers(path[-1]):
            if k not in path:
                rec(path + [k])
    rec([x])
    return out


def run(src, title):
    S = collections.Counter(); t0 = time.time(); tot = 0
    for rank, m in src:
        tot += 1
        for opt, _, _ in valid_states(rank, m):
            st = St(rank, m, opt); S['states'] += 1
            G, col = exchange_digraph(st); small_move = False
            for cyc in nx.simple_cycles(G):
                arcs = [(cyc[t], cyc[(t + 1) % len(cyc)]) for t in range(len(cyc))]
                cs = [col[a] for a in arcs if a in col]
                if len(cs) != len(set(cs)):
                    S['cycle_not_rainbow'] += 1; continue
                heads = {v for (u, v) in arcs if (u, v) in col}
                check_move(st, apply_arcs(st, arcs, heads), set(cyc))
                S['rainbow_cycle_ok_X%d' % len(cs)] += 1
                small_move |= len(cs) <= 1
            for x in range(st.n):
                if st.opt[x] == 1 and st.rank[x][1] in st.J and st.rank[x][2] in st.J:
                    for path in d_paths(st, x):
                        arcs = [(path[t], path[t + 1]) for t in range(len(path) - 1)]
                        new = list(apply_arcs(st, arcs, set())); new[x] = 4
                        check_move(st, tuple(new), set(path)); S['pair_chain_ok'] += 1; small_move = True
            if not small_move and completable_bf(st) is None:
                S['needs_two_X_arcs'] += 1
                if S['needs_two_X_arcs'] == 1:
                    print('  first state needing a rainbow cycle with >= 2 X-arcs:', rank, m, opt, flush=True)
    print(f"{title}: {tot} profiles, {time.time() - t0:.0f}s; " + ", ".join(f"{k}={v}" for k, v in sorted(S.items())), flush=True)


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'small':
        from test_k3s import gen_small
        n, m = int(sys.argv[2]), int(sys.argv[3])
        run(((r, m) for _, _, r in gen_small(n, m)), f"every profile n={n} m={m}")
    else:
        K, seed, N = map(int, sys.argv[2:5]); rng = random.Random(seed)
        def gen():
            for _ in range(K):
                n = rng.randint(2, N); m = rng.randint(n + 1, 2 * n + 3)
                yield [tuple(rng.sample(range(m), 3)) for _ in range(n)], m
        run(gen(), f"random K={K} seed={seed} n<={N}")
