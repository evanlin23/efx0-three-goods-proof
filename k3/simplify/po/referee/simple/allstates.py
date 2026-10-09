"""Test the lemmas of Sections 3-5 on EVERY state of small core profiles,
not only the states DE reaches.

For each core profile and each state Y (5^n of them):
  - Lemma 'stay' (on all pairs Y, Y' when n <= 3, else sampled)
  - for valid Y:
     * Lemma test (a),(b),(c) (when NC holds) against the brute-force Definition 3
     * Theorem 'soundness' for every free agent that can finish, every allowed H (capped),
       two assignments of H; and the all-pairs case with every o
     * Lemma chain for every x with Y_x={a_x}, b_x,c_x in J
     * Improvement Lemma (when hypotheses hold): ring is a ring, trade gives valid improved state
  - Corollary 'Pareto-optimal states'
"""
import sys
import random
from itertools import product, combinations, permutations
from collections import Counter
sys.path.insert(0, '.')
from de import Core, check, CheckError, check_core_alloc


def options(C, i):
    a, b, c = C.rank[i]
    return [frozenset(), frozenset([a]), frozenset([b]), frozenset([c]), C.pairs[i]]


def all_states(C):
    for choice in product(*[options(C, i) for i in C.A]):
        Y = dict(zip(C.A, choice))
        if C.is_state(Y):
            yield Y


def scores(C, Y):
    return tuple(C.score(i, Y[i]) for i in C.A)


def test_profile(v, stats, stay_all=False, rng=None):
    n = len(v)
    m = len(v[0])
    C = Core(v, range(n), range(m))
    states = list(all_states(C))
    valid = [Y for Y in states if C.valid(Y)]
    stats['states'] += len(states)
    stats['valid'] += len(valid)
    # Lemma stay
    pairs_to_test = []
    if stay_all:
        pairs_to_test = [(Y, Z) for Y in valid for Z in states]
    else:
        for Y in valid:
            for Z in rng.sample(states, min(20, len(states))):
                pairs_to_test.append((Y, Z))
    for Y, Z in pairs_to_test:
        sY, sZ = scores(C, Y), scores(C, Z)
        if all(a <= b for a, b in zip(sY, sZ)):
            wanted = C.wanted_goods(Y)
            hd = C.holder(Z)
            if all(g in hd and Z[hd[g]] == frozenset([g]) for g in wanted):
                stats['stay_pairs'] += 1
                check(C.valid(Z), "Lemma stay fails")
    sc_valid = [scores(C, Y) for Y in valid]
    for Y, sY in zip(valid, sc_valid):
        J = C.J(Y)
        Uset = C.U(Y)
        F = C.free(Y)
        allpairs = len(Uset) == len(C.A)
        nc = C.nc(Y, J)
        finishers = []
        for o in F:
            allowed = C.can_finish_sets(Y, o, F, J)
            if nc:
                bl = C.blockers(Y, o, J)
                if not Y[o]:
                    check(not bl, "Lemma test (a)")
                Ho, _ = C.H_o(Y, o, J)  # asserts (b)
                check(bool(allowed) == (len(Ho) <= len(F) - 1), "Lemma test (c)")
                if allowed:
                    check(frozenset(Ho) in allowed, "Lemma test (c): H_o")
                if not Y[o]:
                    check(bool(allowed), "Lemma test (c): free agent holding nothing cannot finish")
            if allowed:
                finishers.append(o)
                for H in allowed[:4]:
                    others = [f for f in F if f != o]
                    for order in (others, others[::-1]):
                        Xc = C.completion(Y, o, H, F, order)
                        check_core_alloc(C, Xc, o)
                        stats['completions'] += 1
        if allpairs:
            for o in C.A:
                Xc = C.completion(Y, o, frozenset(), [])
                check_core_alloc(C, Xc, o)
                stats['completions'] += 1
        # chains for every x
        for x in C.A:
            if Y[x] == C.tops[x] and C.rank[x][1] in J and C.rank[x][2] in J:
                kind, seq, Z = C.chain(Y, x)
                if kind == 'ring':
                    C.check_ring(Y, seq)
                    Z = C.trade_ring(Y, seq)
                    raised = set(seq)
                    stats['chain_rings'] += 1
                else:
                    raised = set(seq)
                    stats['chains'] += 1
                check(C.is_state(Z) and C.valid(Z), "chain: result invalid")
                for i in C.A:
                    s0, s1 = C.score(i, Y[i]), C.score(i, Z[i])
                    check(s1 > s0 if i in raised else s1 == s0, "chain: scores")
        # Improvement lemma
        if not allpairs and not finishers:
            stats['stuck'] += 1
            if nc:
                if not short_ring_exists(C, Y, F, J):
                    stats['no_short_move'] += 1
                    n_, m_ = len(C.A), len(C.G)
                    check(len(F) >= 2 and n_ >= 6 and m_ >= 8, "Prop short: bounds")
                    if len(F) >= 3:
                        check(n_ >= 9 and m_ >= 12, "Prop short: bounds k>=3")
                ring, q, xo = C.improvement_ring(Y)
                npair = C.check_ring(Y, ring)
                stats['ring_pairs'][npair] += 1
                Z = C.trade_ring(Y, ring)
                check(C.is_state(Z) and C.valid(Z), "improve: result invalid")
                for i in C.A:
                    s0, s1 = C.score(i, Y[i]), C.score(i, Z[i])
                    check(s1 > s0 if i in ring else s1 == s0, "improve: scores")
            else:
                stats['stuck_chain'] += 1
    # Corollary po
    for Y, sY in zip(valid, sc_valid):
        dominated = any(all(a >= b for a, b in zip(s2, sY)) and s2 != sY for s2 in sc_valid)
        if not dominated:
            stats['po'] += 1
            J = C.J(Y)
            F = C.free(Y)
            ok = len(C.U(Y)) == len(C.A) or any(C.can_finish_sets(Y, o, F, J, limit=1) for o in F)
            check(ok, "Corollary po fails")


def short_ring_exists(C, Y, F, J):
    Uset = C.U(Y)
    Fs = set(F)
    nodes = [i for i in C.A if i not in Uset and len(Y[i]) == 1]
    want = {i: [] for i in nodes}
    for i in nodes:
        if i in Fs:
            continue
        (y,) = Y[i]
        want[i] = [w for w in C.wanters(Y, y) if w in want]
    # ring of want arrows: a cycle in the want graph (among non-free agents)
    color = {}
    def has_cycle(u):
        color[u] = 1
        for w in want[u]:
            if color.get(w) == 1:
                return True
            if w not in color and has_cycle(w):
                return True
        color[u] = 2
        return False
    for u in nodes:
        if u not in color and has_cycle(u):
            return True
    # one pair arrow o -> x, then a want path x -> ... -> o
    for o in F:
        if len(Y[o]) != 1:
            continue
        for x in C.blockers(Y, o, J):
            if x not in want:
                continue
            seen = {x}
            stack = [x]
            while stack:
                u = stack.pop()
                for w in want[u]:
                    if w == o:
                        return True
                    if w not in seen and w not in Fs:
                        seen.add(w)
                        stack.append(w)
    return False


def random_core(n, m, rng, tie=True):
    v = []
    for i in range(n):
        S = rng.sample(range(m), 3)
        while True:
            if tie and rng.random() < 0.3:
                vals = [rng.choice([1, 2, 3]) for _ in range(3)]
            else:
                vals = [rng.randint(1, 20) for _ in range(3)]
            s = sorted(vals, reverse=True)
            if s[0] < s[1] + s[2]:
                break
        row = [0] * m
        for g, x in zip(S, vals):
            row[g] = x
        v.append(row)
    return v


if __name__ == '__main__':
    mode = sys.argv[1]
    stats = Counter()
    stats['ring_pairs'] = Counter()
    rng = random.Random(12345)
    if mode == 'exh2':
        # every n=2 core profile with m<=6 and values (4,3,2) in all orders
        for m in range(3, 7):
            rows = []
            for S in combinations(range(m), 3):
                for p in permutations((4, 3, 2)):
                    row = [0] * m
                    for g, x in zip(S, p):
                        row[g] = x
                    rows.append(row)
            for r1 in rows:
                for r2 in rows:
                    test_profile([list(r1), list(r2)], stats, stay_all=True)
                    stats['profiles'] += 1
    elif mode == 'exh3':
        m = int(sys.argv[2])
        rows = []
        for S in combinations(range(m), 3):
            for p in permutations((4, 3, 2)):
                row = [0] * m
                for g, x in zip(S, p):
                    row[g] = x
                rows.append(row)
        for r1 in rows:
            for r2 in rows:
                for r3 in rows:
                    test_profile([list(r1), list(r2), list(r3)], stats, stay_all=False, rng=rng)
                    stats['profiles'] += 1
    elif mode == 'paper':
        # the two instances of Section 7 / Appendix A, all their states
        def mk(ranks, m):
            v = []
            for r in ranks:
                row = [0] * m
                for g, x in zip(r, (4, 3, 2)):
                    row[g] = x
                v.append(row)
            return v
        test_profile(mk([(0, 4, 6), (1, 4, 7), (2, 5, 8), (3, 5, 9), (2, 3, 4), (0, 1, 5)], 10), stats, rng=rng)
        test_profile(mk([(4, 5, 0), (6, 7, 1), (4, 1, 2), (5, 3, 1), (6, 0, 2), (7, 3, 0)], 8), stats, rng=rng)
        stats['profiles'] += 2
    elif mode == 'rand':
        N = int(sys.argv[2])
        for t in range(N):
            n = rng.choice([3, 4, 4, 5, 5, 5])
            m = rng.randint(3, n + 5)
            v = random_core(n, m, rng)
            test_profile(v, stats, stay_all=(n <= 3), rng=rng)
            stats['profiles'] += 1
    rp = stats.pop('ring_pairs')
    print(mode, sys.argv[2:] if len(sys.argv) > 2 else '', dict(stats), 'pair arrows in improvement rings', dict(sorted(rp.items())))
