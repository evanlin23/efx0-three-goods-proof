"""Pareto-optimal valid states: the Theorem's conclusion and two questions about strengthenings. Evidence only.
One process.

For every Pareto-optimal valid state (among all valid states of the profile) check:
  thm    completable (NOTES.md definition)                                             -- the Theorem
  free   completable with a FREE absorber, or every agent holds a pair                 -- what the proof gives
  P1/P2  the need digraph is acyclic; no top holder has b and c both junk               -- Lemma 1
  zero   (question Q1) some free agent has nobody exposed, or every agent holds a pair
and count the PO states where `zero` fails (then a HitSet is really needed).

  python3 po_check.py small N M
  python3 po_check.py random K SEED MAXN       (n <= MAXN <= 5: every valid state is enumerated)
"""
import sys, os, random, time, collections
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hall import St, all_states, gen_small, UT, needers


def d_acyclic(st):
    nonU = [i for i in range(st.n) if i not in st.U and st.opt[i] != 0]
    succ = {j: [w for w in needers(st, st.Y[j][0])] if st.Y[j][0] in st.NA else [] for j in nonU}
    color = {}

    def dfs(v):
        color[v] = 1
        for w in succ.get(v, []):
            if color.get(w) == 1:
                return False
            if w not in color and not dfs(w):
                return False
        color[v] = 2
        return True
    return all(dfs(v) for v in nonU if v not in color)


def p2(st):
    return not any(st.opt[x] == 1 and st.rank[x][1] in st.Jset and st.rank[x][2] in st.Jset for x in range(st.n))


def pareto(us):
    A = np.array(us, dtype=np.int8); keep = np.ones(len(A), bool); s = A.sum(1)
    for k in range(len(A)):
        if ((A >= A[k]).all(1) & (s > s[k])).any():
            keep[k] = False
    return np.nonzero(keep)[0]


def check(rank, m, c, first):
    S = [s for s in all_states(rank, m) if St(rank, m, s).valid]
    for k in pareto([[UT[o] for o in s] for s in S]):
        s = S[k]; st = St(rank, m, s); c['PO states'] += 1
        allU = len(st.U) == st.n
        if st.completable() is None:
            c['FAIL thm'] += 1; first.setdefault('thm', (rank, m, s))
        if not (allU or any(st.absorber_ok(o) is not None for o in st.F)):
            c['FAIL free'] += 1; first.setdefault('free', (rank, m, s))
        if not d_acyclic(st):
            c['FAIL P1'] += 1; first.setdefault('P1', (rank, m, s))
        if not p2(st):
            c['FAIL P2'] += 1; first.setdefault('P2', (rank, m, s))
        if not (allU or any(not st.exposed(o) for o in st.F)):
            c['zero fails (HitSet needed)'] += 1; first.setdefault('zero', (rank, m, s))


if __name__ == '__main__':
    t0 = time.time(); c = collections.Counter(); first = {}; P = 0
    if sys.argv[1] == 'small':
        n, m = int(sys.argv[2]), int(sys.argv[3])
        for rank in gen_small(n, m):
            check(rank, m, c, first); P += 1
        label = f"every profile n={n} m={m}"
    else:
        K, seed, N = map(int, sys.argv[2:5]); rng = random.Random(seed)
        for _ in range(K):
            n = rng.randint(2, N); m = rng.randint(max(3, n), 2 * n + 2)
            check([tuple(rng.sample(range(m), 3)) for _ in range(n)], m, c, first); P += 1
        label = f"{K} random profiles n<={N} (seed {seed})"
    print(f"{label}: {P} profiles; {dict(c)}; first {first}  [{time.time() - t0:.0f}s]", flush=True)
