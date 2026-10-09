"""Which potentials Phi have only completable maximisers? (completable = the brief's definition, K3S HitSet with one
slot per free agent; exchange.completable_bf). Evidence only; one process.

  python3 phi_survey.py small N M | random K SEED MAXN | cores MAXN SAMPLE MINN

Phi (larger is better):
  sumU     sum u, u = nothing 0, c 1, b 2, a 3, pair 4           (Pareto-monotone: covered by Theorem PO)
  sumV     sum of values 4, 3, 2, pair 5                          (Pareto-monotone: covered)
  leximin  sorted utility vector                                   (Pareto-monotone: covered)
  minNA_sumU  (-|NA|, sum u)                                       (covered: every move has NA' <= NA)
  minNA    -|NA| alone                                             (NOT Pareto-monotone; not covered)
  maxU     number of pair holders alone                            (not covered)
  maxU_sumU  (|U|, sum u)                                          (covered: every move keeps U and adds to it)
  maxF     number of free agents                                   (not covered)
For each Phi: number of profiles where SOME maximiser is not completable, and the first one.
"""
import sys, os, random, collections, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'explore', 'matching'))
from exchange import St, completable_bf, UT  # noqa: E402
from exp_fast import valid_states  # noqa: E402

VT = (0, 4, 3, 2, 5)
PHI = {
    'sumU': lambda st: sum(UT[o] for o in st.opt),
    'sumV': lambda st: sum(VT[o] for o in st.opt),
    'leximin': lambda st: tuple(sorted(UT[o] for o in st.opt)),
    'minNA_sumU': lambda st: (-len(st.NA), sum(UT[o] for o in st.opt)),
    'minNA': lambda st: -len(st.NA),
    'maxU': lambda st: len(st.U),
    'maxU_sumU': lambda st: (len(st.U), sum(UT[o] for o in st.opt)),
    'maxF': lambda st: len(st.F),
}


def run(src, title):
    bad = collections.Counter(); first = {}; tot = 0; t0 = time.time()
    for rank, m in src:
        tot += 1
        sts = [St(rank, m, s[0]) for s in valid_states(rank, m)]
        comp = {}
        for name, f in PHI.items():
            vals = [f(s) for s in sts]; best = max(vals)
            for s, v in zip(sts, vals):
                if v != best:
                    continue
                if s.opt not in comp:
                    comp[s.opt] = completable_bf(s) is not None
                if not comp[s.opt]:
                    bad[name] += 1
                    first.setdefault(name, (rank, m, s.opt))
                    break
    print(f"{title}: {tot} profiles, {time.time() - t0:.0f}s; profiles with a non-completable maximiser: "
          + ", ".join(f"{k}={bad[k]}" for k in PHI), flush=True)
    for k in PHI:
        if k in first:
            print(f"  first {k}: {first[k]}")


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'small':
        from test_k3s import gen_small
        n, m = int(sys.argv[2]), int(sys.argv[3])
        run(((r, m) for _, _, r in gen_small(n, m)), f"every profile n={n} m={m}")
    elif mode == 'cores':
        from lbx import core_profiles
        N, SAMP, lo = map(int, sys.argv[2:5])
        run(((list(r), m) for _, m, r in core_profiles(N, sample=SAMP, minn=lo)), f"cores n in [{lo},{N}], {SAMP} per core")
    else:
        K, seed, N = map(int, sys.argv[2:5]); rng = random.Random(seed)
        def gen():
            for _ in range(K):
                n = rng.randint(2, N); m = rng.randint(n + 1, 2 * n + 3)
                yield [tuple(rng.sample(range(m), 3)) for _ in range(n)], m
        run(gen(), f"random K={K} seed={seed} n<={N}")
