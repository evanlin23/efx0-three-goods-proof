"""Hard states for the Improvement Lemma (Conjecture PO): valid base states that do not complete and admit no single
move (upgrade, trading cycle, rotation; `explore/matching/exp_local.py`), i.e. counterexamples to Conjecture ST.
For each, list the minimal Pareto-dominating valid states (fewest agents changed). Evidence only."""
import sys, os, random, collections, json
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'explore', 'matching'))
from common import Base, completes, states
from exp_local import one_moves
U = {0: 0, 3: 1, 2: 2, 1: 3, 4: 4}      # utility of an option: nothing < c < b < a < pair

def hard_states(rank, m):
    S = [s for s in states(rank) if Base(rank, m, s).valid]
    out = []
    for s in S:
        b = Base(rank, m, s)
        if completes(b) is not None or one_moves(rank, m, s): continue
        dom = [t for t in S if t != s and all(U[t[i]] >= U[s[i]] for i in range(len(s)))]
        k = min((sum(t[i] != s[i] for i in range(len(s))) for t in dom), default=None)
        mins = [t for t in dom if sum(t[i] != s[i] for i in range(len(s))) == k]
        out.append(dict(state=s, free=b.free, junk=b.J, NA=sorted(b.NA), dominated=bool(dom),
                        min_changed=k, min_dominators=mins[:4]))
    return out

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    n, K = int(sys.argv[1]), int(sys.argv[2])
    found = 0; tot = 0; notdom = 0
    for t in range(K):
        m = rng.randint(n + 1, 2 * n)
        rank = [tuple(rng.sample(range(m), 3)) for _ in range(n)]
        hs = hard_states(rank, m); tot += 1
        for h in hs:
            found += 1; notdom += not h['dominated']
            print(json.dumps(dict(n=n, m=m, rank=rank, **h)), flush=True)
    print(f"# n={n}: {tot} random profiles, {found} hard states (stuck, not completable), {notdom} NOT Pareto-dominated", flush=True)
