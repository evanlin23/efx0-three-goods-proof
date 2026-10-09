"""DE on the tree instances of Appendix A, under the draft-reproducing agent order
and under random agent/good orders: count trades."""
import sys, io, contextlib, random
sys.path.insert(0, '.')
with contextlib.redirect_stdout(io.StringIO()):
    import appendix
from de import de, check_output, Core
rng = random.Random(5)
for k in (2, 3, 4):
    for d in (1, 2, 3):
        v, Y, roots = appendix.tree_state(k, d)
        n = len(v); m = len(v[0])
        C = Core(v, range(n), range(m))
        held = {i: next(iter(Y[i])) for i in range(n)}
        holder = {g: i for i, g in held.items()}
        parent = {}
        for i in range(n):
            a, b, c = C.rank[i]
            if held[i] == c:
                parent[holder[a]] = i; parent[holder[b]] = i
        def depth(i):
            dd = 0
            while i in parent:
                i = parent[i]; dd += 1
            return dd
        order = sorted(range(n), key=lambda i: -depth(i))
        v2 = [v[i] for i in order]
        st = {}
        X = de(v2, checks=True, stats=st); check_output(v2, X, st)
        mx = 0
        for t in range(200 if n <= 30 else 30):
            perm = list(range(n)); rng.shuffle(perm)
            gp = list(range(m)); rng.shuffle(gp)
            v3 = [[v[i][gp[g]] for g in range(m)] for i in perm]
            s3 = {}
            X3 = de(v3, checks=True, stats=s3); check_output(v3, X3, s3)
            mx = max(mx, s3['trades'])
        print(f'k={k} d={d} n={n} m={m}: draft-order trades={st["trades"]} (ring pair arrows {st.get("ring_pairs")}); max trades over random orders={mx}', flush=True)
