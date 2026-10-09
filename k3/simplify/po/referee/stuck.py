import sys, random, itertools
sys.path.insert(0, '.')
import ref
rank = [(0,4,6),(1,4,7),(2,5,8),(3,5,9),(2,3,4),(0,1,5)]
I = ref.Inst(rank, 10)
H = [0,0,0,0,2,2]
S = ref.St(I, H)
print('valid', S.valid, 'F', S.F, 'NA', S.NA, 'J', S.J, 'completable_bf', S.completable_bf())
outs = set()
for seed in range(200):
    rng = random.Random(seed)
    r = ref.improve(S, rng)
    assert r[0] == 'move'
    S2 = r[1]
    outs.add(S2.H)
    assert S2.completable_bf()
print('distinct dominating states found by Lemma 5 over 200 seeds:', sorted(outs))
# full algorithm from SD, all orders
for order in itertools.permutations(range(6)):
    for seed in range(5):
        ref.algorithm(rank, 10, random.Random(seed), list(order))
print('algorithm from SD: all 720 orders x 5 seeds OK', dict(ref.STATS))
