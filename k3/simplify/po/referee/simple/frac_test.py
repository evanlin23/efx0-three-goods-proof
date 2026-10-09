"""DE on exact rational (non-integer) values: the paper says only comparisons matter."""
import sys, random
from fractions import Fraction
sys.path.insert(0, '.')
from de import de, check_output
from random_de import gen
rng = random.Random(99)
ok = 0
for t in range(10000):
    kind = rng.choice(['general', 'core', 'mid', 'planted'])
    v = gen(rng, kind)
    v = [[Fraction(x * rng.randint(1, 7), rng.randint(1, 7)) if x else Fraction(0) for x in row] for row in v]
    st = {}
    X = de(v, checks=True, deep=(t % 10 == 0), stats=st)
    check_output(v, X, st)
    ok += 1
print('fraction-valued random instances ok:', ok)
