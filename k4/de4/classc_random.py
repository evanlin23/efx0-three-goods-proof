#!/usr/bin/env python3
"""Class C (NOTES.md, section 4.3) on random instances: three-good agents and four-good agents with b + d <= a and
a + d <= b + c (types 7 and 9). For every valid state, classc.check_improvement runs the moves of the attempted proof
(chains, finishing by free agents, Q-holders or pair holders, the ring with greedy distinct leftover goods), and
classc.check_every_form tests E (every score-Pareto-maximal valid state finishable). Random instances almost never
contain the label collision of collision.py, which refutes both.

    python3 classc_random.py [instances] [seed]
"""
import random
import sys

from model import random_core_values, describe
import classc


def vals4(rng):
    while True:
        a, b, c, d = random_core_values(rng, 4, hi=rng.choice([10, 20, 40]))
        if b + d <= a and a + d <= b + c:
            return (a, b, c, d)


def main(N, seed):
    rng = random.Random(seed)
    tot, fails, stuck, m_agents = {}, [], 0, 0
    for t in range(N):
        n = rng.choice([2, 3, 4, 4, 5])
        m = rng.randint(4, 3 + n)
        p4 = rng.choice([0.3, 0.7, 1.0])
        v = []
        for _ in range(n):
            vals = vals4(rng) if rng.random() < p4 else random_core_values(rng, 3, hi=rng.choice([10, 20, 40]))
            v.append(dict(zip(rng.sample(range(m), len(vals)), vals)))
        m_agents += sum(1 for vi in v if classc.Agent(vi).kind == 'M')
        try:
            c = classc.check_improvement(v, m)
            for k in c:
                tot[k] = tot.get(k, 0) + c[k]
        except AssertionError as e:
            fails.append((n, m, describe(v), str(e)))
        k, bad = classc.check_every_form(v, m)
        stuck += len(bad)
    print('%d instances (%d agents of type 7 in all): %s' % (N, m_agents, tot))
    print('states where the attempted proof fails: %d; stuck score-Pareto-maximal states: %d' % (len(fails), stuck))
    for f in fails[:5]:
        print('   ', f)


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 6000, int(sys.argv[2]) if len(sys.argv) > 2 else 1)
