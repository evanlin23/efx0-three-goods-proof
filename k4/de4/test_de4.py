#!/usr/bin/env python3
"""Tests of the small-d extension of DE (NOTES.md, Theorem 1). Exit status 0 iff every check passes.

  [1] DE (de4.py) on random admissible instances, peeling included: agents with zero to four relevant goods (four-good
      agents of type (S)), ties among three-good agents, goods nobody values. Every output is checked against the raw
      definition of EFX0, completeness, the shape (all bundles but one have at most two goods), at most n peels and at
      most sum(|R_i| + 1) <= 5n trades.
  [2] Every valid state of random core instances with three-good and (S) agents, through the second implementation
      classc.py: a chain applies, or every agent holds its pair, or an owner can finish (each completion checked raw),
      or the ring of the Improvement Lemma gives a valid state that dominates in scores; and every score-Pareto-maximal
      valid state can be finished by a free agent or a pair holder.
  [3] The two implementations agree: de4.py's output is reproduced by a replay of its trades in classc.py's states.
  [4] Each condition of (S) is needed by DE as it stands: dropping any one of them, DE (run unchanged, with the
      fifth rung) returns an allocation that is not EFX0 on some instance (random instances with one or more
      four-good agents violating only that condition); the smallest one found is printed.

    python3 test_de4.py [scale]        (scale 1: about two minutes)
"""
import random
import sys

from model import is_efx0, describe, val, envious
from de4 import Run, small_d, ranking
import classc

FAILS = []


def check(cond, msg):
    print(('  ok    ' if cond else '  FAIL  ') + msg, flush=True)
    if not cond:
        FAILS.append(msg)


def small_d_values(rng, hi):
    while True:
        a, b, c = sorted(rng.sample(range(1, hi), 3), reverse=True)
        top = min(a - b, b - c, b + c - a)
        if top >= 1:
            return [a, b, c, rng.randint(1, top)]


def random_agent(rng, m, hi=30):
    k = min(m, rng.choice([0, 1, 2, 3, 3, 4, 4, 4]))
    if k == 4:
        vals = small_d_values(rng, hi)
    else:
        vals = [rng.randint(1, rng.choice([3, 10, hi])) for _ in range(k)]
    goods = rng.sample(range(m), k)
    vi = dict(zip(goods, vals))
    assert small_d([vi[g] for g in ranking(vi, list(vi))]) if k == 4 else True
    return vi


def part1(scale):
    print('[1] DE on random admissible instances')
    rng = random.Random(2026)
    runs = peels = trades = with4 = cored = 0
    maxtr = 0
    for t in range(4000 * scale):
        n = rng.randint(1, 7)
        m = rng.randint(1, 11)
        v = [random_agent(rng, m) for _ in range(n)]
        R = Run(n, m, v)
        X = R.run()
        runs += 1
        with4 += any(len(vi) == 4 for vi in v)
        cored += bool(R.trades) or hasattr(R, 'Y')
        goods = sorted(g for B in X for g in B)
        if goods != list(range(m)) or not is_efx0(v, X):
            check(False, 'run %d: incomplete or not EFX0: %s' % (t, describe(v)))
            return
        if sum(1 for B in X if len(B) > 2) > 1:
            check(False, 'run %d: two bundles of more than two goods' % t)
            return
        bound = sum(len(vi) + 1 for vi in v)
        if R.peels > n or R.trades > min(bound, 5 * n):
            check(False, 'run %d: too many peels or trades' % t)
            return
        peels += R.peels
        trades += R.trades
        maxtr = max(maxtr, R.trades)
    check(True, '%d runs (%d with a four-good agent, %d reaching the core), all complete, EFX0, of the shape; %d '
          'peels, %d trades, at most %d in one run' % (runs, with4, cored, peels, trades, maxtr))
    rng = random.Random(7)
    core_runs = core4 = 0
    for t in range(3000 * scale):                               # core instances: no peeling, many trades
        n = rng.randint(2, 8)
        m = rng.randint(max(n, 4), 2 * n + 3)
        v = []
        for _ in range(n):
            if rng.random() < 0.6:
                vals = small_d_values(rng, 40)
            else:
                while True:
                    vals = sorted(rng.sample(range(1, 40), 3), reverse=True)
                    if vals[0] < vals[1] + vals[2]:
                        break
            v.append(dict(zip(rng.sample(range(m), len(vals)), vals)))
        R = Run(n, m, v)
        X = R.run()
        if sorted(g for B in X for g in B) != list(range(m)) or not is_efx0(v, X) or \
                sum(1 for B in X if len(B) > 2) > 1 or R.trades > 5 * n:
            check(False, 'core run %d fails: %s' % (t, describe(v)))
            return
        core_runs += 1
        core4 += sum(1 for vi in v if len(vi) == 4)
        maxtr = max(maxtr, R.trades)
    check(True, '%d core runs (%d four-good agents in all), all complete, EFX0, of the shape, within 5n trades' %
          (core_runs, core4))


def part2(scale):
    print('[2] every valid state of random core instances (classc.py)')
    rng = random.Random(11)
    tot = {}
    stuck = 0
    for t in range(700 * scale):
        n = rng.choice([2, 3, 3, 4, 4, 5])
        m = rng.randint(4, 3 + n)
        v = []
        for _ in range(n):
            if rng.random() < 0.7:
                vals = small_d_values(rng, 40)
            else:
                while True:
                    vals = sorted(rng.sample(range(1, 40), 3), reverse=True)
                    if vals[0] < vals[1] + vals[2]:
                        break
            v.append(dict(zip(rng.sample(range(m), len(vals)), vals)))
        try:
            c = classc.check_improvement(v, m)
            k, bad = classc.check_every_form(v, m)
        except AssertionError as e:
            check(False, 'instance %d: %s; %s' % (t, e, describe(v)))
            return
        for key in c:
            tot[key] = tot.get(key, 0) + c[key]
        stuck += len(bad)
    check(stuck == 0 and 'ring' in tot,
          '%d valid states: %d chains, %d with every agent holding its pair, %d finishable, %d rings, all valid and '
          'dominating; every score-Pareto-maximal state finishable (%d stuck)' %
          (tot['states'], tot['chain'], tot['allpairs'], tot['finish'], tot['ring'], stuck))


def part3(scale):
    print('[3] the two implementations agree')
    rng = random.Random(5)
    agree = 0
    for t in range(1500 * scale):
        n = rng.randint(2, 6)
        m = rng.randint(max(n, 4), 2 * n + 2)
        v = []
        for _ in range(n):
            vals = small_d_values(rng, 40) if rng.random() < 0.6 else None
            if vals is None:
                while True:
                    vals = sorted(rng.sample(range(1, 40), 3), reverse=True)
                    if vals[0] < vals[1] + vals[2]:
                        break
            v.append(dict(zip(rng.sample(range(m), len(vals)), vals)))
        R = Run(n, m, v)
        R.run()
        if not hasattr(R, 'Y'):
            continue
        ags = [classc.Agent(vi) for vi in v]
        # the final state of de4.py is a valid classc state in which classc finds a finishing owner
        st = classc.State(ags, m, [R.Y[i] for i in range(n)])
        ok = st.valid and (all(i in st.U for i in range(n)) or any(st.can_finish(o) is not None for o in st.F))
        sc_de = [R.score(i) for i in range(n)]
        sc_cc = list(st.scores())
        if not ok or sc_de != sc_cc:
            check(False, 'disagreement on %s' % describe(v))
            return
        agree += 1
    check(True, '%d final states of de4.py are valid in classc.py, with the same scores, and finishable there' % agree)


def part4(scale):
    print('[4] each condition of (S) is needed by DE as it stands')
    names = ['b + d <= a', 'c + d <= b', 'a + d <= b + c']
    for k, name in enumerate(names):
        rng = random.Random(100 + k)
        best = None
        for t in range(8000 * scale):
            n = rng.choice([2, 3, 3, 4, 5])
            m = rng.randint(max(n + 1, 4), 2 * n + 2)
            v = []
            for i in range(n):
                if i == 0 or rng.random() < 0.5:
                    while True:
                        a, b, c, d = sorted(rng.sample(range(1, 30), 4), reverse=True)
                        conds = [b + d <= a, c + d <= b, a + d <= b + c]
                        if a < b + c and not conds[k] and all(conds[j] for j in range(3) if j != k):
                            break
                    vals = (a, b, c, d)
                else:
                    while True:
                        vals = sorted(rng.sample(range(1, 30), 3), reverse=True)
                        if vals[0] < vals[1] + vals[2]:
                            break
                v.append(dict(zip(rng.sample(range(m), len(vals)), vals)))
            R = Run(n, m, v, check=False)
            try:
                X = R.run()
            except AssertionError:
                continue
            if not is_efx0(v, X) and (best is None or (n, m) < best[:2]):
                best = (n, m, v, X)
        if best is None:
            check(False, 'dropping %s: no failure of DE found' % name)
        else:
            n, m, v, X = best
            check(True, 'dropping %s: DE returns a non-EFX0 allocation, smallest found n = %d, m = %d: %s; X = %s; '
                  'envious pairs %s' % (name, n, m, describe(v), [sorted(B) for B in X], envious(v, X)))


if __name__ == '__main__':
    scale = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    part1(scale)
    part2(scale)
    part3(scale)
    part4(scale)
    print('\n%s' % ('ALL CHECKS PASSED' if not FAILS else '%d FAILURES' % len(FAILS)))
    sys.exit(1 if FAILS else 0)
