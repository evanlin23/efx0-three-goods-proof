#!/usr/bin/env python3
"""Independent check of the certificates in barrier_certs.json (written from the definitions in NOTES.md, section 3;
it imports nothing from this folder).

For every certificate (a strict type of four-good agent, a ladder for that type, an instance, a state) it checks:
  (1) every agent is a core agent with three goods (strictly balanced) or four goods of the stated type;
  (2) the state is a state of the ladders and is valid (every wanted good is the whole holding of some agent);
  (3) no valid state Pareto-dominates it in scores (all states enumerated);
  (4) no completion of DE's shape is EFX0, even the liberal ones: any owner o takes its holding and the leftover goods
      minus H, and the goods of H go to different agents other than o that hold at most one good (certificates marked
      "finishing": "absorber" instead claim this only for DE's own rule in the form of the Lean formalization: the
      owner is an agent whose holding contains no wanted good, and H goes to free agents);
  (5) the instance has an EFX0 allocation (backtracking search), so the failure is one of the method, not of EFX0.
Then it reports which (type, ladder) pairs of the two ladder families are refuted, lists those that are not, and, for
every certificate with at most 200,000 allocations, whether every EFX0 allocation gives some agent strictly less than
its value in the stuck state (then no method that only raises values can get from that state to an EFX0 allocation).

    python3 check_barrier.py
"""
import itertools
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PAIRS = ['ab', 'ac', 'ad', 'bc', 'bd', 'cd']
SMALL_D = 'a<bc a>bd a>cd b>cd ad<bc'


def total(vi, S):
    return sum(vi.get(g, 0) for g in S)


def envies(vi, own, B):
    """i (with values vi and own value) EFX0-envies bundle B"""
    if len(B) < 2:
        return False
    return max(total(vi, B) - vi.get(h, 0) for h in B) > own


def efx0(v, X):
    for i in range(len(X)):
        own = total(v[i], X[i])
        for j in range(len(X)):
            if j != i and envies(v[i], own, X[j]):
                return False
    return True


def goods_by_value(vi):
    return sorted((g for g in vi if vi[g] > 0), key=lambda g: (-vi[g], g))


def type_string(x):
    a, b, c, d = x
    cmp = [('a', a, 'bc', b + c), ('a', a, 'bd', b + d), ('a', a, 'cd', c + d), ('b', b, 'cd', c + d),
           ('ad', a + d, 'bc', b + c)]
    return ' '.join(p + ('<' if s < t else '>') + q for p, s, q, t in cmp)


def ladder(vi, spec):
    r = goods_by_value(vi)
    if len(r) == 3:
        a, b, c = r
        return [frozenset(), frozenset([c]), frozenset([b]), frozenset([a]), frozenset([b, c])]
    name = dict(zip('abcd', r))
    rungs = [frozenset([g]) for g in r] + [frozenset(name[ch] for ch in s) for s in spec]
    return [frozenset()] + sorted(rungs, key=lambda B: total(vi, B))


def wanted_goods(lads, st):
    w = set()
    for lad, s in zip(lads, st):
        for g in set().union(*lad):
            if g not in lad[s] and any(R == frozenset([g]) for R in lad[s + 1:]):
                w.add(g)
    return w


def valid(lads, st):
    hold = [lad[s] for lad, s in zip(lads, st)]
    alone = set(next(iter(B)) for B in hold if len(B) == 1)
    return wanted_goods(lads, st) <= alone


def states(lads):
    def rec(i, used):
        if i == len(lads):
            yield ()
            return
        for s, B in enumerate(lads[i]):
            if not (B & used):
                for rest in rec(i + 1, used | B):
                    yield (s,) + rest
    return list(rec(0, frozenset()))


def some_completion_efx0(v, m, hold, owners=None, receivers=None):
    """owners, receivers: None for liberal finishing (any owner; receivers hold at most one good)"""
    n = len(hold)
    J = sorted(set(range(m)) - set().union(*hold))
    if not J and owners is None:
        return efx0(v, hold)
    small = [i for i in range(n) if len(hold[i]) <= 1] if receivers is None else receivers
    for o in (range(n) if owners is None else owners):
        rec = [i for i in small if i != o]
        for k in range(len(rec) + 1):
            for H in itertools.combinations(J, k):
                for to in itertools.permutations(rec, k):
                    X = [set(B) for B in hold]
                    X[o] |= set(J) - set(H)
                    for h, i in zip(H, to):
                        X[i].add(h)
                    if efx0(v, X):
                        return True
    return False


def efx0_exists(v, n, m):
    X = [set() for _ in range(n)]

    def rec(g):
        if g == m:
            return efx0(v, X)
        for i in range(n):
            X[i].add(g)
            ok = rec(g + 1)
            X[i].discard(g)
            if ok:
                return True
        return False
    return rec(0)


def check_cert(c):
    n, m = c['n'], c['m']
    v = [{int(g): x for g, x in vi.items()} for vi in c['v']]
    for vi in v:
        r = goods_by_value(vi)
        x = [vi[g] for g in r]
        assert len(r) in (3, 4) and x[0] < sum(x[1:]), 'not a core agent'
        if len(r) == 3:
            assert x[0] > x[1] > x[2], 'three-good agent not strict'
        else:
            assert len(set(sum(s) for k in range(1, 5) for s in itertools.combinations(x, k))) == 15, 'not strict'
            assert type_string(x) == c['type'], 'wrong type'
    lads = [ladder(vi, c['ladder']) for vi in v]
    hold = [frozenset(B) for B in c['state']]
    st = tuple(lads[i].index(hold[i]) for i in range(n))
    assert len(set().union(*hold)) == sum(len(B) for B in hold), 'holdings overlap'
    assert valid(lads, st), 'state not valid'
    for t in states(lads):
        if t != st and all(x >= y for x, y in zip(t, st)) and valid(lads, t):
            raise AssertionError('state is Pareto-dominated by a valid state')
    if c.get('finishing', 'liberal') == 'liberal':
        assert not some_completion_efx0(v, m, [set(B) for B in hold]), 'some completion is EFX0'
    else:
        w = wanted_goods(lads, st)
        top = [st[i] == len(lads[i]) - 1 for i in range(n)]
        free = [i for i in range(n) if not top[i] and len(hold[i]) <= 1 and not (hold[i] & w)]
        owners = [i for i in range(n) if not (hold[i] & w)]
        assert not some_completion_efx0(v, m, [set(B) for B in hold], owners, free), 'some DE completion is EFX0'
    assert efx0_exists(v, n, m), 'no EFX0 allocation'


def value_monotone_obstruction(c, limit=200000):
    """None if there are too many allocations to list; else True iff every EFX0 allocation gives some agent strictly
    less than its value in the stuck state"""
    n, m = c['n'], c['m']
    if n ** m > limit:
        return None
    v = [{int(g): x for g, x in vi.items()} for vi in c['v']]
    base = [total(v[i], c['state'][i]) for i in range(n)]
    for owner in itertools.product(range(n), repeat=m):
        X = [set() for _ in range(n)]
        for g, i in enumerate(owner):
            X[i].add(g)
        if all(total(v[i], X[i]) >= base[i] for i in range(n)) and efx0(v, X):
            return False
    return True


def family1(typ_vals, spec):
    """the natural family: intermediate rungs are pairs that are not envy-free, the top is an envy-free pair"""
    tot = sum(typ_vals)
    val = lambda s: sum(typ_vals['abcd'.index(ch)] for ch in s)
    ef = lambda s: len(s) == 2 and 2 * val(s) >= tot
    return ef(spec[-1]) and not any(ef(s) for s in spec[:-1])


def main():
    d = json.load(open(os.path.join(HERE, 'barrier_certs.json')))
    refuted = set()
    for k, c in enumerate(d['certificates']):
        try:
            check_cert(c)
        except AssertionError as e:
            print('FAIL certificate %d (%s, %s): %s' % (k, c['type'], c['ladder'], e))
            sys.exit(1)
        if c.get('finishing', 'liberal') == 'liberal':
            refuted.add((c['type'], tuple(c['ladder'])))
    nar = sum(1 for c in d['certificates'] if c.get('finishing') == 'absorber')
    print('all %d certificates verified (%d with liberal finishing, %d with DE\'s own finishing)' %
          (len(d['certificates']), len(d['certificates']) - nar, nar))
    reps = {}
    for c in d['certificates']:
        v = [{int(g): x for g, x in vi.items()} for vi in c['v']]
        for vi in v:
            if len(vi) == 4:
                reps.setdefault(c['type'], tuple(vi[g] for g in goods_by_value(vi)))
    surv = [(t, tuple(s)) for t, s in d['survivors']]
    for name, fam in (('natural family (intermediate rungs not envy-free, top an envy-free pair)', True),
                      ('extended family (any pairs below the top; top an envy-free pair or {b, c, d})', False)):
        print(name + ':')
        for typ in sorted(set(t for t, s in refuted) | set(t for t, s in surv)):
            rep = reps.get(typ)
            ref = [s for t, s in refuted if t == typ and (not fam or (rep and family1(rep, s)))]
            sv = [s for t, s in surv if t == typ and (not fam or (rep and family1(rep, s)) or (not rep))]
            print('   %-30s refuted %3d   unrefuted %3d %s' % (typ, len(ref), len(sv),
                  '(small-d)' if typ == SMALL_D else ''))
    print('not refuted (liberal finishing), types other than small-d:')
    narrow = set((c['type'], tuple(c['ladder'])) for c in d['certificates'] if c.get('finishing') == 'absorber')
    for t, s in sorted(surv):
        if t != SMALL_D:
            print('   %-30s %-32s %s' % (t, ' < '.join(s), 'refuted with DE\'s own finishing (absorber certificate)'
                                        if (t, s) in narrow else 'not refuted with DE\'s own finishing either'))
    print('value-monotone obstruction (every EFX0 allocation lowers some agent below the stuck state):')
    res = [value_monotone_obstruction(c) for c in d['certificates']]
    listed = [r for r in res if r is not None]
    print('   %d of the %d certificates with at most 200,000 allocations (%d larger ones not listed)' %
          (sum(listed), len(listed), len(res) - len(listed)))


if __name__ == '__main__':
    main()
