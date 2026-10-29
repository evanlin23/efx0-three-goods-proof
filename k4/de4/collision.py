#!/usr/bin/env python3
"""The collision example of NOTES.md, section 4.3 (n = 4, m = 7): replay.

Goods 0 A, 1 A', 2 C1, 3 D1, 4 C2, 5 D2, 6 h. Agents x, x' have three goods; z, z' have four goods of the type
b + d < a < b + c, a + d < b + c, c + d > b (values 10, 7, 6, 2), each with b equal to the other's top.
"""
from model import all_efx0, bundles, val, describe, is_efx0
import json
import os

import classc
from states import Space, liberal_finishable
from barrier import ladders_for, make_ladder, SMALL_D
from barrier_narrow import absorber_finishable
from types4 import all_types

A, Ap, C1, D1, C2, D2, h = range(7)
NAMES = ['A', "A'", 'C1', 'D1', 'C2', 'D2', 'h']
V = [{Ap: 10, C1: 7, h: 6},              # x: a = A', b = C1, c = h
     {A: 10, C2: 7, h: 6},               # x': a = A, b = C2, c = h
     {A: 10, Ap: 7, C1: 6, D1: 2},       # z: a = A, b = A', c = C1, d = D1
     {Ap: 10, A: 7, C2: 6, D2: 2}]       # z': a = A', b = A, c = C2, d = D2
AG = ['x', "x'", 'z', "z'"]
STATE = [{Ap}, {A}, {C1, D1}, {C2, D2}]


def names(B):
    return '{' + ', '.join(NAMES[g] for g in sorted(B)) + '}'


def main():
    print('instance:', describe(V))
    ags = [classc.Agent(vi) for vi in V]
    st = classc.State(ags, 7, STATE)
    print('state:', ', '.join('%s %s' % (AG[i], names(B)) for i, B in enumerate(st.Y)), ' leftover', names(st.J))
    print('valid:', st.valid, ' free agents:', st.F, ' chains:', classc.chain_candidates(st))
    print('owners that can finish (classc):', [o for o in range(4) if st.can_finish(o) is not None])
    for o in range(4):
        print('   blockers of %s as owner:' % AG[o], [(AG[x], names(S)) for x, S in st.blocker_sets(o)])
    k, bad = classc.check_every_form(V, 7)
    print('classc: %d valid states; stuck score-Pareto-maximal states: %s' %
          (k, [', '.join(names(B) for B in s.Y) for s in bad]))
    print('every ladder of the extended family containing {c, d} (states.py, liberal finishing):')
    for spec in ladders_for((10, 7, 6, 2)):
        if 'cd' not in spec:
            continue
        sp = Space(4, 7, V, make_ladder(spec))
        valid = [s for s in sp.all_states() if sp.info(s)[4]]
        bad = [s for s in sp.pareto_max(valid) if not liberal_finishable(sp, s)]
        print('   %-28s stuck: %s' % (' < '.join(spec), [', '.join(names(B) for B in sp.info(s)[0]) for s in bad]))
    sols = [bundles(4, o) for o in all_efx0(4, 7, V)]
    print('EFX0 allocations: %d' % len(sols))
    keeps = [X for X in sols if {C1, D1} <= X[2] and {C2, D2} <= X[3]]
    print('   in which z keeps C1, D1 and z\' keeps C2, D2: %d' % len(keeps))
    low = [X for X in sols if val(V[2], X[2]) < 8 or val(V[3], X[3]) < 8]
    print('   in which z or z\' is worth less to itself than {c, d} (8): %d of %d' % (len(low), len(sols)))
    base = [val(V[i], STATE[i]) for i in range(4)]
    lower = [X for X in sols if any(val(V[i], X[i]) < base[i] for i in range(4))]
    print('   in which some agent is worth less to itself than in the stuck state %s: %d of %d' %
          (base, len(lower), len(sols)))
    for X in sols[:6]:
        print('     ', ', '.join('%s %s' % (AG[i], names(B)) for i, B in enumerate(X)),
              '  values', [val(V[i], X[i]) for i in range(4)])


def tall_ladders():
    """the collision gadget, built with the representative values of each type that has a tall ladder no search
    refuted, under that ladder with DE's own finishing (valid absorbers): is some score-Pareto-maximal state stuck, and
    is the gadget's state dominated?"""
    d = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'barrier_certs.json')))
    refuted = set((c['type'], tuple(c['ladder'])) for c in d['certificates'] if c.get('finishing') == 'absorber')
    reps = all_types()
    print('the gadget on the tall ladders not refuted (values of x, x\' = 4, 3, 2; z, z\' = the type\'s values):')
    for typ, spec in d['survivors']:
        if typ == SMALL_D or (typ, tuple(spec)) in refuted:
            continue
        a, b, c, dd = reps[typ]
        v = [{Ap: 4, C1: 3, h: 2}, {A: 4, C2: 3, h: 2}, {A: a, Ap: b, C1: c, D1: dd}, {Ap: a, A: b, C2: c, D2: dd}]
        sp = Space(4, 7, v, make_ladder(tuple(spec)))
        valid = [s for s in sp.all_states() if sp.info(s)[4]]
        stuck = [s for s in sp.pareto_max(valid) if not absorber_finishable(sp, s)]
        note = ''
        if frozenset([C1, D1]) in sp.lad[2]:
            st = tuple(sp.lad[i].index(frozenset(B)) for i, B in enumerate(STATE))
            dom = [s for s in valid if s != st and all(p >= q for p, q in zip(s, st))]
            note = 'gadget state %s, dominated by %d valid states' % ('valid' if sp.info(st)[4] else 'not valid',
                                                                       len(dom))
        print('   %-28s %-30s stuck: %d  %s' % (typ, ' < '.join(spec), len(stuck), note))


if __name__ == '__main__':
    main()
    tall_ladders()
