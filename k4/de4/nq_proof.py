#!/usr/bin/env python3
"""The Improvement Lemma for (NQ) instances, as code: every claim of the attempted proof is an assert.

(NQ): every four-good agent has v(c) + v(d) <= v(b) or v(c) + v(d) >= v(a) (types 1, 2, 5, 6, 9, 10, 12 of
types4.py); three-good agents are as in the paper. On the threat ladder (lex.py) such agents satisfy
    (L1) every rung of two or more goods is worth more than a (so its holder wants nothing);
    (L2) the threat sets of a pair rung are exactly its complement pair, if that is worth more; a triple has none.

Attempted target (Improvement Lemma, NQ), FALSE in general (NOTES.md section 7.2: gadgets.collision12 is an (NQ)
instance whose draft is valid, score-Pareto-maximal and not finishable): in a valid state that no owner can finish,
some valid grab exists, or a valid ring:
    sigma(j) = the first agent that wants j's good, for a busy agent j (holding a single wanted good);
    sigma(o) = an agent x with an arrow into the owner o: x moves to a higher rung B made of goods of Y_o, leftover
               goods (its *label*, B & J) and, if x is an owner, its own goods;
with pairwise disjoint labels along the cycle. Then every score-Pareto-maximal valid state is finishable (a ring or a
grab would dominate it), and DE's loop (grab, ring, finish) terminates with an EFX0 allocation.

improve(d) follows the attempted proof; check_instance() runs it on every valid state of an instance. The main
program first checks Lemma 5 ((L1) and (L2) for exactly the (NQ) types) over the twelve strict types, then runs the
proof on random (NQ) instances (no failed assert: the counterexample needs a structure random instances lack), then
shows where it stops on collision12.

    python3 nq_proof.py [instances] [seed]        (default: 3,000 with seed 2 and 4,000 with seed 3)
"""
import random
import sys
from collections import Counter

from model import random_core_values, describe, relevant, val
from der import DER
from lex_test import type_values
from types4 import all_types

TYPES = sorted(all_types())
NQ_TYPES = [TYPES[i - 1] for i in (1, 2, 5, 6, 9, 10, 12)]


def nq_ok(vi):
    r = relevant(vi)
    if len(r) == 3:
        return True
    a, b, c, d = (vi[g] for g in r)
    return c + d <= b or c + d >= a


class Fail(Exception):
    pass


def need(cond, msg):
    if not cond:
        raise Fail(msg)


def grab(d):
    """a valid grab: x moves to a higher rung made of its own goods and leftover goods"""
    for x in range(d.n):
        for s in range(len(d.sp.lad[x]) - 1, d.st[x], -1):
            B = d.sp.lad[x][s]
            if B <= d.Y[x] | d.J:
                new = d.chain(x, B)
                if new is not None:
                    return x, B, new
    return None


def arrows_into(d, o):
    """(x, B, label) for every agent x != o that can move to a higher rung B made of goods of Y_o (at least one),
    leftover goods and, if x is an owner, its own goods"""
    out = []
    for x in range(d.n):
        if x == o:
            continue
        own = d.Y[x] if x in d.owners else frozenset()
        pool = own | d.Y[o] | d.J
        lad = d.sp.lad[x]
        for s in range(len(lad) - 1, d.st[x], -1):
            B = lad[s]
            if B <= pool and B & d.Y[o]:
                out.append((x, B, B & d.J))
    return out


def improve(d, st):
    """returns ('grab', new) or ('ring', new); raises Fail where the proof breaks"""
    d.setup(st)
    g = grab(d)
    if g is not None:
        return 'grab', g[2]
    d.setup(st)
    # (NC): no threat set inside J (Lemma A: else a valid chain, which is a grab)
    for x in range(d.n):
        for T in d.threat_sets(x):
            need(not T <= d.J, 'NC fails without a valid grab')
    # every owner holds a good, and has a blocker
    for o in d.owners:
        need(d.Y[o], 'an owner holds nothing')
        need(d.blockers(o), 'an owner without blockers')
    # G1: a four-good owner's top is not leftover
    for x in d.owners:
        r = relevant(d.v[x])
        if len(r) == 4:
            need(r[0] not in d.J, 'G1: a four-good owner whose top is leftover')
    # G2, G3: label-free arrows from multi-holder blockers and free four-good single blockers
    for o in d.owners:
        arr = arrows_into(d, o)
        lf = set(x for x, B, L in arr if not L)
        for x, T in d.blockers(o):
            if len(d.Y[x]) >= 2:
                need(x in lf, 'G2: a multi-holder blocker without a label-free arrow')
            elif x in d.owners and len(relevant(d.v[x])) == 4:
                need(x in lf, 'G3: a free four-good blocker without a label-free arrow')
    # the walk (as in k3/simplify/po/potential/NOTES.md): from a start agent, follow sigma; at a busy agent sigma is
    # the first agent that wants its good; at an owner, an arrow into it with labels disjoint from those already used
    # on the walk, in the order: pure (the agent keeps none of its own goods) before keeping, label-free before
    # labelled, pairs before triples
    for start in range(d.n):
        res = walk_from(d, start)
        if res is not None:
            new, cyc_info = res
            need(all(a >= b for a, b in zip(new, st)) and new != st, 'ring does not dominate')
            d.walk_start = start
            return 'ring', new
    raise Fail('no start gives a valid ring')


def walk_from(d, start):
    rep, used, walk = {}, set(), []
    j = start
    while j not in walk:
        walk.append(j)
        if j in d.owners:
            cand = [(x, B, L) for x, B, L in arrows_into(d, j) if not (L & used)]
            if not cand:
                return None
            cand.sort(key=lambda c: (bool(c[1] & d.Y[c[0]]), bool(c[2]), len(c[1]), c[0]))
            rep[j] = cand[0][:2]
            used |= cand[0][2]
            j = cand[0][0]
        else:
            j = d.first_wanter(next(iter(d.Y[j])))
    cyc = walk[walk.index(j):]
    k = len(cyc)
    for t, w in enumerate(cyc):
        x = cyc[(t + 1) % k]
        if w not in rep or x not in rep:
            continue
        B = rep[w][1]
        taken_from_x = rep[x][1] & d.Y[x]
        if B & d.Y[x] & taken_from_x:
            alts = [B2 for x2, B2, L2 in arrows_into(d, w) if x2 == x and L2 == (B & d.J)
                    and B2 & d.Y[w] == B & d.Y[w] and not (B2 & d.Y[x] & taken_from_x)]
            if alts:
                rep[w] = (x, alts[0])
    Y = list(d.Y)
    for t, w in enumerate(cyc):
        r = cyc[(t + 1) % k]
        Y[r] = rep[w][1] if w in rep else d.Y[w]
    for t, w in enumerate(cyc):
        if w in rep:
            r = cyc[(t + 1) % k]
            if (Y[r] & d.Y[w]) & Y[w]:
                return None
    new = d.as_state(Y)
    return None if new is None else (new, cyc)
def nq_instance(rng):
    n = rng.choice([2, 3, 3, 4, 4, 5])
    m = rng.randint(4, 3 + n)
    v = []
    for _ in range(n):
        vals = type_values(rng, rng.choice(NQ_TYPES)) if rng.random() < 0.8 else random_core_values(rng, 3)
        v.append(dict(zip(rng.sample(range(m), len(vals)), vals)))
    return n, m, v


def check_instance(n, m, v, out, fails):
    d = DER(n, m, v)
    V = d.sp.valid_states()
    if len(V) > 20000:
        return
    for st in V:
        d.setup(st)
        if all(d.top) or any(d.can_finish(o) is not None for o in d.owners):
            out['finishable'] += 1
            continue
        try:
            d.walk_start = None
            kind, new = improve(d, st)
            out[kind] += 1
            if kind == 'ring' and d.walk_start:
                out['ring (start %s)' % ('later' if d.walk_start else 0)] += 1
        except Fail as e:
            out['FAIL: ' + str(e).split(' %')[0]] += 1
            fails.setdefault(str(e), (describe(v), [sorted(B) for B in d.sp.holdings(st)]))


def lemma5():
    """(L1) and (L2) hold for exactly the (NQ) types (a finite check over the twelve strict types)"""
    from lex import pair_ladder, rung_threat_sets
    ok = True
    for k, t in enumerate(TYPES, 1):
        vals = all_types()[t]
        vi = dict(zip('abcd', vals))
        lad = pair_ladder(vi, 'threat')
        multi = [B for B in lad if len(B) >= 2]
        l1 = all(val(vi, B) > vi['a'] for B in multi)
        l2 = all(rung_threat_sets(vi, B) == ([frozenset('abcd') - B] if len(B) == 2 and
                                             val(vi, frozenset('abcd') - B) > val(vi, B) else []) for B in multi)
        nq = t in NQ_TYPES
        ok &= (l1 and l2) == nq
        print('  type %2d %-28s (NQ) %-5s (L1) %-5s (L2) %s' % (k, t, nq, l1, l2))
    print('Lemma 5: (L1) and (L2) hold exactly for the (NQ) types: %s' % ok)
    return ok


def main(batches):
    ok = lemma5()
    out, fails = Counter(), {}
    for N, seed in batches:
        rng = random.Random(seed)
        for t in range(N):
            check_instance(*nq_instance(rng), out, fails)
    print('the attempted proof on random (NQ) instances (%s):' % ', '.join('%d with seed %d' % b for b in batches))
    for k in sorted(out):
        print('  %-58s %d' % (k, out[k]))
    for msg, ex in list(fails.items())[:12]:
        print('  %s: %s' % (msg, ex))
    from gadgets import collision12
    n, m, v = collision12()
    d = DER(n, m, v)
    draft = tuple(d.rung(i, frozenset([i])) for i in range(n))
    d.setup(draft)
    print('collision12 (all agents (NQ): %s): draft valid %s, an owner can finish: %s' %
          (all(nq_ok(vi) for vi in v), d.sp.is_valid(draft), any(d.can_finish(o) is not None for o in d.owners)))
    try:
        improve(d, draft)
        print('  the proof finds a move (unexpected)')
        ok = False
    except Fail as e:
        print('  the proof stops at: %s' % e)
    return 0 if ok and not fails else 1


if __name__ == '__main__':
    if len(sys.argv) > 1:
        sys.exit(main([(int(sys.argv[1]), int(sys.argv[2]) if len(sys.argv) > 2 else 1)]))
    sys.exit(main([(3000, 2), (4000, 3)]))
