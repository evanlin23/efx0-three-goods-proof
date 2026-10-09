"""Conjecture ST (every valid state with no single move completes) is false: n = 6, m = 10.
Goods: A1=0 A1'=1 A2=2 A2'=3 p1=4 p2=5 g1=6 g1'=7 g2=8 g2'=9; agents x1, x1', x2, x2', o1, o2."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'explore', 'matching'))
from common import Base, completes, states
from exp_local import one_moves
U = {0: 0, 3: 1, 2: 2, 1: 3, 4: 4}
rank = [(0, 4, 6), (1, 4, 7), (2, 5, 8), (3, 5, 9), (2, 3, 4), (0, 1, 5)]; m = 10
opt = (1, 1, 1, 1, 3, 3)          # options: 1 = a, 3 = c; the x's hold their tops, o1 holds 4, o2 holds 5
b = Base(rank, m, opt)
print("valid:", b.valid, " NA:", sorted(b.NA), " junk:", b.J, " free:", b.free)
print("completable:", completes(b) is not None, " single moves:", one_moves(rank, m, opt))
dom = [s for s in states(rank) if s != opt and Base(rank, m, s).valid and all(U[s[i]] >= U[opt[i]] for i in range(6))]
print("Pareto-dominating valid states (option per agent; 4 = pair):", dom)
print("all of them completable:", all(completes(Base(rank, m, s)) is not None for s in dom))
