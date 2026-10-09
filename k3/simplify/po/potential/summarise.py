"""Summarise test_exchange.py logs into the table of NOTES.md §7: python3 summarise.py LOG..."""
import re, sys
print("| set | profiles | valid states | not completable | fixed by D-cycle / pair chain / rainbow cycle | "
      "Pareto-optimal (all completable) | max moves of LS-R | rainbow cycles used, by number of exposure arcs |")
print("|---|---|---|---|---|---|---|---|")
for f in sys.argv[1:]:
    for line in open(f):
        if 'profiles,' not in line:
            continue
        title = line.split(':')[0]
        d = dict(re.findall(r'([\w-]+)=(\d+)', line))
        n = re.search(r': (\d+) profiles', line).group(1)
        am = max(int(k.split('_')[-1]) for k in d if k.startswith('alg_moves_'))
        rl = sorted(k for k in d if k.startswith('rainbow_len'))
        print(f"| {title} | {n} | {d['states']} | {d['not_completable']} | {d.get('not_completable_D-cycle', 0)} / "
              f"{d.get('not_completable_pair-chain', 0)} / {d.get('not_completable_rainbow', 0)} | {d['pareto_optimal']} | "
              f"{am} | {', '.join(k.split('_')[-1] + ': ' + d[k] for k in rl)} |")
