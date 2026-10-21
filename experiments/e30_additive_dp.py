"""E30: the scheme without the Gram matrix itself on the real data, Table 6.7 ("The scheme itself") of Section 6.6
of the paper.  For each instance of the plan below (eps = 0.05) the reference value F* is the optimum OPT(k) by
enumeration ("exact": the industries FF49, window July 2016 - June 2026, and the Hang Seng data port1, M <= 49 and
k <= 5) or the value of greedy selection with exchanges ("heuristic", a lower bound: the larger universes), the guess
is V = F*/1.5, and the table of the dynamic program of clipped_dp.py is built with the constants of Definition 4.7
(clipped_dp.params: eta = sqrt(eps V/2)/(k sqrt K), s_g = sqrt(2 eps V)/((1 + k omega) sqrt K),
Q = k + ceil(sqrt(5 omega k^3 K/eps))) at the node of the grid nearest to the dual point t* of the reference support.
Printed per instance: the size of the table and its bound (2Q+1)^K (k+1) + 1 of Lemma 4.4(a), the number of supports
with at most k names, the merges (an extension of a set landed in an occupied bucket) and their share, the number of
extensions discarded by the box, the largest |key|, the best F_LO of a set of the table divided by F* and the check
of the guarantee 1 - 2 eps; for FF49-K1 and port1-K1 with k = 3 also the whole family over all 2Z+1 nodes of the grid
(the number of distinct sets, its bound (2Z+1) times the table bound, and the best one).  Run from this directory:
python3 -I e30_additive_dp.py > results/E30/e30.log  (about 6.5 minutes on one core, most of it for the Russell 3000);
writes results/E30/results_E30.json.
"""
import itertools
import json
import math
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import clipped_dp as C
import data_real as D

OUT = os.path.join(HERE, 'results', 'E30')


def comb_count(M, k):
    return sum(math.comb(M, r) for r in range(0, k + 1))


def run_node(mdl, k, eps, V, tau, p, order=None):
    m, d, B, Sf = mdl['m'], mdl['d'], mdl['B'], mdl['Sf']
    G = C.gram_root(np.linalg.inv(Sf))
    table, st = C.clipped_dp_stats(m, d, B, Sf, G, tau, p['eta'], k, p['Q'], order)
    best, bestU = -1.0, None
    for (key, n), (val, U) in table.items():
        if n == 0:
            continue
        f = C.flo_exact(m, d, B, Sf, sorted(U))[0]
        if f > best:
            best, bestU = f, U
    return table, st, best, bestU


def experiment(name, K, k, eps=0.05, exact=True, full=False, tlimit=900):
    t0 = time.time()
    mdl = D.model(name, K)
    m, d, B, Sf, M = mdl['m'], mdl['d'], mdl['B'], mdl['Sf'], mdl['M']
    om = mdl['omega']
    P = np.linalg.inv(Sf)
    G = C.gram_root(P)
    if exact:
        Fs, S, tst = C.opt_bruteforce(m, d, B, Sf, k)
        kind = 'exact'
    else:
        Fs, S = C.greedy_swap(m, d, B, Sf, k)
        _, _, tst = C.flo_exact(m, d, B, Sf, S)
        kind = 'heuristic'
    V = Fs / 1.5
    p = C.params(eps, V, k, K, om)
    z, tau = C.nearest_node(G, tst, p['sg'])
    table, st, best, bestU = run_node(mdl, k, eps, V, tau, p)
    nsub = comb_count(M, k) - 1
    tabsz = len(table) - 1
    row = dict(model=mdl['name'], M=M, K=K, k=k, eps=eps, omega=om, F=Fs, kind=kind, V=V,
               eta=p['eta'], sg=p['sg'], Q=p['Q'], Z=p['Z'], table=tabsz,
               table_bound=(k + 1) * (2 * p['Q'] + 1) ** K + 1, subsets=nsub,
               generated=st['generated'], merged=st['merged'], boxed=st['boxed'], maxkey=st['maxkey'],
               ratio=best / Fs, guarantee=1 - 2 * eps, ok=best >= (1 - 2 * eps) * Fs - 1e-12,
               support=sorted(int(i) for i in S), best_support=sorted(int(i) for i in bestU),
               sec=time.time() - t0)
    print('%-9s M=%4d K=%d k=%d (%s) F*=%.5g  Q=%d Z=%d | table %d (bound %.3g), subsets %d, merged %d (%.1f%%), boxed %d, '
          'max|key|=%d | F_best/F* = %.6f %s  [%.0fs]' % (
              mdl['name'], M, K, k, kind, Fs, p['Q'], p['Z'], tabsz, row['table_bound'], nsub, st['merged'],
              100.0 * st['merged'] / max(1, st['generated']), st['boxed'], st['maxkey'], row['ratio'],
              'OK' if row['ok'] else 'VIOLATION', row['sec']), flush=True)
    if full and K == 1:
        fam = set()
        bestall = -1.0
        t1 = time.time()
        for zz in range(-p['Z'], p['Z'] + 1):
            tau2 = np.linalg.solve(G, np.array([zz * p['sg']]))
            tab2, st2, b2, U2 = run_node(mdl, k, eps, V, tau2, p)
            for (key, n), (val, U) in tab2.items():
                fam.add(frozenset(U))
            bestall = max(bestall, b2)
            if time.time() - t1 > tlimit:
                print('  (stopped by the time limit at node %d)' % zz)
                break
        row['family_size'] = len(fam)
        row['family_bound'] = (2 * p['Z'] + 1) * row['table_bound']
        row['family_ratio'] = bestall / Fs
        print('   family (all nodes, K=1): %d distinct sets (bound %.3g), F_best/F* = %.6f' % (
            len(fam), row['family_bound'], row['family_ratio']), flush=True)
    return row


if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    rows = []
    plan = [("FF49", 1, 3, True, True), ("FF49", 3, 3, True, False), ("port1", 1, 3, True, True),
            ("port1", 1, 5, True, False), ("port1", 3, 3, True, False), ("port1", 3, 5, True, False),
            ("port2", 1, 3, False, False), ("port5", 1, 3, False, False), ("SP500", 1, 3, False, False),
            ("SP500", 3, 3, False, False), ("Russell", 1, 3, False, False)]
    for nm, K, k, ex, full in plan:
        try:
            rows.append(experiment(nm, K, k, exact=ex, full=full))
        except Exception as e:  # noqa
            print('ERROR', nm, K, k, repr(e), flush=True)
    with open(os.path.join(OUT, 'results_E30.json'), 'w') as fh:
        json.dump(rows, fh, indent=1, default=float)
    print('violations of the guarantee:', sum(1 for r in rows if not r['ok']), 'of', len(rows))
