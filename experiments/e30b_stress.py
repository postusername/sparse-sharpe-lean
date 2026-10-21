"""E30b: the scaling sentence of Section 7.6 of the paper ("Multiplying the key width and the grid step by a common
factor c ..."), i.e. how conservative the constants of Definition 4.7 are.  Part (a), the only one the paper uses: on
the four real instances with a known optimum (FF49-K1 and FF49-K3 with k = 3, window July 2016 - June 2026; port1-K1
with k = 5 and port1-K3 with k = 3; eps = 0.05, guess V = OPT(k)/1.5) the key width eta and the grid step s_g of
clipped_dp.params are multiplied by c in {1, 3, 10, 30, 100, 300, 1000, 3000} (the box radius becomes
max(1, int(Q/c) + k + 1)), the table is built at the node nearest to the dual point of the optimum, and the size of the
table, the share of merges and the best F_LO of a set of the table divided by the optimum are printed.  Part (b) is
an old random study from an earlier version of the paper, kept for the record but not used in the paper (the random
instances of Section 7.3 are those of e41_random.py): 100 random 'calibrated' and 'stress' models each with M = 16,
K = 1, 2, 3 and k = 3, and the guarantee 1 - 2 eps with the constants of Definition 4.7 at the node nearest to the
dual point of the optimum.  Run from this directory: python3 -I e30b_stress.py > results/E30b/e30b.log  (about
half a minute on one core; only the log).
"""
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import clipped_dp as C
import data_real as D

rng = np.random.default_rng(23)


def best_in_table(m, d, B, Sf, table):
    best = -1.0
    for (key, n), (val, U) in table.items():
        if n == 0:
            continue
        best = max(best, C.flo_exact(m, d, B, Sf, sorted(U))[0])
    return best


def scan(name, K, k, eps=0.05):
    mdl = D.model(name, K)
    m, d, B, Sf = mdl['m'], mdl['d'], mdl['B'], mdl['Sf']
    G = C.gram_root(np.linalg.inv(Sf))
    Fs, S, tst = C.opt_bruteforce(m, d, B, Sf, k)
    om = mdl['omega']
    V = Fs / 1.5
    p = C.params(eps, V, k, K, om)
    print('%s k=%d F*=%.5g (η=%.3g, s_g=%.3g)' % (mdl['name'], k, Fs, p['eta'], p['sg']))
    for c in (1, 3, 10, 30, 100, 300, 1000, 3000):
        sg, eta = p['sg'] * c, p['eta'] * c
        z = np.round(G @ tst / sg)
        tau = np.linalg.solve(G, z * sg)
        table, st = C.clipped_dp_stats(m, d, B, Sf, G, tau, eta, k, max(1, int(p['Q'] / c) + k + 1))
        best = best_in_table(m, d, B, Sf, table)
        print('   scale ×%-5g  table %6d  merged %5.1f%%  F_best/F* = %.6f' % (
            c, len(table) - 1, 100 * st['merged'] / max(1, st['generated']), best / Fs), flush=True)


def random_instance(M, K, regime):
    B = rng.normal(size=(M, K)) * rng.choice([0.5, 1.0, 2.0])
    A = rng.normal(size=(K, K))
    Sf = A @ A.T / K + 0.3 * np.eye(K)
    d = rng.uniform(0.3, 2.0, M)
    if regime == 'calibrated':
        # m = B λ + residual: the expected returns agree with the factor structure
        lam = rng.normal(size=K) * 0.3
        m = B @ lam + rng.normal(size=M) * 0.05 * np.sqrt(d) + 0.05
    else:
        m = rng.normal(size=M) * 0.5 + 0.2   # 'stress': means without factor structure
    return m, d, B, Sf


def stress(K, regime, n=100, M=16, k=3, eps=0.05):
    viol, ratios, hit, merged_frac, tabsz = 0, [], 0, [], []
    for _ in range(n):
        m, d, B, Sf = random_instance(M, K, regime)
        if m.max() <= 0:
            continue
        G = C.gram_root(np.linalg.inv(Sf))
        Fs, S, tst = C.opt_bruteforce(m, d, B, Sf, k)
        if Fs <= 1e-9:
            continue
        om = float((np.einsum('ij,jk,ik->i', B, Sf, B) / d).max())
        V = Fs / 1.5
        p = C.params(eps, V, k, K, om)
        z, tau = C.nearest_node(G, tst, p['sg'])
        table, st = C.clipped_dp_stats(m, d, B, Sf, G, tau, p['eta'], k, p['Q'])
        best = best_in_table(m, d, B, Sf, table)
        ratios.append(best / Fs)
        viol += best < (1 - 2 * eps) * Fs - 1e-12
        hit += best >= Fs - 1e-12
        merged_frac.append(st['merged'] / max(1, st['generated']))
        tabsz.append(len(table) - 1)
    print('K=%d %-10s n=%3d: violations %d, min F_best/F* = %.6f, optimum found in %d%%, merged on average %.1f%%, '
          'table (mean/max) %.0f/%d' % (K, regime, len(ratios), viol, min(ratios), 100 * hit // len(ratios),
                                              100 * np.mean(merged_frac), np.mean(tabsz), max(tabsz)), flush=True)
    return viol


if __name__ == "__main__":
    t0 = time.time()
    for nm, K, k in [("FF49", 1, 3), ("FF49", 3, 3), ("port1", 1, 5), ("port1", 3, 3)]:
        scan(nm, K, k)
    tot = 0
    for K in (1, 2, 3):
        for regime in ('calibrated', 'stress'):
            tot += stress(K, regime)
    print('total violations of the guarantee 1 − 2ε on the random examples:', tot, ' [%.0f s]' % (time.time() - t0))
