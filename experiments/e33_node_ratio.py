"""E33: the data of Figure "nodedist" (fig:nodedist) of Section 6.6 of the paper, cited in the paragraph "Checks of the
estimates": how conservative the estimate at a node of Theorem 4.2(c), F - obj(S, w(tau)) <= nu_S^2 q, is on random
data.  1500 random instances drawn as in check_clipped_dp.py (T2), with the seed 33: M <= 7 assets, K <= 3 factors,
k <= 4; the optimal support S with value F and dual point t0 by enumeration, and the nodes tau = t0 + delta with
random delta ~ N(0, s^2 I), s in {0.01, 0.1, 1}.  For every pair (instance, s) the ratio of the loss to the bound,
(F - obj)/(nu_S^2 q) with q = ||G delta||^2, is written to results/E33/node_ratio.csv (the data file of the figure;
columns instance, shift_sd, M, K, k, nu, q, loss, ratio_to_bound), and the median, the 90% quantile and the maximum
of the ratio are printed for each s.  Run from this directory: python3 -I e33_node_ratio.py > results/E33/e33.log
(a few seconds on one core).
"""
import csv
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import clipped_dp as C

OUT = os.path.join(HERE, 'results', 'E33')
os.makedirs(OUT, exist_ok=True)

rng = np.random.default_rng(33)


def random_instance(M, K, scale_b, scale_m=1.0):
    B = rng.normal(size=(M, K)) * scale_b
    A = rng.normal(size=(K, K))
    Sf = A @ A.T / K + 0.2 * np.eye(K)
    d = rng.uniform(0.3, 2.0, size=M)
    m = rng.normal(size=M) * scale_m + 0.3 * scale_m
    return m, d, B, Sf


rows = []
inst = 0
while inst < 1500:
    M, K = int(rng.integers(3, 8)), int(rng.integers(1, 4))
    k = int(rng.integers(1, min(M, 4) + 1))
    m, d, B, Sf = random_instance(M, K, rng.choice([0.3, 1.0, 3.0, 8.0]))
    if m.max() <= 0:
        continue
    P = np.linalg.inv(Sf)
    G = C.gram_root(P)
    F, S, t = C.opt_bruteforce(m, d, B, Sf, k)
    if F <= 1e-9:
        continue
    inst += 1
    S = list(S)
    nu = 1 + C.leverages(d, B, Sf)[S].sum()
    for scale in (0.01, 0.1, 1.0):
        delta = rng.normal(size=K) * scale
        tau = t + delta
        q = float(np.linalg.norm(G @ delta) ** 2)
        w = C.wclip(m, d, B, tau)
        loss = F - C.obj_lo(m, d, B, Sf, S, w)
        rows.append((inst, scale, M, K, k, float(nu), q, float(loss), float(max(loss, 0.0) / (nu ** 2 * q))))
with open(os.path.join(OUT, 'node_ratio.csv'), 'w', newline='') as f:
    wr = csv.writer(f)
    wr.writerow(['instance', 'shift_sd', 'M', 'K', 'k', 'nu', 'q', 'loss', 'ratio_to_bound'])
    wr.writerows(rows)
r = np.array([x[-1] for x in rows])
print('rows', len(rows), 'max ratio %.4f' % r.max())
for s in (0.01, 0.1, 1.0):
    rs = np.array([x[-1] for x in rows if x[1] == s])
    print('shift sd %g: median %.3g, 90%% %.3g, max %.3g, share below 0.1: %.2f' % (
        s, np.median(rs), np.quantile(rs, 0.9), rs.max(), (rs < 0.1).mean()))
