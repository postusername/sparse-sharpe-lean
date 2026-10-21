"""E41: random instances with M = 16 (Section 6.3, Table 6.3, Figure 6.1) in a 2 x 2 design.

Structure of the factor model:
  * calibrated -- like monthly industry returns: factor covariance diag(0.045^2, 0.03^2, ..., 0.03^2), loadings on the
                  first (market) factor from N(1, 0.3^2) and on the others from N(0, 0.5^2), R_i^2 ~ U(0.2, 0.8);
  * stress     -- unstructured: Sf = A A'/K + 0.2 I and B with standard Gaussian entries, R_i^2 ~ U(0.5, 0.95).
Expected returns:
  * factor     -- explained by the factors: m = B lambda + alpha, lambda_l = sr_l sqrt(Sf_ll) with factor Sharpe ratios
                  sr = 0.6/4.5 (first factor) and 0.2/3 (the others) per period, alpha_i ~ N(0, (0.1 sqrt(d_i))^2);
  * unrelated  -- uniform multiples of the volatilities, m_i = u_i sqrt(V_ii), u_i ~ U(-0.1, 0.3), independent of B.
The idiosyncratic variances are d_i = B_i'Sf B_i (1 - R_i^2)/R_i^2.  The paper's "calibrated regime" is
(calibrated, factor) and its "stress regime" is (stress, unrelated).  Two more regimes separate the loadings from
the leverages omega_i = R_i^2/(1 - R_i^2): (calibrated-highR2, unrelated), the calibrated loadings with
R_i^2 ~ U(0.5, 0.95), and (stress-lowR2, unrelated), the stress loadings with R_i^2 ~ U(0.2, 0.8); and
(stress-nonneg, unrelated) is the stress regime with the loadings replaced by their absolute values (an independent
draw; nonnegative loadings, the hypothesis of Theorem 5.11).  For each regime, K in {1, 2, 3, 5} and
k in {3, 5}, 100 instances are drawn with the seed 41000 + 1000 r + 10 K + k (r = 0..6, the regime).
Per instance: OPT(k) by enumeration of the supports with k assets; the relaxation G*_k = min_t g_k(t) (and its time,
which the outer approximation needs for its first cut); greedy selection
and greedy selection with exchanges; the certificate F_h >= (1 - 2 eps) G*_k with eps = 0.05; screening by Sharpe
ratios (the k largest m_i/sqrt(V_ii), long-only optimum on them); branch and bound of Section 5.3; and the methods of
baselines.py: pga (Lin et al. 2024), oscar (Bae et al. 2025), the SDP bound (P7) of Kim et al. (2016) with and without
Y >= 0, and the outer approximation of Bertsimas and Cory-Wright (2022).
Usage:  python3 -I e41_random.py <regime 0..6> [n=100]   -> one JSON line per instance on stdout
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
import e34_localized as E
import e35_scale as S35
import baselines as BL

REGIMES = [('calibrated', 'factor'), ('calibrated', 'unrelated'), ('stress', 'factor'), ('stress', 'unrelated'),
           ('calibrated-highR2', 'unrelated'), ('stress-lowR2', 'unrelated'), ('stress-nonneg', 'unrelated')]
EPS = 0.05


def instance(rng, M, K, structure, returns):
    if structure.startswith('calibrated'):
        Sf = np.diag(np.r_[0.045, 0.03 * np.ones(K - 1)] ** 2)
        B = np.c_[rng.normal(1.0, 0.3, M), rng.normal(0.0, 0.5, (M, K - 1))]
        R2 = rng.uniform(0.5, 0.95, M) if structure.endswith('highR2') else rng.uniform(0.2, 0.8, M)
    else:
        A = rng.normal(size=(K, K))
        Sf = A @ A.T / K + 0.2 * np.eye(K)
        B = rng.normal(size=(M, K))
        if structure.endswith('nonneg'):
            B = np.abs(B)
        R2 = rng.uniform(0.2, 0.8, M) if structure.endswith('lowR2') else rng.uniform(0.5, 0.95, M)
    sysv = np.einsum('ij,jk,ik->i', B, Sf, B)
    d = sysv * (1 - R2) / R2
    if returns == 'factor':
        sr = np.r_[0.6 / 4.5, (0.2 / 3) * np.ones(K - 1)]
        m = B @ (sr * np.sqrt(np.diag(Sf))) + rng.normal(size=M) * 0.1 * np.sqrt(d)
    else:
        m = rng.uniform(-0.1, 0.3, M) * np.sqrt(sysv + d)
    return m, d, B, Sf


def greedy_only(m, d, B, Sf, k):
    S, best = [], 0.0
    for _ in range(k):
        cand, cv = None, best
        for i in range(len(m)):
            if i not in S:
                v = E.flo(m, d, B, Sf, S + [i])[0]
                if v > cv + 1e-15:
                    cv, cand = v, i
        if cand is None:
            break
        S.append(cand)
        best = cv
    return best, tuple(sorted(S))


def run(m, d, B, Sf, k):
    M, K = B.shape
    rec = {}
    t0 = time.perf_counter()
    opt, Sopt = max((E.flo(m, d, B, Sf, S)[0], S) for S in itertools.combinations(range(M), k))
    rec['t_enum'] = time.perf_counter() - t0
    t0 = time.perf_counter()
    G, that = E.relaxation(m, d, B, Sf, k)
    rec['t_relax'] = time.perf_counter() - t0
    Fg, Sg = greedy_only(m, d, B, Sf, k)
    Fh, Sh = E.greedy_swap(m, d, B, Sf, k)
    P = np.linalg.inv(Sf)
    P = (P + P.T) / 2
    t_h = E.flo(m, d, B, Sf, Sh)[2]
    G = min(G, E.gk(m, d, B, P, k, t_h))
    sr = m / np.sqrt(d + np.einsum('ij,jk,ik->i', B, Sf, B))
    Ssr = np.argsort(-sr, kind='stable')[:k]
    Fsr = E.flo(m, d, B, Sf, list(Ssr))[0]
    vb, Sb, nb, tb, fin = S35.bnb(m, d, B, Sf, k, Fh, Sh, t_h, time_limit=600.0)
    rec.update(opt=opt, G=G, Fg=Fg, Fh=Fh, Fsr=Fsr, bnb=vb, bnb_nodes=nb, bnb_time=tb, bnb_done=fin,
               cert=bool(Fh >= (1 - 2 * EPS) * G), relgap=(G - opt) / opt)
    S1, v, iters, tp = BL.pga_lin2024(m, d, B, Sf, k)
    rec['pga'] = (E.flo(m, d, B, Sf, list(S1))[0] if len(S1) else 0.0)
    rec['pga_iters'] = iters
    S2, to = BL.oscar_bae2025(m, d, B, Sf, k)
    rec['oscar'] = E.flo(m, d, B, Sf, list(S2))[0]
    for key, nonneg in (('sdp', False), ('sdp_nonneg', True)):
        val, ts, st = BL.sdp_kim2016(m, d, B, Sf, k, nonneg=nonneg)
        rec[key] = val
        rec[key + '_status'] = st
    oa = BL.oa_bcw2022(m, d, B, Sf, k, that, list(Sh), time_limit=600.0)
    rec['oa'] = oa['value']
    rec['oa_status'] = oa['status']
    rec['oa_nodes'] = oa['nodes']
    rec['oa_time'] = oa['time']
    return rec


def main():
    r = int(sys.argv[1])
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    structure, returns = REGIMES[r]
    for K in (1, 2, 3, 5):
        for k in (3, 5):
            seed = 41000 + 1000 * r + 10 * K + k
            rng = np.random.default_rng(seed)
            done = 0
            while done < n:
                m, d, B, Sf = instance(rng, 16, K, structure, returns)
                if m.max() <= 0:
                    continue
                rec = dict(structure=structure, returns=returns, K=K, k=k, seed=seed, it=done)
                rec.update(run(m, d, B, Sf, k))
                print(json.dumps(rec), flush=True)
                done += 1


if __name__ == '__main__':
    main()
