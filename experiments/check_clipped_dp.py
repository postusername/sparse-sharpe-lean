"""Checks of the estimates of Section 4, for the paragraph "Checks of the estimates" of Section 7.6 of the paper
(together with e33_node_ratio.py).  On random factor models with at most 10 assets and at most 3 factors it checks
(T1) the defect identity of Theorem 4.1 at random nodes and supports (2000 draws); (T2) the estimates at a node of
Theorem 4.2 for the optimal support, found by enumeration, at nodes displaced from its dual point by Gaussian shifts
with standard deviation 0.01, 0.1 and 1 (1500 draws; printed: the largest ratios of the two sides), and it prints
Example 4.3 (one asset and one factor, where the factor nu is attained); (T3) the guarantee 1 - 2 eps of one guess
(Theorem 4.8) for the table of the dynamic program of clipped_dp.py with the constants of Definition 4.7
(clipped_dp.params) and the guess OPT(k)/1.5, at the node nearest to the dual point of the optimum (300 draws, with
the table bound (2Q+1)^K (k+1) + 1 of Lemma 4.4(a) and the node radius Z), and (T3b) at a node displaced by exactly
s_g/2 in every coordinate of G t (200 draws with large loadings); an assertion stops the script at the first
violation, and it prints OK at the end.  Run from this directory:
python3 -I check_clipped_dp.py > results/CHECK/check_clipped_dp.log  (a few seconds on one core; only the log).
"""
import itertools
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import clipped_dp as C

rng = np.random.default_rng(20261020)


def random_instance(M, K, scale_b, scale_m=1.0, pos_beta=False):
    B = rng.normal(size=(M, K)) * scale_b
    if pos_beta:
        B = np.abs(B)
    A = rng.normal(size=(K, K))
    Sf = A @ A.T / K + 0.2 * np.eye(K)
    d = rng.uniform(0.3, 2.0, size=M)
    m = rng.normal(size=M) * scale_m + 0.3 * scale_m
    return m, d, B, Sf


# ------------------------------------------------------------------ T1: the defect identity
worst1 = 0.0
for _ in range(2000):
    M, K = rng.integers(3, 9), rng.integers(1, 4)
    m, d, B, Sf = random_instance(M, K, rng.choice([0.3, 1.0, 3.0]))
    P = np.linalg.inv(Sf)
    G = C.gram_root(P)
    tau = rng.normal(size=K)
    R = list(rng.choice(M, size=rng.integers(1, M + 1), replace=False))
    w = C.wclip(m, d, B, tau)
    lhs = C.obj_lo(m, d, B, Sf, R, w)
    u = Sf @ B[R].T @ w[R]
    rhs = C.qlo(m, d, B, P, R, tau) - (u - tau) @ P @ (u - tau)
    v = (G @ Sf @ B.T * w).T
    rhs2 = tau @ P @ tau + np.sum(d[R] * w[R] ** 2) - np.sum((G @ tau - v[R].sum(0)) ** 2)
    worst1 = max(worst1, abs(lhs - rhs), abs(lhs - rhs2))
print('T1 identity: max abs error', worst1)
assert worst1 < 1e-9

# ------------------------------------------------------------------ T2: the estimates at a node
worst_a, worst_D, worst_loss = 0.0, 0.0, 0.0
for _ in range(1500):
    M, K = rng.integers(3, 8), rng.integers(1, 4)
    k = int(rng.integers(1, min(M, 4) + 1))
    m, d, B, Sf = random_instance(M, K, rng.choice([0.3, 1.0, 3.0, 8.0]))
    if m.max() <= 0:
        continue
    P = np.linalg.inv(Sf)
    G = C.gram_root(P)
    F, S, t = C.opt_bruteforce(m, d, B, Sf, k)
    if F <= 1e-9:
        continue
    om = C.leverages(d, B, Sf)
    nu = 1 + om[list(S)].sum()
    for scale in [1e-2, 0.1, 1.0]:
        delta = rng.normal(size=K) * scale
        tau = t + delta
        gd = np.linalg.norm(G @ delta)
        a = C.qlo(m, d, B, P, S, tau) - F
        w = C.wclip(m, d, B, tau)
        u = Sf @ B[list(S)].T @ w[list(S)]
        D = (u - tau) @ P @ (u - tau)
        obj = C.obj_lo(m, d, B, Sf, S, w)
        assert a >= -1e-9
        worst_a = max(worst_a, a / (nu * gd ** 2))
        worst_D = max(worst_D, D / (nu ** 2 * gd ** 2))
        # obj(S*, wclip tau) >= F - D  and  F - obj <= k omega a  (cardinality version: sum omega_i a)
        assert obj >= F - D - 1e-8 * (1 + F)
        worst_loss = max(worst_loss, (F - obj) / max(1e-300, (nu - 1) * a) if a > 1e-12 else 0.0)
print('T2 node bounds: a/(ν‖Gδ‖²) <= %.4f ; D/(ν²‖Gδ‖²) <= %.4f ; (F−obj)/((ν−1)a) <= %.4f'
      % (worst_a, worst_D, worst_loss))
assert worst_a <= 1 + 1e-3 and worst_D <= 1 + 1e-3  # 1e-3: loss of precision for delta ~ 1e-3

# Example A (Example 4.3; K = k = 1, d = 1, B = A, m = 1): D = (1+omega)^2 delta^2, loss (1+omega) omega delta^2
for A_ in [1.0, 3.0, 10.0]:
    om = A_ ** 2
    m, d, B, Sf = np.array([1.0]), np.array([1.0]), np.array([[A_]]), np.array([[1.0]])
    F, S, t = C.opt_bruteforce(m, d, B, Sf, 1)
    for delta in [0.01, 0.1]:
        tau = t + delta
        w = C.wclip(m, d, B, tau)
        obj = C.obj_lo(m, d, B, Sf, [0], w)
        print('  Example A: ω=%g δ=%g  F−obj = %.6g  predicted (1+ω)ωδ² = %.6g' % (om, delta, F - obj, (1 + om) * om * delta ** 2))

# ------------------------------------------------------------------ T3: the end-to-end guarantee of the dynamic program
def run_dp_guarantee(m, d, B, Sf, k, eps, use_pdf_step=False, guess=1.5, off=None):
    M, K = B.shape
    P = np.linalg.inv(Sf)
    G = C.gram_root(P)
    F, S, t = C.opt_bruteforce(m, d, B, Sf, k)
    om = C.leverages(d, B, Sf).max()
    V = F / guess
    p = C.params(eps, V, k, K, om)
    sg = p['sg']
    if use_pdf_step:  # the step and key of the specification (TZ): sqrt(eps F)/(2 sqrt(K(1+k omega)))
        sg = math.sqrt(eps * V) / (2 * math.sqrt(K * p['nu']))
    z, tau = C.nearest_node(G, t, sg)
    if off is not None:  # worst node: exactly sg/2 from t* in every coordinate, in G-coordinates
        tau = np.linalg.solve(G, (G @ t / sg + off) * sg)
    table = C.clipped_dp(m, d, B, Sf, G, tau, p['eta'], k, p['Q'])
    bestR, bestF = None, -1.0
    for (key, n), (val, U) in table.items():
        if n == 0:
            continue
        f, _, _ = C.flo_exact(m, d, B, Sf, sorted(U))
        if f > bestF:
            bestF, bestR = f, U
    return F, S, bestF, bestR, len(table), p, float(np.max(np.abs(z))), t, G


cases, viol, tot_tab, max_ratio_tab = 0, 0, 0, 0.0
worst_gap = 0.0
for trial in range(300):
    M = int(rng.integers(5, 11))
    K = int(rng.integers(1, 4))
    k = int(rng.integers(1, 4))
    eps = float(rng.choice([0.05, 0.1, 0.2, 0.4]))
    sb = float(rng.choice([0.3, 1.0, 3.0, 6.0]))
    m, d, B, Sf = random_instance(M, K, sb)
    if m.max() <= 0:
        continue
    F, S, bestF, bestR, ntab, p, zmax, t, G = run_dp_guarantee(m, d, B, Sf, k, eps)
    if F <= 1e-9:
        continue
    cases += 1
    ok = bestF >= (1 - 2 * eps) * F - 1e-9
    viol += (not ok)
    worst_gap = max(worst_gap, (F - bestF) / F / (2 * eps))
    bound = (k + 1) * (2 * p['Q'] + 1) ** K + 1
    assert ntab <= bound
    assert zmax <= p['Z'] + 1e-9, (zmax, p['Z'])
    max_ratio_tab = max(max_ratio_tab, ntab / bound)
print('T3 DP guarantee: %d cases, violations %d, worst loss/(2εF) = %.3f, max table/bound = %.3g'
      % (cases, viol, worst_gap, max_ratio_tab))
assert viol == 0

# the node in the worst position (shift by sg/2 in every G-coordinate) and large leverages omega
viol2, cases2, worst2 = 0, 0, 0.0
for trial in range(200):
    M = int(rng.integers(5, 10))
    K = int(rng.integers(1, 3))
    k = int(rng.integers(1, 4))
    eps = float(rng.choice([0.1, 0.2, 0.4]))
    m, d, B, Sf = random_instance(M, K, float(rng.choice([2.0, 5.0, 10.0])))
    if m.max() <= 0:
        continue
    off = rng.choice([-0.5, 0.5], size=K)
    F, S, bestF, bestR, ntab, p, zmax, t, G = run_dp_guarantee(m, d, B, Sf, k, eps, off=off)
    if F <= 1e-9:
        continue
    cases2 += 1
    viol2 += bestF < (1 - 2 * eps) * F - 1e-9
    worst2 = max(worst2, (F - bestF) / F / (2 * eps))
print('T3b node at distance exactly sg/2 per coordinate: %d cases, violations %d, worst loss/(2εF) = %.3f'
      % (cases2, viol2, worst2))
print('OK')
