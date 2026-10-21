"""E29: the saddle point of the relaxation, the certificate with k+K names and the rounding to exactly k names on the
real data, for Section 7.7 of the paper ("The relaxation, the certificate with k+K names and the rounding").  For the
models of data_real.py in the plan below (the industries FF49, window July 2016 - June 2026, and the Hang Seng data
port1 with K = 1, 3, 5 and k = 3, 5; the OR-Library data sets port2..port5 with k = 5, 10, 20; the S&P 500 and the
Russell 3000 with K = 1, 3, 5, 10 and k = 5, 10, 20, 50) it computes: (1) G*_k = min_t g_k(t) and a minimizer t*
(CVXPY with Clarabel), g_k(t) = t'Sf^{-1}t + (the sum of the k largest scores s_i(t)); (2) the support T of
Theorem 6.15, the union of H (the multipliers equal to 1) and I' (the f fractional ones): the assets with
s_i(t*) > sigma, sigma the k-th largest score, get the multiplier 1, and the multipliers lambda in [0,1]^E of the
assets E that tie at sigma are a vertex of the linear program sum lambda = k - #{s_i(t*) > sigma},
sum_E lambda_i w_i B_i = Sf^{-1}t* - (the sum of w_i B_i over the assets with s_i(t*) > sigma), so that at most K+1
of them are fractional, and T = {lambda > 0}; (3) the checks |T| <= k + K, F_LO(T) >= G*_k (the bicriteria
guarantee) and, where enumeration is possible, OPT(k) <= G*_k <= OPT(k+K); (4) the rounding of Theorem 6.18: among
the C(f, s) sets R that add to H a subset T' of I' with |T'| = s, the best one by objLO(R, w(t*)), its loss
G*_k - obj and the bound min(s, f-s) omega_I' sigma (sigma = s_i(t*) on I').  Run from this directory:
python3 -I e29_dual_rounding.py > results/E29/e29.log  (about 4 minutes on one core); writes
results/E29/results_E29.json, which e29_floor_bound.py reads.
"""
import itertools
import json
import math
import os
import sys
import time

import cvxpy as cp
import numpy as np
from scipy.optimize import linprog

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import clipped_dp as C
import data_real as D

OUT = os.path.join(HERE, 'results', 'E29')


def solve_relaxation(m, d, B, Sf, k):
    """min_t g_k(t) in the scale in which the median of d is 1 (g is invariant: t' = c t, m' = c m, d' = c² d, Σ_f' = c² Σ_f)."""
    M, K = B.shape
    c = 1.0 / math.sqrt(np.median(d))
    m1, d1, Sf1 = m * c, d * c * c, Sf * c * c
    P1 = np.linalg.inv(Sf1)
    P1 = (P1 + P1.T) / 2
    t = cp.Variable(K)
    mu = cp.Variable()
    z = cp.Variable(M, nonneg=True)
    r = m1 - B @ t
    cons = [cp.square(cp.pos(r[i])) / d1[i] <= z[i] + mu for i in range(M)]
    prob = cp.Problem(cp.Minimize(cp.quad_form(t, cp.psd_wrap(P1)) + k * mu + cp.sum(z)), cons)
    last = None
    for kw in (dict(solver=cp.CLARABEL, tol_gap_abs=1e-11, tol_gap_rel=1e-11, tol_feas=1e-11),
               dict(solver=cp.CLARABEL),
               dict(solver=cp.SCS, eps=1e-9, max_iters=200000)):
        try:
            prob.solve(**kw)
            if prob.status in ('optimal', 'optimal_inaccurate') and t.value is not None:
                break
        except Exception as e:  # noqa
            last = e
    if t.value is None:
        raise RuntimeError('solver failed: %r' % (last,))
    lam0 = np.array([c_.dual_value for c_ in cons]).reshape(-1)
    P = np.linalg.inv(Sf)
    P = (P + P.T) / 2
    return float(prob.value), t.value / c, lam0, P


def lp_vertex(B, w, P, tst, Hh, E, k):
    """A vertex λ_E ∈ [0,1], Σλ = k − |H|, Σ_E λ_i w_i B_i = P t* − Σ_H w_i B_i (a linear program with slacks)."""
    M, K = B.shape
    nE = len(E)
    if nE == 0:
        return np.array([]), 0.0
    Aeq = np.zeros((K + 1, nE + 2 * K))
    Aeq[0, :nE] = 1.0
    Aeq[1:, :nE] = (w[E][:, None] * B[E]).T
    Aeq[1:, nE:nE + K] = np.eye(K)
    Aeq[1:, nE + K:] = -np.eye(K)
    rhs = P @ tst
    if len(Hh):
        rhs = rhs - (w[Hh][:, None] * B[Hh]).sum(0)
    beq = np.concatenate([[k - len(Hh)], rhs])
    cvec = np.concatenate([np.zeros(nE), np.ones(2 * K)])
    res = linprog(cvec, A_eq=Aeq, b_eq=beq, bounds=[(0, 1)] * nE + [(0, None)] * (2 * K), method='highs-ds')
    if res.status != 0:
        return None, np.inf
    return res.x[:nE], float(res.fun)


def build_support(m, d, B, Sf, P, tst, G, k):
    """Tries tolerances for the ties s_i(t*) = σ: takes the first one for which the LP is feasible and F_LO(T) ≥ G*(1−1e-7)
    (otherwise the best candidate found)."""
    M, K = B.shape
    w = np.maximum(m - B @ tst, 0) / d
    s = d * w ** 2
    sig = np.sort(s)[::-1][k - 1]
    best = None
    for tol in (1e-10, 1e-9, 1e-8, 1e-7, 1e-6, 1e-5, 1e-4, 1e-3, 1e-2):
        Hh = np.where(s > sig * (1 + tol))[0]
        E = np.where((s <= sig * (1 + tol)) & (s >= sig * (1 - tol)))[0]
        if len(Hh) >= k:
            continue
        lamE, slack = lp_vertex(B, w, P, tst, Hh, E, k)
        if lamE is None or slack > 1e-5 * (1 + np.abs(P @ tst).max()):
            continue
        frac = [E[j] for j in range(len(E)) if 1e-7 < lamE[j] < 1 - 1e-7]
        one = [E[j] for j in range(len(E)) if lamE[j] >= 1 - 1e-7]
        T = sorted(set(Hh.tolist()) | set(one) | set(frac))
        FT = C.flo_exact(m, d, B, Sf, T)[0]
        cand = (FT, T, list(Hh), one, frac, tol, slack)
        if best is None or FT > best[0]:
            best = cand
        if FT >= G * (1 - 1e-7):
            return cand
    return best


def experiment(name, K, k, exact=False, rounding=True):
    t0 = time.time()
    mdl = D.model(name, K)
    m, d, B, Sf, M = mdl['m'], mdl['d'], mdl['B'], mdl['Sf'], mdl['M']
    om_i = np.einsum('ij,jk,ik->i', B, Sf, B) / d
    G, tst, lam0, P = solve_relaxation(m, d, B, Sf, k)
    Gm = C.gram_root(P)
    res = build_support(m, d, B, Sf, P, tst, G, k)
    if res is None:
        raise RuntimeError('no support built')
    FT, T, Hh, one, frac, tol, slack = res
    w = np.maximum(m - B @ tst, 0) / d
    s = d * w ** 2
    # the unconstrained long-only optimum (on the whole universe): an upper bound for every F_LO
    Fall = C.flo_exact(m, d, B, Sf, list(range(M)))[0]
    row = dict(model=mdl['name'], M=M, K=K, k=k, Gstar=float(G), F_T=float(FT), size_T=len(T), H=len(Hh),
               f=len(frac), Fall=float(Fall), omega=float(om_i.max()), tol=float(tol))
    row['ok_size'] = len(T) <= k + K
    row['ok_value'] = FT >= G * (1 - 1e-5)
    if exact and math.comb(M, k) <= 250000:
        Fk, Sk, _ = C.opt_bruteforce(m, d, B, Sf, k)
        row.update(OPTk=float(Fk), ok_lower=bool(Fk <= G * (1 + 1e-6)))
        if math.comb(M, min(M, k + K)) <= 300000:
            FkK, _, _ = C.opt_bruteforce(m, d, B, Sf, min(M, k + K))
            row.update(OPTkK=float(FkK), ok_chain=bool(Fk <= G * (1 + 1e-6) and G <= FkK * (1 + 1e-6)))
    if rounding and frac:
        s_int = int(round(k - len(Hh) - len(one)))
        f = len(frac)
        best = -1.0
        for Tp in itertools.combinations(frac, s_int):
            R = sorted(set(Hh) | set(one) | set(Tp))
            wc = np.maximum(m - B @ tst, 0) / d
            val = C.obj_lo(m, d, B, Sf, R, wc)
            best = max(best, val)
        sigma = float(np.mean(s[frac])) if frac else 0.0
        om_I = float(om_i[frac].max())
        row.update(round_loss=float(G - best), s=s_int, bound_min=float(min(s_int, f - s_int) * om_I * sigma),
                   bound_K=float(K * om_I * sigma), sigma=sigma, om_I=om_I)
        row['ok_round'] = row['round_loss'] <= row['bound_min'] * (1 + 1e-5) + 1e-9
    row['sec'] = time.time() - t0
    msg = '%-12s M=%4d K=%2d k=%2d  G*=%.6g  F(T)=%.6g |T|=%d (H=%d, f=%d) k+K=%d  size_ok=%s value_ok=%s' % (
        mdl['name'], M, K, k, G, FT, len(T), len(Hh), len(frac), k + K, row['ok_size'], row['ok_value'])
    if 'OPTk' in row:
        msg += '  OPT(k)=%.6g' % row['OPTk']
    if 'OPTkK' in row:
        msg += ' OPT(k+K)=%.6g chain=%s' % (row['OPTkK'], row['ok_chain'])
    if 'round_loss' in row:
        msg += '  round loss=%.3g <= min(s,f−s)ωσ=%.3g (%s)' % (row['round_loss'], row['bound_min'], row['ok_round'])
    print(msg + '  [%.0fs]' % row['sec'], flush=True)
    return row


if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    rows = []
    plan = []
    for nm, Ks in [("FF49", [1, 3, 5]), ("port1", [1, 3, 5])]:
        for K in Ks:
            for k in (3, 5):
                plan.append((nm, K, k, True))
    for nm, Ks in [("port2", [1, 3]), ("port3", [1, 3]), ("port4", [1, 3, 5]), ("port5", [1, 3, 5])]:
        for K in Ks:
            for k in (5, 10, 20):
                plan.append((nm, K, k, False))
    for nm, Ks in [("SP500", [1, 3, 5, 10]), ("Russell", [1, 3, 5, 10])]:
        for K in Ks:
            for k in (5, 10, 20, 50):
                plan.append((nm, K, k, False))
    for nm, K, k, ex in plan:
        try:
            rows.append(experiment(nm, K, k, exact=ex))
        except Exception as e:  # noqa
            print('ERROR', nm, K, k, repr(e)[:200], flush=True)
    with open(os.path.join(OUT, 'results_E29.json'), 'w') as fh:
        json.dump(rows, fh, indent=1, default=float)
    print('Total instances: %d; size |T| ≤ k+K: %d; F_LO(T) ≥ G*: %d; chain OPT(k) ≤ G* ≤ OPT(k+K): %d of %d checked; '
          'rounding loss ≤ min(s,f−s)ωσ: %d of %d' % (
              len(rows), sum(r['ok_size'] for r in rows), sum(r['ok_value'] for r in rows),
              sum(1 for r in rows if r.get('ok_chain')), sum(1 for r in rows if 'ok_chain' in r),
              sum(1 for r in rows if r.get('ok_round')), sum(1 for r in rows if 'ok_round' in r)))
