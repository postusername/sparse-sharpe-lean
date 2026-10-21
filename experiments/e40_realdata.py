"""E40: the real data of Sections 6.1 and 6.2 (Tables 6.1 and 6.2, the paragraphs "The certificate at scale" and
"What the guarantee buys").  Data and models: data_real.py (window July 2016 - June 2026 for the industries).

  python3 -I e40_realdata.py optima     -> results/E40/optima.json   (Table 6.1 and the text of Section 6.1)
  python3 -I e40_realdata.py instances  -> results/E40/instances.jsonl (one line per binding instance, Section 6.2)

Table 6.1: FF49-K1, -K3, -K5 and HS-PCA1 (port1, one factor) with k in {3, 5}: the optimum by enumeration of all
supports with k assets (F_LO is monotone), forward greedy selection, the prefix of the Treynor ranking (one factor),
the optimality test of Theorem 5.7 at the dual point of the optimum, and for the instances in which it fails the
certificate with greedy selection with exchanges and branch and bound.
Section 6.2: the industries (K = 1, 3, 5), the five OR-Library portfolio data sets (K = 1, 3, 5), the S&P 500 and
the Russell 3000 (K = 1, 3, 5, 10), k in {5, 10, 20, 50} below n_LO, the number of names of the unconstrained
long-only tangency portfolio: greedy selection, greedy selection with exchanges (F_h), the optimality test at its
dual point, the relaxation G*_k, the certificate gap 1 - F_h/G*_k, branch and bound (relative tolerance 1e-9), and the
screening rules: the k largest Sharpe ratios m_i/sqrt(V_ii), the k largest m_i/sqrt(d_i), the k largest weights of
the unconstrained long-only tangency portfolio, and (one factor) the k largest Treynor ratios, each with its
long-only optimum.  For one factor the sign of the statistical factor is chosen so that the loadings sum to a
positive number (V does not change).
"""
import itertools
import json
import math
import os
import sys
import time

import numpy as np
from scipy.optimize import minimize

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import data_real as D
import e34_localized as E
import e35_scale as S35
import e41_random as R41

OUT = os.path.join(HERE, 'results', 'E40')
EPS = 0.05


def load(name, K):
    mdl = D.model(name, K)
    if K == 1 and mdl['B'].sum() < 0:
        mdl['B'] = -mdl['B']
    return mdl


def lo_tangency(m, d, B, Sf):
    """The unconstrained long-only tangency portfolio through its dual point (Theorem 2.1 with S = all assets)."""
    P = np.linalg.inv(Sf)
    P = (P + P.T) / 2

    def f(t):
        r = np.maximum(m - B @ t, 0.0)
        return t @ P @ t + np.sum(r * r / d), 2 * P @ t - 2 * B.T @ (r / d)
    res = minimize(f, np.zeros(B.shape[1]), jac=True, method='L-BFGS-B',
                   options={'maxiter': 10000, 'gtol': 1e-14, 'ftol': 1e-16})
    w = np.maximum(m - B @ res.x, 0.0) / d
    return w, res.x


def treynor_order(m, B):
    beta = B[:, 0]
    ratio = np.where(beta > 0, m / np.where(beta > 0, beta, 1.0), np.where(m > 0, np.inf, -np.inf))
    return np.argsort(-ratio, kind='stable'), ratio


def sr_annual(F, name):
    return math.sqrt(max(F, 0.0)) * math.sqrt(12 if name.startswith('FF49') else 52)


def label(mdl, i):
    return mdl['names'][i] if mdl['names'] is not None else 'HS%d' % (i + 1)


def optima():
    rows, text = [], {}
    for name, K in [('FF49', 1), ('FF49', 3), ('FF49', 5), ('port1', 1)]:
        mdl = load(name, K)
        m, d, B, Sf = mdl['m'], mdl['d'], mdl['B'], mdl['Sf']
        P = np.linalg.inv(Sf)
        P = (P + P.T) / 2
        M = len(m)
        nm = 'HS-PCA1' if name == 'port1' else mdl['name']
        for k in (3, 5):
            t0 = time.perf_counter()
            opt, Sopt = max((E.flo(m, d, B, Sf, S)[0], S) for S in itertools.combinations(range(M), k))
            tenum = time.perf_counter() - t0
            F, w, tdual = E.flo(m, d, B, Sf, Sopt)
            wclip = np.maximum(m[list(Sopt)] - B[list(Sopt)] @ tdual, 0.0) / d[list(Sopt)]
            s = E.scores(m, d, B, tdual)
            test = set(np.argsort(-s, kind='stable')[:k].tolist()) == set(Sopt)
            Fg, Sg = R41.greedy_only(m, d, B, Sf, k)
            row = dict(model=nm, k=k, support=[label(mdl, i) for i in Sopt], weights=(w / w.sum()).tolist(),
                       SR=sr_annual(opt, nm), greedy=math.sqrt(Fg / opt), test=bool(test), t_enum=tenum,
                       clip_err=float(np.abs(wclip - w).max()), t0=tdual.tolist(), opt=opt)
            if K == 1:
                order, ratio = treynor_order(m, B)
                T = order[:k]
                Ft = E.flo(m, d, B, Sf, list(T))[0]
                row['treynor'] = math.sqrt(Ft / opt)
                q = m / np.sqrt(d)
                out = np.setdiff1d(np.arange(M), T)
                row['prefix_hypothesis'] = bool(q[T].min() >= q[out].max())
                held = set(Sopt)
                above = [i for i in range(M) if i not in held and ratio[i] > tdual[0]]
                row['above_cutoff'] = [label(mdl, i) for i in above]
                row['above_cutoff_treynor'] = {label(mdl, i): float(ratio[i]) for i in list(above) + list(Sopt)}
            if not test:
                Fh, Sh = E.greedy_swap(m, d, B, Sf, k)
                t_h = E.flo(m, d, B, Sf, Sh)[2]
                G, that = E.relaxation(m, d, B, Sf, k)
                G = min(G, E.gk(m, d, B, P, k, t_h))
                vb, Sb, nb, tb, fin = S35.bnb(m, d, B, Sf, k, Fh, Sh, t_h, time_limit=3600.0)
                row.update(cert_gap=1 - Fh / G, bnb_nodes=nb, greedy_swap_opt=bool(Fh >= vb * (1 - 1e-9)))
            if nm == 'FF49-K1' and k == 5:
                x = w / w.sum()
                Vs = np.diag(d[list(Sopt)]) + B[list(Sopt)] @ Sf @ B[list(Sopt)].T
                vol = math.sqrt(12 * x @ Vs @ x)
                text['voltarget'] = dict(fraction=0.10 / vol, ret=0.10 * row['SR'])
            rows.append(row)
            print(json.dumps(row), flush=True)
    os.makedirs(OUT, exist_ok=True)
    json.dump(dict(rows=rows, text=text), open(os.path.join(OUT, 'optima.json'), 'w'), indent=1)


def instances():
    univ = [('FF49', (1, 3, 5))] + [('port%d' % i, (1, 3, 5)) for i in range(1, 6)] + \
           [('SP500', (1, 3, 5, 10)), ('Russell', (1, 3, 5, 10))]
    for name, Ks in univ:
        for K in Ks:
            mdl = load(name, K)
            m, d, B, Sf = mdl['m'], mdl['d'], mdl['B'], mdl['Sf']
            P = np.linalg.inv(Sf)
            P = (P + P.T) / 2
            M = len(m)
            wlo, tlo = lo_tangency(m, d, B, Sf)
            nlo = int((wlo > 0).sum())
            for k in (5, 10, 20, 50):
                rec = dict(universe=name, model=mdl['name'], M=M, K=K, k=k, n_lo=nlo, omega=mdl['omega'])
                if k >= nlo:
                    rec['binding'] = False
                    print(json.dumps(rec), flush=True)
                    continue
                rec['binding'] = True
                t0 = time.perf_counter()
                Fg, Sg = R41.greedy_only(m, d, B, Sf, k)
                rec['t_greedy'] = time.perf_counter() - t0
                t0 = time.perf_counter()
                Fh, Sh = E.greedy_swap(m, d, B, Sf, k)
                rec['t_swap'] = time.perf_counter() - t0
                t_h = E.flo(m, d, B, Sf, Sh)[2]
                s = E.scores(m, d, B, t_h)
                rec['test'] = bool(set(np.argsort(-s, kind='stable')[:k].tolist()) == set(Sh) and len(Sh) == k)
                t0 = time.perf_counter()
                G, that = E.relaxation(m, d, B, Sf, k)
                G = min(G, E.gk(m, d, B, P, k, t_h))
                rec['t_relax'] = time.perf_counter() - t0
                vb, Sb, nb, tb, fin = S35.bnb(m, d, B, Sf, k, Fh, Sh, t_h, time_limit=3600.0)
                rec.update(Fg=Fg, Fh=Fh, G=G, gap=1 - Fh / G, bnb=vb, bnb_nodes=nb, bnb_time=tb, bnb_done=fin,
                           greedy_swap_opt=bool(Fh >= vb * (1 - 1e-9)))
                Vii = d + np.einsum('ij,jk,ik->i', B, Sf, B)
                rules = dict(top_sr=np.argsort(-(m / np.sqrt(Vii)), kind='stable')[:k],
                             top_score0=np.argsort(-(m / np.sqrt(d)), kind='stable')[:k],
                             truncation=np.argsort(-wlo, kind='stable')[:k])
                if K == 1:
                    rules['treynor'] = treynor_order(m, B)[0][:k]
                    rules['treynor_naive'] = np.argsort(-(m / B[:, 0]), kind='stable')[:k]
                for key, Ssel in rules.items():
                    rec[key] = E.flo(m, d, B, Sf, list(Ssel))[0]
                rec['t_total'] = rec['t_greedy'] + rec['t_swap'] + rec['t_relax'] + tb
                rec['sr_opt_annual'] = math.sqrt(vb) * math.sqrt(12 if name == 'FF49' else 52)
                print(json.dumps(rec), flush=True)


if __name__ == '__main__':
    {'optima': optima, 'instances': instances}[sys.argv[1]]()
