"""E35: where the certificate fails, at scale (Section 6.4).

Stress regime of Section 6.3 (e34_localized.stress_instance), M in {50, 200, 1000, 2000}, K in {1, 2, 3},
k in {3, 5, 10}. For each instance:
  * greedy selection with exchanges (F_h), the relaxation G*_k = min_t g_k(t) (Clarabel) and the certificate
    F_h >= (1 - 2 eps) G*_k, eps = 0.05;
  * branch and bound of Section 5.3 (the reference: exact up to the relative tolerance 1e-9; time limit);
  * the localized scheme with pruning (Theorem 5.24) with the constants of Definition 4.7: the number of
    localized nodes over all guesses by the coordinatewise condition (an upper bound), and the run itself when
    the nodes are few.
The MIQP baseline is e35_miqp.py. (The first version of this script also called an MIQP solver; in the run of
the paper that call failed with a NameError, so the JSON lines of results/E35/ carry a field 'miqp' with the
error, or with a Gurobi result for M = 50 from a formulation without the link w_i <= U_i z_i; both are ignored and
superseded by e35_miqp.py. The call has been removed.)
Usage:  python3 -I e35_scale.py <M> <K> <k> <n> [<seed>] [--bnb seconds]   -> one JSON line per instance on stdout.
Driver: e35_driver.sh; aggregation: e35_table.py -> tables/e35_table.md and tables/e35_table.tex.
"""
import json
import math
import sys
import time

import numpy as np
from scipy.optimize import minimize

sys.path.insert(0, __file__.rsplit('/', 1)[0] if '/' in __file__ else '.')
import e34_localized as E

EPS = 0.05


# ---------------------------------------------------------------------------- branch and bound (Section 5.3)

def bnb(m, d, B, Sf, k, Fh, Sh, t_h, tol=1e-9, time_limit=600.0):
    """Depth-first branch and bound with the bound of Proposition 5.8, minimized locally over t from the point
    of the parent; branching order: decreasing score at the dual point of the heuristic; include first.
    Returns (value, support, nodes, time, finished)."""
    M, K = B.shape
    P = np.linalg.inv(Sf)
    P = (P + P.T) / 2
    order = np.argsort(-E.scores(m, d, B, t_h), kind='stable')
    pos = np.empty(M, dtype=int)
    pos[order] = np.arange(M)
    best, bestS = Fh, tuple(sorted(Sh))
    t0 = time.time()
    nodes = 0
    stack = [((), 0, t_h.copy())]
    finished = True
    while stack:
        if time.time() - t0 > time_limit:
            finished = False
            break
        F, p, tpar = stack.pop()
        nodes += 1
        r = k - len(F)
        Fl = list(F)
        R = order[p:]
        if r == 0 or len(R) == 0:
            v = E.flo(m, d, B, Sf, F)[0] if F else 0.0
            if v > best:
                best, bestS = v, tuple(sorted(F))
            continue

        def h(t):
            rr = m - B @ t
            s = np.maximum(rr, 0.0) ** 2 / d
            sR = s[R]
            if r < len(R):
                idx = np.argpartition(sR, -r)[-r:]
                top = R[idx]
            else:
                top = R
            act = np.concatenate([np.array(Fl, dtype=int), top])
            val = float(t @ P @ t + s[act].sum())
            w = np.maximum(rr[act], 0.0) / d[act]
            g = 2 * P @ t - 2 * B[act].T @ w
            return val, g

        res = minimize(h, tpar, jac=True, method='L-BFGS-B', options={'maxiter': 60, 'gtol': 1e-12})
        tb = res.x if res.fun <= h(tpar)[0] else tpar
        bound = min(res.fun, h(tpar)[0])
        # the completion by the r free assets of largest score at tb
        s = E.scores(m, d, B, tb)
        sR = s[R]
        top = R[np.argpartition(sR, -r)[-r:]] if r < len(R) else R
        U = tuple(sorted(Fl + [int(x) for x in top]))
        v = E.flo(m, d, B, Sf, U)[0]
        if v > best:
            best, bestS = v, U
        if bound <= best * (1 + tol):
            continue
        b = int(order[p])
        stack.append((F, p + 1, tb))                 # exclude b (explored second)
        stack.append((F + (b,), p + 1, tb))          # include b (explored first)
    return best, bestS, nodes, time.time() - t0, finished


# ---------------------------------------------------------------------------------------------- one instance

def run_instance(rng, M, K, k, bnb_limit=600.0, node_cap=400, scheme_time=600.0):
    m, d, B, Sf = E.stress_instance(rng, M, K)
    rec = dict(M=M, K=K, k=k)
    if m.max() <= 0:
        rec['skip'] = True
        return rec
    omega = float(E.leverages(d, B, Sf).max())
    P = np.linalg.inv(Sf)
    P = (P + P.T) / 2
    t0 = time.time()
    Fh, Sh = E.greedy_swap(m, d, B, Sf, k)
    rec['t_greedy'] = time.time() - t0
    t_h = E.flo(m, d, B, Sf, Sh)[2]
    t0 = time.time()
    gval, that = E.relaxation(m, d, B, Sf, k)
    gval = min(gval, E.gk(m, d, B, P, k, t_h))
    rec['t_relax'] = time.time() - t0
    rec.update(omega=omega, Fh=Fh, G=gval, gap=1 - Fh / gval, cert=bool(Fh >= (1 - 2 * EPS) * gval))
    # the optimality test at the dual point of the heuristic
    s = E.scores(m, d, B, t_h)
    topk = set(np.argsort(-s)[:k].tolist())
    rec['test'] = bool(set(Sh) == topk and len(Sh) == k)
    # branch and bound
    vb, Sb, nb, tb, fin = bnb(m, d, B, Sf, k, Fh, Sh, t_h, time_limit=bnb_limit)
    rec.update(bnb=vb, bnb_nodes=nb, bnb_time=tb, bnb_done=fin, greedy_opt=bool(Fh >= vb * (1 - 1e-9)))
    # the localized scheme: the number of nodes, and the run if they are few
    theta = Fh / (1 - 2 * EPS)
    J = max(0, math.ceil(math.log2(max(gval / Fh, 1.0))) - 1)
    G = np.linalg.cholesky(P).T
    Gt = G @ that
    nodes_total, cube_total = 0, 0
    for j in range(J + 1):
        p = E.params(EPS, Fh * 2 ** j, k, K, omega)
        _, cube, _ = E.loc_nodes(Gt, p['s'], p['Z'], gval, theta, K, count_only=True)
        cube_total += cube
    rec['loc_cube'] = cube_total
    if gval <= theta:
        rec.update(loc_nodes=0, loc_best=Fh, loc_time=0.0, loc_run=True)
    elif cube_total <= node_cap:
        out = E.localized_scheme(m, d, B, Sf, k, EPS, Fh, Sh, that, gval, omega, prune=True,
                                 node_cap=node_cap, time_cap=scheme_time)
        rec.update(loc_nodes=out['nodes'], loc_best=out['best'], loc_time=out['time'], loc_run=not out['skipped'],
                   loc_tables=out['tables'], loc_records=out['records'], loc_maxtable=out['maxtable'],
                   loc_pruned=out['pruned'] / max(1, out['generated']), loc_cands=out['cands'])
    else:
        rec.update(loc_nodes=None, loc_run=False)
    return rec


def main():
    M, K, k, n = map(int, sys.argv[1:5])
    seed = int(sys.argv[5]) if len(sys.argv) > 5 and not sys.argv[5].startswith('--') else 1000 * M + 10 * K + k
    bnb_limit = 600.0
    if '--bnb' in sys.argv:
        bnb_limit = float(sys.argv[sys.argv.index('--bnb') + 1])
    rng = np.random.default_rng(seed)
    for it in range(n):
        rec = run_instance(rng, M, K, k, bnb_limit=bnb_limit)
        rec['seed'] = seed
        rec['it'] = it
        print(json.dumps(rec), flush=True)


if __name__ == '__main__':
    main()
