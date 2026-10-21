"""E34: the localized scheme (Theorem 5.24) with pruning inside the dynamic program (Lemma 5.23).

Library (used by e35_scale.py and the later scripts) and the one-step checks of Section 6.4 ("One-step checks"):

  (L4 and P1 below are the names used in the code and in the log: the localized nodes of Definition 5.22 and the
  pruning of Lemma 5.23.)
  * L4, one step: for every support S with F_LO(S) >= theta, the node obtained by rounding G t0(S)/s
    coordinatewise lies in the localized set {z : |s z_l - (G that)_l| <= r + s/2, ||s z - G that|| <= r + s sqrt(K)/2},
    r = sqrt(g_k(that) - theta) (no violation allowed);  control: radius r x 0.5 (must break somewhere);
  * P1, one step: at a node tau, the pruned table keeps a representative (same key, score sum not smaller) of every
    S with |S| <= k, Q_S(tau) >= theta and keys in the box (no violation allowed);  control: threshold theta x 1.1
    (must break somewhere);  measured: the share of the records removed by pruning;
  * the whole localized scheme with the constants of Definition 4.7 and pruning: best candidate / optimum.

Instances: the stress regime of Section 6.3 (factor covariance and loadings unstructured Gaussian, R_i^2 ~ U(0.5, 0.95),
expected returns uniform multiples of the volatilities, unrelated to the factors), M = 16 so that every support can
be enumerated. Run:  python3 -I e34_localized.py > e34.log
"""
import itertools
import math
import sys
import time
import warnings

warnings.filterwarnings('ignore', message='Solution may be inaccurate')

import numpy as np
from scipy.optimize import nnls, minimize

# ------------------------------------------------------------------------------------------------ the model


def stress_instance(rng, M, K, regime='stress'):
    """Random factor model. 'stress': loadings and factor covariance unstructured Gaussian, R_i^2 ~ U(0.5, 0.95),
    m_i = u_i * sqrt(V_ii) with u_i ~ U(-0.1, 0.3) (unrelated to the loadings). 'calibrated': m = B lambda + small
    alpha, as in Section 6.3."""
    A = rng.normal(size=(K, K))
    Sf = A @ A.T / K + 0.2 * np.eye(K)
    B = rng.normal(size=(M, K))
    sysv = np.einsum('ij,jk,ik->i', B, Sf, B)
    R2 = rng.uniform(0.5, 0.95, size=M)
    d = sysv * (1 - R2) / R2
    if regime == 'stress':
        m = rng.uniform(-0.1, 0.3, size=M) * np.sqrt(sysv + d)
    else:
        lam = np.r_[0.3, 0.1 * np.ones(K - 1)] if K > 1 else np.r_[0.3]
        m = B @ lam + rng.normal(size=M) * 0.05 * np.sqrt(d)
    return m, d, B, Sf


def leverages(d, B, Sf):
    return np.einsum('ij,jk,ik->i', B, Sf, B) / d


def flo(m, d, B, Sf, S):
    """F_LO(S), the optimal weights on S and the dual point t0 = Sf B_S' w (NNLS on the Cholesky factor)."""
    S = list(S)
    if not S:
        return 0.0, np.zeros(0), np.zeros(B.shape[1])
    BS = B[S]
    V = np.diag(d[S]) + BS @ Sf @ BS.T
    L = np.linalg.cholesky(V)
    c = np.linalg.solve(L, m[S])
    w, res = nnls(L.T, c)
    val = float(c @ c - res ** 2)
    return max(val, 0.0), w, Sf @ BS.T @ w


def scores(m, d, B, t):
    return np.maximum(m - B @ t, 0.0) ** 2 / d


def gk(m, d, B, P, k, t):
    s = scores(m, d, B, t)
    top = np.partition(s, -k)[-k:] if k < len(s) else s
    return float(t @ P @ t + top.sum())


def gk_grad(m, d, B, P, k, t):
    r = m - B @ t
    s = np.maximum(r, 0.0) ** 2 / d
    idx = np.argpartition(s, -k)[-k:] if k < len(s) else np.arange(len(s))
    val = float(t @ P @ t + s[idx].sum())
    w = np.maximum(r[idx], 0.0) / d[idx]
    grad = 2 * P @ t - 2 * B[idx].T @ w
    return val, grad


def relaxation(m, d, B, Sf, k):
    """G*_k = min_t g_k(t) as a second-order cone program (Clarabel through CVXPY), scaled so that median(d) = 1."""
    import cvxpy as cp
    M, K = B.shape
    c = 1.0 / math.sqrt(np.median(d))
    m1, d1, Sf1 = m * c, d * c * c, Sf * c * c
    P1 = np.linalg.inv(Sf1)
    P1 = (P1 + P1.T) / 2
    t = cp.Variable(K)
    mu = cp.Variable()
    z = cp.Variable(M, nonneg=True)
    r = m1 - B @ t
    cons = [cp.multiply(cp.square(cp.pos(r)), 1.0 / d1) <= z + mu]
    prob = cp.Problem(cp.Minimize(cp.quad_form(t, cp.psd_wrap(P1)) + k * mu + cp.sum(z)), cons)
    for kw in (dict(solver=cp.CLARABEL, tol_gap_abs=1e-10, tol_gap_rel=1e-10, tol_feas=1e-10),
               dict(solver=cp.CLARABEL)):
        try:
            prob.solve(**kw)
            if prob.status in ('optimal', 'optimal_inaccurate') and t.value is not None:
                break
        except Exception:  # noqa
            pass
    P = np.linalg.inv(Sf)
    P = (P + P.T) / 2
    if t.value is None:
        # the conic solver failed (it happens at M = 2000 in rare instances): fall back to L-BFGS from t = 0;
        # every point gives a valid bound, only its quality is affected
        tt = np.zeros(K)
    else:
        tt = t.value / c
    # polish with L-BFGS from the conic solution (every point gives a valid bound; keep the smaller value)
    res = minimize(lambda x: gk_grad(m, d, B, P, k, x), tt, jac=True, method='L-BFGS-B',
                   options={'maxiter': 200, 'gtol': 1e-14, 'ftol': 1e-16})
    if res.fun < gk(m, d, B, P, k, tt):
        tt = res.x
    return gk(m, d, B, P, k, tt), tt


def greedy_swap(m, d, B, Sf, k, max_rounds=50):
    """Greedy forward selection with exact values, improved by exchanges of one asset (first improvement)."""
    M = len(m)
    S, best = [], 0.0
    for _ in range(k):
        cand, cv = None, best
        for i in range(M):
            if i in S:
                continue
            v = flo(m, d, B, Sf, S + [i])[0]
            if v > cv + 1e-15:
                cv, cand = v, i
        if cand is None:
            break
        S.append(cand)
        best = cv
    for _ in range(max_rounds):
        improved = False
        for a in range(len(S)):
            for i in range(M):
                if i in S:
                    continue
                T = S.copy()
                T[a] = i
                v = flo(m, d, B, Sf, T)[0]
                if v > best * (1 + 1e-12) + 1e-15:
                    S, best, improved = T, v, True
                    break
            if improved:
                break
        if not improved:
            break
    return best, tuple(sorted(S))


def brute_force(m, d, B, Sf, k):
    M = len(m)
    best, bS = 0.0, ()
    for S in itertools.combinations(range(M), min(k, M)):
        v = flo(m, d, B, Sf, S)[0]
        if v > best:
            best, bS = v, S
    return best, bS


# ------------------------------------------------------------------------------------------ the scheme


def params(eps, V, k, K, omega):
    """Definition 4.7: key width eta, grid step s, key box Q, node radius Z (as in the Lean definitions)."""
    nu = 1 + k * omega
    eta = math.sqrt(eps * V / 2) / (k * math.sqrt(K))
    s = math.sqrt(2 * eps * V) / (nu * math.sqrt(K))
    Q = k + math.ceil(math.sqrt(5 * omega * k ** 3 * K / eps))
    Z = math.ceil(nu * math.sqrt(K / eps) + 0.5)
    return dict(nu=nu, eta=eta, s=s, Q=Q, Z=Z)


def loc_nodes(Gt, s, Z, gval, theta, K, radius_factor=1.0, count_only=False, cap=None):
    """The localized nodes of Definition 5.22: none if g <= theta; otherwise the nodes z, |z_l| <= Z, with
    |s z_l - (G that)_l| <= r + s/2 for all l and ||s z - G that|| <= r + s sqrt(K)/2, r = sqrt(g - theta)
    (times radius_factor for the control). Returns (list of z or None, count of the cube, count after the ball)."""
    if gval <= theta:
        return [], 0, 0
    r = math.sqrt(gval - theta) * radius_factor
    lo = np.maximum(np.ceil((Gt - r - s / 2) / s), -Z).astype(np.int64)
    hi = np.minimum(np.floor((Gt + r + s / 2) / s), Z).astype(np.int64)
    if np.any(hi < lo):
        return [], 0, 0
    cube = int(np.prod((hi - lo + 1).astype(float)))
    if count_only or (cap is not None and cube > cap):
        return None, cube, None
    axes = [np.arange(lo[l], hi[l] + 1) for l in range(K)]
    grid = np.array(np.meshgrid(*axes, indexing='ij')).reshape(K, -1).T
    rho = r + s * math.sqrt(K) / 2
    keep = np.sum((s * grid - Gt) ** 2, axis=1) <= rho ** 2 * (1 + 1e-12)
    return grid[keep], cube, int(keep.sum())


def node_point(Ginv, s, z):
    return Ginv @ (s * z)


def top_suffix(svals, order, k):
    """top[j][r] = the largest sum of at most r scores among the assets order[j:], r = 0..k (O(Mk))."""
    M = len(order)
    top = np.zeros((M + 1, k + 1))
    best = []  # the k largest of the suffix, sorted decreasingly
    for j in range(M - 1, -1, -1):
        v = svals[order[j]]
        best.append(v)
        best.sort(reverse=True)
        del best[k:]
        cs = np.concatenate([[0.0], np.cumsum(best)])
        top[j, :len(cs)] = cs
        top[j, len(cs):] = cs[-1]
    return top


def pruned_table(m, d, B, Sf, G, P, tau, eta, Q, k, theta=None, order=None, stats=None, keep_sets=True):
    """Algorithm 4.1 at the node tau, vectorized, with the pruning of Lemma 5.23 (theta=None: no pruning).

    After the step for asset order[j], a record U is discarded if tau'P tau + sum_U s + top_{k-|U|}(order[j+1:]) < theta.
    Records: keys (T x (K+1) int64: rounded vector sum and |U|), values (sum of scores), members (T x k, -1 padded).
    Returns (keys, vals, members)."""
    M, K = B.shape
    w = np.maximum(m - B @ tau, 0.0) / d
    s = d * w ** 2
    v = (G @ Sf @ B.T * w).T                     # M x K: v_i = w_i G Sf B_i
    kv = np.floor(v / eta + 1e-12).astype(np.int64)
    if order is None:
        order = np.argsort(-s, kind='stable')     # the theorem holds for every order
    base = float(tau @ P @ tau)
    top = top_suffix(s, order, k) if theta is not None else None
    keys = np.zeros((1, K + 1), dtype=np.int64)
    vals = np.zeros(1)
    mem = -np.ones((1, k), dtype=np.int64)
    st = dict(generated=0, boxed=0, pruned=0, merged=0, maxtable=1)
    for j, i in enumerate(order):
        can = keys[:, K] < k
        nk = keys[can].copy()
        nk[:, :K] += kv[i]
        nk[:, K] += 1
        nv = vals[can] + s[i]
        nm = mem[can].copy()
        if len(nm):
            nm[np.arange(len(nm)), keys[can, K]] = i
        st['generated'] += len(nk)
        inbox = np.all(np.abs(nk[:, :K]) <= Q, axis=1)
        st['boxed'] += int((~inbox).sum())
        nk, nv, nm = nk[inbox], nv[inbox], nm[inbox]
        K2 = np.vstack([keys, nk])
        V2 = np.concatenate([vals, nv])
        M2 = np.vstack([mem, nm])
        if theta is not None:
            rem = top[j + 1]                    # the assets processed later
            bound = base + V2 + rem[k - K2[:, K]]
            ok = bound >= theta
            st['pruned'] += int((~ok).sum())
            K2, V2, M2 = K2[ok], V2[ok], M2[ok]
        # one record per key: the largest value
        if len(V2) == 0:
            keys, vals, mem = K2, V2, M2
            break
        idx = np.lexsort((-V2,) + tuple(K2[:, c] for c in range(K, -1, -1)))
        K2, V2, M2 = K2[idx], V2[idx], M2[idx]
        first = np.ones(len(V2), dtype=bool)
        first[1:] = np.any(K2[1:] != K2[:-1], axis=1)
        st['merged'] += int((~first).sum())
        keys, vals, mem = K2[first], V2[first], M2[first]
        st['maxtable'] = max(st['maxtable'], len(vals))
    if stats is not None:
        stats.update(st)
    return keys, vals, mem


def candidates_from_table(mem):
    out = set()
    for row in mem:
        U = tuple(sorted(int(x) for x in row if x >= 0))
        if U:
            out.add(U)
    return out


def localized_scheme(m, d, B, Sf, k, eps, Fh, Sh, that, gval, omega, prune=True, radius_factor=1.0,
                     theta_factor=1.0, node_cap=20000, time_cap=None):
    """The localized scheme of Theorem 5.24 (with the pruning of Lemma 5.23 if prune): candidates = {S_h} and the tables at the localized nodes of the guesses
    V_j = F_h 2^j, j <= J, g(that) <= 2^{J+1} F_h; theta = F_h/(1 - 2 eps). Returns a dict with the best value."""
    M, K = B.shape
    P = np.linalg.inv(Sf)
    P = (P + P.T) / 2
    G = np.linalg.cholesky(P).T                       # G'G = P
    Ginv = np.linalg.inv(G)
    Gt = G @ that
    theta = Fh / (1 - 2 * eps)
    J = max(0, math.ceil(math.log2(max(gval / Fh, 1.0))) - 1)
    out = dict(theta=theta, J=J, nodes=0, cube=0, tables=0, records=0, pruned=0, generated=0, cands=0,
               best=Fh, bestS=Sh, skipped=False, time=0.0, maxtable=0)
    t0 = time.time()
    if gval <= theta:
        out['time'] = time.time() - t0
        return out
    cands = set()
    for j in range(J + 1):
        V = Fh * 2 ** j
        p = params(eps, V, k, K, omega)
        nodes, cube, nb = loc_nodes(Gt, p['s'], p['Z'], gval, theta, K, radius_factor, cap=node_cap)
        out['cube'] += cube
        if nodes is None:
            out['skipped'] = True
            out['nodes'] += cube
            continue
        out['nodes'] += len(nodes)
        for z in nodes:
            tau = node_point(Ginv, p['s'], z.astype(float))
            st = {}
            _, _, mem = pruned_table(m, d, B, Sf, G, P, tau, p['eta'], p['Q'], k,
                                     theta=theta * theta_factor if prune else None, stats=st)
            out['tables'] += 1
            out['records'] += len(mem)
            out['pruned'] += st['pruned']
            out['generated'] += st['generated']
            out['maxtable'] = max(out['maxtable'], st['maxtable'])
            cands |= candidates_from_table(mem)
            if time_cap is not None and time.time() - t0 > time_cap:
                out['skipped'] = True
                break
    out['cands'] = len(cands)
    for U in cands:
        v = flo(m, d, B, Sf, U)[0]
        if v > out['best']:
            out['best'], out['bestS'] = v, U
    out['time'] = time.time() - t0
    return out


# --------------------------------------------------------------------------------------- one-step checks


def all_supports(M, k):
    for r in range(1, k + 1):
        yield from itertools.combinations(range(M), r)


def check_instance(rng, M, K, k, eps=0.05):
    """One instance of the stress regime: L4 (localized nodes) and P1 (pruning), each for one step, with their controls."""
    m, d, B, Sf = stress_instance(rng, M, K)
    if m.max() <= 0:
        return None
    P = np.linalg.inv(Sf)
    P = (P + P.T) / 2
    G = np.linalg.cholesky(P).T
    Ginv = np.linalg.inv(G)
    omega = float(leverages(d, B, Sf).max())
    info = {S: flo(m, d, B, Sf, S) for S in all_supports(M, k)}
    OPT = max(v[0] for v in info.values())
    Sopt = max(info, key=lambda S: info[S][0])
    gval, that = relaxation(m, d, B, Sf, k)
    Gt = G @ that
    res = dict(OPT=OPT, gap=1 - OPT / gval, L4=0, L4viol=0, L4ctrl=0, L4tight=0.0, P1=0, P1viol=0, P1ctrl=0,
               prunedshare=0.0, ctrl_checked=0)
    # L4: thresholds below the optimum; every support with value >= theta
    V = OPT / 1.5
    p = params(eps, V, k, K, omega)
    s = p['s']
    for frac in (0.8, 0.9, 0.95, 0.99):
        theta = frac * OPT
        r = math.sqrt(max(gval - theta, 0.0))
        for S, (v, w, t0) in info.items():
            if v < theta:
                continue
            z = np.round(G @ t0 / s)
            dz = s * z - Gt
            ok_cube = np.all(np.abs(dz) <= r + s / 2 + 1e-12)
            ok_ball = np.sum(dz ** 2) <= (r + s * math.sqrt(K) / 2) ** 2 * (1 + 1e-12)
            ok_box = np.all(np.abs(z) <= p['Z'])
            res['L4'] += 1
            res['L4viol'] += not (ok_cube and ok_ball and ok_box)
            rc = 0.5 * r
            ok_c = np.all(np.abs(dz) <= rc + s / 2 + 1e-12) and np.sum(dz ** 2) <= (rc + s * math.sqrt(K) / 2) ** 2
            res['L4ctrl'] += not ok_c
            res['L4tight'] = max(res['L4tight'], math.sqrt(np.sum((G @ t0 - Gt) ** 2)) / max(r, 1e-300))
    # P1: the node nearest to the dual point of the optimum and two shifted nodes; theta = OPT (valid for S_opt)
    z0 = np.round(G @ info[Sopt][2] / s)
    nodes = [z0, z0 + 1, z0 - np.r_[1, np.zeros(K - 1)]]
    for z in nodes:
        tau = Ginv @ (s * z)
        sc = scores(m, d, B, tau)
        w = np.maximum(m - B @ tau, 0.0) / d
        v = (G @ Sf @ B.T * w).T
        kv = np.floor(v / p['eta'] + 1e-12).astype(np.int64)
        Qtau = {S: float(tau @ P @ tau + sc[list(S)].sum()) for S in info}
        for theta, tag in ((OPT, 'P1'), (1.1 * OPT, 'P1ctrl')):
            st = {}
            keys, vals, mem = pruned_table(m, d, B, Sf, G, P, tau, p['eta'], p['Q'], k, theta=theta, stats=st)
            tab = {tuple(kk): vv for kk, vv in zip(map(tuple, keys), vals)}
            if tag == 'P1':
                res['prunedshare'] = max(res['prunedshare'], st['pruned'] / max(1, st['generated']))
            for S, q in Qtau.items():
                if q < OPT:            # the lemma speaks about Q_S(tau) >= theta; the control uses the same S
                    continue
                subs_ok = all(np.all(np.abs(kv[list(U)].sum(axis=0)) <= p['Q'])
                              for r_ in range(1, len(S) + 1) for U in itertools.combinations(S, r_))
                if not subs_ok:
                    continue
                key = tuple(np.r_[kv[list(S)].sum(axis=0), len(S)])
                have = key in tab and tab[key] >= sc[list(S)].sum() - 1e-12
                if tag == 'P1':
                    res['P1'] += 1
                    res['P1viol'] += not have
                else:
                    res['ctrl_checked'] += 1
                    res['P1ctrl'] += not have
    # the whole scheme from the heuristic
    Fh, Sh = greedy_swap(m, d, B, Sf, k)
    cap = 3000
    out = localized_scheme(m, d, B, Sf, k, eps, Fh, Sh, that, gval, omega, prune=True, node_cap=cap)
    full = not out['skipped']
    res.update(Fh=Fh, best=out['best'], nodes=out['nodes'], tables=out['tables'], cert=gval <= Fh / (1 - 2 * eps),
               complete=full, schemeviol=full and out['best'] < (1 - 2 * eps) * OPT - 1e-12,
               found=full and out['best'] >= OPT * (1 - 1e-9), greedyopt=Fh >= OPT * (1 - 1e-9))
    if full:
        out2 = localized_scheme(m, d, B, Sf, k, eps, Fh, Sh, that, gval, omega, prune=True, radius_factor=0.5,
                                node_cap=cap)
        out3 = localized_scheme(m, d, B, Sf, k, eps, Fh, Sh, that, gval, omega, prune=True, theta_factor=1.1,
                                node_cap=cap)
        res.update(found_r05=out2['best'] >= OPT * (1 - 1e-9), found_t11=out3['best'] >= OPT * (1 - 1e-9))
    else:
        res.update(found_r05=False, found_t11=False)
    return res


def main():
    rng = np.random.default_rng(2025)
    t0 = time.time()
    tot = dict(L4=0, L4viol=0, L4ctrl=0, P1=0, P1viol=0, P1ctrl=0, ctrl_checked=0)
    print('E34: one-step checks of L4 and P1 with controls (stress regime, M = 16), and the whole localized scheme')
    for K in (1, 2, 3):
        for k in (3, 5):
            rows = []
            for _ in range(40):
                r = check_instance(rng, 16, K, k)
                if r is not None:
                    rows.append(r)
            for key in tot:
                tot[key] += sum(r[key] for r in rows)
            n = len(rows)
            nodes = [r['nodes'] for r in rows if not r['cert']]
            print('K=%d k=%d n=%d | L4: %d checks, %d violations; control r x 0.5: %d broken (max dist/r %.3f) | '
                  'P1: %d checks, %d violations; control theta x 1.1: %d of %d broken; pruned share max %.2f | '
                  'scheme: certificate passes %d, greedy optimal %d, complete runs %d, optimum found %d '
                  '(r x 0.5: %d, theta x 1.1: %d), violations of 1-2eps %d, nodes when the certificate fails: '
                  'median %s max %s  [%.0f s]' % (
                      K, k, n, sum(r['L4'] for r in rows), sum(r['L4viol'] for r in rows),
                      sum(r['L4ctrl'] for r in rows), max(r['L4tight'] for r in rows),
                      sum(r['P1'] for r in rows), sum(r['P1viol'] for r in rows), sum(r['P1ctrl'] for r in rows),
                      sum(r['ctrl_checked'] for r in rows), max(r['prunedshare'] for r in rows),
                      sum(r['cert'] for r in rows), sum(r['greedyopt'] for r in rows),
                      sum(r['complete'] for r in rows), sum(r['found'] for r in rows),
                      sum(r['found_r05'] for r in rows), sum(r['found_t11'] for r in rows),
                      sum(r['schemeviol'] for r in rows),
                      int(np.median(nodes)) if nodes else '-', max(nodes) if nodes else '-', time.time() - t0),
                  flush=True)
    print('TOTAL', tot, '[%.0f s]' % (time.time() - t0))


if __name__ == '__main__':
    main()
