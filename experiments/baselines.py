"""Methods from the literature, applied to the data (m, d, B, Sf) of a factor model V = diag(d) + B Sf B'.

  * pga_lin2024    -- the proximal gradient algorithm of Lin, Lai and Li (NeurIPS 2024), Algorithm A1: minimize
                      f(v) = v'(V + rho I)v / 2 - m'v over v >= 0 with at most k nonzeros; step 0.999 / lambda_max,
                      start v = m, stop when ||v_new - v|| <= 1e-5 ||v|| or after 10^4 iterations.  The paper adds the
                      ridge rho = 10^-3 to a sample covariance matrix; V is positive definite, so rho = 0 here.
  * oscar_bae2025  -- the asset selection of Bae, Jeon, Park, Lee and Kim (arXiv:2502.11701): with V = L L' (Cholesky,
                      assets in the given order) keep the k largest |(L^{-1} m)_i|.  Their method re-solves the tangency
                      portfolio without sign constraints on the selected assets; here the long-only optimum is taken.
                      signed=True keeps the k largest (L^{-1} m)_i instead (a long-only variant).
  * sdp_kim2016    -- the semidefinite relaxation (P7) of Kim, Lee, Kim and Kim (Oper. Res. Lett. 2016):
                      max <m m', Y> s.t. sum_ij |Y_ij| <= k tr Y, <V, Y> = 1, Y psd; an upper bound on the squared
                      Sharpe ratio of portfolios with at most k assets of any sign.  With nonneg=True the constraint
                      Y >= 0 (elementwise) is added, which is valid for long-only portfolios.

Every method returns a support; its value is the long-only optimum F_LO on that support (common.flo), except the SDP,
which returns a bound.
"""
import time

import numpy as np
import scipy.linalg as sla
from scipy.sparse.linalg import LinearOperator, eigsh


def _matvec(d, B, Sf):
    return lambda v: d * v + B @ (Sf @ (B.T @ v))


def lambda_max(d, B, Sf):
    M = len(d)
    if M <= 400:
        V = np.diag(d) + B @ Sf @ B.T
        return float(np.linalg.eigvalsh(V)[-1])
    op = LinearOperator((M, M), matvec=_matvec(d, B, Sf), dtype=float)
    return float(eigsh(op, k=1, which='LA', tol=1e-10, return_eigenvectors=False)[0])


def pga_lin2024(m, d, B, Sf, k, rho=0.0, tol=1e-5, maxit=10 ** 4):
    """Algorithm A1 of Lin, Lai and Li (2024) with p = m and Q_eps = V + rho I.  Returns (support, v, iterations, seconds)."""
    t0 = time.perf_counter()
    mv = _matvec(d + rho, B, Sf)
    alpha = 0.999 / lambda_max(d + rho, B, Sf)
    v = m.astype(float).copy()                     # Algorithm A1 starts at v = p
    it = 0
    while it < maxit:
        u = v - alpha * (mv(v) - m)
        h = np.maximum(u, 0.0)
        nz = np.flatnonzero(h)
        if len(nz) > k:                            # keep the k largest entries; ties to the lowest index (stable sort)
            keep = nz[np.argsort(-h[nz], kind='stable')[:k]]
            hh = np.zeros_like(h)
            hh[keep] = h[keep]
            h = hh
        it += 1
        nv = np.linalg.norm(v)
        done = nv == 0 or np.linalg.norm(h - v) <= tol * nv
        v = h
        if done:
            break
    return np.flatnonzero(v), v, it, time.perf_counter() - t0


def oscar_bae2025(m, d, B, Sf, k, signed=False):
    """Selection rule of Bae et al. (2025): the k largest |L^{-1} m| with V = L L'.  With signed=True the k largest
    (L^{-1} m)_i instead: a long-only variant, since the assets with negative entries are the ones that their long-short
    portfolio sells short.  Returns (support, seconds)."""
    t0 = time.perf_counter()
    V = np.diag(d) + B @ Sf @ B.T
    L = np.linalg.cholesky(V)
    z = sla.solve_triangular(L, m, lower=True)
    sel = np.argsort(-(z if signed else np.abs(z)), kind='stable')[:k]
    return np.sort(sel), time.perf_counter() - t0


def sdp_kim2016(m, d, B, Sf, k, nonneg=False, solver='CLARABEL'):
    """Optimal value of (P7) (an upper bound on the largest squared Sharpe ratio with at most k assets); inputs are
    rescaled by the mean variance, which leaves the squared Sharpe ratio unchanged.  Returns (value, seconds, status)."""
    import cvxpy as cp
    V = np.diag(d) + B @ Sf @ B.T
    s = float(np.mean(np.diag(V)))
    V, mm = V / s, m / np.sqrt(s)
    M = len(m)
    Y = cp.Variable((M, M), symmetric=True)
    cons = [Y >> 0, cp.trace(V @ Y) == 1]
    if nonneg:
        cons += [Y >= 0, cp.sum(Y) <= k * cp.trace(Y)]
    else:
        cons += [cp.sum(cp.abs(Y)) <= k * cp.trace(Y)]
    prob = cp.Problem(cp.Maximize(mm @ Y @ mm), cons)
    t0 = time.perf_counter()
    prob.solve(solver=solver)
    return float(prob.value) if prob.value is not None else float('nan'), time.perf_counter() - t0, prob.status


# ------------------------------------------------------------------------------------------------------------------
# Outer approximation of Bertsimas and Cory-Wright (INFORMS J. Comput. 2022), adapted to max_{|S|<=k} F_LO(S).
#
# Their cut, with the ridge term replaced by the idiosyncratic variances (their Section 3.2, "extracting diagonal
# dominance", gamma_i = 1/d_i), is in our notation the weak duality inequality: for every t in R^K
#     F_LO(S) <= t'P t + sum_{i in S} s_i(t),   i.e.   eta <= t'P t + sum_i s_i(t) z_i,
# valid for all z, and tight at z = 1_S when t is the dual point of S (Theorem 2.1).  The master problem is
# max eta s.t. the cuts, sum z <= k, z binary; it is solved by SCIP with the cuts as lazy constraints at integer
# points.  Root: the cut at the minimizer of g_k (the bound of the Boolean / perspective relaxation, which their
# in-out procedure approximates), the cut at the dual point of the warm start, and Kelley cuts at fractional LP
# points (at most 200 at the root, at most 20 at each of the first 50 other nodes, as in their paper); warm start:
# the heuristic support, as the first incumbent.
# ------------------------------------------------------------------------------------------------------------------

def _flo_dual(m, d, B, Sf, S):
    """F_LO(S), the optimal weights and the dual point t0 = Sf B_S' w (NNLS on the Cholesky factor)."""
    from scipy.optimize import nnls
    S = list(S)
    if not S:
        return 0.0, np.zeros(0), np.zeros(B.shape[1])
    BS = B[S]
    V = np.diag(d[S]) + BS @ Sf @ BS.T
    L = np.linalg.cholesky(V)
    c = np.linalg.solve(L, m[S])
    w, res = nnls(L.T, c)
    return max(float(c @ c - res ** 2), 0.0), w, Sf @ BS.T @ w


def _frac_point(m, d, B, P, zf, t0):
    """argmin_t t'Pt + sum_i zf_i s_i(t): the best cut for a fractional z (convex and C^1 in t)."""
    from scipy.optimize import minimize

    def f(t):
        r = np.maximum(m - B @ t, 0.0)
        val = t @ P @ t + np.sum(zf * r * r / d)
        g = 2 * P @ t - 2 * B.T @ (zf * r / d)
        return val, g
    res = minimize(f, t0, jac=True, method='L-BFGS-B', options={'maxiter': 200, 'gtol': 1e-12, 'ftol': 1e-15})
    return res.x


def oa_bcw2022(m, d, B, Sf, k, t_root, warm_S, time_limit=600.0, gap=1e-6, root_cuts=200, node_cuts=20,
               cut_nodes=50, verbose=False):
    """Returns a dict: status, time, support and exact value of the incumbent, dual bound, gap, nodes, cut counts."""
    from pyscipopt import Model, Conshdlr, SCIP_RESULT, quicksum
    M, K = B.shape
    P = np.linalg.inv(Sf)
    P = (P + P.T) / 2
    mdl = Model()
    if not verbose:
        mdl.hideOutput()
    z = [mdl.addVar(vtype='B', name='z%d' % i) for i in range(M)]
    eta = mdl.addVar(lb=0.0, ub=None, name='eta')
    mdl.addCons(quicksum(z) <= k)
    stats = dict(lazy=0, frac=0, root=0)

    def cut_expr(t):
        s = np.maximum(m - B @ t, 0.0) ** 2 / d
        idx = np.flatnonzero(s > 0)
        return eta <= float(t @ P @ t) + quicksum(float(s[i]) * z[i] for i in idx)

    t_warm = _flo_dual(m, d, B, Sf, warm_S)[2]
    for t in (t_root, t_warm):
        mdl.addCons(cut_expr(t))
    mdl.setObjective(eta, 'maximize')

    class OA(Conshdlr):
        def __init__(self):
            self.last_t = t_root.copy()
            self.node_cuts = {}

        def _support(self, sol):
            zv = np.array([self.model.getSolVal(sol, zi) for zi in z])
            return [i for i in range(M) if zv[i] > 0.5], self.model.getSolVal(sol, eta)

        def _violated(self, sol):
            S, ev = self._support(sol)
            F, w, t0 = _flo_dual(m, d, B, Sf, S)
            return ev > F + 1e-6 * max(1.0, abs(F)), t0

        def conscheck(self, constraints, solution, checkintegrality, checklprows, printreason, completely):
            viol, _ = self._violated(solution)
            return {'result': SCIP_RESULT.INFEASIBLE if viol else SCIP_RESULT.FEASIBLE}

        def _enforce(self):
            viol, t0 = self._violated(None)
            if viol:
                self.model.addCons(cut_expr(t0), removable=False)
                stats['lazy'] += 1
                return {'result': SCIP_RESULT.CONSADDED}
            return {'result': SCIP_RESULT.FEASIBLE}

        def consenfolp(self, constraints, nusefulconss, solinfeasible):
            return self._enforce()

        def consenfops(self, constraints, nusefulconss, solinfeasible, objinfeasible):
            return self._enforce()

        def conssepalp(self, constraints, nusefulconss):
            node = self.model.getCurrentNode().getNumber()
            depth = self.model.getDepth()
            if depth == 0:
                if stats['root'] >= root_cuts:
                    return {'result': SCIP_RESULT.DIDNOTRUN}
            else:
                if node not in self.node_cuts and len(self.node_cuts) >= cut_nodes:
                    return {'result': SCIP_RESULT.DIDNOTRUN}
                if self.node_cuts.get(node, 0) >= node_cuts:
                    return {'result': SCIP_RESULT.DIDNOTRUN}
            zf = np.clip(np.array([self.model.getSolVal(None, zi) for zi in z]), 0.0, 1.0)
            ev = self.model.getSolVal(None, eta)
            t = _frac_point(m, d, B, P, zf, self.last_t)
            s = np.maximum(m - B @ t, 0.0) ** 2 / d
            if ev > float(t @ P @ t + zf @ s) + 1e-7 * max(1.0, abs(ev)):
                self.last_t = t
                self.model.addCons(cut_expr(t), removable=True)
                stats['frac'] += 1
                if depth == 0:
                    stats['root'] += 1
                else:
                    self.node_cuts[node] = self.node_cuts.get(node, 0) + 1
                return {'result': SCIP_RESULT.CONSADDED}
            return {'result': SCIP_RESULT.DIDNOTFIND}

        def conslock(self, constraint, locktype, nlockspos, nlocksneg):
            # eta <= Phi(z) with Phi nondecreasing in z: increasing eta or decreasing a z_i may violate it
            self.model.addVarLocksType(eta, locktype, nlocksneg, nlockspos)
            for zi in z:
                self.model.addVarLocksType(zi, locktype, nlockspos, nlocksneg)

    hdlr = OA()
    mdl.includeConshdlr(hdlr, 'OA', 'outer approximation cuts', sepapriority=1, enfopriority=-1, chckpriority=-1,
                        sepafreq=1, needscons=True)
    cons = mdl.createCons(hdlr, 'oa')
    mdl.addPyCons(cons)
    mdl.setParam('limits/time', float(time_limit))
    mdl.setParam('limits/gap', float(gap))
    mdl.setParam('lp/threads', 1)
    mdl.setParam('parallel/maxnthreads', 1)
    mdl.setParam('misc/allowstrongdualreds', False)
    mdl.setParam('misc/allowweakdualreds', False)
    sol = mdl.createSol()
    Fw = _flo_dual(m, d, B, Sf, warm_S)[0]
    for i in range(M):
        mdl.setSolVal(sol, z[i], 1.0 if i in set(warm_S) else 0.0)
    mdl.setSolVal(sol, eta, Fw * (1 - 1e-9))
    mdl.addSol(sol)
    t0 = time.perf_counter()
    mdl.optimize()
    el = time.perf_counter() - t0
    best = mdl.getBestSol()
    S = [i for i in range(M) if mdl.getSolVal(best, z[i]) > 0.5]
    F = _flo_dual(m, d, B, Sf, S)[0]
    return dict(status=mdl.getStatus(), time=el, support=S, value=F, bound=mdl.getDualbound(),
                gap=(mdl.getDualbound() - F) / max(F, 1e-300), nodes=mdl.getNNodes(), **stats)
