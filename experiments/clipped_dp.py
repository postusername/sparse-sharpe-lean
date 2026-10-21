"""The scheme without the Gram matrix (Section 4 of the paper): an additive key built from the clipped weights at
a node tau.  Library used by check_clipped_dp.py, e30_additive_dp.py, e30b_stress.py and e33_node_ratio.py.

Problem: F_LO(S) = max{2 m_S'w - w'V_S w : w >= 0}, V = diag(d) + B Sf B'.
Duality: F_LO(S) = min_t QLO(S, t), QLO(S, t) = t'Pt + sum_{i in S} s_i(t), P = Sf^{-1},
s_i(t) = (m_i - B_i't)_+^2 / d_i.  The clipped weight w_i(tau) = (m_i - B_i'tau)_+ / d_i is feasible, and
(the primal-dual defect identity, Theorem 4.1 of the paper; Lean: objLO_wclip_deficit, Factor/ClippedNode.lean)

    objLO(R, wclip(tau)) = tau'P tau + sum_R s_i(tau) - ||G tau - sum_R v_i(tau)||^2,   v_i(tau) = G Sf B_i w_i(tau),

with G'G = P.  The right-hand side depends on R only through (sum_R s_i, sum_R v_i, |R|): the key
(sum_R floor(v_i/eta), |R|) is additive, and the dynamic program is an ordinary knapsack without the Gram matrix.

Parameters (Definition 4.7 of the paper; the grid step is taken with nu = 1 + k omega, not with sqrt(nu)):
    nu = 1 + k omega,  eta = sqrt(eps V/2) / (k sqrt(K)),  s_g = sqrt(2 eps V) / (nu sqrt(K)),
    Q = k + ceil(sqrt(5 omega k^3 K / eps)),  Z = ceil(nu sqrt(K/eps) + 1/2).
"""
import itertools
import math

import numpy as np
from scipy.optimize import nnls


def vmat(m, d, B, Sf):
    return np.diag(d) + B @ Sf @ B.T


def flo_exact(m, d, B, Sf, S):
    """F_LO(S), the optimal weights and the dual point t* = Sf B_S' w (NNLS on the Cholesky factor)."""
    S = list(S)
    if not S:
        return 0.0, np.zeros(0), np.zeros(B.shape[1])
    V = vmat(m, d, B, Sf)[np.ix_(S, S)]
    L = np.linalg.cholesky(V)
    c = np.linalg.solve(L, m[S])
    w, res = nnls(L.T, c)
    val = float(c @ c - res ** 2)
    t = Sf @ B[S].T @ w
    return max(val, 0.0), w, t


def opt_bruteforce(m, d, B, Sf, k):
    M = len(m)
    best, bestS, bestt = 0.0, (), np.zeros(B.shape[1])
    for r in range(1, k + 1):
        for S in itertools.combinations(range(M), r):
            v, w, t = flo_exact(m, d, B, Sf, S)
            if v > best:
                best, bestS, bestt = v, S, t
    return best, bestS, bestt


def wclip(m, d, B, tau):
    return np.maximum(m - B @ tau, 0.0) / d


def obj_lo(m, d, B, Sf, S, w):
    S = list(S)
    V = vmat(m, d, B, Sf)[np.ix_(S, S)]
    return float(2 * m[S] @ w[S] - w[S] @ V @ w[S])


def qlo(m, d, B, P, S, t):
    S = list(S)
    r = np.maximum(m[S] - B[S] @ t, 0.0)
    return float(t @ P @ t + np.sum(r ** 2 / d[S]))


def gram_root(P):
    """G with G'G = P."""
    return np.linalg.cholesky(P).T


def clipped_dp(m, d, B, Sf, G, tau, eta, k, Q, order=None):
    """One table of the dynamic program at the node tau. Returns a dict key -> (value sum s_i, frozenset).

    Key = (sum floor(v_i/eta) in Z^K, |U|); the set with the largest sum s_i is kept; keys outside the box
    (|coord| <= Q, |U| <= k) are discarded at every step.
    """
    M, K = B.shape
    w = wclip(m, d, B, tau)
    s = d * w ** 2
    v = (G @ Sf @ B.T * w).T          # M x K, v_i = G Σ_f B_i w_i
    kv = np.floor(v / eta + 1e-12).astype(np.int64)  # eps: protection against 1-ulp errors
    table = {(tuple([0] * K), 0): (0.0, frozenset())}
    for i in (range(M) if order is None else order):
        new = dict(table)
        for (key, n), (val, U) in table.items():
            if n >= k:
                continue
            key2 = (tuple(int(a + b) for a, b in zip(key, kv[i])), n + 1)
            if max(abs(c) for c in key2[0]) > Q:
                continue
            val2 = val + s[i]
            cur = new.get(key2)
            if cur is None or val2 > cur[0]:
                new[key2] = (val2, U | {i})
        table = new
    return table


def params(eps, V, k, K, omega):
    nu = 1 + k * omega
    eta = math.sqrt(eps * V / 2) / (k * math.sqrt(K))
    sg = math.sqrt(2 * eps * V) / (nu * math.sqrt(K))
    # key box of Definition 4.7 (Lean clipQ); was k + ceil(3/sqrt(2) k^1.5 sqrt(K omega/eps)), which is smaller
    Q = k + math.ceil(math.sqrt(5 * omega * k ** 3 * K / eps))
    Z = math.ceil(nu * math.sqrt(K / eps) + 0.5)
    return dict(nu=nu, eta=eta, sg=sg, Q=Q, Z=Z)


def nearest_node(G, tstar, sg):
    z = np.round(G @ tstar / sg)
    tau = np.linalg.solve(G, z * sg)
    return z, tau


def leverages(d, B, Sf):
    return np.einsum('ij,jk,ik->i', B, Sf, B) / d


def clipped_dp_stats(m, d, B, Sf, G, tau, eta, k, Q, order=None):
    """Like clipped_dp, but also returns statistics: the number of generated sets, the number of merges
    (a set landed in an already occupied bucket), the number discarded by the box and the largest |key|."""
    M, K = B.shape
    w = wclip(m, d, B, tau)
    s = d * w ** 2
    v = (G @ Sf @ B.T * w).T
    kv = np.floor(v / eta + 1e-12).astype(np.int64)
    table = {(tuple([0] * K), 0): (0.0, frozenset())}
    st = dict(generated=0, merged=0, boxed=0, replaced=0)
    for i in (range(M) if order is None else order):
        new = dict(table)
        for (key, n), (val, U) in table.items():
            if n >= k:
                continue
            key2 = (tuple(int(a + b) for a, b in zip(key, kv[i])), n + 1)
            st['generated'] += 1
            if max(abs(c) for c in key2[0]) > Q:
                st['boxed'] += 1
                continue
            val2 = val + s[i]
            cur = new.get(key2)
            if cur is None:
                new[key2] = (val2, U | {i})
            else:
                st['merged'] += 1
                if val2 > cur[0]:
                    new[key2] = (val2, U | {i})
                    st['replaced'] += 1
        table = new
    st['maxkey'] = max((max(abs(c) for c in key) for (key, n) in table), default=0)
    return table, st


def greedy_swap(m, d, B, Sf, k, iters=50):
    """Greedy selection by the increase of F_LO plus exchanges (a heuristic, as in the paper): a lower bound on OPT(k)."""
    M = len(m)
    S = []
    best = 0.0
    for _ in range(k):
        cand = None
        for i in range(M):
            if i in S:
                continue
            v = flo_exact(m, d, B, Sf, S + [i])[0]
            if v > best + 1e-15:
                best, cand = v, i
        if cand is None:
            break
        S.append(cand)
    improved = True
    it = 0
    while improved and it < iters:
        improved = False
        it += 1
        for a in range(len(S)):
            for i in range(M):
                if i in S:
                    continue
                T = S.copy()
                T[a] = i
                v = flo_exact(m, d, B, Sf, T)[0]
                if v > best + 1e-12:
                    S, best, improved = T, v, True
    return best, tuple(sorted(S))
