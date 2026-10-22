"""E44: the scale-free scheme of plan C1 (no omega anywhere) and its controls, on small random instances.

Everything is in G-coordinates: rows b_i = G Sigma_f B_i / sqrt(d_i) in R^K (|b_i|^2 = omega_i), y_i = m_i / sqrt(d_i),
Q_S(x) = |x|^2 + sum_{i in S} (y_i - b_i.x)_+^2 and F_LO(S) = min_x Q_S(x), computed exactly by enumeration of the
self-consistent active sets (Theorem X of the formalization); OPT(k) by enumeration of the supports.  S-bar is the set
of rows of the assets together with the K anchor rows (e_l, 0) of the ridge |x|^2.

The scheme (one guess F^ = OPT, eps = 0.05):
  for every K-tuple T of rows of S-bar with det B_T != 0 and with at most k assets, the assets of T are forced into
  every candidate; nodes x(rho) solve y_T - B_T x = rho with rho on the lattice step*Z^K in [-R, R]^K, R = sqrt(2 F^),
  step = c_step * sqrt(2 eps F^) / sqrt(K); admitted assets have Cramer coordinates c_i = B_T^{-T} b_i with
  |c_i|_inf <= 1; the key of an asset at a node is floor(r_i(x)_+ c_i / eta) and a count, eta = c_key *
  sqrt(eps F^ / 2) / (k sqrt K); the key box is |kappa_l| <= k + ceil(sqrt(3 k F^) / eta).  No quantity depends on omega.
  The value of a candidate is always the exact F_LO, and the scheme returns the best one.
Controls, which must fail somewhere: 'step10_key30' (step x10 and key x30), 'ggrid' (the K-tuple of anchors only and
no filter: the grid in G-coordinates with the coarse step, i.e. Algorithm 4.1 without the factor nu); 'nofilter' is
the scheme without the filter |c_i|_inf <= 1 (reported, not a control).  The number of distinct candidates is reported
next to the number of all supports with at most k assets: for these sizes the union over all K-tuples and nodes keeps
most supports, so the parts below are weak evidence; the informative test is the one-step check ('onestep').

One-step check (the lemmas of plan C1, one node, one table): T is a K-tuple of maximal volume among the rows of
S-bar* (the active assets of the optimum S* at its dual point x0, and the anchors), rho0 = y_T - B_T x0, the node is
the lattice point nearest to rho0, the table is built there with the forced assets of T and the Cramer key, and the
ratio best/OPT over the sets of this single table is reported, together with the weights of the rows of T at the
optimum (w_T = B_T^{-T} x0 - sum over S* minus T of r_i(x0)_+ c_i) and the number of them below k eta ('tight' rows; the class
of Lemma 5 of the plan has at most one).  Controls at the same instance: the node of the lattice with step x10
('node10'), the key x30 ('key30'), the nearest node of the grid in G-coordinates with the key of Algorithm 4.1
('gnode'), and a K-tuple of the rows of S-bar* of non-maximal volume ('wrongT', when one exists).

Instances: families rand, cluster, ortho (K = 2, M = 9, k = 3, 40 each), rand30 and cluster30 (K = 2, M = 30, k = 3,
10 each), rand with K = 3 (M = 7, k = 3, 15), adversarial instances found by hill climbing against the controls, and
for the one-step check the families rand, cluster, ortho with K = 2, 3 and M = 12 (100 instances each).
The one-tuple scheme of Remark 5.15 of the paper (Lean sfCandidates, main_theorem_sf; Definition 5.10 and Theorem 5.11
of version 0.26) itself (part def510_<family>_<K>, the instances of onestep_<family>_<K>): one guess
F^ = OPT, T of maximal volume among the rows of S-bar*, the lattice step sqrt(eps F^)/(C sqrt K), C = (k + K) K, the
additive key (floor(r_i c_i / eta), floor(r_i^2 / zeta), 1) with the box of the definition, and a table for every row l
that keeps the smallest Cramer sum; the node of the proof of main_theorem_sf ('rule': the corner of the cell given by the
signs of H for the row of the smallest position of the optimum) and the best corner of the cell ('cell'); the class of
the theorem (at most one position with sqrt(d_i) w*_i < 2 sqrt(eps OPT / K)) is recorded.  Controls: a K-tuple of
non-maximal volume ('wrongT') and the anchor rows as T without the filter ('anchorT', the grid in G-coordinates without
nu).  Part advdef_<K>: hill climbing against the node of the proof.  The parts above (onestep, lemmas, advstep and the
whole scheme) use the coarser plan C1 variant described at the top (step sqrt(2 eps F^ / K), key without the score
coordinate, the table keeps the largest sum of scores).
Usage:  python3 -I e44_scalefree.py <part> > results/E44/<part>.jsonl
        part: rand, cluster, ortho, rand30, cluster30, k3, adv, onestep_<family>_<K>, lemmas_<family>_<K>, advstep_<K>,
              def510_<family>_<K>, advdef_<K>
"""
import itertools
import json
import math
import os
import sys

import numpy as np

EPS = 0.05
HERE = os.path.dirname(os.path.abspath(__file__))


# ------------------------------------------------------------------------------------------- exact values
def F_ls(b, y, A):
    K = b.shape[1]
    if len(A) == 0:
        return 0.0, np.zeros(K)
    BA, yA = b[list(A)], y[list(A)]
    g = BA.T @ yA
    x = np.linalg.solve(np.eye(K) + BA.T @ BA, g)
    return float(yA @ yA - g @ x), x


def F_lo(b, y, S, tol=1e-12):
    best = 0.0
    S = list(S)
    for r in range(1, len(S) + 1):
        for A in itertools.combinations(S, r):
            val, x = F_ls(b, y, A)
            res = y[list(A)] - b[list(A)] @ x
            if np.all(res >= -tol * (1.0 + np.abs(y[list(A)]))):
                best = max(best, val)
    return best


def opt_lo(b, y, k):
    best, arg = 0.0, ()
    for r in range(1, k + 1):
        for S in itertools.combinations(range(len(y)), r):
            v = F_lo(b, y, S)
            if v > best:
                best, arg = v, S
    return best, arg


# ------------------------------------------------------------------------------------------- instances
def gen(rng, fam, M, K):
    if fam == "rand":
        L = rng.uniform(0, 3)
        lam = 10 ** rng.uniform(-1, L, size=M)
        u = rng.normal(size=(M, K))
        u /= np.linalg.norm(u, axis=1, keepdims=True)
        b = lam[:, None] * u
        y = (rng.normal(size=M) + 0.3) * np.sqrt(1 + lam ** 2) * 10 ** rng.uniform(-0.5, 0.5, size=M)
    elif fam == "cluster":
        lam = 10 ** rng.uniform(1, 3)
        nh = rng.integers(2, 5)
        u0 = rng.normal(size=K)
        u0 /= np.linalg.norm(u0)
        bh = lam * (u0 + 0.05 * rng.normal(size=(nh, K)))
        yh = lam * (1 + 0.02 * rng.normal(size=nh)) * rng.uniform(0.5, 2)
        nl = M - nh
        bl = rng.normal(size=(nl, K)) * rng.uniform(0.1, 2, size=(nl, 1))
        yl = rng.normal(size=nl) * 2 + 1
        b, y = np.vstack([bh, bl]), np.concatenate([yh, yl])
    elif fam == "ortho":
        lam = 10 ** rng.uniform(1, 3)
        b, y = np.zeros((M, K)), np.zeros(M)
        for l in range(K):
            b[l, l], y[l] = lam, 1.0
        b[K:] = rng.normal(size=(M - K, K)) * rng.uniform(0.01, 1, size=(M - K, 1))
        y[K:] = np.abs(rng.normal(size=M - K)) * rng.uniform(0.01, 0.3)
    else:
        raise ValueError(fam)
    return b, y


# ------------------------------------------------------------------------------------------- the scheme
def table(b, y, x, k, eta, C, qbox, adm):
    """Algorithm 4.1 at the node x with the Cramer key: kappa = sum floor(r_i(x)_+ c_i / eta), count; box qbox."""
    r = np.maximum(y - b @ x, 0.0)
    s = r ** 2
    keys = np.floor((r[:, None] * C) / eta).astype(np.int64)
    tab = {(0,) * C.shape[1] + (0,): ((), 0.0)}
    for i in adm:
        new = dict(tab)
        ci = tuple(keys[i]) + (1,)
        for kap, (U, sc) in tab.items():
            if kap[-1] + 1 > k:
                continue
            kp = tuple(a + c for a, c in zip(kap, ci))
            if max(abs(v) for v in kp[:-1]) > qbox:
                continue
            if kp not in new or sc + s[i] > new[kp][1]:
                new[kp] = (U + (i,), sc + s[i])
        tab = new
    return [U for (U, _) in tab.values()]


def scheme(b, y, k, Fh, c_step=1.0, c_key=1.0, tuples="all", cfilter=True):
    M, K = b.shape
    Bbar = np.vstack([b, np.eye(K)])
    ybar = np.concatenate([y, np.zeros(K)])
    step = c_step * math.sqrt(2 * EPS * Fh) / math.sqrt(K)
    R = math.sqrt(2 * Fh)
    zmax = int(math.ceil(R / step))
    eta = c_key * math.sqrt(EPS * Fh / 2) / (k * math.sqrt(K))
    qbox = k + int(math.ceil(math.sqrt(3 * k * Fh) / eta))
    Ts = itertools.combinations(range(M + K), K) if tuples == "all" else [tuple(range(M, M + K))]
    seen, best, nodes = set(), 0.0, 0
    for T in Ts:
        BT = Bbar[list(T)]
        if abs(np.linalg.det(BT)) < 1e-12 * (1 + np.prod(np.linalg.norm(BT, axis=1))):
            continue
        TA = [i for i in T if i < M]
        if len(TA) > k:
            continue
        C = np.linalg.solve(BT.T, b.T).T          # rows: Cramer coordinates B_T^{-T} b_i
        adm = [i for i in range(M) if i not in TA and (not cfilter or np.max(np.abs(C[i])) <= 1 + 1e-9)]
        for z in itertools.product(range(-zmax, zmax + 1), repeat=K):
            x = np.linalg.solve(BT, ybar[list(T)] - step * np.array(z, float))
            nodes += 1
            for U in table(b, y, x, k - len(TA), eta, C, qbox, adm):
                W = tuple(sorted(TA + list(U)))
                if W and W not in seen:
                    seen.add(W)
                    v = F_lo(b, y, W)
                    if v > best:
                        best = v
    return best, nodes, len(seen)


SCHEMES = {
    "sf": dict(),
    "nofilter": dict(cfilter=False),
    "step10_key30": dict(c_step=10.0, c_key=30.0),
    "ggrid": dict(tuples="anchors", cfilter=False),
}


def evaluate(b, y, k):
    OPT, S = opt_lo(b, y, k)
    M = len(y)
    rec = dict(OPT=OPT, S=[int(i) for i in S], omega=float(np.max(np.sum(b ** 2, axis=1))),
               supports=sum(math.comb(M, r) for r in range(1, k + 1)))
    for name, kw in SCHEMES.items():
        best, nodes, cands = scheme(b, y, k, OPT, **kw)
        rec[name] = best / OPT
        rec[name + "_nodes"] = nodes
        rec[name + "_cands"] = cands
    return rec


# ------------------------------------------------------------------------------------------- one-step check
def active_point(b, y, S):
    """The dual point x0 of S and its active set (the optimal self-consistent subset, Theorem X)."""
    best, bx, bA = -1.0, np.zeros(b.shape[1]), ()
    for r in range(0, len(S) + 1):
        for A in itertools.combinations(S, r):
            val, x = F_ls(b, y, A)
            if r and np.any(y[list(A)] - b[list(A)] @ x < -1e-12 * (1 + np.abs(y[list(A)]))):
                continue
            if val > best:
                best, bx, bA = val, x, A
    return bx, bA


def node_table(b, y, k, Fh, T, rho, eta, forced=True, cfilter=True, gkey=False, x=None):
    M, K = b.shape
    Bbar = np.vstack([b, np.eye(K)])
    ybar = np.concatenate([y, np.zeros(K)])
    if x is None:
        x = np.linalg.solve(Bbar[list(T)], ybar[list(T)] - rho)
    C = b.copy() if gkey else np.linalg.solve(Bbar[list(T)].T, b.T).T
    TA = [i for i in T if i < M] if forced else []
    adm = [i for i in range(M) if i not in TA and (not cfilter or np.max(np.abs(C[i])) <= 1 + 1e-9)]
    qbox = k + int(math.ceil(math.sqrt(3 * k * Fh) / eta)) if not gkey else 10 ** 9
    best = 0.0
    for U in table(b, y, x, k - len(TA), eta, C, qbox, adm):
        W = tuple(sorted(TA + list(U)))
        if W:
            best = max(best, F_lo(b, y, W))
    return best


def onestep(b, y, k):
    M, K = b.shape
    OPT, S = opt_lo(b, y, k)
    x0, A = active_point(b, y, list(S))
    Bbar = np.vstack([b, np.eye(K)])
    ybar = np.concatenate([y, np.zeros(K)])
    rows = list(A) + list(range(M, M + K))
    vols = sorted(((abs(np.linalg.det(Bbar[list(T)])), T) for T in itertools.combinations(rows, K)), reverse=True)
    T = vols[0][1]
    BT = Bbar[list(T)]
    C = np.linalg.solve(BT.T, b.T).T
    r0 = np.maximum(y - b @ x0, 0.0)
    eta = math.sqrt(EPS * OPT / 2) / (k * math.sqrt(K))
    # weights of the rows of T at the optimum (Cramer witness at x0); the anchors carry the ridge
    xi0 = np.linalg.solve(BT.T, x0)
    kap = sum((r0[i] * C[i] for i in S if i not in T), np.zeros(K))
    wT = xi0 - kap
    tight = [int(l) for l in range(K) if T[l] < M and wT[l] < k * eta]
    rho0 = ybar[list(T)] - BT @ x0
    step = math.sqrt(2 * EPS * OPT) / math.sqrt(K)
    rec = dict(OPT=OPT, S=[int(i) for i in S], omega=float(np.max(np.sum(b ** 2, axis=1))), T=[int(t) for t in T],
               nassetsT=sum(1 for t in T if t < M), maxCramer=float(max(np.max(np.abs(C[i])) for i in A)) if A else 0.0,
               wT=[float(v) for v in wT], tight=len(tight), keta=k * eta)
    rho = step * np.round(rho0 / step)
    rec["one"] = node_table(b, y, k, OPT, T, rho, eta) / OPT
    rho10 = 10 * step * np.round(rho0 / (10 * step))
    rec["node10"] = node_table(b, y, k, OPT, T, rho10, eta) / OPT
    rec["key30"] = node_table(b, y, k, OPT, T, rho, 30 * eta) / OPT
    xg = step * np.round(x0 / step)      # the nearest node of the G-grid without nu
    rec["gnode"] = node_table(b, y, k, OPT, tuple(range(M, M + K)), None, eta, forced=False, cfilter=False,
                              gkey=True, x=xg) / OPT
    others = [Tw for v, Tw in vols[1:] if v > 1e-9 * vols[0][0] and v < 0.5 * vols[0][0]]
    if others:
        Tw = others[0]
        rhow = step * np.round((ybar[list(Tw)] - Bbar[list(Tw)] @ x0) / step)
        rec["wrongT"] = node_table(b, y, k, OPT, Tw, rhow, eta) / OPT
    return rec


# ------------------------------------------------------------------------------------------- the lemmas of the step
def lemmas(b, y, k):
    """Checks of the inequalities of the step (SPEC_C1.md) at the node nearest to rho0, in the row form of S-bar:
    row weights omega_j = res_j(x) off T (clipped for assets, -x_l for the anchors), omega_T = -sum_{j not in T} res_j c_j
    (Cramer witness: sum_j omega_j a_j = 0), obj = Q_X(x) - |omega_T - r_T|^2, grad_rho Q = 2 (r_T - omega_T)."""
    M, K = b.shape
    OPT, S = opt_lo(b, y, k)
    x0, A = active_point(b, y, list(S))
    S = list(A)                                   # w.l.o.g. every asset of the optimum is active
    Bbar = np.vstack([b, np.eye(K)])
    ybar = np.concatenate([y, np.zeros(K)])
    rows = S + list(range(M, M + K))
    T = max(itertools.combinations(rows, K), key=lambda T: abs(np.linalg.det(Bbar[list(T)])))
    BT = Bbar[list(T)]
    Cr = np.linalg.solve(BT.T, Bbar.T).T          # Cramer coordinates of all rows (assets and anchors)
    eta = math.sqrt(EPS * OPT / 2) / (k * math.sqrt(K))
    step = math.sqrt(2 * EPS * OPT) / math.sqrt(K)
    rho0 = ybar[list(T)] - BT @ x0
    rho = step * np.round(rho0 / step)
    x = np.linalg.solve(BT, ybar[list(T)] - rho)

    def res(j):
        r = ybar[j] - Bbar[j] @ x
        return max(r, 0.0) if j < M else r

    def Q(X):
        return sum(res(j) ** 2 for j in list(X) + list(range(M, M + K)))

    def omegaT(X):
        return -sum((res(j) * Cr[j] for j in list(X) + list(range(M, M + K)) if j not in T), np.zeros(K))

    rT = np.array([res(j) if j >= M else ybar[j] - Bbar[j] @ x for j in T])
    nS = len(S) + K
    QS = Q(S)
    gS = 2 * (rT - omegaT(S))
    gx = 2 * (x - sum((max(y[i] - b[i] @ x, 0.0) * b[i] for i in S), np.zeros(K)))   # gradient in G-coordinates
    rec = dict(OPT=OPT, S=[int(i) for i in S], T=[int(t) for t in T], omega=float(np.max(np.sum(b ** 2, axis=1))),
               lemma1=(QS - OPT) / (nS * K * float(np.sum((rho - rho0) ** 2)) + 1e-300),
               lemma3=0.25 * float(gS @ gS) / (nS * K * (QS - OPT)) if QS > OPT else 0.0,
               lemma3_G=0.25 * float(gx @ gx) / (nS * K * (QS - OPT)) if QS > OPT else 0.0)
    # the representative of the bucket of S* (the assets of S* outside T) in the table at x
    TA = [t for t in T if t < M]
    adm = [i for i in range(M) if i not in TA and np.max(np.abs(Cr[i])) <= 1 + 1e-9]
    r = np.maximum(y - b @ x, 0.0)
    keys = np.floor((r[:, None] * Cr[:M]) / eta).astype(np.int64)
    key = lambda U: tuple(int(v) for v in sum((keys[i] for i in U), np.zeros(K, dtype=np.int64))) + (len(U),)
    rest = [i for i in S if i not in TA]
    tab = {}
    for i in adm:
        new = dict(tab)
        new.setdefault((0,) * K + (0,), ((), 0.0))
        for kap, (U, sc) in list(new.items()):
            if kap[-1] + 1 > k - len(TA):
                continue
            kp = tuple(a + c for a, c in zip(kap, tuple(keys[i]) + (1,)))
            if kp not in new or sc + r[i] ** 2 > new[kp][1]:
                new[kp] = (U + (i,), sc + r[i] ** 2)
        tab = new
    kS = key(rest)
    X = list(tab[kS][0]) if kS in tab else None
    rec["bucket_found"] = X is not None
    if X is not None:
        wS, wX = omegaT(rest + TA), omegaT(X + TA)
        rec["key_dev"] = float(np.max(np.abs(wX - wS))) / (k * eta)              # lemma 4: < 1
        tight = [l for l in range(K) if T[l] < M and wS[l] < k * eta]
        rec["tight"] = len(tight)
        neg = [l for l in range(K) if T[l] < M and wX[l] < 0]
        rec["sign_fail"] = len(neg)
        if not neg:
            w = np.zeros(M)
            for i in X:
                w[i] = r[i]
            for l in range(K):
                if T[l] < M:
                    w[T[l]] = wX[l]
            obj = 2 * y @ w - w @ w - float(np.sum((b.T @ w) ** 2))
            bound = OPT - (0.5 * math.sqrt(float(gS @ gS)) + k * eta * math.sqrt(K)) ** 2
            rec["lemma5_slack"] = (obj - bound) / OPT                              # lemma 5: >= 0
            rec["obj_ratio"] = obj / OPT
    return rec


# ------------------------------------------------------------------------------------------- adversary of the step
def corner_step(b, y, k):
    """The step of the proof: T of maximal volume among the rows of S-bar*, the 2^K corners of the lattice cell around
    rho0, one table at each; returns the best ratio over the corners and the number of tight rows of T at x0."""
    M, K = b.shape
    OPT, S = opt_lo(b, y, k)
    if OPT <= 1e-9:
        return 1.0, 0, OPT
    x0, A = active_point(b, y, list(S))
    Bbar = np.vstack([b, np.eye(K)])
    ybar = np.concatenate([y, np.zeros(K)])
    rows = list(A) + list(range(M, M + K))
    T = max(itertools.combinations(rows, K), key=lambda T: abs(np.linalg.det(Bbar[list(T)])))
    BT = Bbar[list(T)]
    Cr = np.linalg.solve(BT.T, Bbar.T).T
    eta = math.sqrt(EPS * OPT / 2) / (k * math.sqrt(K))
    step = math.sqrt(2 * EPS * OPT) / math.sqrt(K)
    rho0 = ybar[list(T)] - BT @ x0
    res0 = lambda j: (ybar[j] - Bbar[j] @ x0) if j >= M else max(ybar[j] - Bbar[j] @ x0, 0.0)
    wstar = -sum((res0(j) * Cr[j] for j in rows if j not in T), np.zeros(K))
    tight = sum(1 for l in range(K) if T[l] < M and wstar[l] < k * eta)
    lo = np.floor(rho0 / step)
    best = 0.0
    for corner in itertools.product((0, 1), repeat=K):
        rho = step * (lo + np.array(corner))
        best = max(best, node_table(b, y, k, OPT, T, rho, eta) / OPT)
        if best >= 1 - 1e-9:
            break
    return best, tight, OPT


def adversary_step(seed, K, iters, restarts, M=8, k=3):
    """Hill climbing that minimizes the best corner of the step (corner_step) over instances with K factors."""
    rng = np.random.default_rng(seed)
    worst = None
    for _ in range(restarts):
        xs = rng.normal(size=K) * rng.uniform(0.5, 5)
        lam = 10 ** rng.uniform(-1, 4, size=M)
        u = rng.normal(size=(M, K))
        u /= np.linalg.norm(u, axis=1, keepdims=True)
        b = lam[:, None] * u
        y = b @ xs + 10 ** rng.uniform(-2, 1.5, size=M) * rng.choice([1, 1, -1], size=M)
        f = corner_step(b, y, k)
        for _ in range(iters):
            b2, y2 = b.copy(), y.copy()
            i = rng.integers(0, M)
            v = rng.random()
            if v < 0.3:
                b2[i] *= 10 ** rng.normal(0, 0.3)
            elif v < 0.55:
                b2[i] += rng.normal(size=K) * 0.2 * np.linalg.norm(b2[i])
            elif v < 0.85:
                y2[i] += rng.normal() * (0.1 + 0.3 * abs(y2[i]))
            else:
                j = rng.integers(0, M)
                b2[i] = b2[j] * (1 + 0.01 * rng.normal(size=K))
                y2[i] = y2[j] * (1 + 0.01 * rng.normal())
            f2 = corner_step(b2, y2, k)
            if f2[2] > 1e-9 and f2[0] <= f[0]:
                b, y, f = b2, y2, f2
        if worst is None or f[0] < worst[0][0]:
            worst = (f, b.copy(), y.copy())
    return worst


# ------------------------------------------------------------------------------------------- the one-tuple scheme itself
def def510_table(b, y, x, k, eps, Fh, Cr, adm, l, keep="minkappa"):
    """The table of the one-tuple scheme (sfTable) at the node x for the row l of T: Algorithm 4.1 over the admitted assets with the
    exactly additive key (floor(r_i c_i / eta), floor(r_i^2 / zeta), 1), r_i = (y_i - b_i.x)_+, and the value
    -r_i c_il, so that every key keeps a set with the smallest exact sum of r_i c_il ('minkappa'); keep='maxscore'
    keeps the largest sum of r_i^2 instead.  Keys outside the box [-Z_lambda, Z_lambda]^K x [0, Z_q] x [0, k] are
    dropped."""
    M, K = b.shape
    eta = math.sqrt(eps * Fh) / (k * math.sqrt(K))
    zeta = eps * Fh / k
    Zl = math.ceil(k * math.sqrt(K) * math.sqrt(k * (2 + eps) / eps)) + k
    Zq = math.ceil((2 + eps) * k / eps)
    r = np.maximum(y - b @ x, 0.0)
    keys = {i: tuple(int(v) for v in np.floor(r[i] * Cr[i] / eta)) + (int(math.floor(r[i] ** 2 / zeta)), 1)
            for i in adm}
    val = {i: (-r[i] * Cr[i, l]) if keep == "minkappa" else r[i] ** 2 for i in adm}
    tab = {(0,) * (K + 2): ((), 0.0)}
    for i in adm:
        new = dict(tab)
        for kap, (U, v) in tab.items():
            kp = tuple(a + c for a, c in zip(kap, keys[i]))
            if max(abs(c) for c in kp[:K]) > Zl or kp[K] > Zq or kp[K + 1] > k:
                continue
            if kp not in new or v + val[i] > new[kp][1]:
                new[kp] = (U + (i,), v + val[i])
        tab = new
    return [U for (U, _) in tab.values()]


def def510_best(b, y, k, eps, Fh, T, rho, ls, keep="minkappa", cfilter=True):
    """The best exact F_LO over the candidates T_A + R of the tables of the one-tuple scheme at the node with residuals rho
    of the rows of T, for the rows l in ls, and the smallest such best over l (the proof needs one given l)."""
    M, K = b.shape
    Bbar = np.vstack([b, np.eye(K)])
    ybar = np.concatenate([y, np.zeros(K)])
    BT = Bbar[list(T)]
    x = np.linalg.solve(BT, ybar[list(T)] - rho)
    Cr = np.linalg.solve(BT.T, Bbar.T).T
    TA = [i for i in T if i < M]
    adm = [i for i in range(M) if i not in TA and (not cfilter or np.max(np.abs(Cr[i])) <= 1 + 1e-9)]
    per_l = []
    for l in ls:
        best = 0.0
        for U in def510_table(b, y, x, k, eps, Fh, Cr, adm, l, keep):
            W = tuple(sorted(set(TA) | set(U)))
            if W and len(W) <= k:
                best = max(best, F_lo(b, y, W))
        per_l.append(best)
    return max(per_l), min(per_l)


def def510_step(b, y, k, eps=EPS):
    """One-step check of the one-tuple scheme (sfCandidates, main_theorem_sf), with one guess F^ = OPT: T of maximal volume among the
    rows of S-bar* (S* the active assets of the optimum at its dual point x0), the lattice step s = sqrt(eps F^)/(C sqrt K),
    C = (k + K) K.  'rule': the corner of the cell around rho0 with sign(drho_m) = -sign(H_lm) for the row l of the
    smallest position of S* if it lies in T, the table of that row (any corner and the worst row l otherwise);
    'cell': the best over the 2^K corners and all rows l.  'small' counts the positions of S* with
    r_i(x0) = sqrt(d_i) w*_i < 2 sqrt(eps OPT / K); the class of main_theorem_sf is small <= 1, where the theorem
    guarantees 'rule' >= 1 - 5 eps.  Controls: 'wrongT' (a K-tuple of non-maximal volume), 'anchorT' (the anchor rows as
    T and no filter |c_i| <= 1: the grid in G-coordinates without nu), 'maxscore' (the table keeps the largest sum of
    scores instead of the smallest Cramer sum; reported)."""
    M, K = b.shape
    OPT, S = opt_lo(b, y, k)
    x0, A = active_point(b, y, list(S))
    Bbar = np.vstack([b, np.eye(K)])
    ybar = np.concatenate([y, np.zeros(K)])
    rows = list(A) + list(range(M, M + K))
    vols = sorted(((abs(np.linalg.det(Bbar[list(T)])), T) for T in itertools.combinations(rows, K)), reverse=True)
    T = vols[0][1]
    BT = Bbar[list(T)]
    Cr = np.linalg.solve(BT.T, Bbar.T).T
    r0 = {i: float(y[i] - b[i] @ x0) for i in A}
    thr = 2 * math.sqrt(eps * OPT / K)
    small = sorted((i for i in A if r0[i] < thr), key=lambda i: r0[i])
    C = (k + K) * K
    s = math.sqrt(eps * OPT) / (C * math.sqrt(K))
    rho0 = ybar[list(T)] - BT @ x0
    lo = np.floor(rho0 / s)
    H = sum((np.outer(Cr[j], Cr[j]) for j in rows if j not in T), np.zeros((K, K)))
    i0 = small[0] if small else (min(A, key=lambda i: r0[i]) if A else None)
    l0 = list(T).index(i0) if i0 is not None and i0 in T else None
    if l0 is not None:
        corner = np.array([0 if H[l0, m] > 0 else 1 for m in range(K)])
        rule = def510_best(b, y, k, eps, OPT, T, s * (lo + corner), [l0])[1]
    else:
        corner = np.round(rho0 / s) - lo
        rule = def510_best(b, y, k, eps, OPT, T, s * (lo + corner), list(range(K)))[1]
    cell = 0.0
    for c in itertools.product((0, 1), repeat=K):
        cell = max(cell, def510_best(b, y, k, eps, OPT, T, s * (lo + np.array(c)), list(range(K)))[0])
        if cell >= 1 - 1e-9:
            break
    rec = dict(OPT=OPT, S=[int(i) for i in S], T=[int(t) for t in T], omega=float(np.max(np.sum(b ** 2, axis=1))),
               small=len(small), in_class=len(small) <= 1, smallT=l0 is not None, rule=rule / OPT, cell=cell / OPT)
    if l0 is not None:
        rec["maxscore"] = def510_best(b, y, k, eps, OPT, T, s * (lo + corner), [l0], keep="maxscore")[1] / OPT
    others = [Tw for v, Tw in vols[1:] if v > 1e-9 * vols[0][0] and v < 0.5 * vols[0][0]]
    if others:
        Tw = others[0]
        rw = Bbar[list(Tw)]
        rhow = ybar[list(Tw)] - rw @ x0
        low = np.floor(rhow / s)
        rec["wrongT"] = max(def510_best(b, y, k, eps, OPT, Tw, s * (low + np.array(c)), list(range(K)))[0]
                            for c in itertools.product((0, 1), repeat=K)) / OPT
    Ta = tuple(range(M, M + K))
    rhoa = -x0
    loa = np.floor(rhoa / s)
    rec["anchorT"] = max(def510_best(b, y, k, eps, OPT, Ta, s * (loa + np.array(c)), list(range(K)), cfilter=False)[0]
                         for c in itertools.product((0, 1), repeat=K)) / OPT
    return rec


def adversary_def510(seed, K, iters, restarts, M=8, k=3):
    """Hill climbing that minimizes the ratio at the node of the proof ('rule' of def510_step) over instances with K
    factors; the instances need not be in the class of main_theorem_sf (it is recorded)."""
    rng = np.random.default_rng(seed)
    worst = None
    for _ in range(restarts):
        xs = rng.normal(size=K) * rng.uniform(0.5, 5)
        lam = 10 ** rng.uniform(-1, 4, size=M)
        u = rng.normal(size=(M, K))
        u /= np.linalg.norm(u, axis=1, keepdims=True)
        b = lam[:, None] * u
        y = b @ xs + 10 ** rng.uniform(-2, 1.5, size=M) * rng.choice([1, 1, -1], size=M)
        if opt_lo(b, y, k)[0] <= 1e-9:
            continue
        f = def510_step(b, y, k)
        for _ in range(iters):
            b2, y2 = b.copy(), y.copy()
            i = rng.integers(0, M)
            v = rng.random()
            if v < 0.3:
                b2[i] *= 10 ** rng.normal(0, 0.3)
            elif v < 0.55:
                b2[i] += rng.normal(size=K) * 0.2 * np.linalg.norm(b2[i])
            elif v < 0.85:
                y2[i] += rng.normal() * (0.1 + 0.3 * abs(y2[i]))
            else:
                j = rng.integers(0, M)
                b2[i] = b2[j] * (1 + 0.01 * rng.normal(size=K))
                y2[i] = y2[j] * (1 + 0.01 * rng.normal())
            if opt_lo(b2, y2, k)[0] <= 1e-9:
                continue
            f2 = def510_step(b2, y2, k)
            if f2["rule"] <= f["rule"]:
                b, y, f = b2, y2, f2
        if worst is None or f["rule"] < worst[0]["rule"]:
            worst = (f, b.copy(), y.copy())
    return worst


# ------------------------------------------------------------------------------------------- adversary
def adversary(seed, target, iters, restarts, M=8, K=2, k=3):
    """Hill climbing that minimizes the ratio of the scheme `target` (a control) on instances with K = 2."""
    rng = np.random.default_rng(seed)
    worst = None
    for _ in range(restarts):
        kind = rng.integers(0, 3)
        xs = rng.normal(size=K) * rng.uniform(0.5, 5)
        lam = 10 ** rng.uniform(-1, 4, size=M)
        ang = rng.uniform(0, 2 * np.pi, size=M)
        b = lam[:, None] * np.stack([np.cos(ang), np.sin(ang)], 1)
        if kind == 0:
            y = b @ xs + 10 ** rng.uniform(-2, 1.5, size=M) * rng.choice([1, 1, -1], size=M)
        elif kind == 1:
            y = (rng.normal(size=M) + 0.3) * np.sqrt(1 + lam ** 2)
        else:
            d0 = rng.normal(size=K)
            d0 /= np.linalg.norm(d0)
            sgn = rng.choice([1, -1], size=M)
            b = lam[:, None] * (sgn[:, None] * d0 + 0.2 * rng.normal(size=(M, K)))
            y = b @ xs + 10 ** rng.uniform(-1.5, 1.5, size=M)

        def score(b, y):
            OPT, _ = opt_lo(b, y, k)
            if OPT <= 1e-9:
                return 1.0
            return scheme(b, y, k, OPT, **SCHEMES[target])[0] / OPT

        f = score(b, y)
        for _ in range(iters):
            b2, y2 = b.copy(), y.copy()
            i = rng.integers(0, M)
            u = rng.random()
            if u < 0.3:
                b2[i] *= 10 ** rng.normal(0, 0.3)
            elif u < 0.55:
                a = rng.normal(0, 0.3)
                b2[i] = np.array([[math.cos(a), -math.sin(a)], [math.sin(a), math.cos(a)]]) @ b2[i]
            elif u < 0.85:
                y2[i] += rng.normal() * (0.1 + 0.3 * abs(y2[i]))
            else:
                j = rng.integers(0, M)
                b2[i] = b2[j] * (1 + 0.01 * rng.normal(size=K))
                y2[i] = y2[j] * (1 + 0.01 * rng.normal())
            f2 = score(b2, y2)
            if f2 <= f:
                b, y, f = b2, y2, f2
        if worst is None or f < worst[0]:
            worst = (f, b.copy(), y.copy())
    return worst


def main():
    part = sys.argv[1]
    if part in ("rand", "cluster", "ortho"):
        rng = np.random.default_rng({"rand": 1, "cluster": 2, "ortho": 3}[part])
        for t in range(40):
            b, y = gen(rng, part, 9, 2)
            rec = dict(part=part, t=t, K=2, M=9, k=3)
            rec.update(evaluate(b, y, 3))
            print(json.dumps(rec), flush=True)
    elif part in ("rand30", "cluster30"):
        fam = part[:-2]
        rng = np.random.default_rng({"rand30": 4, "cluster30": 5}[part])
        for t in range(10):
            b, y = gen(rng, fam, 30, 2)
            rec = dict(part=part, t=t, K=2, M=30, k=3)
            rec.update(evaluate(b, y, 3))
            print(json.dumps(rec), flush=True)
    elif part.startswith("onestep_"):
        _, fam, K = part.split("_")
        K = int(K)
        rng = np.random.default_rng(1000 * K + {"rand": 1, "cluster": 2, "ortho": 3}[fam])
        t = 0
        while t < 100:
            b, y = gen(rng, fam, 12, K)
            if opt_lo(b, y, 3)[0] <= 0:
                continue
            rec = dict(part=part, t=t, K=K, M=12, k=3)
            rec.update(onestep(b, y, 3))
            print(json.dumps(rec), flush=True)
            t += 1
    elif part.startswith("lemmas_"):
        _, fam, K = part.split("_")
        K = int(K)
        rng = np.random.default_rng(2000 * K + {"rand": 1, "cluster": 2, "ortho": 3}[fam])
        t = 0
        while t < 100:
            b, y = gen(rng, fam, 12, K)
            if opt_lo(b, y, 3)[0] <= 0:
                continue
            rec = dict(part=part, t=t, K=K, M=12, k=3)
            rec.update(lemmas(b, y, 3))
            print(json.dumps(rec), flush=True)
            t += 1
    elif part.startswith("def510_"):
        _, fam, K = part.split("_")
        K = int(K)
        rng = np.random.default_rng(1000 * K + {"rand": 1, "cluster": 2, "ortho": 3}[fam])
        t = 0
        while t < 100:
            b, y = gen(rng, fam, 12, K)
            if opt_lo(b, y, 3)[0] <= 0:
                continue
            rec = dict(part=part, t=t, K=K, M=12, k=3)
            rec.update(def510_step(b, y, 3))
            print(json.dumps(rec), flush=True)
            t += 1
    elif part.startswith("advdef_"):
        K = int(part.split("_")[1])
        for seed in (201, 202, 203, 204):
            f, b, y = adversary_def510(seed, K, iters=40, restarts=6)
            rec = dict(part=part, seed=seed, K=K, M=8, k=3, b=b.tolist(), y=y.tolist())
            rec.update(f)
            print(json.dumps(rec), flush=True)
    elif part.startswith("advstep_"):
        K = int(part.split("_")[1])
        for seed in (101, 102, 103, 104):
            (f, tight, OPT), b, y = adversary_step(seed, K, iters=40, restarts=6)
            print(json.dumps(dict(part=part, seed=seed, K=K, M=8, k=3, ratio=f, tight=tight, OPT=OPT,
                                  omega=float(np.max(np.sum(b ** 2, axis=1))), b=b.tolist(), y=y.tolist())), flush=True)
    elif part == "k3":
        rng = np.random.default_rng(7)
        t = 0
        while t < 15:
            b, y = gen(rng, "rand", 7, 3)
            rec = dict(part=part, t=t, K=3, M=7, k=3)
            rec.update(evaluate(b, y, 3))
            print(json.dumps(rec), flush=True)
            t += 1
    elif part == "adv":
        for seed, target in ((11, "ggrid"), (32, "step10_key30"), (33, "step10_key30")):
            f, b, y = adversary(seed, target, iters=25, restarts=8)
            rec = dict(part=part, seed=seed, target=target, K=2, M=8, k=3, b=b.tolist(), y=y.tolist())
            rec.update(evaluate(b, y, 3))
            print(json.dumps(rec), flush=True)
    else:
        raise ValueError(part)


if __name__ == "__main__":
    main()
