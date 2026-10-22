"""E45: the scheme without omega for long-only portfolios with K factors on all instances (Theorem 5.13 of the paper,
Lean `main_theorem_univ`): one-step checks at the node of the proof, with controls.

G-coordinates as in e44_scalefree.py: asset rows b_i (|b_i|^2 = omega_i), targets y_i, anchor rows (e_l, 0);
Q_S(x) = |x|^2 + sum_{i in S} (y_i - b_i.x)_+^2, F_LO(S) = min_x Q_S(x), computed exactly by enumeration of the
self-consistent active sets (least squares by QR, so that leverages up to 1e10 stay accurate); OPT(k) by enumeration
of the supports.

The step of the proof, with one guess F^ = OPT and eps = 0.05 (all parameters as in Definition 5.12 / UniversalScheme.lean):
  tau = sqrt(eps F^)/(3k); the positions of the optimum split into large (weight >= tau) and small ones;
  J' = the small positions kept by Caratheodory's theorem for cones (elimination along null combinations; at most K
  assets, nonnegative weights with the same vector sum and a sum of weights that does not grow); T = a K-tuple of maximal volume among the large rows and the anchors (the witness basis);
  T2 = a K-tuple of maximal volume among the large rows, J' and the anchors (the lattice basis);
  the node solves y_T2 - B_T2 x = s * floor(rho0 / s), s = sqrt(eps F^)/(12k(k+1)K sqrt K) (the corner of the proof);
  the knapsack of Algorithm 4.1 over the assets outside T and J' with |c_i|_inf <= 1 (Cramer coordinates of T), the
  additive key (floor(r_i c_i / eta), floor(r_i^2 / zeta), 1), eta = sqrt(eps F^)/(12 k^2 sqrt K), zeta = eps F^/k,
  the box of the definition; a table keeps the largest score sum per key.
Reported per instance: the number of small positions of the optimum in the sense of Remark 5.15
(sqrt(d_i) w*_i < 2 sqrt(eps OPT / K); the class of the one-tuple scheme, Lean main_theorem_sf, is <= 1), the number of small positions in the
sense of the proof (< tau) and |J'|; 'dp' = F_LO(T_A + J' + R)/OPT for the set R of the table in the key of the
large assets outside T; 'worst' = the smallest such ratio over ALL subsets R of the admitted assets with that key
(not only the survivors of the table); 'cert' = the smallest value of the witness of the proof over the same sets,
divided by OPT (the theorem: >= 1 - 2 eps); 'best' = the best candidate of the table.
Controls at the same instances (each must fail somewhere): 'key30' (key widths x30: worst ratio over the bucket),
'noJ' (no forced small assets: J' empty, the small assets enter the knapsack when admitted; worst ratio over the
bucket of the admitted part of the optimum), 'gridT' (the node on the lattice in the residual coordinates of T
instead of T2: the witness of the proof over the bucket), 'Tall' (T of maximal volume among all rows of the
optimum, small ones included, as in Remark 5.15, the small assets outside T forced, the lattice in the coordinates of
T: the witness of the proof over the bucket; -inf when a row of T gets a negative weight).
Usage:  python3 -I e45_universal.py <part> > results/E45/<part>.jsonl
        part: step_<family>_<K> (family hedge, rand, cluster, ortho; K = 2, 3; 100 instances, M = 10, k = 4),
              adv_<K> (hill climbing against 'worst' at the node of the proof)
"""
import itertools
import json
import math
import sys

import numpy as np

EPS = 0.05


# ------------------------------------------------------------------------------------------- exact values
def F_ls(b, y, A):
    K = b.shape[1]
    if len(A) == 0:
        return 0.0, np.zeros(K)
    A = list(A)
    Mx = np.vstack([b[A], np.eye(K)])
    t = np.concatenate([y[A], np.zeros(K)])
    x = np.linalg.lstsq(Mx, t, rcond=None)[0]
    r = t - Mx @ x
    return float(r @ r), x


def selfconsistent(b, y, S, tol=1e-10):
    """Value F_LO(S), the dual point and the active subset (Theorem X: the best self-consistent subset)."""
    best, bx, bA = -1.0, np.zeros(b.shape[1]), ()
    for r in range(0, len(S) + 1):
        for A in itertools.combinations(S, r):
            val, x = F_ls(b, y, A)
            if r and np.any(y[list(A)] - b[list(A)] @ x < -tol * (1 + np.abs(y[list(A)]))):
                continue
            if val > best:
                best, bx, bA = val, x, A
    return best, bx, bA


def F_lo(b, y, S):
    return selfconsistent(b, y, list(S))[0]


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
    if fam == "hedge":
        nh = int(rng.integers(2, min(5, M - 2) + 1))
        nl = M - nh
        xs = rng.normal(size=K) * rng.uniform(0.5, 3)
        bl = rng.normal(size=(nl, K)) * rng.uniform(0.2, 2, size=(nl, 1))
        yl = bl @ xs + np.abs(rng.normal(size=nl)) * rng.uniform(0.3, 3)
        lam = 10 ** rng.uniform(2, 5, size=nh)
        u = rng.normal(size=(nh, K))
        u /= np.linalg.norm(u, axis=1, keepdims=True)
        bh = lam[:, None] * u
        yh = bh @ xs + rng.uniform(-0.5, 0.5, size=nh) * rng.uniform(0, 2)
        b, y = np.vstack([bl, bh]), np.concatenate([yl, yh])
        p = rng.permutation(M)
        return b[p], y[p]
    if fam == "rand":
        L = rng.uniform(0, 3)
        lam = 10 ** rng.uniform(-1, L, size=M)
        u = rng.normal(size=(M, K))
        u /= np.linalg.norm(u, axis=1, keepdims=True)
        b = lam[:, None] * u
        y = (rng.normal(size=M) + 0.3) * np.sqrt(1 + lam ** 2) * 10 ** rng.uniform(-0.5, 0.5, size=M)
        return b, y
    if fam == "cluster":
        lam = 10 ** rng.uniform(1, 3)
        nh = int(rng.integers(2, 5))
        u0 = rng.normal(size=K)
        u0 /= np.linalg.norm(u0)
        bh = lam * (u0 + 0.05 * rng.normal(size=(nh, K)))
        yh = lam * (1 + 0.02 * rng.normal(size=nh)) * rng.uniform(0.5, 2)
        nl = M - nh
        bl = rng.normal(size=(nl, K)) * rng.uniform(0.1, 2, size=(nl, 1))
        yl = rng.normal(size=nl) * 2 + 1
        return np.vstack([bh, bl]), np.concatenate([yh, yl])
    if fam == "ortho":
        lam = 10 ** rng.uniform(1, 3)
        b, y = np.zeros((M, K)), np.zeros(M)
        for l in range(K):
            b[l, l], y[l] = lam, 1.0
        b[K:] = rng.normal(size=(M - K, K)) * rng.uniform(0.01, 1, size=(M - K, 1))
        y[K:] = np.abs(rng.normal(size=M - K)) * rng.uniform(0.01, 0.3)
        return b, y
    raise ValueError(fam)


# ------------------------------------------------------------------------------------------- the step
def maxvol(Bbar, rows, K):
    best, arg = -1.0, None
    for T in itertools.combinations(rows, K):
        v = abs(np.linalg.det(Bbar[list(T)]))
        if v > best:
            best, arg = v, T
    return arg


def caratheodory(b, w, J):
    """Caratheodory's theorem for cones by elimination: while the rows of J' (initially J) are linearly dependent,
    move along a null combination (oriented so that the sum of the weights does not grow) until a weight vanishes.
    The result has linearly independent rows (at most K), nonnegative weights mu with sum_J' mu_j b_j = sum_J w_j b_j
    and sum mu <= sum_J w (Lemma 5.11 uses the convex version, with at most K + 1 rows and the same sum; both are
    candidates of the scheme)."""
    rho = {j: float(w[j]) for j in J if w[j] > 0}
    while rho:
        S = list(rho)
        nrm = np.array([np.linalg.norm(b[j]) for j in S])
        U = np.array([b[j] for j in S]).T / nrm
        if np.linalg.matrix_rank(U, tol=1e-10) == len(S):
            break
        c = np.linalg.svd(U)[2][-1] / nrm
        if c.sum() < 0:
            c = -c
        pos = [n for n in range(len(S)) if c[n] > 1e-15 * np.max(np.abs(c))]
        theta = min(rho[S[n]] / c[n] for n in pos)
        for n, j in enumerate(S):
            rho[j] -= theta * c[n]
        rho = {j: v for j, v in rho.items() if v > 1e-14 * (1 + sum(w[i] for i in J))}
    return rho


def params(k, K, Fh, eps):
    q = math.sqrt(eps * Fh)
    return dict(tau=q / (3 * k), s=q / (12 * k * (k + 1) * K * math.sqrt(K)), eta=q / (12 * k * k * math.sqrt(K)),
                zeta=eps * Fh / k, Zk=math.ceil(12 * k * k * math.sqrt(K) * math.sqrt(k * (4 + eps) / eps)) + k,
                Zq=math.ceil((4 + eps) * k / eps))


def node_of(Bbar, ybar, T2, x0, s):
    BT = Bbar[list(T2)]
    rho0 = ybar[list(T2)] - BT @ x0
    z = np.floor(rho0 / s)
    return np.linalg.solve(BT, ybar[list(T2)] - s * z)


def keys_at(b, y, x, lam, pool, eta, zeta):
    r = np.maximum(y - b @ x, 0.0)
    return {i: tuple(int(v) for v in np.floor(r[i] * lam[i] / eta)) + (int(math.floor(r[i] ** 2 / zeta)), 1)
            for i in pool}, r


def knap(pool, key, val, box_ok):
    """Algorithm 4.1 with the additive key: every set of the table is kept and extended; keys outside the box are
    dropped; of the sets with the same key the one with the largest value is kept."""
    K1 = len(next(iter(key.values()))) if key else 1
    tab = {(0,) * K1: ((), 0.0)}
    for i in pool:
        new = dict(tab)
        for kap, (U, v) in tab.items():
            kp = tuple(a + c for a, c in zip(kap, key[i]))
            if not box_ok(kp):
                continue
            if kp not in new or v + val[i] > new[kp][1]:
                new[kp] = (U + (i,), v + val[i])
        tab = new
    return tab


def witness(Bbar, ybar, M, K, T, lam, x, R, Jp, mu):
    """Objective sum (2 y w - w^2) of the witness of the proof: r_+(x) on R, r(x) on the anchors outside T, mu on
    J', the rows of T by Cramer stationarity; and the smallest weight of an asset row of T (long-only if >= 0)."""
    rn = ybar - Bbar @ x
    w = np.zeros(M + K)
    for i in R:
        w[i] = max(rn[i], 0.0)
    for a in range(M, M + K):
        if a not in T:
            w[a] = rn[a]
    for j in Jp:
        w[j] = mu[j]
    F = sum(w[i] * lam[i] for i in range(M + K) if i not in T)
    for l, t in enumerate(T):
        w[t] = -F[l]
    obj = float(np.sum(2 * ybar * w - w ** 2))
    minT = min([w[t] for t in T if t < M], default=float("inf"))
    return obj, minT


def bucket(pool, key, target):
    """All subsets of the admitted assets with the key and the count of the target."""
    kt = tuple(sum(key[i][c] for i in target) for c in range(len(next(iter(key.values()))))) if target else None
    if not target:
        return [()]
    return [R for R in itertools.combinations(pool, len(target))
            if tuple(sum(key[i][c] for i in R) for c in range(len(kt))) == kt]


def step(b, y, k, eps=EPS):
    M, K = b.shape
    OPT, S = opt_lo(b, y, k)
    _, x0, A = selfconsistent(b, y, list(S))
    A = list(A)
    Bbar, ybar = np.vstack([b, np.eye(K)]), np.concatenate([y, np.zeros(K)])
    w = {i: float(y[i] - b[i] @ x0) for i in A}
    P = params(k, K, OPT, eps)
    AN = [i for i in A if w[i] >= P["tau"]]
    AJ = [i for i in A if w[i] < P["tau"]]
    anchors = list(range(M, M + K))
    mu = caratheodory(b, w, AJ)
    Jp = sorted(mu)
    T = maxvol(Bbar, AN + anchors, K)
    T2 = maxvol(Bbar, AN + Jp + anchors, K)
    lam = np.linalg.solve(Bbar[list(T)].T, Bbar.T).T
    TA = [t for t in T if t < M]
    US = [i for i in AN if i not in TA]
    thr = 2 * math.sqrt(eps * OPT / K)
    rec = dict(OPT=OPT, S=[int(i) for i in S], omega=float(np.max(np.sum(b ** 2, axis=1))),
               small=sum(1 for i in A if w[i] < thr), tight=len(AJ), Jp=len(Jp),
               heavyJp=sum(1 for j in Jp if np.max(np.abs(lam[j])) > 1 + 1e-9))
    rec["in_class"] = rec["small"] <= 1

    def run(T, T2, Jp, mu, target, cfac=1.0, grid=None):
        lam = np.linalg.solve(Bbar[list(T)].T, Bbar.T).T
        TA = [t for t in T if t < M]
        x = node_of(Bbar, ybar, grid if grid is not None else T2, x0, P["s"])
        pool = [i for i in range(M) if i not in TA and i not in Jp and np.max(np.abs(lam[i])) <= 1 + 1e-9]
        key, r = keys_at(b, y, x, lam, pool, cfac * P["eta"], cfac * P["zeta"])
        Zk, Zq = P["Zk"], P["Zq"]

        def box_ok(kp):
            return max(abs(v) for v in kp[:K]) <= Zk and 0 <= kp[K] <= Zq and kp[K + 1] <= k

        target = [i for i in target if i in pool]
        out = {}
        if pool:
            tab = knap(pool, key, {i: r[i] ** 2 for i in pool}, box_ok)
            kt = tuple(sum(key[i][c] for i in target) for c in range(K + 2)) if target else (0,) * (K + 2)
            if kt in tab:
                out["dp"] = F_lo(b, y, sorted(set(TA) | set(Jp) | set(tab[kt][0]))) / OPT
            best = 0.0
            for U, _ in tab.values():
                X = sorted(set(TA) | set(Jp) | set(U))
                if X and len(X) <= k:
                    best = max(best, F_lo(b, y, X))
            out["best"] = best / OPT
        else:
            out["dp"] = out["best"] = F_lo(b, y, sorted(set(TA) | set(Jp))) / OPT
        worst, cert, minT = float("inf"), float("inf"), float("inf")
        for R in (bucket(pool, key, target) if pool else [()]):
            X = sorted(set(TA) | set(Jp) | set(R))
            worst = min(worst, F_lo(b, y, X) / OPT)
            o, mt = witness(Bbar, ybar, M, K, T, lam, x, R, Jp, mu)
            cert, minT = min(cert, o / OPT if mt >= -1e-12 else -float("inf")), min(minT, mt)
        out.update(worst=worst, cert=cert, minT=minT)
        return out

    main = run(T, T2, Jp, mu, US)
    rec.update(main)
    rec["key30"] = run(T, T2, Jp, mu, US, cfac=30.0)["worst"]
    rec["noJ"] = run(T, T2, [], {}, US + AJ)["worst"]
    g = run(T, T2, Jp, mu, US, grid=T)
    rec["gridT"] = g["cert"]
    # the basis of Remark 5.15 (main_theorem_sf): T of maximal volume among all rows of the optimum (small ones included), the small
    # assets outside T forced, the lattice in the residual coordinates of T
    Ta = maxvol(Bbar, A + anchors, K)
    Jo = [j for j in AJ if j not in Ta]
    lam_a = np.linalg.solve(Bbar[list(Ta)].T, Bbar.T).T
    mu_a = {j: w[j] for j in Jo}
    ga = run(Ta, Ta, Jo, mu_a, [i for i in AN if i not in Ta], grid=Ta)
    rec["Tall"] = ga["cert"]
    rec["Tall_minT"] = ga["minT"]
    rec["Tall_tight_in_T"] = sum(1 for j in AJ if j in Ta)
    return rec


def adversary(seed, K, iters, restarts, M=8, k=3):
    rng = np.random.default_rng(seed)
    worst = None
    for _ in range(restarts):
        b, y = gen(rng, "hedge", M, K)
        if opt_lo(b, y, k)[0] <= 1e-9:
            continue
        f = step(b, y, k)
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
            if np.max(np.sum(b2 ** 2, axis=1)) > 1e10 or opt_lo(b2, y2, k)[0] <= 1e-9:
                continue
            f2 = step(b2, y2, k)
            if f2["worst"] <= f["worst"]:
                b, y, f = b2, y2, f2
        if worst is None or f["worst"] < worst[0]["worst"]:
            worst = (f, b.copy(), y.copy())
    return worst


def main():
    part = sys.argv[1]
    if part.startswith("step_"):
        _, fam, K = part.split("_")
        K = int(K)
        rng = np.random.default_rng(4500 + 10 * K + {"hedge": 1, "rand": 2, "cluster": 3, "ortho": 4}[fam])
        t = 0
        while t < 100:
            b, y = gen(rng, fam, 10, K)
            if opt_lo(b, y, 4)[0] <= 1e-9:
                continue
            rec = dict(part=part, t=t, K=K, M=10, k=4)
            rec.update(step(b, y, 4))
            print(json.dumps(rec), flush=True)
            t += 1
    elif part.startswith("adv_"):
        K = int(part.split("_")[1])
        for seed in (451, 452, 453, 454):
            f, b, y = adversary(seed, K, iters=30, restarts=5)
            rec = dict(part=part, seed=seed, K=K, M=8, k=3, b=b.tolist(), y=y.tolist())
            rec.update(f)
            print(json.dumps(rec), flush=True)
    else:
        raise ValueError(part)


if __name__ == "__main__":
    main()
