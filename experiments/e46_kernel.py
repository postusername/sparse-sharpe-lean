"""E46: the kernel of Section 5.5 (Lean `kerK`, `kernel_value`, `card_kerK_le`) and the one-pass lower bound
(Lean `onepass_lower`), with controls that must fail.

G-coordinates as in e45_universal.py: asset rows b_i (|b_i|^2 = omega_i), targets y_i, Sigma_f = I;
F_LO(S) = min_x |x|^2 + sum_{i in S} (y_i - b_i.x)_+^2 exactly (e45_universal.F_lo), OPT(k) by enumeration.

The kernel (Definition 5.16): for b_i != 0, l = the first coordinate of largest |b_il|, rho = |b_il|, the sign of
b_il, the scale class sigma = floor(log rho / log(1+eps)), the angular grid floor((b_ij/rho)/theta_sigma) for j != l
with theta_sigma = eps/(sqrt(2k) K (1+eps)^(sigma+1)); the rows b_i = 0 form one cell.  Score y_i/rho_i (y_i for
b_i = 0), ties by index; the kernel keeps the k assets of largest score in every cell.  Theorem 5.17:
OPT over the kernel >= (1 - 4 eps) OPT(k).
Controls (each must fail somewhere): 'nogrid' (cells without the angular grid), 'grid30' and 'grid100' (theta x 30,
x 100), 'noscale' (one scale class).

Parts:
  rand_<K>  (K = 1, 2, 3): 120 instances, k = 2, eps in {0.05, 0.1}; families 'crowd' and 'heavycrowd' (40 each,
            M = 24: a few base rows, every asset a copy turned slightly, rescaled within 1 + eps, with its own target;
            in 'heavycrowd' some base rows are heavy hedges) and 'hedge' of e45 (40, M = 12, not crowded).
  lb_<K>    (K = 2, 3): the instances of Proposition 5.19: n^(K-1) assets with m = 0, d = 1 and rows A(1, g/n),
            g in {0..n-1}^(K-1), and one asset with m = 1 and row -A(1, h/n), for every h; k = 2, eps = 1/4,
            A^2 = 8 n^2/(1 - eps).  Reports whether the kernel keeps every asset of the first group and the
            ratio of the controls (all near-optimal pairs contain h: Lean lb_mem_of_good).
Usage:  python3 -I e46_kernel.py <part> > results/E46/<part>.jsonl
"""
import itertools
import json
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from e45_universal import F_lo, gen  # noqa: E402


def opt_over(b, y, k, pool):
    best, arg = 0.0, ()
    for r in range(1, k + 1):
        for S in itertools.combinations(pool, r):
            v = F_lo(b, y, S)
            if v > best:
                best, arg = v, S
    return best, arg


def cell(bi, k, K, eps, grid_mult=1.0, scale=True, grid=True):
    if not np.any(bi):
        return ('z',)
    l = int(np.argmax(np.abs(bi)))
    s = bool(bi[l] >= 0)
    rho = abs(bi[l])
    sig = math.floor(math.log(rho) / math.log(1 + eps)) if scale else 0
    th = grid_mult * eps / (math.sqrt(2 * k) * K * (1 + eps) ** (sig + 1))
    g = tuple(math.floor(bi[j] / rho / th) for j in range(K) if j != l) if grid else ()
    return (l, s, sig, g)


def kernel(b, y, k, eps, **kw):
    M, K = b.shape
    cells = {}
    for i in range(M):
        c = cell(b[i], k, K, eps, **kw)
        rho = np.max(np.abs(b[i]))
        sc = y[i] if rho == 0 else y[i] / rho
        cells.setdefault(c, []).append((sc, -i, i))
    ker = []
    for v in cells.values():
        v.sort(reverse=True)
        ker += [i for _, _, i in v[:k]]
    return sorted(ker), len(cells)


def gen_crowd(rng, M, K, eps, heavy):
    """Crowded cells: a few base rows of similar scale and different directions; every asset is a copy of a base
    row with its direction turned slightly, its scale changed within the factor 1 + eps and its own target.  With
    'heavy', half of the base rows are heavy hedges (scale 10^2..10^4, targets along a common dual point)."""
    nb = int(rng.integers(2, 5))
    xs = rng.normal(size=K) * rng.uniform(0.3, 2)
    u = rng.normal(size=(nb, K))
    u /= np.linalg.norm(u, axis=1, keepdims=True)
    scale = 10 ** rng.uniform(0, 1) * np.ones(nb)
    if heavy:
        scale[: nb // 2 + 1] = 10 ** rng.uniform(2, 4, size=nb // 2 + 1)
    idx = rng.integers(0, nb, size=M)
    # turns of about a twentieth of the angular width of a cell, so that copies share cells
    turn = 0.05 * eps / (2 * K * (1 + eps) * scale[idx])[:, None] * rng.normal(size=(M, K))
    dirs = u[idx] + turn
    dirs /= np.linalg.norm(dirs, axis=1, keepdims=True)
    rho = scale[idx] * (1 + eps * rng.uniform(0, 1, size=M))
    b = rho[:, None] * dirs
    y = b @ xs + rng.normal(size=M) * rng.uniform(0.2, 2) + (0.5 if not heavy else 0.0)
    return b, y


def part_rand(K, seed):
    rng = np.random.default_rng(seed)
    t = 0
    fams = ['crowd', 'heavycrowd', 'hedge']
    while t < 120:
        fam = fams[t % len(fams)]
        k, eps = 2, float(rng.choice([0.05, 0.1]))
        M = 24 if fam != 'hedge' else 12
        if fam == 'hedge':
            b, y = gen(rng, fam, M, K)
        else:
            b, y = gen_crowd(rng, M, K, eps, fam == 'heavycrowd')
        opt, S = opt_over(b, y, k, range(M))
        if opt <= 1e-9:
            continue
        rec = dict(part=f'rand_{K}', t=t, fam=fam, M=M, K=K, k=k, eps=eps,
                   omega=float(np.max(np.sum(b ** 2, axis=1))))
        for name, kw in [('ker', {}), ('nogrid', dict(grid=False)), ('grid30', dict(grid_mult=30.0)),
                         ('grid100', dict(grid_mult=100.0)), ('noscale', dict(scale=False))]:
            ker, ncell = kernel(b, y, k, eps, **kw)
            v, _ = opt_over(b, y, k, ker)
            rec[name] = v / opt
            rec[name + '_size'] = len(ker)
            if name == 'ker':
                rec['cells'] = ncell
                rec['opt_in_ker'] = bool(set(S) <= set(ker))
        print(json.dumps(rec), flush=True)
        t += 1


def part_lb(K, ns):
    eps, k = 0.25, 2
    for n in ns:
        A = math.sqrt(8 * n * n / (1 - eps))
        grid = list(itertools.product(range(n), repeat=K - 1))
        alice = np.array([[A] + [A * gj / n for gj in g] for g in grid])
        na = len(grid)
        for h in range(na):
            b = np.vstack([alice, -alice[h]])
            y = np.concatenate([np.zeros(na), [1.0]])
            opt = F_lo(b, y, [h, na])
            # every other support with at most two names (Lean lb_obj_le: <= 2 n^2/A^2)
            others = max([F_lo(b, y, [i, na]) for i in range(na) if i != h] + [F_lo(b, y, [na])])
            rec = dict(part=f'lb_{K}', n=n, K=K, k=k, eps=eps, h=h, M=na + 1, A=A,
                       omega=float(np.max(np.sum(b ** 2, axis=1))), opt=opt, others=others,
                       bound=2 * n * n / A ** 2)
            for name, kw in [('ker', {}), ('nogrid', dict(grid=False)), ('grid30', dict(grid_mult=30.0)),
                             ('grid100', dict(grid_mult=100.0))]:
                ker, ncell = kernel(b, y, k, eps, **kw)
                v = max([F_lo(b, y, S) for r in (1, 2) for S in itertools.combinations(ker, r)])
                rec[name] = v / opt
                rec[name + '_alice'] = sum(1 for i in ker if i < na)
            print(json.dumps(rec), flush=True)


def main():
    part = sys.argv[1]
    kind, K = part.rsplit('_', 1)
    K = int(K)
    if kind == 'rand':
        part_rand(K, 4600 + K)
    elif kind == 'lb':
        part_lb(K, [4, 8, 16] if K == 2 else [3, 5])
    else:
        raise ValueError(part)


if __name__ == '__main__':
    main()
