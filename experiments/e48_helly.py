"""E48: the Helly bound of Section 5.6 (Lemma 5.21; Lean `objLO_le_helly`, `objLO_le_helly_free`): with V the best
value of a support with at most min(k, K + 1) names, V <= OPT(k) <= (k + 1) V, long-only and long-short, so that
ceil(log2(k + 1)) + 1 guesses V 2^j replace the ceil(log2(sum_i (m_i)_+^2/(d_i L))) + 1 guesses L 2^j of Theorems 5.6
and 5.13 (`main_theorem_univ_sp`, `main_theorem_ls_sp`).

Row form as in e45_universal.py (Sigma_f = I, d = 1): rows b_i, targets y_i; F_LO and F_LS exactly; OPT(k) by
enumeration.  Families: 'hedge', 'rand', 'cluster', 'ortho' of e45 and 'tri': K + 1 heavy assets (scale 10^2..10^5)
whose rows have a vanishing positive combination (an exact hedge: the K + 1 directions add up to zero before each is
normalized and slightly turned, so the weights of the hedge are the norms, not equal for K >= 2), each with a target
close to that of the common dual point, among light random assets: no support with at most K of them hedges, all
K + 1 together do.  k is drawn from K + 1..5; for k = K + 1, V = OPT(k) by definition, so the lemma is tested on the
instances with k > K + 1.
Reported per instance: OPT(k), V (best support with <= min(k, K+1) names) for LO and LS, the ratio OPT/V (the lemma:
<= k + 1), and the number of guesses of Theorem 5.13 with L the best single asset (ceil(log2(sum (m)_+^2/(d L))) + 1)
against ceil(log2(k + 1)) + 1.
Controls (each must fail, i.e. exceed k + 1 somewhere): V over the supports with one name ('single') and with at most
K names ('ksub') in place of K + 1.
Usage:  python3 -I e48_helly.py <part> > results/E48/<part>.jsonl     (part: rand_<K>, K = 1, 2, 3; 100 instances)
"""
import itertools
import json
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from e45_universal import F_lo, F_ls, gen  # noqa: E402


def best(b, y, kmax, ls=False):
    v = 0.0
    for r in range(1, kmax + 1):
        for S in itertools.combinations(range(len(y)), r):
            v = max(v, F_ls(b, y, S)[0] if ls else F_lo(b, y, S))
    return v


def gen_tri(rng, M, K):
    """K + 1 heavy assets whose rows have a vanishing positive combination, among M - K - 1 light random assets."""
    xs = rng.normal(size=K) * rng.uniform(0.3, 2)
    nl = M - K - 1
    bl = rng.normal(size=(nl, K)) * rng.uniform(0.2, 2, size=(nl, 1))
    yl = bl @ xs + rng.normal(size=nl) * rng.uniform(0.2, 1)
    u = rng.normal(size=(K + 1, K))
    u -= u.mean(axis=0)                                   # the K + 1 directions add up to zero
    u /= np.linalg.norm(u, axis=1, keepdims=True)
    lam = 10 ** rng.uniform(2, 5)
    bh = lam * (u + 1e-3 * rng.normal(size=(K + 1, K)))
    yh = bh @ xs + rng.uniform(0.5, 2, size=K + 1)        # positive residuals at the common dual point
    b, y = np.vstack([bl, bh]), np.concatenate([yl, yh])
    p = rng.permutation(M)
    return b[p], y[p]


def part_rand(K, seed):
    rng = np.random.default_rng(seed)
    fams = ['hedge', 'rand', 'cluster', 'ortho', 'tri']
    t = 0
    while t < 100:
        fam = fams[t % len(fams)]
        M = 9
        k = int(rng.integers(K + 1, min(5, M) + 1))
        b, y = gen_tri(rng, M, K) if fam == 'tri' else gen(rng, fam, M, K)
        rec = dict(part='rand_%d' % K, t=t, fam=fam, M=M, K=K, k=k,
                   omega=float(np.max(np.sum(b ** 2, axis=1))))
        for ls in (False, True):
            tag = 'ls' if ls else 'lo'
            opt = best(b, y, k, ls)
            V = best(b, y, min(k, K + 1), ls)
            rec[tag + '_opt'] = opt
            rec[tag + '_V'] = V
            rec[tag + '_single'] = best(b, y, 1, ls)
            rec[tag + '_ksub'] = best(b, y, K, ls)
        if rec['lo_opt'] <= 1e-9:
            continue
        # guesses of Theorem 5.13 with L the best single asset (d = 1, so (m)_+^2/V_ii = y_+^2/(1+|b|^2))
        L = max(max(yi, 0.0) ** 2 / (1 + float(bi @ bi)) for bi, yi in zip(b, y))
        if L > 0:
            rec['J_data'] = math.ceil(math.log2(sum(max(yi, 0.0) ** 2 for yi in y) / L)) + 1
        rec['J_helly'] = math.ceil(math.log2(k + 1)) + 1
        print(json.dumps(rec), flush=True)
        t += 1


def main():
    kind, K = sys.argv[1].rsplit('_', 1)
    if kind != 'rand':
        raise ValueError(sys.argv[1])
    part_rand(int(K), 4800 + int(K))


if __name__ == '__main__':
    main()
