"""E47: the 3SUM gap of Section 5.5 (Proposition 5.20; Lean `ts_yes`, `ts_le_three`, `ts_no`, `threesum_decide`),
with controls that must fail.

An instance of 3SUM' (three lists LA, LB, LC of integers with |x| <= U: are there a + b = c?) becomes, for K = 3
and k = 3, the M = |LA| + |LB| + |LC| assets with m = 1, d = 1, Sigma_f = I and loadings A(1, 0, a), A(0, 1, b),
-A(1, 1, c), A = 5(U + 1).  Row form as in e45_universal.py: rows b_i = B_i, targets y_i = 1; F_LO and F_LS exactly
(e45_universal.selfconsistent, F_ls); OPT(k) by enumeration of the supports with at most k names.
Proposition 5.20: OPT_LO(3) = OPT_LS(3) = 3 on YES instances; on NO instances every support with at most three
names, with long-only or long-short weights, has objective at most (2(1+3U)^2 + 9)/A^2 < 1.
Controls (each must fail, i.e. let a NO instance get close to 3): 'light' (A = 1: no heavy scale), 'twofactor'
(K = 2 with loadings A(1, a), A(1, b), -A(2, c): the weights of a hedge are not pinned; 'twofactor_cross' is the best
triple with one asset of each list, an exact hedge with the weights (1 + x, 1 - x, 1), x = (c - a - b)/(a - b), and the
value 9/(3 + 2x^2); 'same_sum' records whether two numbers of one list add up to a number of LC, which in this encoding
gives an exact hedge with unit weights and the value 3), 'k4' (k = 4 on the instances of the proposition: a hedge with
fractional weights, e.g. lambda a + (1 - lambda) a' + b = c).
Part 'gap': 200 random instances, n = 2..4 integers per list, U = 2..60; half of them with a planted solution.
Usage:  python3 -I e47_threesum.py gap > results/E47/gap.jsonl
"""
import itertools
import json
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from e45_universal import F_ls, F_lo  # noqa: E402


def rows(LA, LB, LC, A, K=3):
    if K == 3:
        r = [A * np.array([1.0, 0.0, a]) for a in LA] + [A * np.array([0.0, 1.0, b]) for b in LB] \
            + [-A * np.array([1.0, 1.0, c]) for c in LC]
    else:
        r = [A * np.array([1.0, a]) for a in LA] + [A * np.array([1.0, b]) for b in LB] \
            + [-A * np.array([2.0, c]) for c in LC]
    return np.array(r, dtype=float)


def opt(b, k, ls=False):
    y = np.ones(len(b))
    best = 0.0
    for r in range(1, k + 1):
        for S in itertools.combinations(range(len(b)), r):
            v = F_ls(b, y, S)[0] if ls else F_lo(b, y, S)
            best = max(best, v)
    return best


def gen(rng, yes):
    while True:
        n, U = int(rng.integers(2, 5)), int(rng.integers(2, 61))
        LA, LB, LC = (list(map(int, rng.integers(-U, U + 1, size=n))) for _ in range(3))
        if yes:
            a, b = LA[int(rng.integers(n))], LB[int(rng.integers(n))]
            if abs(a + b) > U:
                continue
            LC[int(rng.integers(n))] = a + b
        has = any(a + b == c for a in LA for b in LB for c in LC)
        if has == yes:
            return n, U, LA, LB, LC


def part_gap():
    rng = np.random.default_rng(4700)
    for t in range(200):
        yes = t % 2 == 0
        n, U, LA, LB, LC = gen(rng, yes)
        A = 5 * (U + 1)
        b = rows(LA, LB, LC, A)
        rec = dict(part='gap', t=t, yes=yes, n=n, U=U, M=3 * n, A=A,
                   bound=(2 * (1 + 3 * U) ** 2 + 9) / A ** 2,
                   omega=float(np.max(np.sum(b ** 2, axis=1))),
                   lo=opt(b, 3), ls=opt(b, 3, ls=True))
        if not yes:
            rec['light'] = opt(rows(LA, LB, LC, 1.0), 3)
            b2 = rows(LA, LB, LC, A, K=2)
            rec['twofactor'] = opt(b2, 3)
            y2 = np.ones(len(b2))
            rec['twofactor_cross'] = max(F_lo(b2, y2, (i, n + j, 2 * n + l))
                                         for i in range(n) for j in range(n) for l in range(n))
            rec['same_sum'] = any(L[i] + L[j] == c for L in (LA, LB) for i in range(n) for j in range(i + 1, n)
                                  for c in LC)
            rec['k4'] = opt(b, 4)
        print(json.dumps(rec), flush=True)


def main():
    if sys.argv[1] == 'gap':
        part_gap()
    else:
        raise ValueError(sys.argv[1])


if __name__ == '__main__':
    main()
