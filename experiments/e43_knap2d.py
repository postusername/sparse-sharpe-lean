"""E43: the natural embedding of two-dimensional knapsack into the long-only problem with K = 2 (work plan v0.26, C2).

Is there a cliff, i.e. a gap 1/poly between YES and NO instances with exponentially large omega, as a reduction from
two-dimensional knapsack (no FPTAS unless P = NP; Magazine and Chern 1984, Korte and Schrader 1981) would need?
Values are exact (Theorem X: the best self-consistent active set), in 50-digit arithmetic (mpmath).
  Test A: two heavy anchor rows (b = sgn*Lam*e_l, y = Lam*c) and identical light items (b = s*(1, 0.5), y = 1): the
          increments of F_LO(anchors + m items) in m are smooth for every Lam in {1, 1e3, 1e8} (no cliff).
  Test B: equipartition with n = 4 (8 numbers in [2^(m-1), 2^m)), items b_j = s*(a_j, L - a_j)/L, y_j = 1, one heavy
          hedge along the target (b = -Lam*t/|t|, y = 0, Lam = 1e12), k = n + 1; the NO instance has a near miss by one
          unit (a YES instance with 2 added to one number of the half S*); for each m the scale s is chosen to make
          the relative gap (V_yes - V_no)/V_yes as large as possible.  The gap falls like 4^(-m).
Usage: python3 -I e43_knap2d.py A > results/E43/testA.log;  python3 -I e43_knap2d.py B > results/E43/testB.log
"""
import itertools
import random
import sys

import mpmath as mp

mp.mp.dps = 50
K = 2



def F_ls(b, y, A, K):
    if not A:
        return mp.mpf(0), mp.matrix(K, 1)
    H = mp.eye(K)
    g = mp.matrix(K, 1)
    for i in A:
        for p in range(K):
            g[p] += b[i][p] * y[i]
            for q in range(K):
                H[p, q] += b[i][p] * b[i][q]
    x = mp.lu_solve(H, g)
    val = sum(y[i] ** 2 for i in A) - sum(g[p] * x[p] for p in range(K))
    return val, x


def F_lo(b, y, S, K):
    S = list(S)
    best = mp.mpf(0)
    for r in range(1, len(S) + 1):
        for A in itertools.combinations(S, r):
            val, x = F_ls(b, y, A, K)
            if all(y[i] - sum(b[i][p] * x[p] for p in range(K)) >= -mp.mpf(10) ** (-35) * (1 + abs(y[i])) for i in A):
                if val > best:
                    best = val
    return best



def testA():
    print('Test A: increments of F_LO(anchors + m identical light items)')
    for sgn in (1, -1):
        for Lam in (mp.mpf(1), mp.mpf(10) ** 3, mp.mpf(10) ** 8):
            for c in (mp.mpf('0.5'), mp.mpf(2)):
                b = [[sgn * Lam, 0], [0, sgn * Lam]]
                y = [Lam * c, Lam * c]
                s = mp.mpf('0.3')
                for j in range(8):
                    b.append([s, s * mp.mpf('0.5')]); y.append(mp.mpf(1))
                prev = F_lo(b, y, [0, 1], K)
                inc = []
                for m in range(1, 9):
                    v = F_lo(b, y, [0, 1] + list(range(2, 2 + m)), K)
                    inc.append(float(v - prev)); prev = v
                d2 = max(abs(inc[i + 1] - inc[i]) for i in range(len(inc) - 1))
                print('  sgn %+d Lam %.0e c %.1f  increments %s  max change of increment %.3f' % (
                    sgn, float(Lam), float(c), ' '.join('%.3f' % v for v in inc), d2))


def equipartition_yes(rng, n, m):
    while True:
        a = [rng.randrange(2 ** (m - 1), 2 ** m) for _ in range(2 * n)]
        S = rng.sample(range(2 * n), n)
        rest = [i for i in range(2 * n) if i not in S]
        diff = sum(a[i] for i in S) - sum(a[i] for i in rest)
        if 2 ** (m - 1) <= a[rest[0]] + diff < 2 ** m:
            a[rest[0]] += diff  # now the sum over S equals the sum over the rest
            if len(set(a)) == 2 * n:
                return a


def has_equipartition(a, n):
    A2 = sum(a)
    if A2 % 2:
        return False
    return any(2 * sum(a[i] for i in S) == A2 for S in itertools.combinations(range(len(a)), n))


def equipartition_near(rng, n, m):
    """A NO instance with a near miss by one unit: a YES instance with 2 added to one number of the half S*, so that
    S* and its complement miss A' = total'/2 by exactly one; kept only if no other n-subset hits A'."""
    while True:
        a = equipartition_yes(rng, n, m)
        A2 = sum(a)
        S = next(S for S in itertools.combinations(range(len(a)), n) if 2 * sum(a[i] for i in S) == A2)
        a[S[0]] += 2
        if not has_equipartition(a, n) and max(a) < 2 ** m + 2:
            return a


def equipartition_no(rng, n, m):
    """All 2n numbers odd and A = total/2 odd: every n-subset (n even) has an even sum, so none equals A; near misses
    by one unit exist in general."""
    while True:
        a = [rng.randrange(2 ** (m - 1), 2 ** m) | 1 for _ in range(2 * n)]
        if len(set(a)) == 2 * n and (sum(a) // 2) % 2 == 1:
            assert not has_equipartition(a, n)
            return a


def instance(a, n, s, Lam):
    L = mp.mpf(2) ** (max(a).bit_length() + 1)
    A = mp.mpf(sum(a)) / 2
    t = [A, n * L - A]
    nt = mp.sqrt(t[0] ** 2 + t[1] ** 2)
    b = [[s * aj / L, s * (L - aj) / L] for aj in a]
    y = [mp.mpf(1)] * len(a)
    b.append([-Lam * t[0] / nt, -Lam * t[1] / nt]); y.append(mp.mpf(0))
    return b, y


def opt(b, y, k):
    N = len(y)
    return max(F_lo(b, y, S, K) for S in itertools.combinations(range(N), k))


def testB():
    print('Test B: equipartition, n = 4 (8 numbers ~ 2^m), NO instance with a near miss by one unit, hedge along the target; relative gap (V_yes - V_no)/V_yes')
    rng = random.Random(7)
    n = 4
    for m in (6, 8, 10, 12, 14):
        ay = equipartition_yes(rng, n, m)
        an = equipartition_near(rng, n, m)
        best = None
        for s in (mp.mpf(1), mp.mpf(16), mp.mpf(256), mp.mpf(2) ** 16, mp.mpf(2) ** 24, mp.mpf(2) ** 32):
            Lam = mp.mpf(10) ** 12
            vy = opt(*instance(ay, n, s, Lam), n + 1)
            vn = opt(*instance(an, n, s, Lam), n + 1)
            g = (vy - vn) / vy
            if best is None or g > best[0]:
                best = (g, s, vy, vn)
        print('  m = %2d: largest relative gap %.3e at s = %s (V_yes %.6f, V_no %.6f)' % (
            m, float(best[0]), mp.nstr(best[1], 5), float(best[2]), float(best[3])), flush=True)


if __name__ == '__main__':
    part = sys.argv[1] if len(sys.argv) > 1 else 'B'
    {'A': testA, 'B': testB}[part]()
