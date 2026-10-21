"""E31: Table "Formal size bounds" (tab:bounds) of Section 6.6 of the paper, with its complete version
results/E31/e31_table.md (all 62 instances): formal bounds on the size of the family of candidates of the old scheme
(dynamic program over moments and the Gram matrix, Lean `main_theorem_simple`) and of the scheme without the Gram
matrix (Lean `main_theorem_clipped`), against the number of supports.  For every model of data_real.py (FF49 with
K = 1, 3, 5, window July 2016 - June 2026; port1 and port5 with K = 1, 3, 5; the S&P 500 and the Russell 3000 with
K = 1, 3, 5, 10), omega = max_i B_i'Sf B_i/d_i of the model, k in {5, 10, 20, 50} below M and eps = 0.05, it prints
log10 of: the number of supports with at most k names, sum_{j=1..k} C(M, j); the explicit bound of the old scheme,
(J+1)(2 anchorZ+1)^K (tableBoundAnchorSym+1) of Factor/Practical.lean, and its polynomial form
C_K M^{K+K(K+1)/2} eps^{-K} (k(1+omega))^{2+4K+K(K+1)}, C_K = 8K (12K)^K (141K)^K (37K^2)^{K(K+1)/2}; the explicit
bound of the new scheme (Proposition 4.9), (J+1)(2Z+1)^K ((2Q+1)^K (k+1) + 1) with J = ceil(log2 k(1+omega)),
Z = ceil((1 + k omega) sqrt(K/eps) + 1/2) and Q = k + ceil(sqrt(5 omega k^3 K/eps)) of Definition 4.7, and its
polynomial form 8 (60K)^K eps^{-K} (k(1+omega))^{3K+2}; and the difference of the two explicit bounds; at the end, in
how many instances the new bound is below the old explicit one and below the number of supports.  Run from this
directory: python3 -I e31_size_bounds.py > results/E31/e31.log  (a few seconds); writes results/E31/e31_table.md.
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import data_real as D

OUT = os.path.join(HERE, 'results', 'E31')


def log10_supports(M, k):
    """log10 of the number of supports with at most k names, sum_{j=1..k} C(M, j) (exact integer sum)."""
    return math.log10(sum(math.comb(M, j) for j in range(1, k + 1)))


def old_bound_log10(M, K, k, eps, om):
    C = 8 * K * (12 * K) ** K * (141 * K) ** K * (37 * K * K) ** (K * (K + 1) // 2)
    return (math.log10(C) + (K + K * (K + 1) // 2) * math.log10(M) + K * math.log10(1 / eps)
            + (2 + 4 * K + K * (K + 1)) * math.log10(k * (1 + om)))


def old_explicit_log10(M, K, k, eps, om):
    """(J+1)(2 anchorZ+1)^K (tableBoundAnchorSym+1): the explicit bound of the old scheme (Factor/Practical.lean)."""
    J = math.ceil(math.log2(k * (1 + om)))
    c = 32 * k * (1 + k * om)
    Z = math.ceil(math.sqrt(K * (K + k * om) / (2 * (eps / c))) + 0.5)
    so = math.sqrt(max(1.0, om))
    a = 2 * math.ceil(so * (48 * M * math.sqrt(K) * math.sqrt((k + K) * (k * (1 + k * om)) / eps)) + M) + 1
    b = 2 * math.ceil(8 * (k + K) * M * K * so ** 2 + M) + 1
    tb = K * math.log10(a) + (K * (K + 1) // 2) * math.log10(b) + math.log10(k + K + 1)
    return math.log10(J + 1) + K * math.log10(2 * Z + 1) + tb


def new_bound_log10(K, k, eps, om):
    J = math.ceil(math.log2(k * (1 + om)))
    Z = math.ceil((1 + k * om) * math.sqrt(K / eps) + 0.5)
    Q = k + math.ceil(math.sqrt(5 * om * k ** 3 * K / eps))
    inner = (2 * Q + 1) ** K * (k + 1) + 1
    return math.log10(J + 1) + K * math.log10(2 * Z + 1) + math.log10(inner), dict(J=J, Z=Z, Q=Q)


def new_poly_log10(K, k, eps, om):
    return math.log10(8) + K * math.log10(60 * K) + K * math.log10(1 / eps) + (3 * K + 2) * math.log10(k * (1 + om))


if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    eps = 0.05
    rows = []
    models = [("FF49", [1, 3, 5]), ("port1", [1, 3, 5]), ("port5", [1, 3, 5]),
              ("SP500", [1, 3, 5, 10]), ("Russell", [1, 3, 5, 10])]
    hdr = ("| model | M | K | ω | k | log10 Σ_{j≤k} C(M,j) | old explicit | old poly | new explicit | new poly "
           "| old expl. − new |")
    print(hdr)
    out = [hdr, "|---|---|---|---|---|---|---|---|---|---|---|"]
    for nm, Ks in models:
        for K in Ks:
            mdl = D.model(nm, K)
            M, om = mdl["M"], mdl["omega"]
            for k in (5, 10, 20, 50):
                if k >= M:
                    continue
                lc = log10_supports(M, k)
                lo = old_bound_log10(M, K, k, eps, om)
                le = old_explicit_log10(M, K, k, eps, om)
                ln, par = new_bound_log10(K, k, eps, om)
                lp = new_poly_log10(K, k, eps, om)
                assert ln <= lp + 1e-9, (nm, K, k, ln, lp)
                line = "| %s | %d | %d | %.2f | %d | %.1f | %.1f | %.1f | %.1f | %.1f | %.1f |" % (
                    mdl["name"], M, K, om, k, lc, le, lo, ln, lp, le - ln)
                print(line)
                out.append(line)
                rows.append((mdl["name"], M, K, om, k, lc, lo, ln, lp, le))
    with open(os.path.join(OUT, "e31_table.md"), "w") as fh:
        fh.write("\n".join(out) + "\n")
    better = sum(1 for r in rows if r[7] < r[9])
    print("the new bound is below the old explicit one in %d of %d cases; below the number of supports with at most k "
          "names in %d of %d" % (better, len(rows), sum(1 for r in rows if r[7] < r[5]), len(rows)))
    print("difference of log10 (old explicit − new): min %.1f, max %.1f" % (
        min(r[9] - r[7] for r in rows), max(r[9] - r[7] for r in rows)))
