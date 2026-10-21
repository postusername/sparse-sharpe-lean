"""E35 check: the check of the localized nodes of Section 6.4 of the paper (the paragraph "The localized scheme" and
the last column of Table "The stress regime at scale", tab:scale).  In e35_scale.py the radius of the localized nodes
used gval = min(g_k(that), g_k(t_h)) while the centre was always that (the minimizer returned by the conic solver and
L-BFGS), whereas Definition 5.22 takes radius and centre at the same point.  This script replays every instance of
results/E35/<M>_<K>_<k>.jsonl in which the certificate fails (same seeds and generator), recomputes that and
g_k(that), and counts the localized nodes with the radius sqrt(g_k(that) - theta) around G that (coordinatewise
condition, over all guesses, as in e35_scale.py); it prints the instances in which g_k(that) differs from the stored
G or the count differs from the stored one, and per K the medians and maxima of the stored and the recomputed counts.
Run from this directory: python3 -I e35_loccheck.py > results/E35/e35_loccheck.log  (about 15 seconds on one core;
only the log).
"""
import json, math, os, statistics as st, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import e34_localized as E
EPS = 0.05
here = os.path.dirname(os.path.abspath(__file__))
diff = []
newc = {}
oldc = {}
for M in (50, 200, 1000, 2000):
    for K in (1, 2, 3):
        for k in (3, 5, 10):
            R = [json.loads(l) for l in open(os.path.join(here, 'results', 'E35', f'{M}_{K}_{k}.jsonl')) if l.strip()]
            rng = np.random.default_rng(R[0]['seed'])
            for r in R:
                m, d, B, Sf = E.stress_instance(rng, M, K)
                if r['cert']:
                    continue
                P = np.linalg.inv(Sf); P = (P + P.T) / 2
                Fh, Sh = r['Fh'], None
                g1, that = E.relaxation(m, d, B, Sf, k)
                gthat = E.gk(m, d, B, P, k, that)
                theta = Fh / (1 - 2 * EPS)
                J = max(0, math.ceil(math.log2(max(gthat / Fh, 1.0))) - 1)
                G = np.linalg.cholesky(P).T
                Gt = G @ that
                omega = r['omega']
                cube = 0
                for j in range(J + 1):
                    p = E.params(EPS, Fh * 2 ** j, k, K, omega)
                    _, c, _ = E.loc_nodes(Gt, p['s'], p['Z'], gthat, theta, K, count_only=True)
                    cube += c
                key = (M, K)
                newc.setdefault(K, []).append(cube); oldc.setdefault(K, []).append(r['loc_cube'])
                if cube != r['loc_cube'] or abs(gthat - r['G']) > 1e-12 * max(1, abs(r['G'])):
                    diff.append((M, K, k, r['it'], r['G'], gthat, r['loc_cube'], cube))
print('instances with a failing certificate:', sum(len(v) for v in newc.values()))
print('instances where g_k(that) differs from the stored G or the count differs:', len(diff))
for x in diff[:40]:
    print('  M=%d K=%d k=%d it=%d  stored G=%.12g  g_k(that)=%.12g  rel.diff=%.2e  nodes stored=%d  recomputed=%d' % (
        x[0], x[1], x[2], x[3], x[4], x[5], (x[5] - x[4]) / x[4], x[6], x[7]))
for K in sorted(newc):
    print('K=%d: median nodes stored %s, recomputed %s; max stored %d, recomputed %d' % (
        K, st.median(oldc[K]), st.median(newc[K]), max(oldc[K]), max(newc[K])))
