"""The rounding bound of Section 7.7 of the paper: the bound floor((K+1)/2) omega_I' sigma of Theorem 6.18(ii), which
replaces the older K omega_I' sigma, recomputed from the stored results of e29_dual_rounding.py
(results/E29/results_E29.json; the real data are not needed).  Over the instances with fractional multipliers it
prints the range of c_K omega_I' sigma / G*_k, c_K = floor((K+1)/2), next to the range of K omega_I' sigma / G*_k,
the ratio of the loss of the best rounding to the bound min(s, f-s) omega_I' sigma, the loss as a share of G*_k, and
the number of instances in which the floor bound is informative (below G*_k).  Run from this directory after
e29_dual_rounding.py: python3 -I e29_floor_bound.py > results/E29/e29_floor_bound.log  (under a second)."""
import json, os, statistics as st
here = os.path.dirname(os.path.abspath(__file__))
R = [r for r in json.load(open(os.path.join(here, 'results', 'E29', 'results_E29.json')))
     if r.get('f', 0) >= 2 and 'bound_K' in r]
old = [r['K'] * r['om_I'] * r['sigma'] / r['Gstar'] for r in R]
new = [((r['K'] + 1) // 2) * r['om_I'] * r['sigma'] / r['Gstar'] for r in R]
ratio = [r['round_loss'] / r['bound_min'] for r in R if r['bound_min'] > 0]
loss = [r['round_loss'] / r['Gstar'] for r in R]
print('instances with fractional multipliers:', len(R), '; all within min(s,f-s) bound:', all(r['ok_round'] for r in R))
print('K * omega * sigma / G*        : min %.4g max %.4g' % (min(old), max(old)))
print('floor((K+1)/2) omega sigma / G*: min %.4g max %.4g' % (min(new), max(new)))
print('loss / (min(s,f-s) omega sigma): min %.3g max %.3g median %.3g' % (min(ratio), max(ratio), st.median(ratio)))
print('loss / G*                      : min %.3g max %.3g; below 0.1%%: %d' % (min(loss), max(loss), sum(x < 1e-3 for x in loss)))
print('informative (floor bound < 1)  : %d of %d' % (sum(x < 1 for x in new), len(new)))
