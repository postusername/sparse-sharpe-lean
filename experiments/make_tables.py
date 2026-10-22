"""Tables and numbers of Section 7 (and Section 5.4) from the results of the experiments.

  python3 -I make_tables.py            -> tables/*.tex (the table bodies \\input by the paper) and numbers.md
                                          (every number quoted in the text of Sections 5.4 and 7 and in the Introduction)
Inputs: results/E40 (real data), results/E41 (random instances M = 16), results/E35 and results/E36 (the stress
regime at scale and the methods from the literature), results/E29, E30, E30b, E31, CHECK and E33 (the scheme, the size
bounds, the checks and the relaxation), results/E43 and results/E44 (the knapsack embedding and the checks of the
scheme without omega, quoted in Section 5.4).  No solver is run here; only the random instances of Section 7.3 are drawn
again from their seeds, to count the signs of their loadings.
"""
import collections
import glob
import json
import math
import os
import re
import statistics
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, 'results')
TAB = os.path.join(HERE, 'tables')
NUM = []


def num(key, value, where):
    NUM.append((key, value, where))


def sci(x, digits=1):
    if x == 0:
        return '0'
    e = int(math.floor(math.log10(abs(x))))
    m = x / 10 ** e
    if round(m, digits) >= 10:
        m, e = m / 10, e + 1
    return '$%.*f\\cdot 10^{%d}$' % (digits, m, e)


def jl(path):
    return [json.loads(l) for l in open(path) if l.strip()]


def write(name, lines):
    os.makedirs(TAB, exist_ok=True)
    open(os.path.join(TAB, name), 'w').write('\n'.join(lines) + '\n')


def lchoose(n, k):
    return math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)


def log10_at_most(n, k):
    """log10 of the number of nonempty supports with at most k of n names."""
    terms = [lchoose(n, j) for j in range(1, k + 1)]
    mx = max(terms)
    return (mx + math.log(sum(math.exp(t - mx) for t in terms))) / math.log(10)


# ------------------------------------------------------------------------------------------- real data, Table 7.1
def real_optima():
    D = json.load(open(os.path.join(RES, 'E40', 'optima.json')))
    lines = []
    for r in D['rows']:
        sup = ', '.join('%s %.3f' % (a, w) for a, w in zip(r['support'], r['weights']))
        trey = '%.3f' % r['treynor'] if 'treynor' in r else '---'
        lines.append('%s & %d & %s & %.3f & %.3f & %s & %s\\\\' % (r['model'], r['k'], sup, r['SR'], r['greedy'], trey,
                                                                 'yes' if r['test'] else 'no'))
    write('optima.tex', lines)
    rows = D['rows']
    num('optima: max |w(t0) - w*|', '%.1e' % max(r['clip_err'] for r in rows), '7.1')
    r0 = [r for r in rows if r['model'] == 'FF49-K1' and r['k'] == 3][0]
    num('FF49-K1 k=3: t0 per month', '%.4f' % r0['t0'][0], '7.1')
    num('FF49-K1 k=3: industries above the cut-off besides the held ones', '%d: %s' % (len(r0['above_cutoff']), ', '.join(r0['above_cutoff'])), '7.1')
    tr = r0['above_cutoff_treynor']
    num('FF49-K1 k=3: Treynor ratios (above cut-off and held)', ', '.join('%s %.4f' % kv for kv in sorted(tr.items(), key=lambda kv: -kv[1])), '7.1')
    num('optima: test passes', '%d of %d' % (sum(r['test'] for r in rows), len(rows)), '7.1')
    fail = [r for r in rows if not r['test']]
    num('optima: test fails in', ', '.join('%s k=%d (gap %.2e, nodes %d, greedy+exch optimal %s)' % (
        r['model'], r['k'], r['cert_gap'], r['bnb_nodes'], r['greedy_swap_opt']) for r in fail), '7.1')
    one = [r for r in rows if 'treynor' in r]
    num('prefix hypothesis (Prop 3.3) holds in', '%d of %d one-factor instances' % (sum(r['prefix_hypothesis'] for r in one), len(one)), '7.1')
    num('Treynor prefix: largest loss of SR', '%.1f%%' % (100 * (1 - min(r['treynor'] for r in one))), '7.1')
    vt = D['text']['voltarget']
    num('FF49-K1 k=5, volatility target 10%: risky fraction, expected excess return', '%.1f%%, %.1f%%' % (100 * vt['fraction'], 100 * vt['ret']), '7.1')


# ------------------------------------------------------------------------------- real data, Table 7.2 and the text
def real_instances():
    R = [r for r in jl(os.path.join(RES, 'E40', 'instances.jsonl')) if r.get('binding')]
    allr = jl(os.path.join(RES, 'E40', 'instances.jsonl'))
    lines = []
    for uni, label, M in (('SP500', 'S\\&P 500', 457), ('Russell', 'Russell 3000', 2122)):
        for K in (1, 3, 5, 10):
            cells = []
            nlo = None
            for k in (5, 10, 20, 50):
                r = [x for x in allr if x['universe'] == uni and x['K'] == K and x['k'] == k][0]
                nlo = r['n_lo']
                if not r['binding']:
                    cells.append('---')
                elif r['test']:
                    cells.append('opt')
                else:
                    cells.append('%s\\,(%d)' % (sci(r['gap']), r['bnb_nodes']))
            lines.append('%s & %d & %d & %s\\\\' % (label, K, nlo, ' & '.join(cells)))
        times = []
        for k in (5, 10, 20, 50):
            ts = [x['t_total'] for x in R if x['universe'] == uni and x['k'] == k]
            times.append(('%.1f' % max(ts) if max(ts) < 10 else '%.0f' % max(ts)) if ts else '---')
        lines.append('& \\multicolumn{2}{r}{time, s} & %s\\\\' % ' & '.join(times))
        lines.append('\\midrule')
    sup = ' & '.join('%.1f\\,/\\,%.1f' % (log10_at_most(457, k), log10_at_most(2122, k)) for k in (5, 10, 20, 50))
    lines.append('\\multicolumn{3}{@{}l}{$\\log_{10}$ supports} & %s\\\\' % sup)
    write('large.tex', lines)
    n = len(R)
    num('binding real instances', n, '7.2')
    num('test passes (dual point of greedy with exchanges)', '%d of %d' % (sum(r['test'] for r in R), n), '7.2')
    gaps = [r['gap'] for r in R if not r['test']]
    num('largest certificate gap 1 - F_h/G*', '%.2f%%' % (100 * max(gaps)), '7.2, Introduction')
    num('largest number of B&B nodes', max(r['bnb_nodes'] for r in R), '7.2, Introduction')
    for kk in (5, 10, 20, 50):
        ts = [r['t_total'] for r in R if r['k'] == kk]
        num('largest time, k=%d (s)' % kk, '%.1f' % max(ts), '7.2')
    num('share of the exchanges in the largest time', '%.0f%%' % (100 * max(R, key=lambda r: r['t_total'])['t_swap'] / max(r['t_total'] for r in R)), '7.2')
    num('largest number of supports (log10, at most k names)', '%.1f' % max(log10_at_most(r['M'], r['k']) for r in R), '7.2')
    nopt = [r for r in R if not r['greedy_swap_opt']]
    num('greedy with exchanges not optimal in', '; '.join('%s k=%d: B&B improves the SR by %.3f%%' % (
        r['model'], r['k'], 100 * (math.sqrt(r['bnb'] / r['Fh']) - 1)) for r in nopt) or 'none', '7.2')
    for Ks, lab in (((1,), 'one factor'), ((5, 10), 'five or ten factors')):
        sub = [r for r in R if r['K'] in Ks]
        num('test passes with %s' % lab, '%d of %d' % (sum(r['test'] for r in sub), len(sub)), '7.2')
    groups = (('industries', ('FF49',)), ('OR-Library', tuple('port%d' % i for i in range(1, 6))),
              ('S&P 500', ('SP500',)), ('Russell 3000', ('Russell',)))
    for lab, us in groups:
        sub = [r for r in R if r['universe'] in us]
        vals = []
        for key in ('top_sr', 'top_score0', 'truncation', 'treynor_naive'):
            v = [math.sqrt(r[key] / r['bnb']) for r in sub if key in r]
            vals.append('%.3f' % min(v) if v else '---')
        num('screening worst fractions (top SR, top m/sqrt d, truncation, Treynor) on %s' % lab, ', '.join(vals), '7.2')
    num('greedy without exchanges: worst fraction', '%.3f' % min(math.sqrt(r['Fg'] / r['bnb']) for r in R), '7.2')
    num('greedy with exchanges: worst fraction (rounded down)', '%.4f' % (math.floor(1e4 * min(math.sqrt(r['Fh'] / r['bnb']) for r in R)) / 1e4), '7.2')
    worst = min(min(math.sqrt(r[key] / r['bnb']) for key in ('top_sr', 'top_score0', 'truncation', 'treynor_naive') if key in r) for r in R)
    num('screening rules: largest loss of SR (Introduction)', '%.1f%%' % (100 * (1 - worst)), 'Introduction')
    num('largest in-sample annualized SR on the S&P 500 and the Russell 3000', '%.2f' % max(r['sr_opt_annual'] for r in R if r['universe'] in ('SP500', 'Russell')), '7.7')


# ---------------------------------------------------------------------------------- random instances, M = 16 (E41)
REG = [('calibrated', 'factor'), ('calibrated', 'unrelated'), ('stress', 'factor'), ('stress', 'unrelated'),
       ('calibrated-highR2', 'unrelated'), ('stress-lowR2', 'unrelated'), ('stress-nonneg', 'unrelated')]


def e41():
    data = collections.defaultdict(list)
    for p in sorted(glob.glob(os.path.join(RES, 'E41', 'regime_*.jsonl'))):
        for x in jl(p):
            data[(x['structure'], x['returns'])].append(x)
    opt_ok = lambda v, x: v >= x['opt'] * (1 - 1e-9)
    loss = lambda v, x: 100 * (1 - math.sqrt(max(v, 0.0) / x['opt']))
    # Table 7.3: the stress regime, per (K, k)
    lines = []
    st = data[('stress', 'unrelated')]
    for K in (1, 2, 3, 5):
        for k in (3, 5):
            L = [x for x in st if x['K'] == K and x['k'] == k]
            lines.append('%d & %d & %d & %d & %d & %d & %s & %.1f & %.1f & %d & %d\\\\' % (
                K, k, sum(x['relgap'] < 1e-9 for x in L), sum(opt_ok(x['Fg'], x) for x in L),
                sum(opt_ok(x['Fh'], x) for x in L), sum(x['cert'] for x in L), sci(max(x['relgap'] for x in L)),
                max(loss(x['Fg'], x) for x in L), statistics.mean(loss(x['Fsr'], x) for x in L),
                sum(abs(x['bnb'] - x['opt']) <= 1e-8 * x['opt'] for x in L), max(x['bnb_nodes'] for x in L)))
    write('random.tex', lines)
    json.dump({'%d_%d' % (K, k): dict(
        greedy=sum(opt_ok(x['Fg'], x) for x in st if x['K'] == K and x['k'] == k),
        exch=sum(opt_ok(x['Fh'], x) for x in st if x['K'] == K and x['k'] == k),
        cert=sum(x['cert'] for x in st if x['K'] == K and x['k'] == k),
        loss=max(loss(x['Fg'], x) for x in st if x['K'] == K and x['k'] == k),
        cal_greedy=sum(opt_ok(x['Fg'], x) for x in data[('calibrated', 'factor')] if x['K'] == K and x['k'] == k))
        for K in (1, 2, 3, 5) for k in (3, 5)}, open(os.path.join(TAB, 'random.json'), 'w'), indent=1)
    cal = data[('calibrated', 'factor')]
    num('calibrated: relaxation tight per row (min..max of 100)', '%d..%d' % (
        min(sum(x['relgap'] < 1e-9 for x in cal if x['K'] == K and x['k'] == k) for K in (1, 2, 3, 5) for k in (3, 5)),
        max(sum(x['relgap'] < 1e-9 for x in cal if x['K'] == K and x['k'] == k) for K in (1, 2, 3, 5) for k in (3, 5))), '7.3')
    num('calibrated: greedy with exchanges optimal / certificate 0.9', '%d / %d of %d' % (
        sum(opt_ok(x['Fh'], x) for x in cal), sum(x['cert'] for x in cal), len(cal)), '7.3')
    num('calibrated: largest number of B&B nodes', max(x['bnb_nodes'] for x in cal), '7.3')
    s2 = [x for x in st if x['K'] >= 2]
    num('stress K>=2: relaxation with a gap in', '%d of %d' % (sum(x['relgap'] >= 1e-9 for x in s2), len(s2)), '7.3')
    num('stress: largest relative gap (G* - OPT)/OPT', '%.0f%%' % (100 * max(x['relgap'] for x in st)), '7.3')
    rows2 = [[x for x in s2 if x['K'] == K and x['k'] == k] for K in (2, 3, 5) for k in (3, 5)]
    num('stress K>=2: greedy optimal per row (min..max of 100)', '%d..%d' % (min(sum(opt_ok(x['Fg'], x) for x in L) for L in rows2), max(sum(opt_ok(x['Fg'], x) for x in L) for L in rows2)), '7.3')
    num('stress K>=2: largest loss of greedy', '%.0f%%' % max(loss(x['Fg'], x) for x in s2), '7.3')
    num('stress K>=2: mean loss of screening by SR per row (min..max)', '%.0f%%..%.0f%%' % (min(statistics.mean(loss(x['Fsr'], x) for x in L) for L in rows2), max(statistics.mean(loss(x['Fsr'], x) for x in L) for L in rows2)), '7.3')
    num('stress K>=2: certificate below 0.9 in up to (per row of 100)', max(100 - sum(x['cert'] for x in L) for L in rows2), '7.3')
    num('stress: B&B optimal in all / largest nodes', '%d of %d / %d' % (sum(abs(x['bnb'] - x['opt']) <= 1e-8 * x['opt'] for x in st), len(st), max(x['bnb_nodes'] for x in st)), '7.3')
    # the regimes (Table 7.4)
    lines = []
    lab = {'calibrated': ('market factor', 'U(0.2,0.8)'), 'stress': ('Gaussian', 'U(0.5,0.95)'),
           'calibrated-highR2': ('market factor', 'U(0.5,0.95)'), 'stress-lowR2': ('Gaussian', 'U(0.2,0.8)'),
           'stress-nonneg': ('$|$Gaussian$|$', 'U(0.5,0.95)')}
    for key in REG:
        L = data.get(key)
        if not L:
            continue
        k3 = [x for x in L if x['k'] == 3 and x['K'] >= 2]
        lines.append('%s & %s & %s & %d & %d & %d & %d & %s\\\\' % (
            lab[key[0]][0], lab[key[0]][1], 'factors' if key[1] == 'factor' else 'unrelated', len(L),
            sum(x['relgap'] < 1e-9 for x in L), sum(opt_ok(x['Fh'], x) for x in L), sum(x['cert'] for x in L),
            sci(max(x['relgap'] for x in L))))
        num('regime %s/%s: tight, exch optimal, cert, of n; cert fails for k=3, K>=2' % key, '%d, %d, %d of %d; %d of %d' % (
            sum(x['relgap'] < 1e-9 for x in L), sum(opt_ok(x['Fh'], x) for x in L), sum(x['cert'] for x in L), len(L),
            sum(not x['cert'] for x in k3), len(k3)), '7.3')
    write('regimes.tex', lines)
    # methods from the literature on M = 16
    for key in (('calibrated', 'factor'), ('stress', 'unrelated')):
        L = data[key]
        num('M=16 %s/%s: optimal (pga, oscar, greedy+exch, oa) of n' % key, '%d, %d, %d, %d of %d' % (
            sum(opt_ok(x['pga'], x) for x in L), sum(opt_ok(x['oscar'], x) for x in L), sum(opt_ok(x['Fh'], x) for x in L),
            sum(abs(x['oa'] - x['opt']) <= 1e-7 * x['opt'] for x in L), len(L)), '7.3')
        num('M=16 %s/%s: worst loss (pga, oscar), %%' % key, '%.0f, %.0f' % (max(loss(x['pga'], x) for x in L), max(loss(x['oscar'], x) for x in L)), '7.3')
        num('M=16 %s/%s: median bound/OPT (G*, SDP, SDP with Y>=0)' % key, '%.3f, %.2f, %.3f' % (
            statistics.median(x['G'] / x['opt'] for x in L), statistics.median(x['sdp'] / x['opt'] for x in L),
            statistics.median(x['sdp_nonneg'] / x['opt'] for x in L)), '7.3')
        num('M=16 %s/%s: SDP with Y>=0 below G* in' % key, '%d of %d' % (sum(x['sdp_nonneg'] < x['G'] * (1 - 1e-7) for x in L), len(L)), '7.3')
        num('M=16 %s/%s: OA largest time (s)' % key, '%.2f' % max(x['oa_time'] for x in L), '7.3')


# ------------------------------------------------------------------- methods from the literature (E36, E41)
def literature():
    sig = {}
    for x in jl(os.path.join(RES, 'E36', 'oscar_signed.jsonl')):
        if x['set'] == 'E35':
            sig[('E35', x['M'], x['K'], x['k'], x['it'])] = x['oscar_signed']
        else:
            sig[('E41', x['structure'], x['returns'], x['K'], x['k'], x['it'])] = x['oscar_signed']
    rows = []
    e41 = {}
    for p in sorted(glob.glob(os.path.join(RES, 'E41', 'regime_*.jsonl'))):
        for x in jl(p):
            e41.setdefault((x['structure'], x['returns']), []).append(x)
    L = e41[('stress', 'unrelated')]
    rows.append(dict(M=16, n=len(L),
                     pga=[x['pga'] / x['opt'] for x in L],
                     oscar=[max(x['oscar'], sig[('E41', x['structure'], x['returns'], x['K'], x['k'], x['it'])]) / x['opt'] for x in L],
                     exch=[x['Fh'] / x['opt'] for x in L],
                     oa_ok=[abs(x['oa'] - x['opt']) <= 1e-7 * x['opt'] for x in L], oa_t=[x['oa_time'] for x in L],
                     bnb_t=[x['bnb_time'] for x in L]))
    if all('t_relax' in x for x in L):
        t_sum = [x['oa_time'] + x['t_relax'] for x in L]
        num('literature M=16: OA with the relaxation med/max s; faster than B&B in; relaxation med/max s',
            '%.3f/%.2f; %d of %d; %.3f/%.3f' % (statistics.median(t_sum), max(t_sum),
                                                sum(a < x['bnb_time'] for a, x in zip(t_sum, L)), len(L),
                                                statistics.median(x['t_relax'] for x in L), max(x['t_relax'] for x in L)), '7.5')
    for M in (50, 200, 1000, 2000):
        L = []
        for p in sorted(glob.glob(os.path.join(RES, 'E36', '%d_*_*.jsonl' % M))):
            L += [x for x in jl(p) if not x.get('skip')]
        if not L:
            continue
        ref = {}
        for p in sorted(glob.glob(os.path.join(RES, 'E35', '%d_*_*.jsonl' % M))):
            for x in jl(p):
                ref[(x['K'], x['k'], x['it'])] = x
        oa = [x['oa'] for x in L if 'oa' in x]
        R = [ref[(x['K'], x['k'], x['it'])] for x in L if 'oa' in x]
        t_rel = [r['t_relax'] for r in R]
        t_sum = [o['time'] + r['t_relax'] for o, r in zip(oa, R)]
        num('literature M=%d: OA with the relaxation med/max s; faster than B&B in; relaxation med/max s' % M,
            '%.2f/%.1f; %d of %d; %.2f/%.2f' % (statistics.median(t_sum), max(t_sum),
                                                sum(a < r['bnb_time'] for a, r in zip(t_sum, R)), len(R),
                                                statistics.median(t_rel), max(t_rel)), '7.5')
        rows.append(dict(M=M, n=len(L),
                         pga=[x['pga']['value'] / x['opt'] for x in L],
                         oscar=[max(x['oscar']['value'], sig[('E35', M, x['K'], x['k'], x['it'])]) / x['opt'] for x in L],
                         exch=[x['Fh'] / x['opt'] for x in L],
                         oa_ok=[o['solved'] and o['ratio'] >= 1 - 1e-7 for o in oa], oa_t=[o['time'] for o in oa],
                         bnb_t=[ref[(x['K'], x['k'], x['it'])]['bnb_time'] for x in L]))
    lines = []
    for r in rows:
        ok = lambda v: sum(1 for q in v if q >= 1 - 1e-9)
        worst = lambda v: 100 * (1 - math.sqrt(max(min(v), 0.0)))
        lines.append('%d & %d & %d & %.0f & %d & %.0f & %d & %d & %.2f & %.1f & %.2f & %.1f\\\\' % (
            r['M'], r['n'], ok(r['pga']), worst(r['pga']), ok(r['oscar']), worst(r['oscar']), ok(r['exch']),
            sum(r['oa_ok']), statistics.median(r['oa_t']), max(r['oa_t']), statistics.median(r['bnb_t']), max(r['bnb_t'])))
        num('literature M=%d: n, optimal pga/oscar/exch, OA solved, OA med/max s, B&B med/max s' % r['M'], '%d; %d, %d, %d; %d; %.2f/%.1f; %.2f/%.1f' % (
            r['n'], ok(r['pga']), ok(r['oscar']), ok(r['exch']), sum(r['oa_ok']), statistics.median(r['oa_t']), max(r['oa_t']),
            statistics.median(r['bnb_t']), max(r['bnb_t'])), '7.5')
        num('literature M=%d: worst loss pga, oscar, exch (%%)' % r['M'], '%.0f, %.0f, %.0f' % (worst(r['pga']), worst(r['oscar']), worst(r['exch'])), '7.5')
        num('literature M=%d: median SR fraction pga, oscar' % r['M'], '%.3f, %.3f' % (statistics.median(math.sqrt(max(q, 0)) for q in r['pga']), statistics.median(math.sqrt(max(q, 0)) for q in r['oscar'])), '7.5')
    write('literature.tex', lines)
    num('literature: selection of Bae et al. optimal in, of the stress instances; median SR fraction (min..max over M)', '%d of %d; %.3f..%.3f' % (
        sum(sum(1 for q in r['oscar'] if q >= 1 - 1e-9) for r in rows), sum(r['n'] for r in rows),
        min(statistics.median(math.sqrt(max(q, 0)) for q in r['oscar']) for r in rows),
        max(statistics.median(math.sqrt(max(q, 0)) for q in r['oscar']) for r in rows)), '7.5')
    # the calibrated regime, M = 16
    L = e41[('calibrated', 'factor')]
    num('literature M=16 calibrated: optimal pga, oscar (best of the two rules), of n', '%d, %d of %d' % (
        sum(x['pga'] >= x['opt'] * (1 - 1e-9) for x in L),
        sum(max(x['oscar'], sig[('E41', x['structure'], x['returns'], x['K'], x['k'], x['it'])]) >= x['opt'] * (1 - 1e-9) for x in L), len(L)), '7.5')
    # the SDP bound (M = 16: E41; M = 50: E36)
    for key in (('calibrated', 'factor'), ('stress', 'unrelated')):
        L = e41[key]
        below = [x for x in L if x['sdp_nonneg'] < x['G'] * (1 - 5e-4)]
        num('SDP M=16 %s/%s: median bound/OPT for G*, P7, P7 with Y>=0; P7+ < G* by more than 0.05%% in; by (min..max); (K, k)' % key, '%.3f, %.2f, %.2f; %d of %d; %s; %s' % (
            statistics.median(x['G'] / x['opt'] for x in L), statistics.median(x['sdp'] / x['opt'] for x in L),
            statistics.median(x['sdp_nonneg'] / x['opt'] for x in L), len(below), len(L),
            '%.2f%%..%.1f%%' % (100 * min(1 - x['sdp_nonneg'] / x['G'] for x in below), 100 * max(1 - x['sdp_nonneg'] / x['G'] for x in below)) if below else '-',
            sorted(set((x['K'], x['k']) for x in below))), '7.5')
    L = []
    for p in sorted(glob.glob(os.path.join(RES, 'E36', '50_*_*.jsonl'))):
        L += [x for x in jl(p) if not x.get('skip') and 'sdp' in x]
    if L:
        num('SDP M=50 stress: median bound/OPT for G*, P7, P7 with Y>=0; P7+ < G* in; median/max time P7 and P7+ (s)', '%.3f, %.2f, %.2f; %d of %d; %.1f/%.1f, %.1f/%.1f' % (
            statistics.median(x['G'] / x['opt'] for x in L), statistics.median(x['sdp']['ratio'] for x in L),
            statistics.median(x['sdp_nonneg']['ratio'] for x in L), sum(x['sdp_nonneg']['value'] < x['G'] * (1 - 5e-4) for x in L), len(L),
            statistics.median(x['sdp']['time'] for x in L), max(x['sdp']['time'] for x in L),
            statistics.median(x['sdp_nonneg']['time'] for x in L), max(x['sdp_nonneg']['time'] for x in L)), '7.5')


# ------------------------------------------------------------------------------- formal size bounds (E31)
BOUND_ROWS = [('FF49-K1', 10), ('FF49-K5', 10), ('port1-K3', 10), ('SP500-K1', 20), ('SP500-K10', 20),
              ('Russell-K1', 50), ('Russell-K3', 50), ('Russell-K10', 50)]
LABEL = {'port1-K3': 'HS-PCA3', 'SP500-K1': 'S\\&P500-K1', 'SP500-K10': 'S\\&P500-K10'}


def e31():
    rows = []
    for l in open(os.path.join(RES, 'E31', 'e31_table.md')):
        p = [c.strip() for c in l.strip().strip('|').split('|')]
        if len(p) == 11 and p[1].isdigit():
            rows.append(dict(model=p[0], M=int(p[1]), K=int(p[2]), omega=float(p[3]), k=int(p[4]), supports=float(p[5]),
                             explicit=float(p[8]), poly=float(p[9])))
    lines = []
    for name, k in BOUND_ROWS:
        r = [x for x in rows if x['model'] == name and x['k'] == k][0]
        lines.append('%s & %d & %d & %.2f & %d & %.1f & %.1f & %.1f\\\\' % (LABEL.get(name, name), r['M'], r['K'], r['omega'], k,
                                                                         r['supports'], r['explicit'], r['poly']))
    write('bounds.tex', lines)
    below = [x for x in rows if x['explicit'] < x['supports']]
    num('size bound below the number of supports (at most k names)', '%d of %d' % (len(below), len(rows)), '7.6, Introduction')
    for K in sorted(set(x['K'] for x in rows)):
        sub = [x for x in rows if x['K'] == K]
        num('  ... with K=%d' % K, '%d of %d' % (sum(x['explicit'] < x['supports'] for x in sub), len(sub)), '7.6')
    top = max(rows, key=lambda x: x['explicit'])
    num('largest explicit bound (log10) over all instances', '%.1f (%s, k=%d)' % (top['explicit'], top['model'], top['k']), '7.6, Introduction')
    E40 = [r for r in jl(os.path.join(RES, 'E40', 'instances.jsonl')) if r.get('binding')]
    bind = {(r['model'], r['k']) for r in E40}
    sub = [x for x in rows if (x['model'], x['k']) in bind]
    if sub:
        t2 = max(sub, key=lambda x: x['explicit'])
        num('largest explicit bound (log10) over the binding instances of Section 7.2', '%.1f (%s, k=%d) of %d instances' % (t2['explicit'], t2['model'], t2['k'], len(sub)), '7.6')


# ------------------------------------------------------------------------------------- the scheme itself (E30)
OWN = [('FF49-K1', 3), ('FF49-K3', 3), ('port1-K1', 3), ('port1-K1', 5), ('port1-K3', 3), ('port1-K3', 5),
       ('port2-K1', 3), ('port5-K1', 3), ('SP500-K1', 3), ('SP500-K3', 3), ('Russell-K1', 3)]
OWN_LABEL = {'port1-K1': 'HS-PCA1', 'port1-K3': 'HS-PCA3', 'port2-K1': 'DAX-K1', 'port5-K1': 'Nikkei-K1',
             'SP500-K1': 'S\\&P500-K1', 'SP500-K3': 'S\\&P500-K3'}


def sci_int(x, digits):
    import decimal
    e = int(math.floor(math.log10(x)))
    m = decimal.Decimal(int(x)).scaleb(-e).quantize(decimal.Decimal(1).scaleb(-digits), rounding=decimal.ROUND_HALF_UP)
    return '$%s\\cdot10^{%d}$' % (m, e)


def e30():
    p = os.path.join(RES, 'E30', 'results_E30.json')
    if not os.path.exists(p):
        print('results/E30/results_E30.json missing: run e30_additive_dp.py')
        return
    R = json.load(open(p))
    lines = []
    for name, k in OWN:
        r = [x for x in R if x['model'] == name and x['k'] == k][0]
        lines.append('%s & %d & %d & %d & %s & %s & %s & %s & %.1f\\%% & %.4f\\\\' % (
            OWN_LABEL.get(name, name), r['M'], r['K'], k, 'exact' if r['kind'] == 'exact' else 'heur.',
            '{:,}'.format(r['table']).replace(',', '\\,'), sci_int(r['table_bound'], 1), sci_int(r['subsets'], 2),
            100 * r['merged'] / max(1, r['generated']), r['ratio']))
    write('own.tex', lines)
    sel = [[x for x in R if x['model'] == n and x['k'] == k][0] for n, k in OWN]
    num('scheme itself: worst best/ref over the 11 instances', '%.6f' % min(x['ratio'] for x in sel), '7.6')
    num('scheme itself: table sizes (min..max)', '%d..%d' % (min(x['table'] for x in sel), max(x['table'] for x in sel)), '7.6')
    num('scheme itself: formal bound / table size (min..max)', '%.0f..%.1e' % (min(x['table_bound'] / x['table'] for x in sel), max(x['table_bound'] / x['table'] for x in sel)), '7.6')
    num('scheme itself: merged shares (min..max)', '%.1f%%..%.1f%%' % (min(100 * x['merged'] / x['generated'] for x in sel), max(100 * x['merged'] / x['generated'] for x in sel)), '7.6')
    for x in R:
        if 'family_size' in x:
            # family_size counts the distinct sets of all tables, the empty set included
            num('scheme itself: family over all nodes, %s k=%d: distinct nonempty supports, ratio' % (OWN_LABEL.get(x['model'], x['model']), x['k']), '%d (of %d supports), %.6f' % (x['family_size'] - 1, x['subsets'], x['family_ratio']), '7.6')



# ------------------------------------------------------------- branch and bound at scale and the MIQP solvers (E35)
def scale():
    ref, meds, top = {}, {}, (0.0, None, None)
    for p in sorted(glob.glob(os.path.join(RES, 'E35', '[0-9]*_*_*.jsonl'))):
        L = [x for x in jl(p) if not x.get('skip')]
        for x in L:
            ref[(x['M'], x['K'], x['k'], x['it'])] = x['bnb_time']
            if x['bnb_time'] > top[0]:
                top = (x['bnb_time'], '%d_%d_%d' % (x['M'], x['K'], x['k']), x['bnb_nodes'])
        meds['%d_%d_%d' % (L[0]['M'], L[0]['K'], L[0]['k'])] = statistics.median(x['bnb_time'] for x in L)
    num('stress at scale: B&B median time per configuration (min..max); largest time (configuration, nodes)', '%.3f..%.2f s; %.1f s (%s, %d nodes)' % (
        min(meds.values()), max(meds.values()), top[0], top[1], top[2]), '7.4, Introduction')
    for f in ('persp_gurobi', 'persp_scip', 'bigM_scip'):
        for M in (50, 200, 1000, 2000):
            n = w = 0
            for p in glob.glob(os.path.join(RES, 'E35', 'miqp_%d_*.jsonl' % M)):
                for r in jl(p):
                    o = r.get(f)
                    if not isinstance(o, dict):
                        continue
                    n += 1
                    w += ref[(r['M'], r['K'], r['k'], r['it'])] < (o['time'] if 'error' not in o else float('inf'))
            if n:
                num('MIQP %s, M=%d: branch and bound faster in' % (f, M), '%d of %d' % (w, n), '7.4')


# ------------------------------------------------------------------- the signs of the random loadings (Section 7.3)
def signs():
    sys.path.insert(0, HERE)
    import numpy as np
    import e41_random as R41
    tot = both = neg = 0
    byK = collections.Counter()
    nK = collections.Counter()
    for r, (structure, returns) in enumerate(R41.REGIMES):
        if not structure.startswith('calibrated'):
            continue
        for K in (1, 2, 3, 5):
            for k in (3, 5):
                rng = np.random.default_rng(41000 + 1000 * r + 10 * K + k)
                done = 0
                while done < 100:
                    m, d, B, Sf = R41.instance(rng, 16, K, structure, returns)
                    if m.max() <= 0:
                        continue
                    done += 1
                    tot += 1
                    both += bool(B.min() < 0 < B.max())
                    neg += bool(B[:, 0].min() < 0)
                    byK[K >= 2] += bool(B.min() < 0 < B.max())
                    nK[K >= 2] += 1
    num('market-factor instances with loadings of both signs: K>=2; K=1; with a negative market beta', '%d of %d; %d of %d; %d of %d' % (
        byK[True], nK[True], byK[False], nK[False], neg, tot), '7.3')


# ------------------------------------------------------------------------- coarsening of the constants (E30b)
def e30b():
    R, cur = collections.OrderedDict(), None
    for l in open(os.path.join(RES, 'E30b', 'e30b.log')):
        a = re.match(r'(\S+) k=(\d+) F\*=', l)
        if a:
            cur = (a.group(1), int(a.group(2)))
            R[cur] = {}
            continue
        a = re.match(r'\s+scale \D(\d+)\s+table\s+\d+\s+merged\s+[\d.]+%\s+F_best/F\* = ([\d.]+)', l)
        if a and cur:
            R[cur][int(a.group(1))] = float(a.group(2))
    cs = sorted(next(iter(R.values())))
    num('coarsening by c: worst F_best/F* over the %d instances, c = %s' % (len(R), ', '.join(map(str, cs))),
        ', '.join('%.6f' % min(v[c] for v in R.values()) for c in cs), '7.6, Conclusion')
    big = [min(v[c] for c in cs if c >= 100) for v in R.values()]
    num('coarsening by c>=100: largest loss per instance (min..max); below 1-2eps = 0.9 in',
        '%.1f%%..%.1f%%; %d of %d' % (100 * (1 - max(big)), 100 * (1 - min(big)), sum(b < 0.9 for b in big), len(big)), '7.6')


# ------------------------------------------------------------------ the checks of the estimates (CHECK, E33)
def checks():
    log = open(os.path.join(RES, 'CHECK', 'check_clipped_dp.log')).read()
    t1 = float(re.search(r'T1 identity: max abs error (\S+)', log).group(1))
    n3 = [int(x) for x in re.findall(r'(\d+) cases, violations (\d+)', log)[0]]
    n3b = [int(x) for x in re.findall(r'(\d+) cases, violations (\d+)', log)[1]]
    num('checks: defect identity, largest error; cases of the guarantee at one node and violations', '%.1e; %d + %d cases, %d violations' % (
        t1, n3[0], n3b[0], n3[1] + n3b[1]), '7.6')
    rows = list(csv_rows(os.path.join(RES, 'E33', 'node_ratio.csv')))
    by = collections.defaultdict(list)
    for r in rows:
        by[float(r['shift_sd'])].append(float(r['ratio_to_bound']))
    num('node ratio loss/bound: pairs; median per displacement; largest', '%d; %s; %.4f' % (
        len(rows), ', '.join('%.3g' % statistics.median(by[s]) for s in sorted(by)), max(max(v) for v in by.values())), '7.6')


def csv_rows(path):
    import csv
    with open(path) as f:
        yield from csv.DictReader(f)


# ----------------------------------------------------- the relaxation, the support T and the rounding (E29)
def e29():
    R = json.load(open(os.path.join(RES, 'E29', 'results_E29.json')))
    log = open(os.path.join(RES, 'E29', 'e29.log')).read()
    err = len(re.findall(r'^ERROR ', log, re.M))
    num('relaxation: instances with a vertex, of the plan; |T|<=k+K; F_LO(T)>=G* up to the tolerance', '%d of %d; %d; %d' % (
        len(R), len(R) + err, sum(x['ok_size'] for x in R), sum(x['ok_value'] for x in R)), '7.7')
    num('relaxation: largest (G*-F_LO(T))/G*; F_LO(T) > G* by more than 0.1% in', '%.1e; %d' % (
        max((x['Gstar'] - x['F_T']) / x['Gstar'] for x in R), sum(x['F_T'] > x['Gstar'] * 1.001 for x in R)), '7.7')
    kn = [x for x in R if x.get('OPTk') is not None]
    num('relaxation: OPT(k) known in; OPT(k) <= G* in; largest gap', '%d; %d; %.2f%%' % (
        len(kn), sum(x['OPTk'] <= x['Gstar'] * (1 + 1e-6) for x in kn), 100 * max((x['Gstar'] - x['OPTk']) / x['OPTk'] for x in kn)), '7.7')
    fr = [x for x in R if x['f'] > 0]
    num('relaxation: instances with fractional multipliers; f min..max; largest |T| - k', '%d; %d..%d; %d' % (
        len(fr), min(x['f'] for x in fr), max(x['f'] for x in fr), max(x['size_T'] - x['k'] for x in R)), '7.7')
    fb = open(os.path.join(RES, 'E29', 'e29_floor_bound.log')).read()
    g = lambda pat: re.search(pat, fb).groups()
    num('rounding: loss/bound min, max, median; loss/G* max; below 0.1% in', '%s, %s, %s; %s; %s' % (
        g(r'loss / \(min\(s,f-s\) omega sigma\): min (\S+) max (\S+) median (\S+)') + g(r'loss / G\* +: min \S+ max (\S+); below 0.1%: (\d+)')), '7.7, Conclusion')
    num('rounding: floor((K+1)/2) omega sigma / G* min, max; informative in', '%s, %s; %s of %s' % (
        g(r'floor\(\(K\+1\)/2\) omega sigma / G\*: min (\S+) max (\S+)') + g(r'informative \(floor bound < 1\) +: (\d+) of (\d+)')), '7.7')
    F = [x for x in R if x.get('f', 0) >= 2 and 'bound_K' in x]
    cK = lambda x: (x['K'] + 1) // 2
    inf = lambda x: cK(x) * x['om_I'] * x['sigma'] < x['Gstar']
    lo = [x for x in F if cK(x) * x['om_I'] < x['k']]
    hi = [x for x in F if cK(x) * x['om_I'] >= x['k']]
    num('rounding: informative with floor((K+1)/2) omega_I < k; with >= k; sigma k/G* over the informative of the latter', '%d of %d; %d of %d; %.2f..%.2f' % (
        sum(inf(x) for x in lo), len(lo), sum(inf(x) for x in hi), len(hi),
        min(x['sigma'] * x['k'] / x['Gstar'] for x in hi if inf(x)), max(x['sigma'] * x['k'] / x['Gstar'] for x in hi if inf(x))), '7.7')
    num('relaxation: instances without a support (non-binding, see results/E40)', ', '.join(
        '%s K=%s k=%s' % a for a in re.findall(r'^ERROR (\S+) (\d+) (\d+)', log, re.M)), '7.7')



# ------------------------------------------------------------------------------------------- Section 5.4: E43; E44 (Remark 5.15)
def scalefree():
    """The knapsack embedding (E43, quoted in Section 5.4) and the checks of the one-tuple scheme of Remark 5.15
    (E44, Lean main_theorem_sf; not quoted in the paper)."""
    log = open(os.path.join(RES, 'E43', 'testB.log')).read()
    gaps = [(int(m), float(g)) for m, g in re.findall(r'm = +(\d+): largest relative gap (\S+)', log)]
    num('E43: largest relative gap (V_yes - V_no)/V_yes, m = %d .. %d' % (gaps[0][0], gaps[-1][0]),
        ', '.join('%s' % sci(g) for _, g in gaps), '5.4')
    num('E43: gap ratio per two bits (min..max)',
        '%.1f..%.1f' % (min(gaps[i][1] / gaps[i + 1][1] for i in range(len(gaps) - 1)),
                        max(gaps[i][1] / gaps[i + 1][1] for i in range(len(gaps) - 1))), '5.4')
    E = os.path.join(RES, 'E44')
    one = [r for f in sorted(glob.glob(os.path.join(E, 'onestep_*.jsonl'))) for r in jl(f)]
    num('E44 one step: instances (M, K); the table keeps the optimum in',
        '%d (M = %s, K = %s); %d' % (len(one), sorted({r['M'] for r in one}), sorted({r['K'] for r in one}),
                                     sum(r['one'] >= 1 - 1e-9 for r in one)), 'not quoted (Rem. 5.15)')
    num('E44 one step: instances with 0 / 1 / >= 2 tight rows of T',
        '%d / %d / %d' % (sum(r['tight'] == 0 for r in one), sum(r['tight'] == 1 for r in one),
                          sum(r['tight'] >= 2 for r in one)), 'not quoted (Rem. 5.15)')
    num('E44 one step: largest Cramer coefficient of an active row', '%.6f' % max(r['maxCramer'] for r in one), 'not quoted (Rem. 5.15)')
    num('E44 one step: controls below 0.9 (node x10, key x30, G-node, T not of maximal volume)',
        ', '.join('%d' % sum(r[c] < 0.9 for r in one) for c in ('node10', 'key30', 'gnode', 'wrongT')), 'not quoted (Rem. 5.15)')
    lem = [r for f in sorted(glob.glob(os.path.join(E, 'lemmas_*.jsonl'))) for r in jl(f)]
    num('E44 lemmas: instances; largest ratio of lemma 1, lemma 3; lemma 3 in G-coordinates above 1 in',
        '%d; %.2f, %.2f; %d' % (len(lem), max(r['lemma1'] for r in lem), max(r['lemma3'] for r in lem),
                                sum(r['lemma3_G'] > 1 for r in lem)), 'not quoted (Rem. 5.15)')
    num('E44 lemmas: smallest slack of the step (instances without a sign failure); sign failures (instances, '
        'tight rows of T)',
        '%.3f; %d (%s)' % (min(r['lemma5_slack'] for r in lem if 'lemma5_slack' in r),
                           sum(r['sign_fail'] > 0 for r in lem),
                           ', '.join('%s t=%d: %d' % (r['part'], r['t'], r['tight']) for r in lem if r['sign_fail'])),
        'not quoted (Rem. 5.15)')
    dd = [r for f in sorted(glob.glob(os.path.join(E, 'def510_*.jsonl'))) for r in jl(f)]
    inc, out = [r for r in dd if r['in_class']], [r for r in dd if not r['in_class']]
    num('E44 one-tuple scheme (Remark 5.15): instances; in the class of main_theorem_sf (at most one small position); outside it',
        '%d; %d; %d' % (len(dd), len(inc), len(out)), 'not quoted (Rem. 5.15)')
    num('E44 one-tuple scheme, node of the proof: optimum found in the class; worst ratio in the class',
        '%d of %d; %.4f' % (sum(r['rule'] >= 1 - 1e-9 for r in inc), len(inc), min(r['rule'] for r in inc)), 'not quoted (Rem. 5.15)')
    num('E44 one-tuple scheme, node of the proof outside the class: optimum found; worst ratio',
        '%d of %d; %.4f' % (sum(r['rule'] >= 1 - 1e-9 for r in out), len(out), min(r['rule'] for r in out)), 'not quoted (Rem. 5.15)')
    num('E44 one-tuple scheme, controls below 0.9 (T of non-maximal volume; anchor rows as T without the filter)',
        '%d of %d; %d of %d' % (sum(r['wrongT'] < 0.9 for r in dd if 'wrongT' in r), sum('wrongT' in r for r in dd),
                                sum(r['anchorT'] < 0.9 for r in dd), len(dd)), 'not quoted (Rem. 5.15)')
    num('E44 one-tuple scheme, the table keeping the largest score sum instead: below the optimum in',
        '%d of %d' % (sum(r['maxscore'] < 1 - 1e-9 for r in dd if 'maxscore' in r), sum('maxscore' in r for r in dd)),
        'not quoted (Rem. 5.15)')
    ad = [r for f in sorted(glob.glob(os.path.join(E, 'advdef_*.jsonl'))) for r in jl(f)]
    num('E44 adversary of the node of the proof (one-tuple scheme): runs; smallest ratio; smallest in the class; '
        'largest omega',
        '%d; %.4f; %.4f; %s' % (len(ad), min(r['rule'] for r in ad), min(r['rule'] for r in ad if r['in_class']),
                                sci(max(r['omega'] for r in ad))), 'not quoted (Rem. 5.15)')
    adv = [r for f in sorted(glob.glob(os.path.join(E, 'advstep_*.jsonl'))) for r in jl(f)]
    num('E44 adversary of the step: runs; smallest best-corner ratio; largest omega; largest number of tight rows',
        '%d; %.4f; %s; %d' % (len(adv), min(r['ratio'] for r in adv), sci(max(r['omega'] for r in adv)),
                              max(r['tight'] for r in adv)), 'not quoted (Rem. 5.15)')


# ------------------------------------------------------------------------------------------- Section 5.4: E45
def universal():
    """The step of the scheme without omega for K factors (Theorem 5.13, e45_universal.py)."""
    E = os.path.join(RES, 'E45')
    st = [r for f in sorted(glob.glob(os.path.join(E, 'step_*.jsonl'))) for r in jl(f)]
    num('E45 step: instances (M, k, K); with two or more small positions (outside the class of the one-tuple '
        'scheme); with a small position in the sense of the proof; |I\'| = 0 / 1 / 2 / 3',
        '%d (M = %s, k = %s, K = %s); %d; %d; %s' % (
            len(st), sorted({r['M'] for r in st}), sorted({r['k'] for r in st}), sorted({r['K'] for r in st}),
            sum(not r['in_class'] for r in st), sum(r['tight'] > 0 for r in st),
            ' / '.join('%d' % sum(r['Jp'] == j for r in st) for j in range(4))), '5.4')
    num('E45 step: largest leverage', sci(max(r['omega'] for r in st)), '5.4')
    num('E45 step, node of the proof: smallest ratio over the bucket of the large positions; smallest witness; '
        'smallest ratio of the set kept by the table',
        '%.6f; %.6f; %.6f' % (min(r['worst'] for r in st), min(r['cert'] for r in st),
                              min(r['dp'] for r in st)), '5.4')
    num('E45 step, controls below 0.9 (no forced small positions; key x30; node on the lattice of T; one tuple of '
        'all rows of the optimum)',
        '%d; %d; %d; %d' % (sum(r['noJ'] < 0.9 for r in st), sum(r['key30'] < 0.9 for r in st),
                            sum(r['gridT'] < 0.9 for r in st), sum(r['Tall'] < 0.9 for r in st)), '5.4')
    num('E45 step, one tuple of all rows: a small position of T with a negative weight in; these weights',
        '%d of %d; %s' % (sum(r['Tall_minT'] < 0 for r in st), len(st),
                          ', '.join(sci(r['Tall_minT']) for r in st if r['Tall_minT'] < 0)), '5.4')
    ad = [r for f in sorted(glob.glob(os.path.join(E, 'adv_*.jsonl'))) for r in jl(f)]
    num('E45 adversary of the node of the proof: runs (M, k, K); smallest ratio over the bucket; smallest witness; '
        'largest leverage',
        '%d (M = %s, k = %s, K = %s); %.6f; %.6f; %s' % (
            len(ad), sorted({r['M'] for r in ad}), sorted({r['k'] for r in ad}), sorted({r['K'] for r in ad}),
            min(r['worst'] for r in ad), min(r['cert'] for r in ad), sci(max(r['omega'] for r in ad))), '5.4')


# ------------------------------------------------------------------------------------------- Section 5.5: E46
def kernel46():
    """The kernel of Section 5.5 (Theorem 5.17, Lean kerK / kernel_value) and the instances of Proposition 5.19."""
    E = os.path.join(RES, 'E46')
    rnd = {K: [r for r in jl(os.path.join(E, 'rand_%d.jsonl' % K))] for K in (1, 2, 3)}
    crowd = {K: [r for r in R if r['fam'] != 'hedge'] for K, R in rnd.items()}
    hedge = {K: [r for r in R if r['fam'] == 'hedge'] for K, R in rnd.items()}

    def mean2(xs):
        # exact mean, rounded half up to two decimals
        import decimal
        from fractions import Fraction
        f = Fraction(sum(Fraction(x) for x in xs), len(xs))
        return str((decimal.Decimal(f.numerator) / decimal.Decimal(f.denominator)).quantize(
            decimal.Decimal('0.01'), rounding=decimal.ROUND_HALF_UP))
    num('E46 crowded random instances (families crowd and heavycrowd; K = 1, 2, 3): instances; mean kernel size / M; '
        'smallest OPT(kernel)/OPT; instances whose optimum is not in the kernel',
        '; '.join('K=%d: %d, %s/%d, %.6f, %d' % (
            K, len(R), mean2([r['ker_size'] for r in R]), R[0]['M'], min(r['ker'] for r in R),
            sum(not r['opt_in_ker'] for r in R)) for K, R in crowd.items()), '5.5')
    num('E46 instances of the hedge family of E45 (K = 1, 2, 3): instances; instances in which the kernel keeps every '
        'asset; M', '; '.join('K=%d: %d, %d, %d' % (K, len(R), sum(r['ker_size'] == r['M'] for r in R), R[0]['M'])
                              for K, R in hedge.items()), '5.5')
    num('E46 random instances: eps values; largest leverage (crowded; hedge family)', '%s; %s; %s' % (
        sorted({r['eps'] for R in rnd.values() for r in R}),
        sci(max(r['omega'] for R in crowd.values() for r in R)), sci(max(r['omega'] for R in hedge.values() for r in R))),
        '5.5')
    for c in ('nogrid', 'grid30', 'grid100', 'noscale'):
        num('E46 random instances (crowded and hedge family), control %s: below 1 - 4 eps (K = 1, 2, 3); '
            'smallest ratio' % c,
            '; '.join('%d' % sum(r[c] < 1 - 4 * r['eps'] for r in R) for R in rnd.values()) + '; %.3f' % min(
                r[c] for R in rnd.values() for r in R), '5.5')
    for K in (2, 3):
        L = jl(os.path.join(E, 'lb_%d.jsonl' % K))
        for n in sorted({r['n'] for r in L}):
            R = [r for r in L if r['n'] == n]
            na = R[0]['M'] - 1
            num('E46 lower-bound instances K = %d, n = %d: M; omega; kernel keeps (of the first group); smallest '
                'OPT(kernel)/OPT; largest other pair / OPT (bound 2n^2/A^2 / OPT); controls nogrid, grid30, grid100 '
                '(smallest ratio); nogrid keeps at most (of the first group)' % (K, n),
                '%d; %s; %d of %d; %.4f; %.4f (%.4f); %.4f, %.4f, %.4f; %d' % (
                    R[0]['M'], sci(R[0]['omega']), min(r['ker_alice'] for r in R), na, min(r['ker'] for r in R),
                    max(r['others'] / r['opt'] for r in R), max(r['bound'] / r['opt'] for r in R),
                    min(r['nogrid'] for r in R), min(r['grid30'] for r in R), min(r['grid100'] for r in R),
                    max(r['nogrid_alice'] for r in R)), '5.5')


def threesum47():
    """The 3SUM gap of Section 5.5 (Proposition 5.20, Lean ts_yes / ts_no / threesum_decide), with controls."""
    R = jl(os.path.join(RES, 'E47', 'gap.jsonl'))
    Y = [r for r in R if r['yes']]
    N = [r for r in R if not r['yes']]
    num('E47 3SUM gap (K = 3, k = 3): YES instances; smallest OPT_LO(3); smallest OPT_LS(3)',
        '%d; %.6f; %.6f' % (len(Y), min(r['lo'] for r in Y), min(r['ls'] for r in Y)), '5.5')
    num('E47 3SUM gap: NO instances; largest OPT_LO(3); largest OPT_LO(3)/bound; largest OPT_LS(3)/bound; '
        'largest bound (2(1+3U)^2+9)/A^2',
        '%d; %.4f; %.4f; %.4f; %.4f' % (len(N), max(r['lo'] for r in N), max(r['lo'] / r['bound'] for r in N),
                                        max(r['ls'] / r['bound'] for r in N), max(r['bound'] for r in N)), '5.5')
    num('E47 3SUM gap: integers per list; U; M; largest leverage',
        '%d..%d; %d..%d; %s; %s' % (min(r['n'] for r in R), max(r['n'] for r in R), min(r['U'] for r in R),
                                    max(r['U'] for r in R), ', '.join(str(m) for m in sorted({r['M'] for r in R})),
                                    sci(max(r['omega'] for r in R))), '5.5')
    num('E47 3SUM gap, controls on the NO instances (light A = 1; two factors; k = 4): instances with OPT above 1; '
        'largest OPT',
        '; '.join('%s %d, %.4f' % (c, sum(r[c] > 1 for r in N), max(r[c] for r in N))
                  for c in ('light', 'twofactor', 'k4')), '5.5')


if __name__ == '__main__':
    real_optima()
    real_instances()
    e41()
    literature()
    e31()
    e30()
    scale()
    e30b()
    checks()
    e29()
    signs()
    scalefree()
    universal()
    kernel46()
    threesum47()
    with open(os.path.join(HERE, 'numbers.md'), 'w') as f:
        f.write('# Numbers quoted in the text (generated by make_tables.py)\n\n| quantity | value | where |\n|---|---|---|\n')
        for k, v, w in NUM:
            f.write('| %s | %s | %s |\n' % (k, v, w))
    for k, v, w in NUM:
        print('%-75s %s' % (k, v))
