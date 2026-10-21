"""E36: methods from the literature (Section 7.5) on the instances of E35 (the stress regime at scale, Section 7.4).

Replays the instances of the configuration (M, K, k) of e35_scale.py (same seed 1000 M + 10 K + k, same generator)
and runs, for each instance:
  * pga    -- Lin, Lai and Li (2024), proximal gradient (baselines.pga_lin2024); the long-only optimum on its support;
  * oscar  -- Bae et al. (2025), Cholesky-based selection (baselines.oscar_bae2025); the long-only optimum on its support;
  * oa     -- Bertsimas and Cory-Wright (2022), outer approximation with lazy cuts in SCIP (baselines.oa_bcw2022),
              warm start: greedy selection with exchanges; relative gap 1e-6; time limit (default 600 s); one thread;
  * sdp    -- Kim et al. (2016), the semidefinite relaxation (P7), and (P7) with Y >= 0 (baselines.sdp_kim2016),
              solved with Clarabel; only for M <= 200.
The reference values (branch and bound, the relaxation G*_k, greedy selection with exchanges F_h) are read from
results/E35/<M>_<K>_<k>.jsonl.
Usage:  python3 -I e36_baselines.py <M> <K> <k> <n> <methods> [--tl seconds] [--oa n_oa] [--sdp n_sdp]
        methods: comma separated subset of pga,oscar,oa,sdp ;  --oa / --sdp: run oa / sdp only on the first instances
Output: one JSON line per instance on stdout.
"""
import json
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import e34_localized as E
import baselines as BL


def main():
    M, K, k, n = map(int, sys.argv[1:5])
    methods = sys.argv[5].split(',')
    tl = float(sys.argv[sys.argv.index('--tl') + 1]) if '--tl' in sys.argv else 600.0
    n_oa = int(sys.argv[sys.argv.index('--oa') + 1]) if '--oa' in sys.argv else n
    n_sdp = int(sys.argv[sys.argv.index('--sdp') + 1]) if '--sdp' in sys.argv else n
    ref = {}
    with open(os.path.join(HERE, 'results', 'E35', '%d_%d_%d.jsonl' % (M, K, k))) as f:
        for line in f:
            r = json.loads(line)
            ref[r['it']] = r
    seed = 1000 * M + 10 * K + k
    rng = np.random.default_rng(seed)
    for it in range(n):
        m, d, B, Sf = E.stress_instance(rng, M, K)
        rec = dict(M=M, K=K, k=k, seed=seed, it=it)
        if m.max() <= 0 or ref.get(it, {}).get('skip'):
            rec['skip'] = True
            print(json.dumps(rec), flush=True)
            continue
        R = ref[it]
        opt = R['bnb']
        rec.update(opt=opt, G=R['G'], Fh=R['Fh'])
        if 'pga' in methods:
            S, v, iters, t = BL.pga_lin2024(m, d, B, Sf, k)
            F = E.flo(m, d, B, Sf, list(S))[0] if len(S) else 0.0
            rec['pga'] = dict(value=F, size=len(S), iters=iters, time=t, ratio=F / opt)
        if 'oscar' in methods:
            S, t = BL.oscar_bae2025(m, d, B, Sf, k)
            t1 = time.perf_counter()
            F = E.flo(m, d, B, Sf, list(S))[0]
            rec['oscar'] = dict(value=F, time=t + time.perf_counter() - t1, ratio=F / opt)
        if 'oa' in methods and it < n_oa:
            t1 = time.perf_counter()
            Fh, Sh = E.greedy_swap(m, d, B, Sf, k)
            gval, that = E.relaxation(m, d, B, Sf, k)
            prep = time.perf_counter() - t1
            out = BL.oa_bcw2022(m, d, B, Sf, k, that, list(Sh), time_limit=tl)
            out['prep_time'] = prep
            out['ratio'] = out['value'] / opt
            out['solved'] = out['status'] in ('optimal', 'gaplimit')
            del out['support']
            rec['oa'] = out
        if 'sdp' in methods and it < n_sdp and M <= 200:
            for key, nonneg in (('sdp', False), ('sdp_nonneg', True)):
                val, t, st = BL.sdp_kim2016(m, d, B, Sf, k, nonneg=nonneg)
                rec[key] = dict(value=val, time=t, status=st, ratio=val / opt)
        print(json.dumps(rec), flush=True)


if __name__ == '__main__':
    main()
