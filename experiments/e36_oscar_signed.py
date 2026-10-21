"""E36b: the long-only variant of the selection of Bae et al. (2025) (baselines.oscar_bae2025 with signed=True) on
the instances of E35 (stress regime at scale) and of E41 (random instances with M = 16), replayed with the same seeds.
Usage:  python3 -I e36_oscar_signed.py > results/E36/oscar_signed.jsonl     (a few minutes)
"""
import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import e34_localized as E
import e41_random as R41
import baselines as BL


def value(m, d, B, Sf, k):
    S, t = BL.oscar_bae2025(m, d, B, Sf, k, signed=True)
    return E.flo(m, d, B, Sf, list(S))[0]


def main():
    for M in (50, 200, 1000, 2000):
        n = 30 if M <= 200 else 20
        for K in (1, 2, 3):
            for k in (3, 5, 10):
                seed = 1000 * M + 10 * K + k
                rng = np.random.default_rng(seed)
                for it in range(n):
                    m, d, B, Sf = E.stress_instance(rng, M, K)
                    if m.max() <= 0:
                        continue
                    print(json.dumps(dict(set='E35', M=M, K=K, k=k, it=it, oscar_signed=value(m, d, B, Sf, k))), flush=True)
    for r, (structure, returns) in enumerate(R41.REGIMES):
        for K in (1, 2, 3, 5):
            for k in (3, 5):
                seed = 41000 + 1000 * r + 10 * K + k
                rng = np.random.default_rng(seed)
                done = 0
                while done < 100:
                    m, d, B, Sf = R41.instance(rng, 16, K, structure, returns)
                    if m.max() <= 0:
                        continue
                    print(json.dumps(dict(set='E41', structure=structure, returns=returns, K=K, k=k, it=done,
                                          oscar_signed=value(m, d, B, Sf, k))), flush=True)
                    done += 1


if __name__ == '__main__':
    main()
