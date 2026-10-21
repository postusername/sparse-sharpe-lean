#!/bin/bash
# E35 (Section 7.4): the stress regime at scale, 36 configurations, 3 workers with one thread each;
# one JSON line per instance in results/E35/<M>_<K>_<k>.jsonl.  About 6 minutes with 3 workers.
cd "$(dirname "$0")"
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
mkdir -p results/E35
for M in 50 200 1000 2000; do
  n=30; [ $M -ge 1000 ] && n=20
  for K in 1 2 3; do for k in 3 5 10; do echo "$M $K $k $n"; done; done
done | xargs -P 3 -L 1 sh -c 'python3 -I e35_scale.py $0 $1 $2 $3 --bnb 600 > results/E35/$0_$1_$2.jsonl 2> results/E35/$0_$1_$2.err'
