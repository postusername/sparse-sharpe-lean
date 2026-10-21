#!/bin/bash
# E36: the methods of baselines.py on all instances of E35 -> results/E36/<M>_<K>_<k>.jsonl (3 workers, one thread each).
# The SDP (P7) is solved for M = 50 only: for M = 200 the conic solver needs more than the 15 GB of the machine.
cd "$(dirname "$0")"
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
mkdir -p results/E36
for M in 50 200 1000 2000; do
  n=30; [ $M -ge 1000 ] && n=20
  nsdp=0; [ $M -eq 50 ] && nsdp=30
  for K in 1 2 3; do for k in 3 5 10; do echo "$M $K $k $n $nsdp"; done; done
done | xargs -P 3 -L 1 sh -c 'python3 -I e36_baselines.py $0 $1 $2 $3 pga,oscar,oa,sdp --sdp $4 --tl 600 > results/E36/$0_$1_$2.jsonl 2> results/E36/$0_$1_$2.err; echo "$0 $1 $2 exit $?"'
