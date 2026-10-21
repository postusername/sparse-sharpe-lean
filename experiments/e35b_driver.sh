#!/bin/bash
# E35b (Section 7.4): the MIQP baseline (e35_miqp.py) on the first instances of every configuration of E35
# (read from results/E35/<M>_<K>_<k>.jsonl, so run e35_driver.sh first); 3 workers, one thread each, 600 s per solve.
# Output: results/E35/miqp_<M>_<K>_<k>_<tag>.jsonl.  About 40 minutes with 3 workers.
cd "$(dirname "$0")"
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
{
for K in 1 2 3; do for k in 3 5 10; do
  echo "50 $K $k 3 persp_gurobi,persp_scip,bigM_scip all"
  echo "200 $K $k 3 persp_scip,bigM_scip all"
done; done
for K in 1 2 3; do for k in 3 5 10; do
  echo "1000 $K $k 1 bigM_scip bigM"
  echo "1000 $K $k 2 persp_scip persp"
  echo "2000 $K $k 1 persp_scip persp"
done; done
} | xargs -P 3 -L 1 sh -c 'python3 -I e35_miqp.py $0 $1 $2 $3 $4 --tl 600 > results/E35/miqp_$0_$1_$2_$5.jsonl 2> results/E35/miqp_$0_$1_$2_$5.err'
