# Experiments of Sections 5.4 and 7 of the paper.  `make data` downloads the public data (checked against data/SHA256SUMS);
# `make all` recomputes every experiment (several hours: the solver times recorded in results/ alone add up to about
# 5 hours on one core); `make tables` rebuilds the tables, the numbers of the text and the data files of the figures
# from the stored results in results/ (seconds).
PY = OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 python3 -I

.PHONY: all data tables e29 e30 e30b e31 e33 check e34 e35 e35b e35loc e36 e40 e41 e43 e44 e45 e46 e47 e48 clean-tables

all: data e40 e41 e34 e35 e35b e35loc e36 e29 e30 e30b e31 e33 check e43 e44 e45 e46 e47 e48 tables

data:
	$(PY) -c "import sys; sys.path.insert(0, '.'); import data_real as D; D.load_ff_monthly(); [D.load_port(i) for i in range(1, 6)]; D.load_indtrack(6); D.load_indtrack(8); print('data ok')"

# Sections 7.1-7.2: real data (Tables 7.1, 7.2, the certificate at scale, the screening rules); about 5 minutes
e40:
	mkdir -p results/E40
	$(PY) e40_realdata.py optima > results/E40/optima.log
	$(PY) e40_realdata.py instances > results/E40/instances.jsonl

# Section 7.3: random instances with M = 16 in seven regimes (Tables 7.3, 7.4, Figure 7.1); about 5 minutes on 4 cores
e41:
	mkdir -p results/E41
	for r in 0 1 2 3 4 5 6; do echo $$r; done | xargs -P 4 -I{} sh -c '$(PY) e41_random.py {} 100 > results/E41/regime_{}.jsonl'

# Section 7.4: one-step checks of the localized scheme (1 minute), the stress regime at scale, the MIQP baseline,
# the check of the localized nodes
e34:
	mkdir -p results/E34
	$(PY) e34_localized.py > results/E34/e34.log
e35:
	./e35_driver.sh
e35b: e35
	./e35b_driver.sh
e35loc: e35
	mkdir -p results/E35
	$(PY) e35_loccheck.py > results/E35/e35_loccheck.log

# Section 7.5 (methods from the literature) on the instances of E35 and E41; about 2 hours on 3 cores
e36: e35
	./e36_driver.sh
	$(PY) e36_oscar_signed.py > results/E36/oscar_signed.jsonl

# The embedding of two-dimensional knapsack (plan C2): no cliff, the gap between YES and NO instances falls like
# 4^(-m) (e43_knap2d.py, 50-digit arithmetic; about a minute on one core)
e43:
	mkdir -p results/E43
	$(PY) e43_knap2d.py A > results/E43/testA.log
	$(PY) e43_knap2d.py B > results/E43/testB.log

# The scheme with one maximum-volume K-tuple (Remark 5.15, Lean main_theorem_sf): one-step checks of its lemmas with
# controls, the adversary of the step, and the whole scheme on small instances (e44_scalefree.py; from 20 seconds to 2 minutes per part on one core, rand30
# and cluster30 about 7 minutes, k3 about 14 minutes; about 15 minutes on 4 cores)
E44PARTS = onestep_rand_2 onestep_cluster_2 onestep_ortho_2 onestep_rand_3 onestep_cluster_3 onestep_ortho_3 \
           lemmas_rand_2 lemmas_cluster_2 lemmas_ortho_2 lemmas_rand_3 lemmas_cluster_3 lemmas_ortho_3 \
           advstep_2 advstep_3 def510_rand_2 def510_cluster_2 def510_ortho_2 def510_rand_3 def510_cluster_3 \
           def510_ortho_3 advdef_2 advdef_3 rand cluster ortho rand30 cluster30 k3 adv
e44:
	mkdir -p results/E44
	for p in $(E44PARTS); do echo $$p; done | xargs -P 4 -I{} sh -c '$(PY) e44_scalefree.py {} > results/E44/{}.jsonl'

# The scheme without omega for K factors (Theorem 5.13): the step at the node of the proof on 800 instances with
# controls, and an adversarial search (e45_universal.py; about 2 minutes per part with K = 2 and 5 with K = 3, the
# adversaries about 15 minutes; about 30 minutes on 4 cores)
E45PARTS = step_hedge_2 step_rand_2 step_cluster_2 step_ortho_2 step_hedge_3 step_rand_3 step_cluster_3 step_ortho_3 \
           adv_2 adv_3
e45:
	mkdir -p results/E45
	for p in $(E45PARTS); do echo $$p; done | xargs -P 4 -I{} sh -c '$(PY) e45_universal.py {} > results/E45/{}.jsonl'

# Section 5.5: the kernel (top k per cell) on crowded random instances and on the instances of the one-pass lower
# bound, with controls (e46_kernel.py; about a minute per part)
E46PARTS = rand_1 rand_2 rand_3 lb_2 lb_3
e46:
	mkdir -p results/E46
	for p in $(E46PARTS); do echo $$p; done | xargs -P 4 -I{} sh -c '$(PY) e46_kernel.py {} > results/E46/{}.jsonl'

# Section 5.5: the 3SUM gap for K = 3, k = 3 on random YES and NO instances, with controls (e47_threesum.py; under
# a minute)
e47:
	mkdir -p results/E47
	$(PY) e47_threesum.py gap > results/E47/gap.jsonl

# Section 5.6: the Helly bound V <= OPT(k) <= (k+1)V on random instances, with controls (e48_helly.py; a minute
# per part)
E48PARTS = rand_1 rand_2 rand_3
e48:
	mkdir -p results/E48
	for p in $(E48PARTS); do echo $$p; done | xargs -P 3 -I{} sh -c '$(PY) e48_helly.py {} > results/E48/{}.jsonl'

# Sections 7.6-7.7: the scheme itself, size bounds, checks of the estimates, the relaxation and the rounding
e30:
	mkdir -p results/E30
	$(PY) e30_additive_dp.py > results/E30/e30.log
e30b:
	mkdir -p results/E30b
	$(PY) e30b_stress.py > results/E30b/e30b.log
e31:
	mkdir -p results/E31
	$(PY) e31_size_bounds.py > results/E31/e31.log
e33:
	mkdir -p results/E33
	$(PY) e33_node_ratio.py > results/E33/e33.log
check:
	mkdir -p results/CHECK
	$(PY) check_clipped_dp.py > results/CHECK/check_clipped_dp.log
e29:
	mkdir -p results/E29
	$(PY) e29_dual_rounding.py > results/E29/e29.log
	$(PY) e29_floor_bound.py > results/E29/e29_floor_bound.log

tables:
	mkdir -p tables
	$(PY) e35_table.py > tables/e35_table.md
	$(PY) make_tables.py > tables/make_tables.log
	@echo "tables/ written; copy tables/*.tex and tables/random.json into the paper (see README.md)"
