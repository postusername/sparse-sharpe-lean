# Experiments of Section 6 of the paper.  `make data` downloads the public data (checked against data/SHA256SUMS);
# `make all` recomputes every experiment (several hours: the solver times recorded in results/ alone add up to about
# 5 hours on one core); `make tables` rebuilds the tables, the numbers of the text and the data files of the figures
# from the stored results in results/ (seconds).
PY = OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 python3 -I

.PHONY: all data tables e29 e30 e30b e31 e33 check e34 e35 e35b e35loc e36 e40 e41 clean-tables

all: data e40 e41 e34 e35 e35b e35loc e36 e29 e30 e30b e31 e33 check tables

data:
	$(PY) -c "import sys; sys.path.insert(0, '.'); import data_real as D; D.load_ff_monthly(); [D.load_port(i) for i in range(1, 6)]; D.load_indtrack(6); D.load_indtrack(8); print('data ok')"

# Sections 6.1-6.2: real data (Tables 6.1, 6.2, the certificate at scale, the screening rules); about 5 minutes
e40:
	mkdir -p results/E40
	$(PY) e40_realdata.py optima > results/E40/optima.log
	$(PY) e40_realdata.py instances > results/E40/instances.jsonl

# Section 6.3: random instances with M = 16 in seven regimes (Tables 6.3, 6.4, Figure 6.1); about 5 minutes on 4 cores
e41:
	mkdir -p results/E41
	for r in 0 1 2 3 4 5 6; do echo $$r; done | xargs -P 4 -I{} sh -c '$(PY) e41_random.py {} 100 > results/E41/regime_{}.jsonl'

# Section 6.4: one-step checks of the localized scheme (1 minute), the stress regime at scale, the MIQP baseline,
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

# Section 6.5 (methods from the literature) on the instances of E35 and E41; about 2 hours on 3 cores
e36: e35
	./e36_driver.sh
	$(PY) e36_oscar_signed.py > results/E36/oscar_signed.jsonl

# Sections 6.6-6.7: the scheme itself, size bounds, checks of the estimates, the relaxation and the rounding
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
