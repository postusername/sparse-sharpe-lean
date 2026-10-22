# Experiments of the paper

This directory contains the scripts, the stored results and the data checksums of Section 7 of the paper
*Approximability of sparse tangency portfolios under a factor model: a classification*. The Lean formalization is in
the rest of the repository.

    make data      # download the public data into data/ and check them against data/SHA256SUMS
    make all       # recompute every experiment (several hours; the recorded solver times add up to
                   # about 5 hours on one core) and rebuild the tables
    make tables    # rebuild the tables, the numbers of the text and the figure data from results/ (seconds)

`make tables` writes `tables/*.tex` (the bodies of the tables of Section 7, which the paper reads with `\tabinput`),
`tables/random.json` (the data of Figure 7.1, read by `tools/make_figures.py` of the paper source),
`tables/e35_table.md` and `numbers.md`. `numbers.md` lists the numbers quoted in the text of Sections 5.4 and 7 and in the
Introduction, with their values from the stored results; the per-configuration numbers of Section 7.4 are in
`tables/e35_table.md`, and the one-step checks of Section 7.4 in `results/E34/e34.log`.

## Environment

The results in `results/` were computed single-threaded, with at most four processes at a time, on an Intel Xeon
processor with four cores at 2.1 GHz and 15 GB of memory, with the packages of `requirements.txt` (Python 3.13.16).
Times depend on the machine; everything else is deterministic (fixed seeds; the solvers run with one thread), except
the incumbent and the gap of a solver that stops at its time limit. Gurobi is used only through its size-limited license (models with
quadratic terms and at most 200 variables, i.e. only `M = 50`); SCIP 10.0 is open source.

## Data

* K. R. French data library: `49_Industry_Portfolios_CSV.zip`, `F-F_Research_Data_Factors_CSV.zip`,
  `F-F_Research_Data_5_Factors_2x3_CSV.zip` (monthly; the paper uses the 120 months July 2016 – June 2026, fixed in
  `data_real.py`). The library is updated every month and revised from time to time; `data_real.py` warns when a
  downloaded file differs from the one used for the paper (`data/SHA256SUMS`, files of 2026-10-21).
* OR-Library (J. E. Beasley): `port1.txt` – `port5.txt` (Chang et al. 2000) and `indtrack6.txt`, `indtrack8.txt`
  (Canakgoz and Beasley 2009).

The data files are not stored in the repository; `make data` downloads them.

## What produces what

| paper | script | results | table body |
|---|---|---|---|
| Table 7.1 and the text of Section 7.1 | `e40_realdata.py optima` | `results/E40/optima.json`, `optima.log` | `tables/optima.tex` |
| Table 7.2, "The certificate at scale", "What the guarantee buys" | `e40_realdata.py instances` | `results/E40/instances.jsonl` | `tables/large.tex` |
| Table 7.3, Table 7.4, Figure 7.1 (random instances, seven regimes) | `e41_random.py <regime>` | `results/E41/regime_*.jsonl` | `tables/random.tex`, `tables/regimes.tex`, `tables/random.json` |
| Section 7.4, "One-step checks" | `e34_localized.py` | `results/E34/e34.log` | — |
| Table 7.5 and the rest of Section 7.4 (stress regime at scale) | `e35_driver.sh` → `e35_scale.py` | `results/E35/<M>_<K>_<k>.jsonl` | `tables/e35_table.tex` (`e35_table.py`) |
| Section 7.4, mixed-integer solvers | `e35b_driver.sh` → `e35_miqp.py` | `results/E35/miqp_*.jsonl` | `tables/e35_table.md` |
| Section 7.4, check of the localized nodes | `e35_loccheck.py` | `results/E35/e35_loccheck.log` | — |
| Table 7.6 and Section 7.5, methods from the literature | `e36_driver.sh` → `e36_baselines.py`; `e36_oscar_signed.py`; `e41_random.py` | `results/E36/`, `results/E41/` | `tables/literature.tex` |
| Table 7.7 and Section 7.6, the scheme itself | `e30_additive_dp.py` | `results/E30/` | `tables/own.tex` |
| Section 7.6, coarsening of the constants | `e30b_stress.py` | `results/E30b/` | — |
| Section 7.6, formal size bounds (Table 7.8, Figure 7.2) | `e31_size_bounds.py` | `results/E31/` | `tables/bounds.tex` |
| Section 7.6, checks of the estimates, Figure 7.3 | `check_clipped_dp.py`, `e33_node_ratio.py` | `results/CHECK/`, `results/E33/node_ratio.csv` | — |
| Section 7.7, the relaxation, the certificate with `k+K` names and the rounding | `e29_dual_rounding.py`, `e29_floor_bound.py` | `results/E29/` | — |
| Section 5.4, the embedding of two-dimensional knapsack (work plan v0.26, C2): no cliff, the gap between YES and NO instances falls like 4^(−m) | `e43_knap2d.py A`, `e43_knap2d.py B` (`make e43`) | `results/E43/testA.log`, `testB.log` | — |
| Section 5.4, the scheme without ω for K factors (Theorem 5.13): the step at the node of the proof on 800 instances, every set of the bucket of the large positions, the witness of the proof, controls (no forced small positions, key ×30, the node on the lattice of the witness tuple, one tuple of all rows) and an adversary | `e45_universal.py <part>` (`make e45`) | `results/E45/` | — |
| Section 5.5, the kernel (Theorem 5.17) on 360 crowded random instances (K = 1, 2, 3) and on the instances of Proposition 5.19, with controls (one scale class, no angular grid, the grid ×30 and ×100) | `e46_kernel.py <part>` (`make e46`) | `results/E46/` | — |
| Section 5.5, the 3SUM gap (Proposition 5.20) on 200 random YES and NO instances (K = 3, k = 3), with controls (A = 1, two factors, k = 4) | `e47_threesum.py gap` (`make e47`) | `results/E47/` | — |
| Remark 5.15, the scheme with one maximum-volume K-tuple on the instances with at most one small position (Lean `main_theorem_sf`, work plan v0.26, C1): its step at the node of the proof with controls and an adversary (`def510_*`, `advdef_*`); a coarser variant: one-step checks of its lemmas with controls, the adversary of the step, the whole scheme on small instances; not quoted in the paper | `e44_scalefree.py <part>` (`make e44`) | `results/E44/` | — |

Libraries: `data_real.py` (data and factor models), `e34_localized.py` (the long-only value `F_LO` by nonnegative
least squares, scores, the dual bound `g_k`, the relaxation `G*_k`, greedy selection with exchanges, the localized
scheme), `e35_scale.py` (branch and bound), `clipped_dp.py` (the dynamic program of Algorithm 4.1), `baselines.py`
(the methods from the literature: the proximal gradient algorithm of Lin, Lai and Li (2024), the asset selection of
Bae et al. (2025), the semidefinite relaxation of Kim et al. (2016) and the outer approximation of Bertsimas and
Cory-Wright (2022), each described in its docstring together with what was adapted to the long-only problem).

## Notes

* The first run of E35 set no limit on the threads of the linear algebra libraries (three workers on four cores); its
  times of greedy selection, the relaxation and branch and bound were 1.2 to 35 times larger (median per
  configuration). The stored results are a rerun with one thread per worker (`e35_driver.sh`): every value, number
  of nodes and flag is identical, only the times changed. So that every time in the paper comes from single-threaded
  runs with at most four processes on the four cores, E40, E41 and the MIQP runs (`e35b_driver.sh`), which were
  single-threaded but may have shared the machine with other jobs, were rerun as well: the same values, the same
  statuses, incumbents and crashes of the solvers, and times within a few percent (E41 now also records the time of
  the relaxation).
* The first run of the MIQP baseline used a perspective formulation without the link `w_i <= U_i z_i`; with it,
  SCIP reported values above the optimum (feasibility tolerance), and that run was discarded.
* For `M = 2000`, SCIP 10.0 aborts with a memory-corruption error (SIGABRT, exit status 134 in a shell) on three
  instances, reproducibly (in both runs); `e35_miqp.py` runs every solve in a child process and records such a crash
  in the result line ("the solver process died with exit code -6"), with the messages of the C library in the `.err`
  file.
* The semidefinite relaxation of Kim et al. is solved for `M <= 50` only: with `M = 200` Clarabel needs more than the
  15 GB of the machine.
