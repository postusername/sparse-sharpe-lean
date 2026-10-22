# SparseSharpe: Lean 4 formalization

Machine-checked proofs for the paper

> Andrey Pavlov, *Approximability of sparse tangency portfolios under a factor model: a
> classification* (manuscript, 2026).

The paper studies the choice of at most `k` of `M` assets with long-only weights that maximize
the Sharpe ratio when the covariance matrix has the factor structure
`V = diag(d) + B Σ_f Bᵀ` with a fixed number `K` of factors. It gives approximation schemes that
return a fully invested long-only portfolio whose Sharpe ratio is at least `√(1 − 2ε)` times the
optimum. The main one picks this portfolio from an explicit family of candidate supports whose size
is bounded by a polynomial in `M`, `k` and `1/ε` for fixed `K`, with no dependence on the leverages
or on the magnitudes of the data; with short sales, a family of the same kind gives a portfolio of
gross exposure 1 whose Sharpe ratio is at least `√(1 − 17ε/8)` times the optimum. Another scheme
has a family independent of `M` whose size is polynomial in `k`, `1/ε` and the leverage bound `ω`. For practice,
the paper adds a dual certificate (the dual of the perspective relaxation), an optimality test, a
bound for branch and bound, and a localized scheme whose grid is confined by the gap of the
certificate.

Every theorem, proposition, lemma and corollary of the paper is proved here. In the PDF, each
numbered result has a superscript **L** that links to its Lean statement in this repository.
Appendix C of the paper lists all results with their declarations, and also the declarations
that their proofs use. `lake build` checks all proofs; `lake env lean SparseSharpe/Audit.lean`
prints the axioms of every declaration of the paper (only `propext`, `Classical.choice` and
`Quot.sound`).

The directory [experiments](experiments/) contains the scripts, the stored results and the data
checksums of the numerical experiments of Sections 5.4–5.6 and 7 of the paper; `make all` there recomputes
them and `make tables` rebuilds every table and figure of Section 7 and the numbers of the text (see
[experiments/README.md](experiments/README.md)).

## Version 0.29: no `ω` at all — Helly's theorem for the guesses

New file `Factor/HellyGuess`. With `Φ` the best value of a support with at most `min(k, K + 1)` names,
`Φ ≤ OPT(k) ≤ (k + 1)Φ`, with and without short sales (Helly's theorem in `ℝ^K`, from Mathlib: the sets
`D_i = {t : t'Σ_f⁻¹t ≤ Φ, (m_i − ⟨B_i,t⟩)₊²/d_i ≤ Φ}` are convex and any `K + 1` of them meet at the dual point of a small
support). So `⌈log₂(k + 1)⌉ + 1` guesses `Φ·2^j` replace the guesses `L·2^j`, whose number grew with the logarithm of the
data, and the families of Theorems 5.6 and 5.13 have sizes polynomial in `M`, `k` and `1/ε` alone (fixed `K`): the
leverages and the magnitudes of the data do not enter at all. The long-only version is the new Main Theorem of the paper;
the former Main Theorem (a family independent of `M`, polynomial in `ω`) is Theorem 1.1. Theorem 1.1 can take the guesses
`Φ·2^j` too (`main_theorem_clipped_helly`): its family stays independent of `M`, with fewer guesses when `ω` is large, but
computing `Φ` by enumeration takes `O(M^{K+1})` quadratic programs, while the guesses `L·2^j` take time `O(M)`.

| Paper (v0.29) | Declaration | File |
|---|---|---|
| Main Theorem (long-only, any fixed `K`, size polynomial in `M`, `k`, `1/ε`) | `main_theorem_univ_sp`, `exists_small_best`, `univ_instance_two_sp` | [Factor/HellyGuess.lean](SparseSharpe/Factor/HellyGuess.lean) |
| Helly's theorem for the value (Lemma 5.21) | `objLO_le_helly`, `objLO_le_helly_free`, `convex_sumsq_le`, `convex_clip_le`, `convex_sq_affine_le` | [Factor/HellyGuess.lean](SparseSharpe/Factor/HellyGuess.lean) |
| Consequence `Φ ≤ OPT(k) ≤ (k + 1)Φ` (Lemma 5.21) | `opt_le_helly`, `opt_le_helly_free` | [Factor/HellyGuess.lean](SparseSharpe/Factor/HellyGuess.lean) |
| Short sales, guesses without the data (Theorem 5.22) | `main_theorem_ls_sp`, `exists_small_best_free`, `ls_instance_sp` | [Factor/HellyGuess.lean](SparseSharpe/Factor/HellyGuess.lean) |
| Theorem 1.1 (the former Main Theorem: a family independent of `M`) | `main_theorem_clipped` | [Factor/ClippedTrading.lean](SparseSharpe/Factor/ClippedTrading.lean) |
| Theorem 1.1 with the guesses `Φ·2^j` (remark in Section 5.6) | `main_theorem_clipped_helly`, `clipped_instance_helly` | [Factor/HellyGuess.lean](SparseSharpe/Factor/HellyGuess.lean) |

## Version 0.28: neither `M` nor `ω` — a kernel and two lower bounds

New files `Factor/OnePassLower`, `Factor/Kernel`, `Factor/KernelScheme`, `Factor/ThreeSumGap`. The kernel keeps, in every cell of scale and
direction, the `k` assets with the largest return per unit of factor risk; every long-only portfolio with at most `k`
names is replaced by one inside the kernel with objective at least `1 − 4ε` times its own, and the kernel has at most
`k(1 + 2K·N_σ·(2G+1)^{K−1})` assets, with `N_σ` the number of scale classes and `G ≈ (1+ε)√ω·√(2k)K/ε`. For one factor
this is `k(2N_σ+1)`, logarithmic in the data, so the scheme of Theorem 5.13 on the kernel has a family whose size does not
depend on `M` and depends on the data only through logarithms (the theorems are stated for `Σ_f = I`; `objLO_factor`
reduces any `Σ_f` to it). For `K ≥ 2` and `k = 2` a scheme that reads the assets once must keep `n^{K−1}` assets on explicit
instances with `M = n^{K−1} + 1` and `ω ≤ 8Kn²/(1−ε)` (`lb_count`), which the kernel matches up to the factor `N_σ`. For `K ≥ 3` an instance of 3SUM' (are there `a + b = c` in three lists of integers?)
becomes a problem with `k = 3` whose optimum is `3` if the answer is yes and at most `1` otherwise, with or without short
sales; so under the 3SUM hypothesis no algorithm is subquadratic in `M` without depending on `ω` (the running-time
conclusion is not formalized).

| Paper (v0.28) | Declaration | File |
|---|---|---|
| Remark 2.2 now credits Kwan (1984, 1988) and Cheung–Kwan (1988) | — | — |
| The kernel (Definition 5.16) | `kerK`, `kcell`, `kscore`, `topK` | [Factor/Kernel.lean](SparseSharpe/Factor/Kernel.lean) |
| The kernel: value and size (Theorem 5.17); the change of variables `Σ_f → I` | `kernel_value`, `card_kerK_le`, `krho_le_sqrt`, `kdom`, `exchange_topK`, `objLO_factor`, `exists_factor_root` | [Factor/Kernel.lean](SparseSharpe/Factor/Kernel.lean) |
| The scheme on the kernel (Theorem 5.18) | `main_theorem_kernel`, `kerCandidates`, `kernel_instance` | [Factor/KernelScheme.lean](SparseSharpe/Factor/KernelScheme.lean) |
| One pass needs `M` or `ω` (Proposition 5.19) | `onepass_lower`, `lb_mem_of_good`, `lb_obj_le`, `lb_pair_obj`, `lb_leverage_le`, `lb_count`, `onepass_instance` | [Factor/OnePassLower.lean](SparseSharpe/Factor/OnePassLower.lean) |
| A gap from 3SUM (Proposition 5.20) | `threesum_decide`, `threesum_decide_pad`, `ts_yes`, `ts_le_three`, `ts_no`, `objLO_padZero`, `threesum_instance` | [Factor/ThreeSumGap.lean](SparseSharpe/Factor/ThreeSumGap.lean) |

## Version 0.27: the scheme without the leverage bound for long-only portfolios with `K` factors

New file `Factor/UniversalScheme`. The classification of the paper is complete: the long-only problem with any
fixed number of factors has a scheme without the leverage bound, on all instances (no condition on the optimal
portfolio), with the guarantee `1 − 2ε`. The witness of a candidate is built in the Cramer coordinates of a
maximum-volume `K`-tuple of the rows that are not small (no sign problem); the small positions of the optimum are
reduced to at most `K + 1` by Carathéodory's theorem and keep fixed weights; the node lies on the lattice of the
residual coordinates of a second maximum-volume `K`-tuple. The class version of v0.26 (`main_theorem_sf`) is kept;
the paper mentions it in Remark 5.15.

| Paper (v0.27) | Declaration | File |
|---|---|---|
| A witness with prescribed weights (Lemma 5.10) | `rowObj_wGen_ge`, `isStat_wGen`, `cramer_stat` | [Factor/UniversalScheme.lean](SparseSharpe/Factor/UniversalScheme.lean) |
| Few small positions, Carathéodory (Lemma 5.11) | `rowObj_carath`, `exists_carath`, `carath_loss_le` | [Factor/UniversalScheme.lean](SparseSharpe/Factor/UniversalScheme.lean) |
| The scheme without `ω` for `K` factors (Definition 5.12) | `univCandidates`, `univFamily`, `univTable` | [Factor/UniversalScheme.lean](SparseSharpe/Factor/UniversalScheme.lean) |
| `K` factors, long-only, from the data (Theorem 5.13) | `main_theorem_univ`, `card_univCandidates_le`, `univ_one_guess`, `univ_cert` | [Factor/UniversalScheme.lean](SparseSharpe/Factor/UniversalScheme.lean) |
| Two small positions (Example 5.14) | `univ_instance_two`, `univ_instance_two_small` | [Factor/UniversalScheme.lean](SparseSharpe/Factor/UniversalScheme.lean) |
| One tuple and the corner rule (Remark 5.15) | `main_theorem_sf`, `spec7_counterexample`, `spec7_fails` | [Factor/ScaleFreeScheme.lean](SparseSharpe/Factor/ScaleFreeScheme.lean), [Factor/ScaleFreeStep.lean](SparseSharpe/Factor/ScaleFreeStep.lean) |

## Version 0.26: schemes without the leverage bound

New files `Factor/SchemeLS`, `SchemeLO1`, `Factor/ScaleFreeStep` and `Factor/ScaleFreeScheme`. The three
schemes of Section 5 of the paper are stated from the data, with explicit instances of their hypotheses.

| Paper (v0.26) | Declaration | File |
|---|---|---|
| Long-short duality (Lemma 5.1) | `isGreatest_objLO_free` | [Factor/SchemeLS.lean](SparseSharpe/Factor/SchemeLS.lean) |
| Clamp of a maximum-volume tuple (Lemma 5.2) | `gram_le_card_mul_gramK`, `abs_cf_le_one` | [Factor/MaxVolume.lean](SparseSharpe/Factor/MaxVolume.lean) |
| A node in the residual coordinates (Theorem 5.3) | `exists_grid_node` | [Factor/GridK.lean](SparseSharpe/Factor/GridK.lean) |
| The long-short step (Lemma 5.5) | `fptasK_step` | [Factor/FPTASK.lean](SparseSharpe/Factor/FPTASK.lean) |
| Short sales, `K` fixed, from the data (Theorem 5.6) | `main_theorem_ls`, `card_lsCandidates_poly`, `ls_instance` | [Factor/SchemeLS.lean](SparseSharpe/Factor/SchemeLS.lean) |
| The one-factor step (Lemma 5.8) | `OneFactor.lo_step` | [LOFptas.lean](SparseSharpe/LOFptas.lean) |
| One factor, long-only, from the data (Theorem 5.9) | `main_theorem_lo1`, `card_lo1Candidates_poly`, `lo1_instance` | [SchemeLO1.lean](SparseSharpe/SchemeLO1.lean) |
| The Cramer witness, the step without `ν`, the signs of the weights | `cramer_witness`, `objLO_cramer`, `sf_step_eps`, `sf_signs_one_tight` | [Factor/ScaleFreeStep.lean](SparseSharpe/Factor/ScaleFreeStep.lean) |
| `K` factors, long-only, at most one small position (Theorem 5.11) | `main_theorem_sf`, `sf_instance_two` | [Factor/ScaleFreeScheme.lean](SparseSharpe/Factor/ScaleFreeScheme.lean) |
| The corner needs active rows (Remark 5.12) | `spec7_counterexample`, `spec7_fails` | [Factor/ScaleFreeStep.lean](SparseSharpe/Factor/ScaleFreeStep.lean) |

## Version 0.25: localization by the certificate, the perspective relaxation, nonnegative loadings

New files `Factor/Localize`, `PrunedDP`, `Perspective` and `NonnegGap`; `SaddleRounding` and `SaddleExistence`
now round with `⌊(K+1)/2⌋` fractional names.

| Paper (v0.25) | Declaration | File |
|---|---|---|
| Estimates at a node, with strong convexity (Theorem 4.2) | `node_estimates` | [Factor/Localize.lean](SparseSharpe/Factor/Localize.lean) |
| Localization by the gap of the certificate (Theorem 5.21) | `localize` | [Factor/Localize.lean](SparseSharpe/Factor/Localize.lean) |
| The localized nodes (Definition 5.22) and their number | `locNodes`, `card_locNodes_le` | [Factor/Localize.lean](SparseSharpe/Factor/Localize.lean) |
| Pruning keeps the representatives (Lemma 5.23) | `clipTableF_rep` | [Factor/PrunedDP.lean](SparseSharpe/Factor/PrunedDP.lean) |
| The localized scheme from the data (Theorem 5.24) | `trading_theorem_localized_pruned` | [Factor/PrunedDP.lean](SparseSharpe/Factor/PrunedDP.lean) |
| The dual bound is the dual of the perspective relaxation (Proposition 5.10) | `perspective_relaxation` | [Factor/Perspective.lean](SparseSharpe/Factor/Perspective.lean) |
| The gap for nonnegative loadings, `K` factors (Theorem 5.11), and its tight example | `dualBound_le_opt_nonneg_K`, `nonneg_gap_example` | [Factor/NonnegGap.lean](SparseSharpe/Factor/NonnegGap.lean) |
| Rounding with `⌊(K+1)/2⌋` (Theorem 5.18, Corollary 5.19) | `saddle_rounding_theorem`, `relaxation_rounding_sharpe` | [Factor/SaddleRounding.lean](SparseSharpe/Factor/SaddleRounding.lean), [Factor/SaddleExistence.lean](SparseSharpe/Factor/SaddleExistence.lean) |

## Version 0.24: rounding at the saddle point, existence of the saddle point, no minimax theorem

New files `Factor/PairRounding`, `SaddleRounding`, `SaddleExistence`, `NodeSharp`, `RootExists` prove, without any
assumption beyond the data, that the relaxation `G*_k = min_t g_k(t)` has a minimizer `t*` at which the clipped
portfolio `w(t*)` on a suitable support of exactly `k` names loses at most `(Kω/k)·G*_k` against `G*_k`
(Theorem 3.2 of the analytic note), and that a support with at most `k+K` names has long-only value at least
`G*_k`. The multiplier `λ*` of the saddle point and its vertex with at most `K+1` fractional coordinates, which
the paper used to take from the minimax theorem of Sion, are now constructed in Lean (Gordan's alternative and a
basic-solution argument).

| Paper (v0.24) | Declaration | File |
|---|---|---|
| Rounding lemma (pairwise merges) | `exists_hasRounding`, `exists_set_sq_le_min` | [Factor/PairRounding.lean](SparseSharpe/Factor/PairRounding.lean) |
| Saddle point: dual bound, minimality, loss = defect | `SaddleData.isMin`, `SaddleData.loss_eq` | [Factor/SaddleRounding.lean](SparseSharpe/Factor/SaddleRounding.lean) |
| Theorem 3.2 in one statement (parts (i)–(iii) of Theorem 5.16 of the paper) | `saddle_rounding_theorem` | [Factor/SaddleRounding.lean](SparseSharpe/Factor/SaddleRounding.lean) |
| Theorem 3.2(a): loss `≤ min(s,f−s)·ωσ ≤ K·ωσ ≤ (Kω/k)·G*_k` | `saddle_rounding_min`, `saddle_rounding_K`, `saddle_rounding_one` | [Factor/SaddleRounding.lean](SparseSharpe/Factor/SaddleRounding.lean) |
| Theorem 3.2(b): average over a representation, `≤ f·σ·Σλ(1−λ)ω_i` | `saddle_rounding_avg`, `exists_isRep` | [Factor/SaddleRounding.lean](SparseSharpe/Factor/SaddleRounding.lean) |
| `L(t,λ) ≤ g_k(t)` on the hypersimplex, equality at a saddle point | `lagrangian_le_dualBound`, `SaddleData.dualBound_eq_lagrangian` | [Factor/SaddleRounding.lean](SparseSharpe/Factor/SaddleRounding.lean) |
| Existence of a minimizer of `g_k` | `exists_isMin_dualBound` | [Factor/SaddleExistence.lean](SparseSharpe/Factor/SaddleExistence.lean) |
| First-order condition (Gordan) | `exists_weights_of_isMin` | [Factor/SaddleExistence.lean](SparseSharpe/Factor/SaddleExistence.lean) |
| Saddle point, vertex with `≤ K+1` fractional coordinates | `exists_saddle`, `exists_saddle_vertex` | [Factor/SaddleExistence.lean](SparseSharpe/Factor/SaddleExistence.lean) |
| Rounding and certificate, unconditional (with weak duality `OPT(k) ≤ G*_k`) | `relaxation_rounding`, `relaxation_bicriteria` | [Factor/SaddleExistence.lean](SparseSharpe/Factor/SaddleExistence.lean) |
| Rounding with the Sharpe-ratio guarantee `√(1−Kω/k)` | `relaxation_rounding_sharpe` | [Factor/SaddleExistence.lean](SparseSharpe/Factor/SaddleExistence.lean) |
| Sharper loss at a node (Remark 4.3) | `objLO_wclip_ge_of_node_sharp` | [Factor/NodeSharp.lean](SparseSharpe/Factor/NodeSharp.lean) |
| The root `G` with `GᵀG = P`, `P Σ_f = I` exists for every positive definite `Σ_f` | `exists_root_of_posDef` | [Factor/RootExists.lean](SparseSharpe/Factor/RootExists.lean) |

## Version 0.23: scheme without the Gram matrix

The newest development (files `Factor/AdditiveKey`, `ClippedNode`, `ClippedDP`, `ClippedTrading`,
`Relaxation`, `CapDuality`) replaces the moment/Gram key of the earlier scheme by an exactly additive key built
from the clipped weights `w(τ)`; it is the one used by the current version of the paper.

| Paper (v0.23) | Declaration | File |
|---|---|---|
| Main Theorem | `main_theorem_clipped` | [Factor/ClippedTrading.lean](SparseSharpe/Factor/ClippedTrading.lean) |
| Defect identity | `objLO_wclip_deficit` | [Factor/ClippedNode.lean](SparseSharpe/Factor/ClippedNode.lean) |
| Estimates at a node | `objLO_wclip_ge_of_node` | [Factor/ClippedNode.lean](SparseSharpe/Factor/ClippedNode.lean) |
| Knapsack with an additive key | `knap_spec` | [Factor/AdditiveKey.lean](SparseSharpe/Factor/AdditiveKey.lean) |
| One guess | `clip_one_guess` | [Factor/ClippedDP.lean](SparseSharpe/Factor/ClippedDP.lean) |
| Trading form | `trading_theorem_clipped`, `trading_theorem_clipped_adaptive` | [Factor/ClippedTrading.lean](SparseSharpe/Factor/ClippedTrading.lean) |
| Polynomial size `8(60K)^K ε^{-K}(k(1+ω))^{3K+2}` | `card_clipCandidates_poly_of_J` | [Factor/ClippedTrading.lean](SparseSharpe/Factor/ClippedTrading.lean) |
| Gap of the relaxation, certificate with `k+K` names | `dualBound_le_two_opt_nonneg`, `bicriteria_certificate` | [Factor/Relaxation.lean](SparseSharpe/Factor/Relaxation.lean) |
| Position limits (weak duality) | `cap_weak_duality` | [Factor/CapDuality.lean](SparseSharpe/Factor/CapDuality.lean) |

The audit file prints the axioms of 699 statements (no `sorry`).

## Main statements of the first edition (historical)

This table keeps the numbering of the first edition of the paper, whose Main Theorem was `main_theorem_simple`; the
current numbering is in the version sections above and in Appendix C of the paper. All declarations are in the namespace
`SparseSharpe.Factor`.

| Paper | Declaration | File |
|---|---|---|
| Main Theorem (first edition) | `main_theorem_simple` | [Factor/Practical.lean](SparseSharpe/Factor/Practical.lean#L1046) |
| Proposition 8.7 (polynomial size) | `NK_le_poly`, `card_candidatesAnchor_poly` | [Factor/Practical.lean](SparseSharpe/Factor/Practical.lean#L843) |
| Theorem 6.15 (one guess, one node) | `main_theorem_list` | [Factor/TradingAnchor.lean](SparseSharpe/Factor/TradingAnchor.lean#L52) |
| Theorem 6.17 (anchor basis) | `main_theorem_anchor_list` | [Factor/TradingAnchor.lean](SparseSharpe/Factor/TradingAnchor.lean#L173) |
| Theorem 8.8 (trading form) | `trading_theorem_anchor`, `trading_theorem` | [Factor/TradingAnchor.lean](SparseSharpe/Factor/TradingAnchor.lean#L880) |
| Theorem 8.13 (adaptive guesses) | `trading_theorem_anchor_adaptive`, `trading_theorem_adaptive` | [Factor/Practical.lean](SparseSharpe/Factor/Practical.lean#L712) |
| Theorem 8.9 (dual bound) | `objLO_le_dualBound` | [Factor/Practical.lean](SparseSharpe/Factor/Practical.lean#L338) |
| Corollary 8.10 (certificate) | `certificate_sharpe`, `certificate_sharpe_eps` | [Factor/Practical.lean](SparseSharpe/Factor/Practical.lean#L427) |
| Theorem 8.11 (optimality test) | `optimal_of_top_at_dual` | [Factor/Practical.lean](SparseSharpe/Factor/Practical.lean#L566) |
| Proposition 8.12 (branch and bound) | `objLO_le_nodeBound` | [Factor/Practical.lean](SparseSharpe/Factor/Practical.lean#L528) |
| Theorem 2.4 (strong duality) | `isGreatest_objLO_isLeast_QLO` | [Factor/Duality.lean](SparseSharpe/Factor/Duality.lean#L294) |
| Theorem 2.7 (reduction) | `isGreatest_phi_selfconsistent` | [Factor/Reduction.lean](SparseSharpe/Factor/Reduction.lean#L247) |
| Theorem 5.2 (rotation invariance) | `rot_preserves_state` | [Factor/Rotation.lean](SparseSharpe/Factor/Rotation.lean#L145) |
| Theorem 6.8 (long-only step) | `psiC_ge_of_approxBucket_calibrated_block` | [Factor/BlockLeverage.lean](SparseSharpe/Factor/BlockLeverage.lean#L396) |
| Theorem 6.11 (dynamic program) | `survivorsBox_spec` | [Factor/DPBox.lean](SparseSharpe/Factor/DPBox.lean#L169) |
| Theorem 7.1 (limit of the covering) | `cover_const_ge_asset` | [Factor/GuaranteeBlock.lean](SparseSharpe/Factor/GuaranteeBlock.lean#L183) |
| Proposition 3.2 (hardness reduction) | `subsetSum_reduction` | [Factor/Landscape.lean](SparseSharpe/Factor/Landscape.lean#L224) |

The hypotheses of the end-to-end statements (`main_theorem_simple`, `main_theorem_list`,
`main_theorem_anchor_list`, the trading theorems) are properties of the data and the
parameters only. `practical_instance` and `trading_theorems_instance` show, on explicit
instances, that all these hypotheses can hold at once and that the conclusions are
nontrivial.

## Building and checking

The toolchain `leanprover/lean4:v4.35.0-rc2` is selected by `lean-toolchain`. Mathlib is
pinned to the tag `v4.35.0-rc2` in `lake-manifest.json`. With [elan](https://github.com/leanprover/elan) installed:

```
lake exe cache get                       # download the prebuilt Mathlib (several GB)
lake build                               # build the formalization
lake env lean SparseSharpe/Audit.lean    # print the axioms of 1106 statements
```

Each of the 1106 statements depends only on `propext`, `Classical.choice` and `Quot.sound`
(some on a subset), and none on `sorryAx`. The sources contain no `sorry`, no `axiom`
declarations and no `native_decide`. The development has 84 files and about 37 400 lines.

## Layout

* `SparseSharpe/`: the one-factor development and generic tools (greedy bounds, the
  long-only certificate for general quadratics, the grid, the invariant of the dynamic
  program).
* `SparseSharpe/Factor/`: the `K`-factor development.
  * Rows, duality and reduction: `LeastSquares`, `Duality`, `Reduction`.
  * Long-short scheme: `FPTASK`, `GridK`, `MaxVolume`, `KeyRounding`.
  * The obstacle: `Rotation`, `Ex135`, `Sticky`.
  * Long-only scheme: `Stability`, `BlockLeverage`, `Cover`, `Leverage`, `Rounding`,
    `GridFilter`, `DPBox`, `DPRun`, `Cost`, `StateCount`, `Main`, `AnchorBasis`.
  * Limits: `GuaranteeBlock`, `Gordan`, `Reachable`.
  * Hardness: `Landscape`, `Padding`.
  * Trading form: `Trading`, `TradingAnchor`.
  * Schemes without the leverage bound: `SchemeLS` (short sales), `ScaleFreeStep` and
    `ScaleFreeScheme` (one tuple, at most one small position), `UniversalScheme` (long-only, any
    fixed `K`); the one-factor scheme is `SparseSharpe/SchemeLO1`.
  * Neither `M` nor `ω`: `Kernel` (the `k` best assets per cell of scale and direction),
    `KernelScheme` (Theorem 5.13 on the kernel), `OnePassLower` (the lower bound for one pass),
    `ThreeSumGap` (the gap from 3SUM for `K ≥ 3`).
  * No `ω` at all: `HellyGuess` (Helly's theorem for the guesses; the strongly polynomial forms of Theorems 5.6
    and 5.13; Theorem 1.1 with these guesses).
  * Symmetric key, dual certificate, adaptive guesses and the simple Main Theorem of the first
    edition: `Practical`.
* `SparseSharpe/Audit.lean`: `#print axioms` for all main statements.

## Conventions and scope

* Real arithmetic is exact, and assets and factors are indexed by arbitrary finite types.
  No matrix is inverted: `Σ_f⁻¹` enters through a matrix `P` with `P Σ_f = I`, and through a
  matrix `G` with `Gᵀ G = P`, which is part of the data. Such `P` and `G` exist for every positive
  definite `Σ_f` (`exists_root_of_posDef`).
* Not formalized: running times (the sizes of all enumerated sets are formalized, a model of
  computation is not), floating-point arithmetic, the search procedures (the numerical minimization of the
  dual bound, greedy selection, branching; the existence of a minimizer and of its multiplier is formalized),
  strong duality with position limits (only weak duality and the certificate are proved), and the
  NP-completeness of SUBSET SUM, which the hardness argument cites.
* Many comments and docstrings are in Russian. The formal statements are
  language-independent.

## Version

The links in the paper point to a fixed commit of this repository. Later commits may shift
line numbers, so a link opens the version that the paper describes.
