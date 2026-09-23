# SparseSharpe: Lean 4 formalization

Machine-checked proofs for the paper

> Andrey Pavlov, *A machine-checked approximation scheme for the sparse long-only tangency
> portfolio under a factor model* (manuscript, 2026).

The paper studies the choice of at most `k` of `M` assets with long-only weights that maximize
the Sharpe ratio when the covariance matrix has the factor structure
`V = diag(d) + B Σ_f Bᵀ` with a fixed number `K` of factors. It gives an approximation scheme
that returns a fully invested long-only portfolio whose Sharpe ratio is at least `√(1 − 2ε)`
times the optimum. The scheme picks this portfolio from an explicit family of candidate
supports whose size is bounded by a polynomial in `M`, `k`, `1/ε` and the leverage bound `ω`
for fixed `K`. For practice, the paper adds a dual certificate, an optimality test and a bound
for branch and bound.

Every theorem, proposition, lemma and corollary of the paper is proved here. In the PDF, each
numbered result has a superscript **L** that links to its Lean statement in this repository.
Appendix B of the paper lists all results with their declarations, and also the declarations
that their proofs use.

## Main statements

All declarations are in the namespace `SparseSharpe.Factor`.

| Paper | Declaration | File |
|---|---|---|
| Main Theorem | `main_theorem_simple` | [Factor/Practical.lean](SparseSharpe/Factor/Practical.lean#L1046) |
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
lake env lean SparseSharpe/Audit.lean    # print the axioms of 518 statements
```

Each of the 518 statements depends only on `propext`, `Classical.choice` and `Quot.sound`
(some on a subset), and none on `sorryAx`. The sources contain no `sorry`, no `axiom`
declarations and no `native_decide`. The development has 60 files and about 20 300 lines.

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
  * Symmetric key, dual certificate, adaptive guesses and the simple Main Theorem:
    `Practical`.
* `SparseSharpe/Audit.lean`: `#print axioms` for all main statements.

## Conventions and scope

* Real arithmetic is exact, and assets and factors are indexed by arbitrary finite types.
  No matrix is inverted: `Σ_f⁻¹` enters through a matrix `P` with `P Σ_f = I`, and through a
  matrix `G` with `Gᵀ G = P`, which is part of the data.
* Not formalized: running times (the sizes of all enumerated sets are formalized, a model of
  computation is not), floating-point arithmetic, the search procedures (minimization of the
  dual bound, greedy selection, branching), and the NP-completeness of SUBSET SUM, which the
  hardness argument cites.
* Many comments and docstrings are in Russian. The formal statements are
  language-independent.

## Version

The links in the paper point to a fixed commit of this repository. Later commits may shift
line numbers, so a link opens the version that the paper describes.
