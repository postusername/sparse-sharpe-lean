import SparseSharpe.Basic
import SparseSharpe.Inertia
import SparseSharpe.Certificate
import SparseSharpe.Counterexample
import SparseSharpe.FPTAS
import SparseSharpe.LongOnly
import SparseSharpe.Grid
import SparseSharpe.LOFilter
import SparseSharpe.Greedy
import SparseSharpe.Existence
import SparseSharpe.GreedyRecursion
import SparseSharpe.TheoremA
import SparseSharpe.Bridge
import SparseSharpe.Factor.KBridge
import SparseSharpe.Factor.Attain
import SparseSharpe.Factor.Duality
import SparseSharpe.Factor.Guarantee
import SparseSharpe.Factor.Cost
import SparseSharpe.Factor.BlockLeverage
import SparseSharpe.Factor.Cover
import SparseSharpe.Factor.GuaranteeBlock
import SparseSharpe.Factor.Gordan
import SparseSharpe.Factor.Reachable
import SparseSharpe.Factor.Nonempty
import SparseSharpe.Factor.Landscape
import SparseSharpe.Factor.AnchorBasis
import SparseSharpe.Factor.DPBox
import SparseSharpe.Factor.Main
import SparseSharpe.Factor.Trading
import SparseSharpe.Factor.TradingAnchor
import SparseSharpe.Factor.Practical
import SparseSharpe.Factor.Padding
import SparseSharpe.Factor.Accumulate
import SparseSharpe.LOFptas
import SparseSharpe.DPInvariant
import SparseSharpe.Factor.LongOnlyK
import SparseSharpe.Factor.ClippedGrid
import SparseSharpe.Factor.ActiveFilter
import SparseSharpe.Factor.Leverage
import SparseSharpe.Factor.Ex125
import SparseSharpe.Factor.Ex135
import SparseSharpe.Factor.Sticky
import SparseSharpe.Factor.Rotation
import SparseSharpe.Factor.EnrichedKey
import SparseSharpe.Factor.StateCount
import SparseSharpe.Factor.Reduction
import SparseSharpe.Factor.Stability
import SparseSharpe.Factor.Rounding
import SparseSharpe.Factor.GridFilter
import SparseSharpe.Factor.KeyRounding
import SparseSharpe.Factor.DPRun
import SparseSharpe.Factor.NormalExists

set_option linter.style.header false

/-! # Аудит: от каких аксиом зависят главные утверждения.
Ожидаемый ответ для всех — только `propext`, `Classical.choice`, `Quot.sound`
(стандартные аксиомы Mathlib). Появление `sorryAx` означало бы дыру в доказательстве. -/

open SparseSharpe SparseSharpe.OneFactor

#print axioms SparseSharpe.OneFactor.lemma1
#print axioms SparseSharpe.OneFactor.Fval_eq_phi_sub
#print axioms SparseSharpe.OneFactor.Mt_prefix_bound
#print axioms SparseSharpe.OneFactor.Mt_range_over_precision
#print axioms SparseSharpe.OneFactor.fptas_step
#print axioms SparseSharpe.OneFactor.fptas_step_explicit
#print axioms SparseSharpe.OneFactor.gap_le
#print axioms SparseSharpe.OneFactor.tight_iff
#print axioms SparseSharpe.OneFactor.tight_iff_slope
#print axioms SparseSharpe.OneFactor.that_eq_of_unique
#print axioms SparseSharpe.OneFactor.tight_of_unique
#print axioms SparseSharpe.OneFactor.certificate_not_tight
#print axioms SparseSharpe.OneFactor.gap_bound_is_attained
#print axioms SparseSharpe.OneFactor.obj_le_phiLO
#print axioms SparseSharpe.geometric_grid_cover
#print axioms SparseSharpe.QuadData.kkt_eq
#print axioms SparseSharpe.QuadData.joint_gain
#print axioms SparseSharpe.QuadData.exists_isGreatest_ell
#print axioms SparseSharpe.QuadData.individual_gain
#print axioms SparseSharpe.OneFactor.filter_loss_bound
#print axioms SparseSharpe.OneFactor.centroid_shift
#print axioms SparseSharpe.OneFactor.centroid_mono
#print axioms SparseSharpe.OneFactor.Fval_sub_le
#print axioms SparseSharpe.QuadData.ell_add
#print axioms SparseSharpe.QuadData.kkt_nonpos
#print axioms SparseSharpe.greedy_guarantee
#print axioms SparseSharpe.gap_geometric
#print axioms SparseSharpe.greedy_theorem
#print axioms SparseSharpe.QuadData.submodularity_ratio_ge
#print axioms SparseSharpe.OneFactor.fptas_constants_consistent
#print axioms SparseSharpe.OneFactor.fptas_at_grid_point
#print axioms SparseSharpe.geometric_grid_cover_above
#print axioms SparseSharpe.one_add_half_inv_pow_le_two
#print axioms SparseSharpe.accumulate_add
#print axioms SparseSharpe.QuadData.submodularity_ratio_ge_of_pd
#print axioms SparseSharpe.OneFactor.toQuad_ell
#print axioms SparseSharpe.accumulate_mul
#print axioms SparseSharpe.OneFactor.lagrange_identity
#print axioms SparseSharpe.OneFactor.Fval_pairwise

/-! ## K факторов (v0.14): ядро FPTAS при фиксированном числе факторов -/

#print axioms SparseSharpe.Factor.phi_eq_add
#print axioms SparseSharpe.Factor.isNormal_of_min
#print axioms SparseSharpe.Factor.row_eq_sum_cf
#print axioms SparseSharpe.Factor.abs_cf_le_one
#print axioms SparseSharpe.Factor.gram_le_card_mul_gramK
#print axioms SparseSharpe.Factor.gramK_le_gram
#print axioms SparseSharpe.Factor.theoremH
#print axioms SparseSharpe.Factor.exists_grid_point
#print axioms SparseSharpe.Factor.exists_point_with_residuals
#print axioms SparseSharpe.Factor.grid_ratio
#print axioms SparseSharpe.Factor.exists_grid_node
#print axioms SparseSharpe.Factor.step_algebra
#print axioms SparseSharpe.Factor.fptasK_step_general
#print axioms SparseSharpe.Factor.fptasK_step
#print axioms SparseSharpe.Factor.mom_close
#print axioms SparseSharpe.Factor.gram_half_of_entrywise
#print axioms SparseSharpe.Factor.abs_gramK2_le
#print axioms SparseSharpe.Factor.abs_momK_le
#print axioms SparseSharpe.Factor.abs_momK_le_of_subset
#print axioms SparseSharpe.Factor.momK_range_over_precision
#print axioms SparseSharpe.Factor.fptasK_at_grid_node
#print axioms SparseSharpe.Factor.phiK_eq
#print axioms SparseSharpe.Factor.Vmat_mulVec
#print axioms SparseSharpe.Factor.isNormal_tw
#print axioms SparseSharpe.Factor.phi_tw
#print axioms SparseSharpe.Factor.exists_maxvol
#print axioms SparseSharpe.Factor.det_anchor_ne_zero
#print axioms SparseSharpe.Factor.maxvol_det_ne_zero
#print axioms SparseSharpe.Factor.exists_maxvol_barK
#print axioms SparseSharpe.Factor.factor_lemma1
#print axioms SparseSharpe.Factor.factor_fptas_at_node
#print axioms SparseSharpe.Factor.accumulate_norm
#print axioms SparseSharpe.Factor.round_step_euclid
#print axioms SparseSharpe.Factor.fptasK_constants_M
#print axioms SparseSharpe.Factor.fptasK_constants_K
#print axioms SparseSharpe.Factor.fptasK_delta_sq
#print axioms SparseSharpe.Factor.fptasK_grid_step

/-! ## Long-only (v0.14): узел сверху от центроида и динамика «минимум M» -/

#print axioms SparseSharpe.OneFactor.phi_le_of_dev_sq
#print axioms SparseSharpe.OneFactor.Mt_neg_of_gt_that
#print axioms SparseSharpe.OneFactor.abs_Mt_le
#print axioms SparseSharpe.OneFactor.selfconsistent_of_Mt_neg
#print axioms SparseSharpe.OneFactor.lo_value_of_selfconsistent
#print axioms SparseSharpe.OneFactor.lo_step

/-! ## Инвариант динамики (v0.14): последнее место, что проверялось только численно -/

#print axioms SparseSharpe.minM_invariant
#print axioms SparseSharpe.maxQ_invariant
#print axioms SparseSharpe.Factor.factor_fptas_value
#print axioms SparseSharpe.OneFactor.lo_node_exists_grid

/-! ## Long-only при `K` факторах (`Factor/Clipped.lean`, `Factor/LongOnlyK.lean`) -/

#print axioms SparseSharpe.Factor.sq_posPart_shift_ge
#print axioms SparseSharpe.Factor.psiC_shift_ge
#print axioms SparseSharpe.Factor.psiC_le_phi
#print axioms SparseSharpe.Factor.psiC_eq_phi_of_nonneg
#print axioms SparseSharpe.Factor.psiC_min_of_normal_of_nonneg
#print axioms SparseSharpe.Factor.isLeast_psiC_of_selfconsistent
#print axioms SparseSharpe.Factor.selfconsistent_of_phi_gap
#print axioms SparseSharpe.Factor.isLeast_psiC_of_certificate
#print axioms SparseSharpe.Factor.quad_Vmat
#print axioms SparseSharpe.Factor.young_Sf
#print axioms SparseSharpe.Factor.objLO_le_QLO
#print axioms SparseSharpe.Factor.objLO_wclip
#print axioms SparseSharpe.Factor.wclip_eq_of_kkt
#print axioms SparseSharpe.Factor.objLO_eq_QLO_of_kkt
#print axioms SparseSharpe.Factor.QLO_eq_psiC
#print axioms SparseSharpe.Factor.isGreatest_objLO
#print axioms SparseSharpe.Factor.sq_dotp_le_card_mul_gramK
#print axioms SparseSharpe.Factor.phi_sub_psiC_le
#print axioms SparseSharpe.Factor.phi_sub_psiC_le_at_node
#print axioms SparseSharpe.Factor.phi_sub_psiC_le_of_grid
#print axioms SparseSharpe.Factor.step_algebra_gamma
#print axioms SparseSharpe.Factor.fptasK_step_gamma
#print axioms SparseSharpe.Factor.sq_dotp_le_card_mul_gram_of_subset
#print axioms SparseSharpe.Factor.gram_le_card_mul_gram_of_subset
#print axioms SparseSharpe.Factor.fptasK_step_maxvol
#print axioms SparseSharpe.Factor.psiC_min_le_phi_min
#print axioms SparseSharpe.Factor.sq_dotp_le_gram
#print axioms SparseSharpe.Factor.phi_le_of_bucket
#print axioms SparseSharpe.Factor.phi_normal_le_of_bucket
#print axioms SparseSharpe.Factor.psiC_min_le_of_bucket_of_certificate
#print axioms SparseSharpe.Factor.gramK_le_of_coords
#print axioms SparseSharpe.Factor.gram_le_of_nearest_node
#print axioms SparseSharpe.Factor.res_ge_of_gram_le
#print axioms SparseSharpe.Factor.Bw_sub_smul
#print axioms SparseSharpe.Factor.objLO_null_shift
#print axioms SparseSharpe.Factor.null_shift_loss_le
#print axioms SparseSharpe.Factor.objLO_erase_of_zero
#print axioms SparseSharpe.Factor.phi_eq_add_const
#print axioms SparseSharpe.Factor.gap_eq_of_bucket
#print axioms SparseSharpe.Factor.psiC_min_le_of_bucket_gap
#print axioms SparseSharpe.Factor.phi_erase_add
#print axioms SparseSharpe.Factor.gram_erase_add
#print axioms SparseSharpe.Factor.gram_erase_shift
#print axioms SparseSharpe.Factor.phi_erase_cost
#print axioms SparseSharpe.Factor.sq_res_le_phi_erase_cost
#print axioms SparseSharpe.Factor.quadf_sub_smul
#print axioms SparseSharpe.Factor.bilf_comm
#print axioms SparseSharpe.Factor.objLO_shift
#print axioms SparseSharpe.Factor.objLO_erase_cost
#print axioms SparseSharpe.Factor.Ex125.value
#print axioms SparseSharpe.Factor.Ex125.isLeast_value
#print axioms SparseSharpe.Factor.Ex125.res_eq
#print axioms SparseSharpe.Factor.Ex125.selfcons
#print axioms SparseSharpe.Factor.Ex125.isLeast_LO
#print axioms SparseSharpe.Factor.Ex125.no_good_subset_of
#print axioms SparseSharpe.Factor.Ex125.no_good_subset
#print axioms SparseSharpe.Factor.card_violators_mul_sq_le
#print axioms SparseSharpe.Factor.card_violators_le_gap
#print axioms SparseSharpe.Factor.Ex135.gram_eq
#print axioms SparseSharpe.Factor.Ex135.mom_eq
#print axioms SparseSharpe.Factor.Ex135.Q_lt
#print axioms SparseSharpe.Factor.Ex135.normal_A
#print axioms SparseSharpe.Factor.Ex135.normal_R
#print axioms SparseSharpe.Factor.Ex135.selfcons_A
#print axioms SparseSharpe.Factor.Ex135.not_selfcons_R
#print axioms SparseSharpe.Factor.Ex135.admitted
#print axioms SparseSharpe.Factor.Ex135.gap_gt
#print axioms SparseSharpe.Factor.Ex135.isLeast_LO_A
#print axioms SparseSharpe.Factor.Ex135.isLeast_LO_R
#print axioms SparseSharpe.Factor.Ex135.loss_ge
#print axioms SparseSharpe.Factor.Ex135.eviction_far_node
#print axioms SparseSharpe.Factor.keyOf_mem_keyBox
#print axioms SparseSharpe.Factor.card_keyBox
#print axioms SparseSharpe.Factor.card_states_le
#print axioms SparseSharpe.Factor.card_states_le_of_ratio
#print axioms SparseSharpe.Factor.hatMat_idem
#print axioms SparseSharpe.Factor.lev_nonneg
#print axioms SparseSharpe.Factor.lev_le_one
#print axioms SparseSharpe.Factor.sum_lev_eq_card
#print axioms SparseSharpe.Factor.card_sticky_le
#print axioms SparseSharpe.Factor.sq_dotp_le_lev_mul_gram
#print axioms SparseSharpe.Factor.phi_erase_cost_le_of_lev
#print axioms SparseSharpe.Factor.mom_eq_of_bucket
#print axioms SparseSharpe.Factor.isNormal_of_bucket
#print axioms SparseSharpe.Factor.phi_normal_sub_eq
#print axioms SparseSharpe.Factor.psiC_min_le_of_active_bucket
#print axioms SparseSharpe.Factor.Sticky.gram_eq
#print axioms SparseSharpe.Factor.Sticky.mom_eq
#print axioms SparseSharpe.Factor.Sticky.Q_eq
#print axioms SparseSharpe.Factor.Sticky.normal_A
#print axioms SparseSharpe.Factor.Sticky.normal_R
#print axioms SparseSharpe.Factor.Sticky.selfcons_A
#print axioms SparseSharpe.Factor.Sticky.not_selfcons_R
#print axioms SparseSharpe.Factor.Sticky.admitted_sign
#print axioms SparseSharpe.Factor.Sticky.isLeast_LO_A
#print axioms SparseSharpe.Factor.Sticky.isLeast_LO_R
#print axioms SparseSharpe.Factor.Sticky.gap_eq
#print axioms SparseSharpe.Factor.Sticky.sticky_row_essential
#print axioms SparseSharpe.Factor.sum_rot_mul
#print axioms SparseSharpe.Factor.gram_rot
#print axioms SparseSharpe.Factor.mom_rot
#print axioms SparseSharpe.Factor.phi_rot
#print axioms SparseSharpe.Factor.isNormal_rot
#print axioms SparseSharpe.Factor.rot_preserves_state
#print axioms SparseSharpe.Factor.sumCf_insert
#print axioms SparseSharpe.Factor.sumRes_insert
#print axioms SparseSharpe.Factor.abs_sumCf_le
#print axioms SparseSharpe.Factor.abs_sumRes_le
#print axioms SparseSharpe.Factor.abs_sumRes_le_of_subset

/-! ### Теорема X: редукция long-only к самосогласованным подмножествам -/

#print axioms SparseSharpe.Factor.eq_zero_of_quad_nonneg
#print axioms SparseSharpe.Factor.psiC_eq_phi_activeSet
#print axioms SparseSharpe.Factor.phi_le_psiC_of_selfconsistent
#print axioms SparseSharpe.Factor.psiC_shift_le_active
#print axioms SparseSharpe.Factor.isNormal_activeSet_of_min
#print axioms SparseSharpe.Factor.exists_selfconsistent_subset
#print axioms SparseSharpe.Factor.isGreatest_phi_selfconsistent
#print axioms SparseSharpe.Factor.lo_values_eq_sc_values

/-! ### Теорема W: устойчивость при почти-самосогласованности -/

#print axioms SparseSharpe.Factor.sum_abs_le_sqrt_card_mul
#print axioms SparseSharpe.Factor.gram_sub_le
#print axioms SparseSharpe.Factor.phi_sub_psiC_le_of_slack
#print axioms SparseSharpe.Factor.psiC_ge_of_slack
#print axioms SparseSharpe.Factor.gram_anchor_le_psiC
#print axioms SparseSharpe.Factor.gram_sub_le_of_anchor
#print axioms SparseSharpe.Factor.psiC_ge_of_slack_anchor
#print axioms SparseSharpe.Factor.psiC_ge_one_sub_eps
#print axioms SparseSharpe.Factor.slack_of_node_sign
#print axioms SparseSharpe.Factor.psiC_ge_of_node_sign
#print axioms SparseSharpe.Factor.psiC_ge_of_bucket_node_sign

/-! ### Округлённый ключ: приближённые соседи по корзине -/

#print axioms SparseSharpe.Factor.sqrt_add_le_of_nonneg
#print axioms SparseSharpe.Factor.young_sqrt
#print axioms SparseSharpe.Factor.phi_ge_of_approxBucket
#print axioms SparseSharpe.Factor.phi_normal_ge_of_approxBucket
#print axioms SparseSharpe.Factor.phi_normal_ge_of_approxBucket'
#print axioms SparseSharpe.Factor.gap_le_of_approxBucket
#print axioms SparseSharpe.Factor.psiC_ge_of_approxBucket
#print axioms SparseSharpe.Factor.bucketErr_zero
#print axioms SparseSharpe.Factor.approxBucket_of_exact
#print axioms SparseSharpe.Factor.node_filter_admits
#print axioms SparseSharpe.Factor.slack_of_node_slack
#print axioms SparseSharpe.Factor.psiC_ge_of_bucket_node_slack
#print axioms SparseSharpe.Factor.bucketErr_le_of_small
#print axioms SparseSharpe.Factor.psiC_ge_of_approxBucket_calibrated

/-! ### Связка «сетка → фильтр» -/

#print axioms SparseSharpe.Factor.theta0_sq
#print axioms SparseSharpe.Factor.cal_of_theta0
#print axioms SparseSharpe.Factor.exists_node_closing_step
#print axioms SparseSharpe.Factor.psiC_ge_at_grid_node

/-! ### Связка «округлённый ключ → ApproxBucket» -/

#print axioms SparseSharpe.Factor.abs_sub_le_of_floor_eq
#print axioms SparseSharpe.Factor.gram_rel_close
#print axioms SparseSharpe.Factor.approxBucket_of_key
#print axioms SparseSharpe.Factor.approxBucket_of_keyOf_eq
#print axioms SparseSharpe.Factor.psiC_ge_of_rounded_key_at_node

/-! ### Динамика как функция и сквозной FPTAS -/

#print axioms SparseSharpe.Factor.bucketErr_le_half
#print axioms SparseSharpe.Factor.exists_node_closing_step_half
#print axioms SparseSharpe.Factor.KeyClose.trans
#print axioms SparseSharpe.Factor.KeyClose.insert'
#print axioms SparseSharpe.Factor.KeyClose.of_key_eq
#print axioms SparseSharpe.Factor.KeyClose.toApproxBucket
#print axioms SparseSharpe.Factor.repOf_spec
#print axioms SparseSharpe.Factor.prune_subset
#print axioms SparseSharpe.Factor.card_prune_le
#print axioms SparseSharpe.Factor.survivors_mem
#print axioms SparseSharpe.Factor.survivors_spec
#print axioms SparseSharpe.Factor.key_injOn_survivors
#print axioms SparseSharpe.Factor.survivors_card_le
#print axioms SparseSharpe.Factor.gram_cond_of_subset
#print axioms SparseSharpe.Factor.lo_fptas_step
#print axioms SparseSharpe.Factor.lo_fptas

/-! ### Существование неподвижной точки (гипотеза `hex` снята) -/

#print axioms SparseSharpe.Factor.KMat_mulVec
#print axioms SparseSharpe.Factor.dotProduct_KMat_mulVec
#print axioms SparseSharpe.Factor.mom_eq_dotProduct
#print axioms SparseSharpe.Factor.KMat_posDef
#print axioms SparseSharpe.Factor.exists_isNormal
#print axioms SparseSharpe.Factor.gram_pos_of_det
#print axioms SparseSharpe.Factor.exists_isNormal_of_det


/-! ### Достижимость минимума и сильная двойственность (`Factor/Attain.lean`, `Factor/Duality.lean`) -/

#print axioms SparseSharpe.Factor.exists_gram_lower_bound
#print axioms SparseSharpe.Factor.gram_base_le_psiC
#print axioms SparseSharpe.Factor.exists_min_psiC
#print axioms SparseSharpe.Factor.exists_isLeast_psiC
#print axioms SparseSharpe.Factor.exists_selfconsistent_subset_of_det
#print axioms SparseSharpe.Factor.momC_eq_mom_activeSet
#print axioms SparseSharpe.Factor.momC_barK_eq
#print axioms SparseSharpe.Factor.SP_of_PS
#print axioms SparseSharpe.Factor.Bw_eq_of_min
#print axioms SparseSharpe.Factor.tw_wclip_eq
#print axioms SparseSharpe.Factor.isKKT_wclip_of_min
#print axioms SparseSharpe.Factor.exists_min_QLO
#print axioms SparseSharpe.Factor.isGreatest_objLO_isLeast_QLO
#print axioms SparseSharpe.Factor.isGreatest_objLO_psiC

/-! ### Сквозная гарантия в языке задачи (`Factor/Guarantee.lean`) -/

#print axioms SparseSharpe.Factor.barK_assetsOf
#print axioms SparseSharpe.Factor.card_barK
#print axioms SparseSharpe.Factor.card_assetsOf_eq
#print axioms SparseSharpe.Factor.isGreatest_objLO_phi_of_selfconsistent
#print axioms SparseSharpe.Factor.exists_optimal_selfconsistent
#print axioms SparseSharpe.Factor.lo_fptas_portfolio
#print axioms SparseSharpe.Factor.lo_fptas_portfolio_opt

/-! ### Стоимость: число узлов и число состояний (`Factor/Cost.lean`) -/

#print axioms SparseSharpe.Factor.card_nodeBox
#print axioms SparseSharpe.Factor.mem_nodeBox_of_abs_le
#print axioms SparseSharpe.Factor.zmax_le
#print axioms SparseSharpe.Factor.mem_nodeBox_of_grid
#print axioms SparseSharpe.Factor.nodeCount_le
#print axioms SparseSharpe.Factor.momRange_over_eta_le
#print axioms SparseSharpe.Factor.keyBox_mono
#print axioms SparseSharpe.Factor.survivors_card_le_of_ratio
#print axioms SparseSharpe.Factor.lo_fptas_cost

/-! ### Блочное плечо: Теорема W″ (`Factor/BlockLeverage.lean`) -/

#print axioms SparseSharpe.Factor.gram_split
#print axioms SparseSharpe.Factor.gram_clip_iff
#print axioms SparseSharpe.Factor.sq_sub_resC_le_block
#print axioms SparseSharpe.Factor.phi_sub_psiC_le_block
#print axioms SparseSharpe.Factor.two_sqrt_mul_le
#print axioms SparseSharpe.Factor.psiC_ge_of_slack_block
#print axioms SparseSharpe.Factor.psiC_ge_of_slack_clipSet
#print axioms SparseSharpe.Factor.psiC_ge_one_sub_eps_cover
#print axioms SparseSharpe.Factor.coveredBy_of_uniform
#print axioms SparseSharpe.Factor.coveredBy_of_anchor_cond
#print axioms SparseSharpe.Factor.psiC_ge_of_bucket_node_slack_block
#print axioms SparseSharpe.Factor.psiC_ge_of_bucket_node_slack_anchor'
#print axioms SparseSharpe.Factor.psiC_ge_of_approxBucket_block
#print axioms SparseSharpe.Factor.psiC_ge_of_approxBucket_calibrated_block
#print axioms SparseSharpe.Factor.psiC_ge_of_bucket_node_slack_block'

/-! ### Покрытие нарушителей относительно якорей (`Factor/Cover.lean`) -/

#print axioms SparseSharpe.Factor.AnchorCover.mono
#print axioms SparseSharpe.Factor.coveredBy_of_anchorCover
#print axioms SparseSharpe.Factor.card_clipSet_le_of_base
#print axioms SparseSharpe.Factor.anchorCover_of_anchor_cond
#print axioms SparseSharpe.Factor.anchorCover_of_rowLev
#print axioms SparseSharpe.Factor.anchorCover_of_rowLev_uniform
#print axioms SparseSharpe.Factor.anchorCover_of_family
#print axioms SparseSharpe.Factor.cover_const_ge_single
#print axioms SparseSharpe.Factor.exists_viol_of_ne_zero
#print axioms SparseSharpe.Factor.cover_const_ge_row

/-! ### `δ`-цепочка: узел, шаг и сквозная теорема (`Factor/GridFilter.lean`, `Factor/DPRun.lean`) -/

#print axioms SparseSharpe.Factor.theta0B_sq
#print axioms SparseSharpe.Factor.exists_node_closing_step_block
#print axioms SparseSharpe.Factor.lo_fptas_step_block
#print axioms SparseSharpe.Factor.lo_fptas_block

/-! ### `δ`-цепочка в языке задачи (`Factor/GuaranteeBlock.lean`) -/

#print axioms SparseSharpe.Factor.card_anchorRows
#print axioms SparseSharpe.Factor.gram_anchorRows
#print axioms SparseSharpe.Factor.P_symm
#print axioms SparseSharpe.Factor.sum_G_mul_G
#print axioms SparseSharpe.Factor.sum_SfB_mul_P
#print axioms SparseSharpe.Factor.sum_sq_GSfB
#print axioms SparseSharpe.Factor.sysVar_nonneg
#print axioms SparseSharpe.Factor.sq_dotp_asset_le
#print axioms SparseSharpe.Factor.dotp_asset_at_SfB
#print axioms SparseSharpe.Factor.anchorCover_of_sysVar
#print axioms SparseSharpe.Factor.cover_const_ge_asset
#print axioms SparseSharpe.Factor.lo_fptas_portfolio_block
#print axioms SparseSharpe.Factor.lo_fptas_portfolio_opt_block
#print axioms SparseSharpe.Factor.lo_fptas_portfolio_opt_rowLev

/-! ### `δ`-цепочка: стоимость (`Factor/Cost.lean`) -/

#print axioms SparseSharpe.Factor.zmax_le_block
#print axioms SparseSharpe.Factor.mem_nodeBox_of_grid_block
#print axioms SparseSharpe.Factor.nodeCount_le_block
#print axioms SparseSharpe.Factor.momRange_over_eta_le_block
#print axioms SparseSharpe.Factor.lo_fptas_cost_block

/-! ### Теорема Гордана и дихотомия (`Factor/Gordan.lean`) -/

#print axioms SparseSharpe.Factor.strongDual_eq_dotp
#print axioms SparseSharpe.Factor.gordan
#print axioms SparseSharpe.Factor.gordan_not_both
#print axioms SparseSharpe.Factor.dotp_augRow_none
#print axioms SparseSharpe.Factor.dotp_augRow_some
#print axioms SparseSharpe.Factor.motzkin
#print axioms SparseSharpe.Factor.motzkin_not_both
#print axioms SparseSharpe.Factor.violable_iff_no_certificate
#print axioms SparseSharpe.Factor.violable_of_halfspace
#print axioms SparseSharpe.Factor.violable_iff_halfspace_of_nonneg
#print axioms SparseSharpe.Factor.anchorCover_iff_violable
#print axioms SparseSharpe.Factor.anchorCover_iff_no_certificate
#print axioms SparseSharpe.Factor.anchorCover_iff_halfspace_of_nonneg
#print axioms SparseSharpe.Factor.anchorCover_iff_all_of_halfspace

/-! ### Достижимые множества нарушителей: `O(M^K)` (`Factor/Reachable.lean`) -/

#print axioms SparseSharpe.Factor.mem_violAt
#print axioms SparseSharpe.Factor.mem_reachSets
#print axioms SparseSharpe.Factor.violAt_mem_reachSets
#print axioms SparseSharpe.Factor.sum_res_eq_of_rel
#print axioms SparseSharpe.Factor.not_shatters_of_rel
#print axioms SparseSharpe.Factor.not_shatters_reachSets
#print axioms SparseSharpe.Factor.vcDim_reachSets_le
#print axioms SparseSharpe.Factor.card_reachSets_le
#print axioms SparseSharpe.Factor.sum_choose_le_pow
#print axioms SparseSharpe.Factor.card_reachSets_le_pow
#print axioms SparseSharpe.Factor.rowsK_inl
#print axioms SparseSharpe.Factor.targetsK_inl
#print axioms SparseSharpe.Factor.subset_map_violAt
#print axioms SparseSharpe.Factor.anchorCover_of_reachSets
#print axioms SparseSharpe.Factor.anchorCover_of_reachSets_sysVar

/-! ### Исправления по независимой проверке (сессия 7) -/

#print axioms SparseSharpe.Factor.reflO_orth
#print axioms SparseSharpe.Factor.rot_changes_psiC
#print axioms SparseSharpe.Factor.sumRes_rot
#print axioms SparseSharpe.Factor.sumRes_rot_invariant_iff
#print axioms SparseSharpe.Factor.colsum_iff_rowsum
#print axioms SparseSharpe.Factor.lo_fptas_block_instance
#print axioms SparseSharpe.Factor.lo_fptas_instance

/-! ### Ландшафт трудности: Предложения 3 и 4 (сессия 8, `Factor/Landscape.lean`) -/

#print axioms SparseSharpe.Factor.subsetSum_obj_eq
#print axioms SparseSharpe.Factor.subsetSum_obj_le_card
#print axioms SparseSharpe.Factor.subsetSum_obj_le
#print axioms SparseSharpe.Factor.subsetSum_obj_yes
#print axioms SparseSharpe.Factor.gap_scalar
#print axioms SparseSharpe.Factor.subsetSum_gap
#print axioms SparseSharpe.Factor.subsetSum_obj_le_no
#print axioms SparseSharpe.Factor.subsetSum_reduction
#print axioms SparseSharpe.Factor.subsetSum_instance_pos
#print axioms SparseSharpe.Factor.term_dominates
#print axioms SparseSharpe.Factor.sum_le_sum_of_dominates
#print axioms SparseSharpe.Factor.min_QLO_nonneg
#print axioms SparseSharpe.Factor.egp_prefix_optimal
#print axioms SparseSharpe.Factor.egp_prefix_fails_without_q
#print axioms SparseSharpe.Factor.stateVal_nonneg
#print axioms SparseSharpe.Factor.stateVal_not_close

/-! ### Без перебора `K`-ок и границы зажима: C.4–C.5 (сессия 8, `Factor/AnchorBasis.lean`) -/

#print axioms SparseSharpe.Factor.gram_le_of_pointwise
#print axioms SparseSharpe.Factor.abs_cf_le_of_pointwise
#print axioms SparseSharpe.Factor.pointwise_of_maxvol
#print axioms SparseSharpe.Factor.clamp_of_maxvol
#print axioms SparseSharpe.Factor.theoremH_clamp
#print axioms SparseSharpe.Factor.exists_grid_node_clamp
#print axioms SparseSharpe.Factor.exists_node_closing_step_clamp
#print axioms SparseSharpe.Factor.abs_gramK2_le_rho
#print axioms SparseSharpe.Factor.abs_momK_le_rho
#print axioms SparseSharpe.Factor.keyOf_mem_keyBox_rho
#print axioms SparseSharpe.Factor.survivors_card_le_rho
#print axioms SparseSharpe.Factor.lo_fptas_cost_rho
#print axioms SparseSharpe.Factor.gram_le_improved
#print axioms SparseSharpe.Factor.clamp_lower_blocks
#print axioms SparseSharpe.Factor.clamp_const_ge_blocks
#print axioms SparseSharpe.Factor.lo_fptas_block_clamp
#print axioms SparseSharpe.Factor.lo_fptas_portfolio_anchor
#print axioms SparseSharpe.Factor.abs_cf_anchor_le

/-! ### Динамика с коробкой и главная теорема из входа (сессия 8, `Factor/DPBox.lean`, `Factor/Main.lean`) -/

#print axioms SparseSharpe.Factor.KeyClose.mono
#print axioms SparseSharpe.Factor.survivorsBox_mem
#print axioms SparseSharpe.Factor.survivorsBox_key_mem
#print axioms SparseSharpe.Factor.key_injOn_survivorsBox
#print axioms SparseSharpe.Factor.survivorsBox_card_le
#print axioms SparseSharpe.Factor.survivorsBox_spec
#print axioms SparseSharpe.Factor.keyOf_mem_boxOf
#print axioms SparseSharpe.Factor.card_boxOf
#print axioms SparseSharpe.Factor.lo_fptas_step_box
#print axioms SparseSharpe.Factor.lo_fptas_block_box
#print axioms SparseSharpe.Factor.toNat_two_ceil_mono
#print axioms SparseSharpe.Factor.card_boxOf_le
#print axioms SparseSharpe.Factor.lo_fptas_portfolio_box
#print axioms SparseSharpe.Factor.clamp_anchor
#print axioms SparseSharpe.Factor.main_theorem
#print axioms SparseSharpe.Factor.main_theorem_anchor

/-! ### Trading form: Sharpe ratio, guesses, the scheme as a finite search (session 9, `Factor/Trading.lean`) -/

#print axioms SparseSharpe.Factor.quadf_Sf_Bw_nonneg
#print axioms SparseSharpe.Factor.pVar_ge_diag
#print axioms SparseSharpe.Factor.pVar_nonneg
#print axioms SparseSharpe.Factor.pVar_pos
#print axioms SparseSharpe.Factor.exists_ne_zero_of_pRet_pos
#print axioms SparseSharpe.Factor.objLO_le_ret_sq_div
#print axioms SparseSharpe.Factor.pRet_smul
#print axioms SparseSharpe.Factor.pVar_smul
#print axioms SparseSharpe.Factor.objLO_smul
#print axioms SparseSharpe.Factor.objLO_opt_scale
#print axioms SparseSharpe.Factor.sharpe_smul
#print axioms SparseSharpe.Factor.sharpe_sq
#print axioms SparseSharpe.Factor.sharpe_ge_of_obj_ge
#print axioms SparseSharpe.Factor.normalize_budget
#print axioms SparseSharpe.Factor.Vmat_diag
#print axioms SparseSharpe.Factor.Vmat_diag_pos
#print axioms SparseSharpe.Factor.pRet_single
#print axioms SparseSharpe.Factor.pVar_single
#print axioms SparseSharpe.Factor.objLO_single_value
#print axioms SparseSharpe.Factor.opt_ge_single_of_opt
#print axioms SparseSharpe.Factor.objLO_le_sum_posPart
#print axioms SparseSharpe.Factor.posPart_div_d_le
#print axioms SparseSharpe.Factor.sum_posPart_le
#print axioms SparseSharpe.Factor.exists_doubling_guess
#print axioms SparseSharpe.Factor.exists_guess_of_opt
#print axioms SparseSharpe.Factor.nodePoint_spec
#print axioms SparseSharpe.Factor.card_schemeTable_le
#print axioms SparseSharpe.Factor.card_candidates_le
#print axioms SparseSharpe.Factor.card_assetsOf_le_of_mem_candidates
#print axioms SparseSharpe.Factor.exists_good_candidate
#print axioms SparseSharpe.Factor.exists_best_pair
#print axioms SparseSharpe.Factor.best_pair_sharpe
#print axioms SparseSharpe.Factor.inst_obj_le
#print axioms SparseSharpe.Factor.trading_instance
#print axioms SparseSharpe.Factor.subsetSum_padding
#print axioms SparseSharpe.Factor.padded_pos

/-! ### Every processing order; trading form of the anchor variant; trading theorems from the data (`Factor/TradingAnchor.lean`) -/

#print axioms SparseSharpe.Factor.length_of_nodup_complete
#print axioms SparseSharpe.Factor.main_theorem_list
#print axioms SparseSharpe.Factor.main_theorem_anchor_list
#print axioms SparseSharpe.Factor.card_anchorTable_le
#print axioms SparseSharpe.Factor.card_candidatesAnchor_le
#print axioms SparseSharpe.Factor.card_assetsOf_le_of_mem_candidatesAnchor
#print axioms SparseSharpe.Factor.exists_good_candidate_anchor
#print axioms SparseSharpe.Factor.card_schemeTableList_le
#print axioms SparseSharpe.Factor.card_candidatesList_le
#print axioms SparseSharpe.Factor.card_assetsOf_le_of_mem_candidatesList
#print axioms SparseSharpe.Factor.exists_good_candidate_list
#print axioms SparseSharpe.Factor.exists_best_pair_of_family
#print axioms SparseSharpe.Factor.best_pair_sharpe_of_family
#print axioms SparseSharpe.Factor.best_pair_sharpe_anchor
#print axioms SparseSharpe.Factor.exists_optimal_support
#print axioms SparseSharpe.Factor.sharpe_sq_le_opt
#print axioms SparseSharpe.Factor.obj_le_sharpe_sq
#print axioms SparseSharpe.Factor.normalize_budget_explicit
#print axioms SparseSharpe.Factor.best_pair_sharpe_uniform
#print axioms SparseSharpe.Factor.trading_theorem
#print axioms SparseSharpe.Factor.trading_theorem_anchor
#print axioms SparseSharpe.Factor.trading_instance_anchor
#print axioms SparseSharpe.Factor.trading_theorems_instance
#print axioms SparseSharpe.Factor.sqrt_one_sub_two_eps_of_delta
#print axioms SparseSharpe.Factor.vol_target
#print axioms SparseSharpe.Factor.objLO_nonpos_of_nonpos
#print axioms SparseSharpe.Factor.obj_le_div_of_guarantee
#print axioms SparseSharpe.Factor.cover_const_le_sq_mul

/-! ### Symmetric key, dual certificate, adaptive guesses, simple Main Theorem (`Factor/Practical.lean`) -/

#print axioms SparseSharpe.Factor.keyOf_symm
#print axioms SparseSharpe.Factor.survivorsBox_card_le_sym
#print axioms SparseSharpe.Factor.card_symKeys_keyBox_le
#print axioms SparseSharpe.Factor.card_symKeys_boxOf_le
#print axioms SparseSharpe.Factor.choose_succ_two
#print axioms SparseSharpe.Factor.card_anchorTable_le_sym
#print axioms SparseSharpe.Factor.card_candidatesAnchor_le_sym
#print axioms SparseSharpe.Factor.card_schemeTableList_le_sym
#print axioms SparseSharpe.Factor.card_candidatesList_le_sym
#print axioms SparseSharpe.Factor.supportsLe_nonempty
#print axioms SparseSharpe.Factor.objLO_le_dualBound
#print axioms SparseSharpe.Factor.dualBound_eq_of_top
#print axioms SparseSharpe.Factor.dualBound_zero_le
#print axioms SparseSharpe.Factor.certificate_sharpe
#print axioms SparseSharpe.Factor.certificate_sharpe_eps
#print axioms SparseSharpe.Factor.sum_le_sum_top
#print axioms SparseSharpe.Factor.objLO_le_nodeBound
#print axioms SparseSharpe.Factor.optimal_of_top_at_dual
#print axioms SparseSharpe.Factor.exists_doubling_guess_succ
#print axioms SparseSharpe.Factor.exists_good_candidate_anchor_bracket
#print axioms SparseSharpe.Factor.exists_good_candidate_list_bracket
#print axioms SparseSharpe.Factor.opt_mem_bracket
#print axioms SparseSharpe.Factor.trading_theorem_anchor_adaptive
#print axioms SparseSharpe.Factor.trading_theorem_adaptive
#print axioms SparseSharpe.Factor.guess_count_spec
#print axioms SparseSharpe.Factor.cast_toNat_two_ceil_le
#print axioms SparseSharpe.Factor.NK_le_poly
#print axioms SparseSharpe.Factor.card_candidatesAnchor_poly
#print axioms SparseSharpe.Factor.main_theorem_simple
#print axioms SparseSharpe.Factor.practical_instance
