import SparseSharpe.Greedy

set_option linter.style.header false

namespace SparseSharpe

open Finset

variable {ι : Type*} [Fintype ι]

namespace QuadData

theorem exists_isGreatest_ell (Q : QuadData ι) (T : Finset ι) {c : ℝ} (hc : 0 < c)
    (hpd : ∀ w : ι → ℝ, c * (∑ i, w i ^ 2) ≤ ∑ i, ∑ j, Q.V i j * w i * w j) :
    ∃ w ∈ Feas T, IsGreatest (Q.ell '' Feas T) (Q.ell w) := by
  classical
  let M : ℝ := ∑ i, Q.m i ^ 2
  let R : ℝ := Real.sqrt (4 * M / c ^ 2 + 1)
  let K : Set (ι → ℝ) := Feas T ∩ {w | ∑ i, w i ^ 2 ≤ R ^ 2}
  have hM : 0 ≤ M := by
    dsimp [M]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = 4 * M / c ^ 2 + 1 := by
    dsimp [R]
    rw [Real.sq_sqrt]
    positivity
  have hzero_feas : (0 : ι → ℝ) ∈ Feas T := by simp [Feas]
  have hzeroK : (0 : ι → ℝ) ∈ K := by
    constructor
    · exact hzero_feas
    · simp [hR]
  have hell_zero : Q.ell (0 : ι → ℝ) = 0 := by simp [ell]
  have hcont : Continuous Q.ell := by
    unfold ell
    fun_prop
  have hfeas_closed : IsClosed (Feas T) := by
    rw [Feas]
    change IsClosed ({w : ι → ℝ | ∀ i, 0 ≤ w i} ∩ {w | ∀ i, i ∉ T → w i = 0})
    rw [show {w : ι → ℝ | ∀ i, 0 ≤ w i} = ⋂ i, {w | 0 ≤ w i} by ext w; simp]
    rw [show {w : ι → ℝ | ∀ i, i ∉ T → w i = 0} =
      ⋂ i, ⋂ (_ : i ∉ T), {w | w i = 0} by ext w; simp]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_iInter fun i => isClosed_iInter fun hi => isClosed_eq (continuous_apply i) continuous_const)
  have hball_closed : IsClosed {w : ι → ℝ | ∑ i, w i ^ 2 ≤ R ^ 2} := by
    exact isClosed_le (by fun_prop) continuous_const
  have hKclosed : IsClosed K := hfeas_closed.inter hball_closed
  have hKbounded : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : ι → ℝ)]
    refine ⟨R, fun w hw => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [Pi.norm_def]
    change (↑(Finset.univ.sup fun b => ‖w b‖₊) : ℝ) ≤ (↑(⟨R, hR⟩ : NNReal) : ℝ)
    apply NNReal.coe_le_coe.mpr
    apply Finset.sup_le
    intro i hi
    have hterm : w i ^ 2 ≤ ∑ j, w j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (mem_univ i)
    have hsq : w i ^ 2 ≤ R ^ 2 := hterm.trans hw.2
    have habssq : |w i| ^ 2 ≤ R ^ 2 := by simpa [sq_abs] using hsq
    have habs : |w i| ≤ R := by nlinarith [abs_nonneg (w i)]
    apply NNReal.coe_le_coe.mp
    change |w i| ≤ R
    exact habs
  have hKcompact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKclosed hKbounded
  obtain ⟨w, hwK, hmax⟩ := hKcompact.exists_isMaxOn ⟨0, hzeroK⟩ hcont.continuousOn
  refine ⟨w, hwK.1, ?_⟩
  constructor
  · exact ⟨w, hwK.1, rfl⟩
  · rintro y ⟨v, hv, rfl⟩
    by_cases hvK : v ∈ K
    · exact hmax hvK
    · have hx : R ^ 2 < ∑ i, v i ^ 2 := by
        have : ¬ ∑ i, v i ^ 2 ≤ R ^ 2 := by
          intro h
          exact hvK ⟨hv, h⟩
        exact lt_of_not_ge this
      have hdiv : 4 * M / c ^ 2 < ∑ i, v i ^ 2 := by
        rw [hR2] at hx
        linarith
      have hxc : 4 * M < (∑ i, v i ^ 2) * c ^ 2 := (div_lt_iff₀ hc2).mp hdiv
      have hdecay : 2 * M - (c ^ 2 / 2) * (∑ i, v i ^ 2) < 0 := by
        nlinarith
      have hlin : c * (2 * ∑ i, Q.m i * v i) ≤
          2 * M + (c ^ 2 / 2) * (∑ i, v i ^ 2) := by
        calc
          c * (2 * ∑ i, Q.m i * v i) = ∑ i, c * (2 * Q.m i * v i) := by
            rw [← Finset.mul_sum]
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ ≤ ∑ i, (2 * Q.m i ^ 2 + (c ^ 2 / 2) * v i ^ 2) := by
            apply Finset.sum_le_sum
            intro i _
            nlinarith [sq_nonneg (Q.m i - (c / 2) * v i)]
          _ = 2 * M + (c ^ 2 / 2) * (∑ i, v i ^ 2) := by
            dsimp [M]
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      have hquad := hpd v
      have hcv : c * Q.ell v < 0 := by
        rw [ell]
        nlinarith
      have hvneg : Q.ell v < 0 := by
        rcases (mul_neg_iff.mp hcv) with h | h
        · exact h.2
        · linarith
      have hw_nonneg : 0 ≤ Q.ell w := by
        rw [← hell_zero]
        exact hmax hzeroK
      linarith

end QuadData
end SparseSharpe
