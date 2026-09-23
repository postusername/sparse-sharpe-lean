import SparseSharpe.Certificate

set_option linter.style.header false

/-!
# Контрпример: оптимальности связанного множества недостаточно

Первая редакция Теоремы C утверждала «сертификат точен ⇔ какое-то связанное множество
оптимально», причём «⇐» было объявлено очевидным. Это **ложно**.

Инстанс: `n = 2`, `k = 1`, `m = (1,1)`, `β = (1,−2)`, `d = (1,1)`, `σ² = 1`.
Тогда `φ_{\{0\}}(t) = 2t² − 2t + 1`, `φ_{\{1\}}(t) = 5t² + 4t + 1`, и в точке `t̂ = 0`
оба множества связаны: `φ_{\{0\}}(0) = φ_{\{1\}}(0) = 1 = Φ(0)`, причём `0` минимизирует `Φ`.
При этом `F({0}) = 1/2 = OPT`, то есть `{0}` оптимально и связано, но `Φ(0) = 1 ≠ 1/2`.

Зазор равен ровно `M_0({0})²/κ({0}) = 1/2` — оценка Теоремы C (ii) достигается.
-/

namespace SparseSharpe

open Finset

namespace OneFactor

/-- Контрпример: `m = (1,1)`, `β = (1,−2)`, `d = (1,1)`, `σ² = 1`. -/
noncomputable def Pcex : OneFactor (Fin 2) where
  m := ![1, 1]
  β := ![1, -2]
  d := ![1, 1]
  σ2 := 1
  hd := by intro i; fin_cases i <;> norm_num
  hσ2 := by norm_num

/-- При `n = 2`, `k = 1` допустимых носителей ровно три. -/
lemma adm_two (S : Finset (Fin 2)) (hS : S ∈ adm (Fin 2) 1) :
    S = ∅ ∨ S = {0} ∨ S = {1} := by
  revert hS
  revert S
  decide

lemma Fval_empty : Pcex.Fval ∅ = 0 := by
  simp [OneFactor.Fval, OneFactor.Ccoef, OneFactor.Acoef, OneFactor.kappa, Pcex]

lemma Fval_zero : Pcex.Fval {0} = 1 / 2 := by
  norm_num [OneFactor.Fval, OneFactor.Ccoef, OneFactor.Acoef, OneFactor.kappa, Pcex]

lemma Fval_one : Pcex.Fval {1} = 1 / 5 := by
  norm_num [OneFactor.Fval, OneFactor.Ccoef, OneFactor.Acoef, OneFactor.kappa, Pcex]

lemma phi_empty (t : ℝ) : Pcex.phi ∅ t = t ^ 2 := by
  simp [OneFactor.phi, Pcex]

lemma phi_zero (t : ℝ) : Pcex.phi {0} t = t ^ 2 + (1 - t) ^ 2 := by
  norm_num [OneFactor.phi, Pcex]

lemma phi_one (t : ℝ) : Pcex.phi {1} t = t ^ 2 + (1 + 2 * t) ^ 2 := by
  norm_num [OneFactor.phi, Pcex]
  ring

/-- `OPT = 1/2`, достигается на `{0}`. -/
lemma OPTv_eq : Pcex.OPTv 1 = 1 / 2 := by
  refine le_antisymm (Finset.sup'_le _ _ fun S hS => ?_) ?_
  · rcases adm_two S hS with h | h | h <;> subst h
    · rw [Fval_empty]; norm_num
    · rw [Fval_zero]
    · rw [Fval_one]; norm_num
  · rw [← Fval_zero]
    exact Fval_le_OPTv (by decide)

/-- `Φ(0) = 1`. -/
lemma Phi_zero_eq : Pcex.Phi 1 0 = 1 := by
  refine le_antisymm (Finset.sup'_le _ _ fun S hS => ?_) ?_
  · rcases adm_two S hS with h | h | h <;> subst h
    · rw [phi_empty]; norm_num
    · rw [phi_zero]; norm_num
    · rw [phi_one]; norm_num
  · have : Pcex.phi {0} 0 = 1 := by rw [phi_zero]; norm_num
    rw [← this]
    exact phi_le_Phi (by decide)

/-- `t̂ = 0` действительно минимизирует `Φ`. -/
lemma Phi_min (t : ℝ) : (1 : ℝ) ≤ Pcex.Phi 1 t := by
  rcases le_or_gt t 0 with ht | ht
  · have h : (1 : ℝ) ≤ Pcex.phi {0} t := by rw [phi_zero]; nlinarith
    exact le_trans h (phi_le_Phi (by decide))
  · have h : (1 : ℝ) ≤ Pcex.phi {1} t := by rw [phi_one]; nlinarith
    exact le_trans h (phi_le_Phi (by decide))

/-- Множество `{0}` **связано** в `t̂ = 0`. -/
lemma zero_is_tied : Pcex.phi {0} 0 = Pcex.Phi 1 0 := by
  rw [phi_zero, Phi_zero_eq]; norm_num

/-- Множество `{0}` **оптимально**. -/
lemma zero_is_optimal : Pcex.Fval {0} = Pcex.OPTv 1 := by
  rw [Fval_zero, OPTv_eq]

/-- **Контрпример к ложному «⇐» первой редакции.**
Множество `{0}` одновременно оптимально и связано в минимуме `Φ`,
но сертификат не точен: `Φ(0) = 1 ≠ 1/2 = OPT`. -/
theorem certificate_not_tight :
    Pcex.phi {0} 0 = Pcex.Phi 1 0 ∧ Pcex.Fval {0} = Pcex.OPTv 1 ∧
      Pcex.Phi 1 0 ≠ Pcex.OPTv 1 :=
  ⟨zero_is_tied, zero_is_optimal, by rw [Phi_zero_eq, OPTv_eq]; norm_num⟩

/-- Следствие: по Теореме C (iii) ни у одного связанного множества нет нулевого наклона. -/
theorem no_tied_set_has_zero_slope :
    ¬ ∃ T ∈ adm (Fin 2) 1, Pcex.phi T 0 = Pcex.Phi 1 0 ∧ Pcex.that T = 0 := by
  rw [← tight_iff]
  rw [Phi_zero_eq, OPTv_eq]
  norm_num

/-- Зазор в точности равен оценке Теоремы C (ii): `M_0({0})²/κ({0}) = 1/2`. -/
theorem gap_bound_is_attained :
    Pcex.Phi 1 0 - Pcex.OPTv 1 = (Pcex.Mt {0} 0) ^ 2 / Pcex.kappa {0} := by
  rw [Phi_zero_eq, OPTv_eq]
  norm_num [OneFactor.Mt, OneFactor.kappa, Pcex]

end OneFactor

end SparseSharpe
