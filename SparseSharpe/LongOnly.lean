import SparseSharpe.Basic

set_option linter.style.header false

/-!
# Long-only: тождество двойственности и сертификат (Предложение 2)

Для long-only версии `F_LO(S) = max_{w ≥ 0} [2m'w − w'Vw]` двойственная функция —
та же, но с положительной частью:

  `φ^LO_S(t) = t²/σ² + Σ_{i∈S} ((m_i − tβ_i)₊)²/d_i`.

Тождество `dualityIdentityLO` отличается от long-short одним дополнительным
слагаемым `2 w_i ((m_i − tβ_i)₊ − (m_i − tβ_i))`, неотрицательным при `w_i ≥ 0`.
Отсюда слабая двойственность `obj(w) ≤ φ^LO_S(t)` — а из неё Предложение 2:
`UB_LO(k) := min_t max_{|S| ≤ k} φ^LO_S(t) ≥ OPT_LO(k)`.
-/

namespace SparseSharpe

open Finset

variable {ι : Type*}

namespace OneFactor

variable {P : OneFactor ι} {S : Finset ι} {t : ℝ}

/-- Точное тождество для long-only версии. -/
lemma dualityIdentityLO (w : ι → ℝ) (t : ℝ) :
    P.phiLO S t - P.obj S w
      = (t - P.σ2 * ∑ i ∈ S, P.β i * w i) ^ 2 / P.σ2
        + ∑ i ∈ S, (P.d i * (w i - (max (P.m i - t * P.β i) 0) / P.d i) ^ 2
            + 2 * w i * ((max (P.m i - t * P.β i) 0) - (P.m i - t * P.β i))) := by
  have hexp : ∀ i ∈ S,
      P.d i * (w i - (max (P.m i - t * P.β i) 0) / P.d i) ^ 2
        + 2 * w i * ((max (P.m i - t * P.β i) 0) - (P.m i - t * P.β i))
      = P.d i * (w i) ^ 2 - 2 * (P.m i * w i) + 2 * t * (P.β i * w i)
        + (max (P.m i - t * P.β i) 0) ^ 2 / P.d i := by
    intro i _
    have h := (P.hd i).ne'
    field_simp
    ring
  have hσ := P.hσ2.ne'
  rw [Finset.sum_congr rfl hexp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [OneFactor.phiLO, OneFactor.obj]
  field_simp
  ring

/-- **Слабая двойственность (long-only).** При `w ≥ 0` на `S` имеем `obj(w) ≤ φ^LO_S(t)`. -/
theorem obj_le_phiLO {w : ι → ℝ} (hw : ∀ i ∈ S, 0 ≤ w i) (t : ℝ) :
    P.obj S w ≤ P.phiLO S t := by
  have h := dualityIdentityLO (P := P) (S := S) w t
  have h1 : 0 ≤ (t - P.σ2 * ∑ i ∈ S, P.β i * w i) ^ 2 / P.σ2 := by
    have := P.hσ2; positivity
  have h2 : 0 ≤ ∑ i ∈ S, (P.d i * (w i - (max (P.m i - t * P.β i) 0) / P.d i) ^ 2
      + 2 * w i * ((max (P.m i - t * P.β i) 0) - (P.m i - t * P.β i))) := by
    refine Finset.sum_nonneg fun i hi => ?_
    have hpos : 0 ≤ P.d i * (w i - (max (P.m i - t * P.β i) 0) / P.d i) ^ 2 :=
      mul_nonneg (P.hd i).le (sq_nonneg _)
    have hmax : P.m i - t * P.β i ≤ max (P.m i - t * P.β i) 0 := le_max_left _ _
    have : 0 ≤ 2 * w i * ((max (P.m i - t * P.β i) 0) - (P.m i - t * P.β i)) :=
      mul_nonneg (by linarith [hw i hi]) (by linarith)
    linarith
  linarith

/-- `φ^LO_S(t) ≤ φ_S(t)`: знаковое ограничение делает двойственную функцию меньше. -/
lemma phiLO_le_phi : P.phiLO S t ≤ P.phi S t := by
  have h : ∀ i ∈ S, (max (P.m i - t * P.β i) 0) ^ 2 / P.d i
      ≤ (P.m i - t * P.β i) ^ 2 / P.d i := by
    intro i _
    have hd := P.hd i
    have hsq : (max (P.m i - t * P.β i) 0) ^ 2 ≤ (P.m i - t * P.β i) ^ 2 := by
      rcases le_or_gt (P.m i - t * P.β i) 0 with hle | hgt
      · rw [max_eq_right hle]
        simpa using sq_nonneg (P.m i - t * P.β i)
      · rw [max_eq_left hgt.le]
    rw [← sub_nonneg, ← sub_div]
    exact div_nonneg (by linarith) hd.le
  simp only [OneFactor.phi, OneFactor.phiLO]
  have := Finset.sum_le_sum h
  linarith

/-- `φ^LO_S(t) ≥ 0`. -/
lemma phiLO_nonneg : 0 ≤ P.phiLO S t := by
  have h1 : (0:ℝ) ≤ t ^ 2 / P.σ2 := by have := P.hσ2; positivity
  have h2 : (0:ℝ) ≤ ∑ i ∈ S, (max (P.m i - t * P.β i) 0) ^ 2 / P.d i :=
    Finset.sum_nonneg fun i _ => by have := (P.hd i).le; positivity
  simpa [OneFactor.phiLO] using add_nonneg h1 h2

end OneFactor

end SparseSharpe
