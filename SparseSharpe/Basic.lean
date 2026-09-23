import Mathlib

set_option linter.style.header false

/-!
# Разрежённая максимизация Шарпа: однофакторная модель, основные определения

Файл фиксирует обозначения и доказывает **Лемму 1** — минимаксное тождество

  `F(S) = min_t [ t²/σ² + Σ_{i∈S} (m_i − tβ_i)²/d_i ]`,

где `F(S) = max_w [2 m'w − w'Vw]` при `V = D + σ²ββ'` и носителе `w` внутри `S`.

Доказательство не использует теорию двойственности: всё следует из точного
алгебраического тождества `dualityIdentity` («разность двух сумм квадратов»).
-/

namespace SparseSharpe

open Finset

variable {ι : Type*}

/-- Данные однофакторной модели: избыточные доходности `m`, беты `β`,
идиосинкратические дисперсии `d > 0`, дисперсия фактора `σ² > 0`. -/
structure OneFactor (ι : Type*) where
  m : ι → ℝ
  β : ι → ℝ
  d : ι → ℝ
  σ2 : ℝ
  hd : ∀ i, 0 < d i
  hσ2 : 0 < σ2

namespace OneFactor

/-- Первичная целевая функция `2 m'w − w'Vw` на носителе `S` (Замечание 0). -/
noncomputable def obj (P : OneFactor ι) (S : Finset ι) (w : ι → ℝ) : ℝ :=
  2 * ∑ i ∈ S, P.m i * w i -
    ((∑ i ∈ S, P.d i * (w i) ^ 2) + P.σ2 * (∑ i ∈ S, P.β i * w i) ^ 2)

/-- Двойственная функция одного переменного `t` (long-short). -/
noncomputable def phi (P : OneFactor ι) (S : Finset ι) (t : ℝ) : ℝ :=
  t ^ 2 / P.σ2 + ∑ i ∈ S, (P.m i - t * P.β i) ^ 2 / P.d i

/-- Двойственная функция одного переменного `t` (long-only): та же формула
с положительной частью, `((m_i − tβ_i)₊)²/d_i`. -/
noncomputable def phiLO (P : OneFactor ι) (S : Finset ι) (t : ℝ) : ℝ :=
  t ^ 2 / P.σ2 + ∑ i ∈ S, (max (P.m i - t * P.β i) 0) ^ 2 / P.d i

/-- Кривизна: `κ(S) = 1/σ² + Σ_{i∈S} β_i²/d_i`. -/
noncomputable def kappa (P : OneFactor ι) (S : Finset ι) : ℝ :=
  1 / P.σ2 + ∑ i ∈ S, (P.β i) ^ 2 / P.d i

/-- `A(S) = Σ_{i∈S} m_iβ_i/d_i`. -/
noncomputable def Acoef (P : OneFactor ι) (S : Finset ι) : ℝ :=
  ∑ i ∈ S, P.m i * P.β i / P.d i

/-- `C(S) = Σ_{i∈S} m_i²/d_i`. -/
noncomputable def Ccoef (P : OneFactor ι) (S : Finset ι) : ℝ :=
  ∑ i ∈ S, (P.m i) ^ 2 / P.d i

/-- Минимизатор `φ_S`: `t̂(S) = A(S)/κ(S)`. -/
noncomputable def that (P : OneFactor ι) (S : Finset ι) : ℝ := P.Acoef S / P.kappa S

/-- Значение задачи на носителе `S`: `F(S) = C(S) − A(S)²/κ(S)`. -/
noncomputable def Fval (P : OneFactor ι) (S : Finset ι) : ℝ :=
  P.Ccoef S - (P.Acoef S) ^ 2 / P.kappa S

/-- Оптимальные веса на носителе `S`: `w_i = (m_i − t̂β_i)/d_i`. -/
noncomputable def wopt (P : OneFactor ι) (S : Finset ι) : ι → ℝ :=
  fun i => (P.m i - P.that S * P.β i) / P.d i

variable {P : OneFactor ι} {S : Finset ι}

lemma kappa_pos : 0 < P.kappa S := by
  have h1 : (0:ℝ) < 1 / P.σ2 := by have := P.hσ2; positivity
  have h2 : (0:ℝ) ≤ ∑ i ∈ S, (P.β i) ^ 2 / P.d i :=
    Finset.sum_nonneg fun i _ => by have := (P.hd i).le; positivity
  simpa [OneFactor.kappa] using add_pos_of_pos_of_nonneg h1 h2

lemma kappa_ne_zero : P.kappa S ≠ 0 := ne_of_gt kappa_pos

lemma Acoef_eq : P.Acoef S = P.that S * P.kappa S := by
  have hκ : P.kappa S ≠ 0 := kappa_ne_zero
  rw [OneFactor.that, div_mul_cancel₀ _ hκ]

/-- `φ_S` — квадратичная функция `κ t² − 2A t + C`. -/
lemma phi_eq_quadratic (t : ℝ) :
    P.phi S t = P.kappa S * t ^ 2 - 2 * P.Acoef S * t + P.Ccoef S := by
  have key : ∀ i ∈ S, (P.m i - t * P.β i) ^ 2 / P.d i
      = (P.m i) ^ 2 / P.d i - 2 * t * (P.m i * P.β i / P.d i)
        + t ^ 2 * ((P.β i) ^ 2 / P.d i) := by
    intro i _
    have h := (P.hd i).ne'
    field_simp
    ring
  have hσ := P.hσ2.ne'
  rw [OneFactor.phi, Finset.sum_congr rfl key]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [OneFactor.kappa, OneFactor.Acoef, OneFactor.Ccoef]
  field_simp
  ring

/-- Выделение полного квадрата: `φ_S(t) = F(S) + κ(S)·(t − t̂(S))²`. -/
lemma phi_eq_completed_square (t : ℝ) :
    P.phi S t = P.Fval S + P.kappa S * (t - P.that S) ^ 2 := by
  have hκ : P.kappa S ≠ 0 := kappa_ne_zero
  have hdiv : (P.Acoef S) ^ 2 / P.kappa S = (P.that S) ^ 2 * P.kappa S := by
    rw [Acoef_eq]; field_simp
  rw [phi_eq_quadratic, OneFactor.Fval, hdiv, Acoef_eq]
  ring

lemma phi_that : P.phi S (P.that S) = P.Fval S := by
  rw [phi_eq_completed_square]; ring

/-- `F(S)` — минимум `φ_S`. -/
lemma Fval_le_phi (t : ℝ) : P.Fval S ≤ P.phi S t := by
  have h : 0 ≤ P.kappa S * (t - P.that S) ^ 2 :=
    mul_nonneg kappa_pos.le (sq_nonneg _)
  rw [phi_eq_completed_square]
  linarith

lemma isLeast_phi : IsLeast (Set.range (P.phi S)) (P.Fval S) :=
  ⟨⟨P.that S, phi_that⟩, by rintro x ⟨t, rfl⟩; exact Fval_le_phi t⟩

/-!
## Тождество слабой двойственности
-/

/-- Точное алгебраическое тождество, из которого следует вся Лемма 1:
`φ_S(t) − obj(w)` есть сумма двух квадратичных невязок. -/
lemma dualityIdentity (w : ι → ℝ) (t : ℝ) :
    P.phi S t - P.obj S w
      = (t - P.σ2 * ∑ i ∈ S, P.β i * w i) ^ 2 / P.σ2
        + ∑ i ∈ S, P.d i * (w i - (P.m i - t * P.β i) / P.d i) ^ 2 := by
  have hexp : ∀ i ∈ S, P.d i * (w i - (P.m i - t * P.β i) / P.d i) ^ 2
      = P.d i * (w i) ^ 2 - 2 * (P.m i * w i) + 2 * t * (P.β i * w i)
        + (P.m i - t * P.β i) ^ 2 / P.d i := by
    intro i _
    have h := (P.hd i).ne'
    field_simp
    ring
  have hσ := P.hσ2.ne'
  rw [Finset.sum_congr rfl hexp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [OneFactor.phi, OneFactor.obj]
  field_simp
  ring

/-- Слабая двойственность: `obj(w) ≤ φ_S(t)` для всех `w` и `t`. -/
lemma obj_le_phi (w : ι → ℝ) (t : ℝ) : P.obj S w ≤ P.phi S t := by
  have h := dualityIdentity (P := P) (S := S) w t
  have h1 : 0 ≤ (t - P.σ2 * ∑ i ∈ S, P.β i * w i) ^ 2 / P.σ2 := by
    have := P.hσ2; positivity
  have h2 : 0 ≤ ∑ i ∈ S, P.d i * (w i - (P.m i - t * P.β i) / P.d i) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (P.hd i).le (sq_nonneg _)
  linarith

/-- Стационарность оптимальных весов: `Σ_{i∈S} β_i w_i = t̂/σ²`. -/
lemma sum_beta_wopt : ∑ i ∈ S, P.β i * P.wopt S i = P.that S / P.σ2 := by
  have hσ := P.hσ2.ne'
  have hκ : P.kappa S ≠ 0 := kappa_ne_zero
  have e1 : ∑ i ∈ S, P.β i * P.wopt S i
      = P.Acoef S - P.that S * ∑ i ∈ S, (P.β i) ^ 2 / P.d i := by
    rw [OneFactor.Acoef, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := (P.hd i).ne'
    simp only [OneFactor.wopt]
    field_simp
  have hB : ∑ i ∈ S, (P.β i) ^ 2 / P.d i = P.kappa S - 1 / P.σ2 := by
    simp [OneFactor.kappa]
  rw [e1, hB, Acoef_eq]
  field_simp
  ring

/-- Сильная двойственность: на `wopt` достигается `F(S)`. -/
lemma obj_wopt : P.obj S (P.wopt S) = P.Fval S := by
  have h := dualityIdentity (P := P) (S := S) (P.wopt S) (P.that S)
  have hσ := P.hσ2.ne'
  have h1 : P.σ2 * ∑ i ∈ S, P.β i * P.wopt S i = P.that S := by
    rw [sum_beta_wopt]; field_simp
  have hz : ∑ i ∈ S, P.d i * (P.wopt S i - (P.m i - P.that S * P.β i) / P.d i) ^ 2 = 0 :=
    Finset.sum_eq_zero fun i _ => by simp [OneFactor.wopt]
  rw [h1, hz, sub_self, phi_that] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    add_zero] at h
  linarith

/-- **Лемма 1 (long-short).** `F(S)` — одновременно максимум первичной задачи
и минимум двойственной: `max_w obj(w) = F(S) = min_t φ_S(t)`. -/
theorem lemma1_isGreatest : IsGreatest (Set.range (P.obj S)) (P.Fval S) :=
  ⟨⟨P.wopt S, obj_wopt⟩, by
    rintro x ⟨w, rfl⟩
    exact le_trans (obj_le_phi w (P.that S)) (le_of_eq phi_that)⟩

theorem lemma1 :
    IsGreatest (Set.range (P.obj S)) (P.Fval S) ∧ IsLeast (Set.range (P.phi S)) (P.Fval S) :=
  ⟨lemma1_isGreatest, isLeast_phi⟩

end OneFactor

end SparseSharpe
