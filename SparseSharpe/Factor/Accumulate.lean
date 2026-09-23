import SparseSharpe.Factor.State

set_option linter.style.header false

/-!
# Накопление погрешности округления и согласованность констант алгоритма

Динамика округляет отслеживаемое состояние только на шагах «взять», и таких шагов
не больше `k`. Здесь формализовано ровно то, что из этого следует, и ровно та
подстановка констант, ради которой в одномерном случае пришлось заводить
`fptas_constants_consistent` (там в черновике дважды была арифметическая ошибка).

* `accumulate_norm` — за `j` шагов погрешность не превосходит `j·ρ` (в любой
  нормированной группе: годится и для евклидова `M̃`, и для поэлементного `Κ̃`);
* `round_step_euclid` — одно округление по координатам с шагом `s` даёт
  евклидову погрешность `≤ s√K/2`;
* `fptasK_constants_M`, `fptasK_constants_K`, `fptasK_delta_sq` — подстановка
  шагов корзин из `code/SPEC_FPTAS_K.md` §3 в гипотезы `fptasK_step`
  и `gram_half_of_entrywise`.
-/

namespace SparseSharpe.Factor

open Finset

/-- **Накопление аддитивной погрешности.** Истинный префикс растёт на `δ j`,
отслеживаемое значение — на `δ j` плюс округление длины `≤ ρ`. Тогда за `j` шагов
расхождение не больше `j·ρ`. -/
theorem accumulate_norm {E : Type*} [SeminormedAddCommGroup E] (u v : ℕ → E)
    (δ : ℕ → E) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hu : ∀ j, u (j + 1) = u j + δ j)
    (hv : ∀ j, ‖v (j + 1) - (v j + δ j)‖ ≤ ρ)
    (h0 : v 0 = u 0) : ∀ j : ℕ, ‖v j - u j‖ ≤ j * ρ := by
  intro j
  induction j with
  | zero => simp [h0]
  | succ j ih =>
      have hsplit : v (j + 1) - u (j + 1)
          = (v (j + 1) - (v j + δ j)) + (v j - u j) := by
        rw [hu j]; abel
      calc ‖v (j + 1) - u (j + 1)‖
          ≤ ‖v (j + 1) - (v j + δ j)‖ + ‖v j - u j‖ := by
            rw [hsplit]; exact norm_add_le _ _
        _ ≤ ρ + j * ρ := add_le_add (hv j) ih
        _ = (j + 1 : ℕ) * ρ := by push_cast; ring

/-- Одно покоординатное округление с шагом `s` даёт евклидову погрешность `≤ s√K/2`
(в форме суммы квадратов: `≤ K·s²/4`). -/
theorem round_step_euclid {κ : Type*} [Fintype κ] {s : ℝ} (hs : 0 ≤ s) (x : κ → ℝ)
    (hx : ∀ l, |x l| ≤ s / 2) : ∑ l, (x l) ^ 2 ≤ (Fintype.card κ : ℝ) * s ^ 2 / 4 := by
  calc ∑ l, (x l) ^ 2 ≤ ∑ _l : κ, (s / 2) ^ 2 := by
        refine Finset.sum_le_sum fun l _ => ?_
        have h := hx l
        nlinarith [abs_nonneg (x l), sq_abs (x l)]
    _ = (Fintype.card κ : ℝ) * s ^ 2 / 4 := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; ring

/-- **Согласованность констант по `M̃`.** При ширине корзины `s_M = √(εV)/(2(k+1)√K)`
накопленная за `k+1` шагов евклидова погрешность равна ровно `Δ = √(εV)/4`. -/
theorem fptasK_constants_M {ε V Kc kk sM : ℝ} (hKc : 0 < Kc) (hkk : 0 < kk)
    (hs : sM = Real.sqrt (ε * V) / (2 * kk * Real.sqrt Kc)) :
    kk * (sM * Real.sqrt Kc / 2) = Real.sqrt (ε * V) / 4 := by
  have hKcs : Real.sqrt Kc ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hKc)
  rw [hs]
  field_simp
  ring

/-- **Согласованность констант по `Κ̃`.** При ширине корзины `s_Κ = 1/((k+1)K)`
накопленная за `k+1` шагов поэлементная погрешность равна `ξ = 1/(2K)`,
а это ровно гипотеза `ξ·K ≤ 1/2` леммы `gram_half_of_entrywise`. -/
theorem fptasK_constants_K {Kc kk sK : ℝ} (hKc : 0 < Kc) (hkk : 0 < kk)
    (hs : sK = 1 / (kk * Kc)) :
    kk * (sK / 2) = 1 / (2 * Kc) ∧ (1 / (2 * Kc)) * Kc = 1 / 2 := by
  constructor
  · rw [hs]; field_simp
  · field_simp

/-- **Подстановка `Δ` в гипотезу шага.** При `Δ = √(εV)/4`, `0 ≤ ε`, `V ≤ F`
выполнено `Δ² ≤ εF/16` — ровно гипотеза `fptasK_step`. -/
theorem fptasK_delta_sq {ε V F Δ : ℝ} (hε : 0 ≤ ε) (hV : 0 ≤ V) (hVF : V ≤ F)
    (hΔ : Δ = Real.sqrt (ε * V) / 4) : Δ ^ 2 ≤ ε * F / 16 := by
  have h1 : Real.sqrt (ε * V) ^ 2 = ε * V := Real.sq_sqrt (by positivity)
  rw [hΔ, div_pow, h1]
  have : ε * V ≤ ε * F := mul_le_mul_of_nonneg_left hVF hε
  nlinarith

/-- **Шаг сетки.** При `s = 2√(εV/(K·C))` покрытие с точностью `s/2` по каждой
координате даёт `‖h‖² ≤ εV/C` — ровно гипотеза Теоремы H (с `V ≤ F`). -/
theorem fptasK_grid_step {ε V Kc C s : ℝ} (hKc : 0 < Kc) (hC : 0 < C)
    (hε : 0 ≤ ε) (hV : 0 ≤ V) (hs : s = 2 * Real.sqrt (ε * V / (Kc * C))) :
    Kc * s ^ 2 / 4 = ε * V / C := by
  have h1 : Real.sqrt (ε * V / (Kc * C)) ^ 2 = ε * V / (Kc * C) :=
    Real.sq_sqrt (by positivity)
  rw [hs, mul_pow, h1]
  field_simp
  ring

end SparseSharpe.Factor
