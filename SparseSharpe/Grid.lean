import Mathlib

set_option linter.style.header false

/-!
# Геометрическая сетка: лемма о покрытии

Для Леммы G нужна сетка узлов, которая любую точку `y > 0` приближает снизу
с **относительной** точностью `η`. Геометрическая прогрессия `Δ₀(1+η)^s` это делает,
и число узлов на диапазоне `[Δ₀, Δmax]` равно `⌈log(Δmax/Δ₀)/log(1+η)⌉ = O(log(Δmax/Δ₀)/η)`.

В приложении `η = √(ε/(k+1))`, так что узлов вокруг каждой из `n+1` точек `r_j`
нужно `O(√((k+1)/ε)·L)`, где `L` — длина записи входа. Это полиномиально.
-/

namespace SparseSharpe

/-- **Вилка.** Для `Δ₀ ≤ y` найдётся `s` с `Δ₀(1+η)^s ≤ y < Δ₀(1+η)^{s+1}`. -/
theorem geometric_grid_bracket {y Δ₀ η : ℝ} (hΔ : 0 < Δ₀) (hη : 0 < η) (hy : Δ₀ ≤ y) :
    ∃ s : ℕ, Δ₀ * (1 + η) ^ s ≤ y ∧ y < Δ₀ * (1 + η) ^ s * (1 + η) := by
  have h1η : (1:ℝ) < 1 + η := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le hΔ hy
  -- множество показателей, при которых узел уже «перелетел» `y`, непусто
  have hex : ∃ s : ℕ, y < Δ₀ * (1 + η) ^ s := by
    obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt (y / Δ₀) h1η
    exact ⟨s, by rwa [div_lt_iff₀ hΔ, mul_comm] at hs⟩
  classical
  have hs₀spec : y < Δ₀ * (1 + η) ^ (Nat.find hex) := Nat.find_spec hex
  have hs₀pos : Nat.find hex ≠ 0 := by
    intro h
    rw [h, pow_zero, mul_one] at hs₀spec
    linarith
  obtain ⟨s, hsucc⟩ : ∃ s : ℕ, Nat.find hex = s + 1 :=
    ⟨Nat.find hex - 1, (Nat.succ_pred_eq_of_ne_zero hs₀pos).symm⟩
  have hle : Δ₀ * (1 + η) ^ s ≤ y := by
    have hlt : s < Nat.find hex := by rw [hsucc]; exact Nat.lt_succ_self s
    have hmin := Nat.find_min hex hlt
    push_neg at hmin
    exact hmin
  refine ⟨s, hle, ?_⟩
  rw [hsucc] at hs₀spec
  have e : Δ₀ * (1 + η) ^ (s + 1) = Δ₀ * (1 + η) ^ s * (1 + η) := by ring
  rw [e] at hs₀spec
  exact hs₀spec

/-- **Покрытие снизу.** Узел `Δ₀(1+η)^s` приближает `y` снизу с относительной
точностью `η`. -/
theorem geometric_grid_cover {y Δ₀ η : ℝ} (hΔ : 0 < Δ₀) (hη : 0 < η) (hy : Δ₀ ≤ y) :
    ∃ s : ℕ, Δ₀ * (1 + η) ^ s ≤ y ∧ y - Δ₀ * (1 + η) ^ s ≤ η * y := by
  obtain ⟨s, hle, hlt⟩ := geometric_grid_bracket hΔ hη hy
  refine ⟨s, hle, ?_⟩
  have hnode : 0 < Δ₀ * (1 + η) ^ s := by positivity
  nlinarith [hlt, hle, hnode]

/-- **Покрытие сверху.** Соседний узел `Δ₀(1+η)^{s+1}` приближает `y` сверху
с той же относительной точностью `η`. Значит узел нужной точности есть
**по обе стороны** от `y`; для long-only (§5 заметки) нужен именно верхний. -/
theorem geometric_grid_cover_above {y Δ₀ η : ℝ} (hΔ : 0 < Δ₀) (hη : 0 < η) (hy : Δ₀ ≤ y) :
    ∃ s : ℕ, y ≤ Δ₀ * (1 + η) ^ s ∧ Δ₀ * (1 + η) ^ s - y ≤ η * y := by
  obtain ⟨s, hle, hlt⟩ := geometric_grid_bracket hΔ hη hy
  refine ⟨s + 1, ?_, ?_⟩
  · have e : Δ₀ * (1 + η) ^ (s + 1) = Δ₀ * (1 + η) ^ s * (1 + η) := by ring
    rw [e]; linarith
  · have e : Δ₀ * (1 + η) ^ (s + 1) = Δ₀ * (1 + η) ^ s * (1 + η) := by ring
    rw [e]
    nlinarith [hle, hlt, hη]

/-! ### Накопление погрешностей за шаги динамики

Два утверждения, закрывающие ровно те места, где в черновике §4 заметки были
допущены арифметические ошибки в константах.
-/

/-- Аддитивная погрешность за `j` шагов не превосходит `j·η`. -/
theorem accumulate_add {M Mtrue : ℕ → ℝ} {η : ℝ} (hη : 0 ≤ η)
    (h0 : M 0 = Mtrue 0)
    (hstep : ∀ j, |M (j + 1) - Mtrue (j + 1)| ≤ |M j - Mtrue j| + η) (j : ℕ) :
    |M j - Mtrue j| ≤ j * η := by
  induction j with
  | zero => simp [h0]
  | succ n ih =>
    have := hstep n
    push_cast
    linarith

/-- Мультипликативная погрешность за `j` шагов не превосходит `ξ^j`.
Здесь `a j` — отношение истинного веса к весу представителя на шаге `j`. -/
theorem accumulate_mul {a : ℕ → ℝ} {ξ : ℝ} (hξ : 1 ≤ ξ) (hpos : ∀ j, 0 ≤ a j)
    (h0 : a 0 ≤ 1) (hstep : ∀ j, a (j + 1) ≤ ξ * a j) (j : ℕ) :
    a j ≤ ξ ^ j := by
  induction j with
  | zero => simpa using h0
  | succ n ih =>
    calc a (n + 1) ≤ ξ * a n := hstep n
      _ ≤ ξ * ξ ^ n := by
          exact mul_le_mul_of_nonneg_left ih (by linarith)
      _ = ξ ^ (n + 1) := by ring

/-- **Шаг корзин по весу.** При шаге `1 + 1/(2N)` накопленный за `N` шагов
множитель не превосходит `2` (на самом деле `√e ≈ 1.649`). Именно эта
подстановка была в черновике сделана неверно: при шаге `1 + 1/N` множитель
равен `e ≈ 2.718 > 2`, а лемма `fptas_step_explicit` требует ровно `2`. -/
theorem one_add_half_inv_pow_le_two {N : ℕ} (hN : 0 < N) :
    (1 + 1 / (2 * (N : ℝ))) ^ N ≤ 2 := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hbase : (0:ℝ) ≤ 1 + 1 / (2 * (N : ℝ)) := by positivity
  have h1 : (1:ℝ) + 1 / (2 * (N : ℝ)) ≤ Real.exp (1 / (2 * (N : ℝ))) := by
    have := Real.add_one_le_exp (1 / (2 * (N : ℝ)))
    linarith
  have hhalf : Real.exp (1 / 2) ≤ 2 := by
    have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have hlt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hpos : 0 < Real.exp (1 / 2) := Real.exp_pos _
    nlinarith [hsq, hlt, hpos]
  calc (1 + 1 / (2 * (N : ℝ))) ^ N
      ≤ (Real.exp (1 / (2 * (N : ℝ)))) ^ N := pow_le_pow_left₀ hbase h1 N
    _ = Real.exp ((N : ℝ) * (1 / (2 * (N : ℝ)))) := by rw [← Real.exp_nat_mul]
    _ = Real.exp (1 / 2) := by
        congr 1
        field_simp
    _ ≤ 2 := hhalf

end SparseSharpe
