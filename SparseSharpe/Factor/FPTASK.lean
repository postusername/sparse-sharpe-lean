import SparseSharpe.Factor.GridK

set_option linter.style.header false

/-!
# Шаг FPTAS при `K` факторах

Итог динамики: вместо истинного оптимума `S` она возвращает **представителя** `R`,
про которого известно ровно три вещи (см. `code/SPEC_FPTAS_K.md`, §3):

* `Q(R) ≥ Q(S)` — второй момент представителя не меньше;
* `|⟨M(R) − M(S), v⟩| ≤ Δ·√gram(S,v)` — первый момент известен с точностью `Δ`
  (в координатах `K`-ки; `√gram(S,·)` мажорирует евклидову норму по нижней части зажима);
* `gram(R,v) ≥ ½·gram(S,v)` — форма Грама представителя не сильно меньше
  (аддитивное округление `Κ̃` с шагом `1/((k+1)K)` даёт это по **верхней** части зажима).

`fptasK_step` выводит отсюда `F(R) ≥ (1 − 17ε/8)·F(S)`. Никаких обращений матриц:
`F(R) = min_v φ_R(t+v)`, и оценка доказывается сразу для всех `v`.

Арифметическое ядро вынесено в `step_algebra` — ровно та подстановка констант, в которой
в одномерном случае дважды была ошибка (см. `findings_v11.md`, §4).
-/

namespace SparseSharpe.Factor

open Finset

/-- Арифметическое ядро шага: при `0 ≤ x ≤ √P + b` (и `Δ, b ≥ 0`)

    P − x²/2 − 2Δx  ≥  −b² − 4bΔ − 2Δ².

Слева — то, что остаётся от `φ_R(t+v) − F` после всех оценок; справа — итоговая потеря. -/
lemma step_algebra {P x b Δ : ℝ} (hP : 0 ≤ P) (hx : 0 ≤ x) (hΔ : 0 ≤ Δ)
    (hxle : x ≤ Real.sqrt P + b) :
    -(b ^ 2) - 4 * b * Δ - 2 * Δ ^ 2 ≤ P - x ^ 2 / 2 - 2 * Δ * x := by
  have hp0 : 0 ≤ Real.sqrt P := Real.sqrt_nonneg P
  have hp : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP
  have hdiff : 0 ≤ Real.sqrt P + b - x := by linarith
  nlinarith [sq_nonneg (Real.sqrt P - b - 2 * Δ),
    mul_nonneg hdiff (by linarith : (0:ℝ) ≤ Real.sqrt P + b + x),
    mul_nonneg hΔ hdiff]

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {S R : Finset ι} {t th : κ → ℝ}

/-- **Шаг FPTAS (K факторов).** Общая форма: три свойства представителя ⟹ оценка снизу
на `φ_R(t+v)` при любом `v`, то есть на `F(R) = min_v φ_R(t+v)`. -/
theorem fptasK_step_general (hnormal : IsNormal a y S th) {Δ : ℝ}
    (hΔ0 : 0 ≤ Δ)
    (hQR : phi a y S t ≤ phi a y R t)
    (hM : ∀ v, mom a y R t v - mom a y S t v ≤ Δ * Real.sqrt (gram a S v))
    (hKR : ∀ v, gram a S v / 2 ≤ gram a R v) (v : κ → ℝ) :
    phi a y S th - (Real.sqrt (phi a y S t - phi a y S th)) ^ 2
      - 4 * Real.sqrt (phi a y S t - phi a y S th) * Δ - 2 * Δ ^ 2
      ≤ phi a y R (t + v) := by
  set F := phi a y S th with hF
  set Q := phi a y S t with hQdef
  -- `b² = Q − F` — отклонение узла от оптимума, измеренное формой Грама
  have hQF : Q - F = gram a S (t - th) := by rw [hQdef, hF, phi_eq_add hnormal t]; ring
  have hQF0 : 0 ≤ Q - F := hQF ▸ gram_nonneg a S (t - th)
  set b := Real.sqrt (Q - F) with hbdef
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hb2 : b ^ 2 = gram a S (t - th) := by rw [hbdef, Real.sq_sqrt hQF0, hQF]
  -- `x² = gram(S,v)`
  set x := Real.sqrt (gram a S v) with hxdef
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = gram a S v := Real.sq_sqrt (gram_nonneg a S v)
  -- `P = gram(S, t+v−t̂)`, и `φ_S(t+v) = F + P`
  set P := gram a S (t + v - th) with hPdef
  have hP0 : 0 ≤ P := gram_nonneg a S _
  have hSv : phi a y S (t + v) = F + P := by rw [hF, hPdef, phi_eq_add hnormal (t + v)]
  -- неравенство треугольника: `x ≤ √P + b`
  have hvsplit : (t + v - th) + (-(t - th)) = v := by abel
  have hxle : x ≤ Real.sqrt P + b := by
    have h := sqrt_gram_add_le a S (t + v - th) (-(t - th))
    rw [hvsplit, gram_neg] at h
    rw [hxdef, hbdef, hQF]
    exact h
  -- собираем: φ_R(t+v) ≥ F + P − x²/2 − 2Δx
  have hshR := phi_shift a y R t v
  have hshS := phi_shift a y S t v
  have hMv := hM v
  have hKRv := hKR v
  have hchain : F + P - x ^ 2 / 2 - 2 * Δ * x ≤ phi a y R (t + v) := by
    have hSexp : Q - 2 * mom a y S t v = F + P - x ^ 2 := by
      rw [hx2]
      have : phi a y S (t + v) = Q - 2 * mom a y S t v + gram a S v := hshS
      rw [hSv] at this
      linarith
    have : phi a y R (t + v) = phi a y R t - 2 * mom a y R t v + gram a R v := hshR
    rw [this]
    have hmom : -2 * mom a y R t v ≥ -2 * mom a y S t v - 2 * Δ * x := by
      have := hMv
      rw [← hxdef] at this
      linarith
    linarith [hQR, hKRv, hSexp, hmom]
  have := step_algebra hP0 hx0 hΔ0 hxle
  linarith

/-- **Шаг FPTAS с явными константами.** При `Q ≤ (1+ε)F` и `Δ² ≤ εF/16`

    F(R) ≥ (1 − 17ε/8)·F(S).

Гипотеза о `Δ` — неравенство, а не равенство: подстановка констант алгоритма
(`η = √(εVW̃)/(4(k+1))`, `Δ = (k+1)η`) проверяется отдельно, см. `fptasK_constants`. -/
theorem fptasK_step (hnormal : IsNormal a y S th) {ε Δ : ℝ}
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ^ 2 ≤ ε * phi a y S th / 16)
    (hQ : phi a y S t ≤ (1 + ε) * phi a y S th)
    (hQR : phi a y S t ≤ phi a y R t)
    (hM : ∀ v, mom a y R t v - mom a y S t v ≤ Δ * Real.sqrt (gram a S v))
    (hKR : ∀ v, gram a S v / 2 ≤ gram a R v) (v : κ → ℝ) :
    (1 - 17 * ε / 8) * phi a y S th ≤ phi a y R (t + v) := by
  set F := phi a y S th with hF
  set Q := phi a y S t with hQdef
  have hF0 : 0 ≤ F := phi_nonneg a y S th
  have hQF0 : 0 ≤ Q - F := by
    have := phi_min hnormal t
    rw [← hF, ← hQdef] at this; linarith
  set b := Real.sqrt (Q - F) with hbdef
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hb2 : b ^ 2 = Q - F := Real.sq_sqrt hQF0
  have hble : b ^ 2 ≤ ε * F := by rw [hb2]; linarith
  -- `4bΔ ≤ 2b² + 2Δ²·... ` — среднее арифметическое-геометрическое с весом
  have hbΔ : 4 * b * Δ ≤ ε * F := by
    have h1 : 16 * Δ ^ 2 ≤ ε * F := by linarith
    nlinarith [sq_nonneg (2 * b - 8 * Δ), hb0, hΔ0, hble, h1]
  have hΔ2 : 2 * Δ ^ 2 ≤ ε * F / 8 := by linarith
  have hmain := fptasK_step_general hnormal hΔ0 hQR hM hKR v
  rw [← hF, ← hQdef, ← hbdef] at hmain
  nlinarith [hmain, hble, hbΔ, hΔ2]


/-! ### Обобщение: постоянный множитель в `hKR` и запас в `hQR`

Для long-only при `K ≥ 2` (`theory_note_v5.md`, §7.2) шаг нужен в ослабленном виде:

* `hQR` — с аддитивным запасом `σ` (строки `A*`, ставшие в узле неактивными,
  не видны динамике, и их вклад в `Q` теряется; он мал — `Factor/ClippedGrid.lean`);
* `hKR` — с произвольным множителем `γ ≥ 1` вместо `2` (та же причина: форма Грама
  представителя сравнивается не со всем `S̄*`, а с его активной частью, и переход
  между ними стоит множителя `|S̄*|·K` по правилу Крамера).

Итог тот же по форме: `φ_R(t+v) ≥ F − (γ+1)(b+Δ)² − σ`, где `b² = φ_S(t) − φ_S(t̂)`.
При `γ = 2`, `σ = 0` это слабее `fptasK_step_general` на постоянный множитель,
зато гипотезы достижимы в зажатой задаче. -/

/-- Арифметическое ядро обобщённого шага:

    P − x² + x²/γ − 2Δx  ≥  −(γ+1)(b+Δ)²   при `0 ≤ x ≤ √P + b`, `γ ≥ 1`. -/
lemma step_algebra_gamma {P x b Δ γ : ℝ} (hP : 0 ≤ P) (hx : 0 ≤ x) (hΔ : 0 ≤ Δ)
    (hb : 0 ≤ b) (hγ : 1 ≤ γ) (hxle : x ≤ Real.sqrt P + b) :
    -((γ + 1) * (b + Δ) ^ 2) ≤ P - x ^ 2 + x ^ 2 / γ - 2 * Δ * x := by
  have hγ0 : (0:ℝ) < γ := lt_of_lt_of_le one_pos hγ
  have hγne : γ ≠ 0 := ne_of_gt hγ0
  have hu0 : 0 ≤ Real.sqrt P := Real.sqrt_nonneg _
  have hu2 : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP
  set u := Real.sqrt P with hudef
  have hcinv : (0:ℝ) < 1 / γ := by positivity
  have hc0 : (0:ℝ) ≤ 1 - 1 / γ := by
    have h : 1 / γ ≤ 1 := by rw [div_le_one hγ0]; exact hγ
    linarith
  set c := 1 - 1 / γ with hcdef
  have hc1 : c ≤ 1 := by rw [hcdef]; linarith
  have hA0 : 0 ≤ c * b + Δ := add_nonneg (mul_nonneg hc0 hb) hΔ
  -- 1) левая часть в терминах `c`
  have hL : P - x ^ 2 + x ^ 2 / γ - 2 * Δ * x = u ^ 2 - c * x ^ 2 - 2 * Δ * x := by
    rw [hu2, hcdef]; field_simp; ring
  -- 2) выражение убывает по `x` на `[0, u+b]`
  have hdec : u ^ 2 - c * (u + b) ^ 2 - 2 * Δ * (u + b)
      ≤ u ^ 2 - c * x ^ 2 - 2 * Δ * x := by
    have h1 : (0:ℝ) ≤ u + b - x := by linarith
    have h2 : (0:ℝ) ≤ u + b + x := by linarith
    nlinarith [mul_nonneg hc0 (mul_nonneg h1 h2), mul_nonneg hΔ h1]
  -- 3) полный квадрат по `u`
  have hsq : u ^ 2 - c * (u + b) ^ 2 - 2 * Δ * (u + b)
      = (1 / γ) * (u - γ * (c * b + Δ)) ^ 2
        - γ * (c * b + Δ) ^ 2 - c * b ^ 2 - 2 * Δ * b := by
    rw [hcdef]; field_simp; ring
  have hsq0 : 0 ≤ (1 / γ) * (u - γ * (c * b + Δ)) ^ 2 :=
    mul_nonneg hcinv.le (sq_nonneg _)
  -- 4) остаток не превосходит `(γ+1)(b+Δ)²`
  have hrem : γ * (c * b + Δ) ^ 2 + c * b ^ 2 + 2 * Δ * b ≤ (γ + 1) * (b + Δ) ^ 2 := by
    have hAle : c * b + Δ ≤ b + Δ := by nlinarith
    have h1 : (c * b + Δ) ^ 2 ≤ (b + Δ) ^ 2 := by nlinarith
    have h2 : c * b ^ 2 + 2 * Δ * b ≤ (b + Δ) ^ 2 := by nlinarith [sq_nonneg Δ, sq_nonneg b]
    nlinarith [mul_le_mul_of_nonneg_left h1 hγ0.le]
  rw [hL]
  linarith

/-- **Обобщённый шаг FPTAS.** `hQR` с запасом `σ`, `hKR` с множителем `γ ≥ 1`. -/
theorem fptasK_step_gamma (hnormal : IsNormal a y S th) {Δ γ σ : ℝ}
    (hΔ0 : 0 ≤ Δ) (hγ : 1 ≤ γ) (hσ0 : 0 ≤ σ)
    (hQR : phi a y S t ≤ phi a y R t + σ)
    (hM : ∀ v, mom a y R t v - mom a y S t v ≤ Δ * Real.sqrt (gram a S v))
    (hKR : ∀ v, gram a S v / γ ≤ gram a R v) (v : κ → ℝ) :
    phi a y S th - (γ + 1) * (Real.sqrt (phi a y S t - phi a y S th) + Δ) ^ 2 - σ
      ≤ phi a y R (t + v) := by
  set F := phi a y S th with hF
  set Q := phi a y S t with hQdef
  have hQF : Q - F = gram a S (t - th) := by rw [hQdef, hF, phi_eq_add hnormal t]; ring
  have hQF0 : 0 ≤ Q - F := hQF ▸ gram_nonneg a S (t - th)
  set b := Real.sqrt (Q - F) with hbdef
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  set x := Real.sqrt (gram a S v) with hxdef
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = gram a S v := Real.sq_sqrt (gram_nonneg a S v)
  set P := gram a S (t + v - th) with hPdef
  have hP0 : 0 ≤ P := gram_nonneg a S _
  have hSv : phi a y S (t + v) = F + P := by rw [hF, hPdef, phi_eq_add hnormal (t + v)]
  have hvsplit : (t + v - th) + (-(t - th)) = v := by abel
  have hxle : x ≤ Real.sqrt P + b := by
    have h := sqrt_gram_add_le a S (t + v - th) (-(t - th))
    rw [hvsplit, gram_neg] at h
    rw [hxdef, hbdef, hQF]
    exact h
  have hSexp : Q - 2 * mom a y S t v = F + P - x ^ 2 := by
    rw [hx2]
    have h : phi a y S (t + v) = Q - 2 * mom a y S t v + gram a S v := phi_shift a y S t v
    rw [hSv] at h; linarith
  have hR : phi a y R (t + v) = phi a y R t - 2 * mom a y R t v + gram a R v :=
    phi_shift a y R t v
  have hKRv : gram a S v / γ ≤ gram a R v := hKR v
  have hMv := hM v
  rw [← hxdef] at hMv
  rw [← hx2] at hKRv
  have hchain : F + P - x ^ 2 + x ^ 2 / γ - 2 * Δ * x - σ ≤ phi a y R (t + v) := by
    rw [hR]; linarith
  have halg := step_algebra_gamma hP0 hx0 hΔ0 hb0 hγ hxle
  linarith


/-! ### Непустота гипотез обобщённого шага

При `γ = 2`, `σ = 0` гипотезы — это в точности гипотезы `fptasK_step_general`,
но проверять надо, что они выполнимы одновременно. Пример: одна строка `a = (1)`,
`y = 1`, `S = R = univ`, `t̂ = 1`, узел `t = 1`, `Δ = 0`. -/
example :
    IsNormal (ι := Fin 1) (κ := Fin 1) (fun _ _ => 1) (fun _ => 1) Finset.univ
        (fun _ => 1)
    ∧ (phi (ι := Fin 1) (κ := Fin 1) (fun _ _ => 1) (fun _ => 1) Finset.univ (fun _ => 1)
        ≤ phi (ι := Fin 1) (κ := Fin 1) (fun _ _ => 1) (fun _ => 1) Finset.univ
          (fun _ => 1) + 0)
    ∧ (∀ v : Fin 1 → ℝ,
        mom (ι := Fin 1) (fun _ _ => 1) (fun _ => 1) Finset.univ (fun _ => 1) v
          - mom (ι := Fin 1) (fun _ _ => 1) (fun _ => 1) Finset.univ (fun _ => 1) v
        ≤ 0 * Real.sqrt (gram (ι := Fin 1) (fun _ _ => 1) Finset.univ v))
    ∧ (∀ v : Fin 1 → ℝ,
        gram (ι := Fin 1) (fun _ _ => 1) Finset.univ v / 2
          ≤ gram (ι := Fin 1) (fun _ _ => 1) Finset.univ v) := by
  refine ⟨fun v => by simp [mom, dotp], by simp, fun v => by simp, fun v => ?_⟩
  have := gram_nonneg (ι := Fin 1) (fun _ _ => (1:ℝ)) Finset.univ v
  linarith


/-! ### Шаг Теоремы M: гипотеза `hKR` выводится из максимально-объёмной `K`-ки -/

/-- **Шаг Теоремы M** (`theory_note_v5.md`, §8.2). Если максимально-объёмная `K`-ка
набора `S` целиком лежит в `R`, то третья гипотеза шага выполняется автоматически
с множителем `γ = |S|·K`, и остаётся проверить только `hQR` (с запасом `σ`) и `hM`.

Именно это снимает зазор (i): строки `S`, не попавшие в `R`, выражаются через
строки `K`-ки с коэффициентами `≤ 1`, поэтому их отсутствие стоит постоянного
множителя, а не `(1 + ‖a_i‖²)`. -/
theorem fptasK_step_maxvol {T : κ → ι} [DecidableEq ι]
    (hnormal : IsNormal a y S th) (hmax : MaxVol a S T)
    (hdet : (rowMat a T).det ≠ 0) (hTR : ∀ l, T l ∈ R) {Δ σ : ℝ}
    (hΔ0 : 0 ≤ Δ) (hσ0 : 0 ≤ σ) (hγ1 : 1 ≤ (S.card * Fintype.card κ : ℝ))
    (hQR : phi a y S t ≤ phi a y R t + σ)
    (hM : ∀ v, mom a y R t v - mom a y S t v ≤ Δ * Real.sqrt (gram a S v)) (v : κ → ℝ) :
    phi a y S th - ((S.card * Fintype.card κ : ℝ) + 1)
        * (Real.sqrt (phi a y S t - phi a y S th) + Δ) ^ 2 - σ
      ≤ phi a y R (t + v) := by
  have hγ0 : (0:ℝ) < (S.card * Fintype.card κ : ℝ) := lt_of_lt_of_le one_pos hγ1
  refine fptasK_step_gamma hnormal hΔ0 hγ1 hσ0 hQR hM (fun v' => ?_) v
  rw [div_le_iff₀ hγ0]
  calc gram a S v' ≤ (S.card * Fintype.card κ : ℝ) * gram a R v' :=
        gram_le_card_mul_gram_of_subset hmax hdet hTR v'
    _ = gram a R v' * (S.card * Fintype.card κ : ℝ) := by ring

end SparseSharpe.Factor
