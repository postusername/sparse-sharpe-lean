import SparseSharpe.Inertia

set_option linter.style.header false

/-!
# Ядро FPTAS: почему округление становится полиномиальным

Стандартное «округление профиля» для динамики Теоремы B ломается: целевая функция
`C − σ²A²/(1+σ²B)` — разность, и относительная погрешность в `A` даёт погрешность
`2δ·A²/κ = 2δ(C − F)`, несоизмеримую с `F`, когда сокращение велико.

Здесь доказаны два утверждения, которые эту трудность снимают.

* `Mt_range_over_precision` — **главная лемма**. Если точка сетки `t` такова, что
  `φ_S(t) ≤ (1+ε)F(S)`, то отношение «диапазон промежуточных значений `M`» к
  «требуемой точности по `M`» ограничено величиной `2N√((1+ε)/ε)`, зависящей
  только от `ε` и `N = k+1` — **и ни от каких величин входа**. Поэтому корзин
  по `M` нужно `O(k/√ε)`, а не псевдополиномиально много.

* `fptas_step` — оценка снизу на значение, возвращаемое округлённой динамикой,
  и её числовое следствие `fptas_step_explicit`: `F(R) ≥ (1 − 3ε)·F(S*)`.
-/

namespace SparseSharpe

open Finset

variable {ι : Type*}

namespace OneFactor

variable {P : OneFactor ι} {S S' R : Finset ι} {t : ℝ}

/-- **Главная лемма FPTAS.** `η` — требуемая точность по `M`,
`η² = ε·F(S)·κ(S)/(4N²)`. Тогда для любого подмножества `S' ⊆ S`

  `M_t(S')² ≤ (4N²(1+ε)/ε)·η²`,   то есть  `|M_t(S')|/η ≤ 2N√((1+ε)/ε)`.

Правая часть зависит только от `ε` и `N`; величины входа (`m`, `β`, `d`, `σ²`)
в неё не входят. Это и есть причина, по которой число корзин по `M`
в динамике равно `O(k/√ε)`. -/
theorem Mt_range_over_precision {ε η N : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (hη : η ^ 2 = ε * P.Fval S * P.kappa S / (4 * N ^ 2))
    (hS' : S' ⊆ S) (hgood : P.phi S t ≤ (1 + ε) * P.Fval S) :
    (P.Mt S' t) ^ 2 ≤ (4 * N ^ 2 * (1 + ε) / ε) * η ^ 2 := by
  have h1 : (P.Mt S' t) ^ 2 ≤ P.kappa S * P.phi S t := Mt_prefix_bound hS'
  have h2 : P.kappa S * P.phi S t ≤ P.kappa S * ((1 + ε) * P.Fval S) :=
    mul_le_mul_of_nonneg_left hgood kappa_pos.le
  have hNe : (4 : ℝ) * N ^ 2 ≠ 0 := by positivity
  have key : (4 * N ^ 2 * (1 + ε) / ε) * (ε * P.Fval S * P.kappa S / (4 * N ^ 2))
      = P.kappa S * ((1 + ε) * P.Fval S) := by
    field_simp
  rw [hη, key]
  linarith

/-- **Шаг FPTAS.** Пусть `t` — хорошая точка сетки для оптимального носителя `S*`
(то есть `φ_{S*}(t) ≤ (1+ε)F(S*)`), а округлённая динамика вернула носитель `R`
с большим вторым моментом (`φ_{S*}(t) ≤ φ_R(t)`), близким первым моментом
(`|M_t(R) − M_t(S*)| ≤ δ`) и весом, не слишком малым (`1/κ(R) ≤ c/κ(S*)`).
Тогда значение на `R` отстаёт от оптимума не более чем на явную величину. -/
theorem fptas_step {ε δ c : ℝ} (hε : 0 ≤ ε) (hc : 1 ≤ c)
    (hgood : P.phi S t ≤ (1 + ε) * P.Fval S)
    (hQ : P.phi S t ≤ P.phi R t)
    (hM : |P.Mt R t - P.Mt S t| ≤ δ)
    (hW : 1 / P.kappa R ≤ c / P.kappa S) :
    P.Fval S - (c - 1) * ε * P.Fval S
        - c * (2 * δ * |P.Mt S t| + δ ^ 2) / P.kappa S
      ≤ P.Fval R := by
  have hκS : 0 < P.kappa S := kappa_pos
  have hκR : 0 < P.kappa R := kappa_pos
  have hround := rounding_bound (W := P.kappa S) (W' := P.kappa R)
    (Q := P.phi S t) (Q' := P.phi R t) (M := P.Mt S t) (M' := P.Mt R t)
    (δ := δ) (c := c) hκS hκR hW hQ hM (by linarith)
  have hFR : P.Fval R = P.phi R t - (P.Mt R t) ^ 2 / P.kappa R :=
    Fval_eq_phi_sub t
  have hFS : P.Fval S = P.phi S t - (P.Mt S t) ^ 2 / P.kappa S :=
    Fval_eq_phi_sub t
  have hgap : (P.Mt S t) ^ 2 / P.kappa S ≤ ε * P.Fval S := by linarith
  have hsplit : c * ((P.Mt S t) ^ 2 + 2 * δ * |P.Mt S t| + δ ^ 2) / P.kappa S
      = c * ((P.Mt S t) ^ 2 / P.kappa S)
        + c * (2 * δ * |P.Mt S t| + δ ^ 2) / P.kappa S := by
    field_simp
    ring
  rw [hsplit] at hround
  have hcg : c * ((P.Mt S t) ^ 2 / P.kappa S)
      ≤ (P.Mt S t) ^ 2 / P.kappa S + (c - 1) * (ε * P.Fval S) := by
    nlinarith [hgap, hc, hε, div_nonneg (sq_nonneg (P.Mt S t)) hκS.le]
  rw [hFR]
  linarith

/-- Числовое следствие: при `N ≥ 2`, `c = 2` и `δ² = ε·F(S)·κ(S)/(4N²)`
(то есть при ширине корзины по `M`, отвечающей Главной лемме)
динамика теряет не больше `3ε` относительной точности. -/
theorem fptas_step_explicit {ε δ N : ℝ} (hε : 0 ≤ ε) (hN : 2 ≤ N)
    (hδ : δ ^ 2 ≤ ε * P.Fval S * P.kappa S / (4 * N ^ 2)) (hδ0 : 0 ≤ δ)
    (hgood : P.phi S t ≤ (1 + ε) * P.Fval S)
    (hQ : P.phi S t ≤ P.phi R t)
    (hM : |P.Mt R t - P.Mt S t| ≤ δ)
    (hW : 1 / P.kappa R ≤ 2 / P.kappa S) :
    (1 - 3 * ε) * P.Fval S ≤ P.Fval R := by
  have hκS : 0 < P.kappa S := kappa_pos
  have hF : 0 ≤ P.Fval S := Fval_nonneg
  have hN0 : (0:ℝ) < N := by linarith
  have hεF : 0 ≤ ε * P.Fval S := mul_nonneg hε hF
  have hstep := fptas_step (ε := ε) (δ := δ) (c := 2) hε (by norm_num) hgood hQ hM hW
  set M := P.Mt S t with hMdef
  have habs : 0 ≤ |M| := abs_nonneg M
  have hsq : |M| ^ 2 = M ^ 2 := sq_abs M
  -- AM-GM: `2δ|M| ≤ M²/N + Nδ²`
  have hAM : 2 * δ * |M| ≤ M ^ 2 / N + N * δ ^ 2 := by
    have h := sq_nonneg (|M| - N * δ)
    have h2 : 0 ≤ M ^ 2 - 2 * N * δ * |M| + N ^ 2 * δ ^ 2 := by nlinarith [h, hsq]
    rw [← sub_nonneg]
    have key : M ^ 2 / N + N * δ ^ 2 - 2 * δ * |M|
        = (M ^ 2 - 2 * N * δ * |M| + N ^ 2 * δ ^ 2) / N := by
      field_simp
      ring
    rw [key]
    exact div_nonneg h2 hN0.le
  have hgap : M ^ 2 / P.kappa S ≤ ε * P.Fval S := by
    have := Fval_eq_phi_sub (P := P) (S := S) t
    linarith
  have hbound : (2 * δ * |M| + δ ^ 2) / P.kappa S ≤ (11 / 16) * (ε * P.Fval S) := by
    have h1 : (2 * δ * |M| + δ ^ 2) / P.kappa S
        ≤ (M ^ 2 / N + (N + 1) * δ ^ 2) / P.kappa S := by
      have hnum : 2 * δ * |M| + δ ^ 2 ≤ M ^ 2 / N + (N + 1) * δ ^ 2 := by
        have hexp : (N + 1) * δ ^ 2 = N * δ ^ 2 + δ ^ 2 := by ring
        rw [hexp]
        linarith
      rw [← sub_nonneg, ← sub_div]
      exact div_nonneg (sub_nonneg.mpr hnum) hκS.le
    have h2 : (M ^ 2 / N + (N + 1) * δ ^ 2) / P.kappa S
        = (1 / N) * (M ^ 2 / P.kappa S) + (N + 1) * (δ ^ 2 / P.kappa S) := by
      field_simp
    have hNpos : (0:ℝ) < 4 * N ^ 2 := by positivity
    have h3 : δ ^ 2 / P.kappa S ≤ ε * P.Fval S / (4 * N ^ 2) := by
      have key : δ ^ 2 * (4 * N ^ 2) ≤ ε * P.Fval S * P.kappa S := by
        have h := mul_le_mul_of_nonneg_right hδ hNpos.le
        rwa [div_mul_cancel₀ _ hNpos.ne'] at h
      rw [div_le_div_iff₀ hκS hNpos]
      linarith [key]
    have h4 : (1 / N) * (M ^ 2 / P.kappa S) ≤ (1 / N) * (ε * P.Fval S) :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    have h6 : (1 / N) * (ε * P.Fval S) ≤ (1 / 2) * (ε * P.Fval S) := by
      have hcc : (1:ℝ) / N ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hN0 (by norm_num)]; linarith
      exact mul_le_mul_of_nonneg_right hcc hεF
    have h5 : (N + 1) * (ε * P.Fval S / (4 * N ^ 2)) ≤ (3 / 16) * (ε * P.Fval S) := by
      have hcoef : (N + 1) / (4 * N ^ 2) ≤ 3 / 16 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hN]
      calc (N + 1) * (ε * P.Fval S / (4 * N ^ 2))
          = ((N + 1) / (4 * N ^ 2)) * (ε * P.Fval S) := by ring
        _ ≤ (3 / 16) * (ε * P.Fval S) := mul_le_mul_of_nonneg_right hcoef hεF
    rw [h2] at h1
    have h3' : (N + 1) * (δ ^ 2 / P.kappa S)
        ≤ (N + 1) * (ε * P.Fval S / (4 * N ^ 2)) :=
      mul_le_mul_of_nonneg_left h3 (by linarith)
    linarith [h5]
  have hfin : (2 : ℝ) * (2 * δ * |M| + δ ^ 2) / P.kappa S ≤ (11 / 8) * (ε * P.Fval S) := by
    have he : (2 : ℝ) * (2 * δ * |M| + δ ^ 2) / P.kappa S
        = 2 * ((2 * δ * |M| + δ ^ 2) / P.kappa S) := by ring
    rw [he]
    linarith
  nlinarith [hstep, hfin, hεF]


/-- **Согласованность констант алгоритма.** Ровно та подстановка, в которой
дважды была допущена арифметическая ошибка в черновике заметки, — поэтому
она вынесена в отдельное проверяемое утверждение.

Пусть догадки удовлетворяют `V ≤ F(S)` и `W̃ ≤ κ(S)` (это обеспечивают перебор
по `V` и корзины по весу), ширина корзины по `M` равна `η = √(ε·V·W̃)/(4(k+1))`,
а накопленная за `k+1` шагов погрешность есть `δ = (k+1)·η`. Тогда выполнена
гипотеза `hδ` теоремы `fptas_step_explicit` при `N = 2`. -/
theorem fptas_constants_consistent {ε V W η δ : ℝ} {k : ℕ}
    (hε : 0 ≤ ε) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hVF : V ≤ P.Fval S) (hWκ : W ≤ P.kappa S)
    (hη : η = Real.sqrt (ε * V * W) / (4 * ((k : ℝ) + 1)))
    (hδ : δ = ((k : ℝ) + 1) * η) :
    δ ^ 2 ≤ ε * P.Fval S * P.kappa S / (4 * 2 ^ 2) := by
  have hk1 : (0:ℝ) < (k : ℝ) + 1 := by positivity
  have hprod : 0 ≤ ε * V * W := by positivity
  have hδ' : δ = Real.sqrt (ε * V * W) / 4 := by
    rw [hδ, hη]
    field_simp
  have hsq : δ ^ 2 = ε * V * W / 16 := by
    rw [hδ', div_pow, Real.sq_sqrt hprod]
    norm_num
  have hκ : 0 ≤ P.kappa S := kappa_pos.le
  have hmono : ε * V * W ≤ ε * P.Fval S * P.kappa S := by
    have h1 : ε * V ≤ ε * P.Fval S := mul_le_mul_of_nonneg_left hVF hε
    have h2 : 0 ≤ ε * V := by positivity
    calc ε * V * W ≤ ε * V * P.kappa S := mul_le_mul_of_nonneg_left hWκ h2
      _ ≤ ε * P.Fval S * P.kappa S := mul_le_mul_of_nonneg_right h1 hκ
  rw [hsq]
  norm_num
  linarith


/-- **Итог одного узла сетки** — сборка §4 заметки в одно утверждение.
Гипотезы ровно те, что обеспечивает алгоритм:
`V, W̃` — догадки снизу по `F(S)` и `κ(S)`; `η` — ширина корзины по `M`;
`δ = (k+1)η` — накопленная за шаги динамики погрешность; `hgood` — Лемма G;
`hQ, hM, hWR` — инвариант округлённой динамики.
Вывод: возвращённый носитель `R` теряет не больше `3ε`. -/
theorem fptas_at_grid_point {ε V W η δ : ℝ} {k : ℕ}
    (hε : 0 ≤ ε) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hVF : V ≤ P.Fval S) (hWκ : W ≤ P.kappa S)
    (hη : η = Real.sqrt (ε * V * W) / (4 * ((k : ℝ) + 1)))
    (hδ : δ = ((k : ℝ) + 1) * η)
    (hgood : P.phi S t ≤ (1 + ε) * P.Fval S)
    (hQ : P.phi S t ≤ P.phi R t)
    (hM : |P.Mt R t - P.Mt S t| ≤ δ)
    (hWR : 1 / P.kappa R ≤ 2 / P.kappa S) :
    (1 - 3 * ε) * P.Fval S ≤ P.Fval R := by
  have hk1 : (0:ℝ) < (k : ℝ) + 1 := by positivity
  have hδ0 : 0 ≤ δ := by
    rw [hδ, hη]
    have : 0 ≤ Real.sqrt (ε * V * W) := Real.sqrt_nonneg _
    positivity
  exact fptas_step_explicit (N := 2) hε (by norm_num)
    (fptas_constants_consistent hε hV hW hVF hWκ hη hδ) hδ0 hgood hQ hM hWR

end OneFactor

end SparseSharpe
