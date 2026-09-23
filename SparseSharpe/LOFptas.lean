import SparseSharpe.LOFilter

set_option linter.style.header false

/-!
# Long-only: узел сверху от центроида и шаг динамики «минимум `M`»

Прошлая схема (`theory_note_v3.md`, §5) округляла `M` и максимизировала `Q`;
тогда из `M_t(A*) ≤ 0` не следовало `M_t(R) ≤ 0`, и представитель мог оказаться
не самосогласованным. Обходы (а) и (б) отброшены контрпримерами.

Здесь формализована **смена ролей**: целевая функция округляется (её погрешность
входит в оценку аддитивно), а **ограничение держится точным** — динамика хранит
в каждом состоянии множество с **минимальным точным** `M`. Тогда для представителя
`M(R) ≤ M(A*) < 0` автоматически, и самосогласованность получается **по построению**,
без всякого фильтра и без Теоремы L.

* `phi_le_of_dev_sq` — Лемма G в удобной форме: `κ(t−t̂)² ≤ εF ⟹ φ ≤ (1+ε)F`;
* `Mt_neg_of_gt_that`, `abs_Mt_le` — знак и величина `M_t(A*)` в таком узле;
* `selfconsistent_of_Mt_neg` — **из `M_t(R) < 0` и пула `{i : m_i ≥ tβ_i}`
  следует самосогласованность `R`**;
* `lo_value_of_selfconsistent` — для самосогласованного `R` значение long-only
  задачи равно `F(R)` (long-short оптимум достижим неотрицательными весами);
* **`lo_step`** — итог: `F(R) ≥ (1 − 33ε/8)·F(A*)`.

Спецификация алгоритма — `code/SPEC_LO.md`.
-/

namespace SparseSharpe

open Finset

variable {ι : Type*} {P : OneFactor ι} {A R : Finset ι} {t : ℝ}

namespace OneFactor

/-- Лемма G в форме, которой пользуется long-only: отклонение узла измеряется
величиной `κ·(t − t̂)²`, и она же — единственное, что нужно. -/
theorem phi_le_of_dev_sq {ε : ℝ} (hε : 0 ≤ ε)
    (h : P.kappa A * (t - P.that A) ^ 2 ≤ ε * P.Fval A) :
    P.phi A t ≤ (1 + ε) * P.Fval A := by
  rw [phi_eq_completed_square]
  nlinarith [h]

/-- В узле строго выше центроида первый момент отрицателен. -/
theorem Mt_neg_of_gt_that (h : P.that A < t) : P.Mt A t < 0 := by
  rw [Mt_eq]
  have hκ : 0 < P.kappa A := kappa_pos
  nlinarith

/-- И по модулю не превосходит `√(ε·F·κ)`, если узел удовлетворяет Лемме G. -/
theorem abs_Mt_le {ε : ℝ} (hε : 0 ≤ ε) (hF : 0 ≤ P.Fval A)
    (h : P.kappa A * (t - P.that A) ^ 2 ≤ ε * P.Fval A) :
    (P.Mt A t) ^ 2 ≤ ε * P.Fval A * P.kappa A := by
  rw [Mt_eq]
  have hκ : 0 < P.kappa A := kappa_pos
  have hsq : (P.kappa A * (P.that A - t)) ^ 2
      = P.kappa A * (P.kappa A * (t - P.that A) ^ 2) := by ring
  rw [hsq]
  nlinarith [h, hκ.le]

/-- **Самосогласованность по построению.** Если все активы `R` лежат не ниже узла
(`m_i ≥ tβ_i`, то есть `r_i ≥ t` при `β > 0`) и первый момент в узле отрицателен,
то `R` самосогласовано: `m_i > t̂(R)β_i` для всех `i ∈ R`. -/
theorem selfconsistent_of_Mt_neg (hβ : ∀ i ∈ R, 0 < P.β i)
    (hpool : ∀ i ∈ R, t * P.β i ≤ P.m i) (hM : P.Mt R t < 0) :
    ∀ i ∈ R, 0 < P.m i - P.that R * P.β i := by
  have hκ : 0 < P.kappa R := kappa_pos
  have hlt : P.that R < t := by
    have := Mt_eq (P := P) (S := R) (t := t)
    nlinarith [hM, hκ, this]
  intro i hi
  have h1 : t * P.β i ≤ P.m i := hpool i hi
  have h2 : 0 < P.β i := hβ i hi
  nlinarith

/-- **Значение long-only задачи на самосогласованном носителе равно `F(R)`.**
Оптимальные веса long-short задачи неотрицательны ровно при самосогласованности,
а сверху `F(R)` ограничивает даже без знаковых ограничений. -/
theorem lo_value_of_selfconsistent
    (hsc : ∀ i ∈ R, 0 ≤ P.m i - P.that R * P.β i) :
    IsGreatest {v : ℝ | ∃ w : ι → ℝ, (∀ i ∈ R, 0 ≤ w i) ∧ v = P.obj R w} (P.Fval R) := by
  constructor
  · refine ⟨P.wopt R, fun i hi => ?_, obj_wopt.symm⟩
    have hd := P.hd i
    have := hsc i hi
    rw [OneFactor.wopt]
    positivity
  · rintro v ⟨w, -, rfl⟩
    exact le_trans (obj_le_phi w (P.that R)) (le_of_eq phi_that)

/-- **Существование годного узла (Л1).** Нужен узел строго выше центроида, не дальше
`W` от него и не выше самого низкого актива оптимума. Разбор двух случаев:
если запас `μ = r_min − t̂` не больше `W`, годится сам `r_min` (семейство узлов `{r_i}`);
если больше — годится любой узел сетки около `t̂ + 3W/4`, а сетка с шагом `s ≤ W/2`
такой узел содержит. -/
theorem lo_node_exists {that rmin W s : ℝ} (hW : 0 < W) (hμ : that < rmin)
    (hs : 0 < s) (hstep : s ≤ W / 2) (G : Set ℝ)
    (hG : ∀ x : ℝ, ∃ g ∈ G, |g - x| ≤ s / 2) :
    ∃ t, that < t ∧ t ≤ that + W ∧ t ≤ rmin ∧ (t = rmin ∨ t ∈ G) := by
  by_cases hcase : rmin ≤ that + W
  · exact ⟨rmin, hμ, hcase, le_refl _, Or.inl rfl⟩
  · rw [not_le] at hcase
    obtain ⟨g, hgG, hgx⟩ := hG (that + 3 * W / 4)
    have habs := abs_le.mp hgx
    refine ⟨g, ?_, ?_, ?_, Or.inr hgG⟩
    · linarith [habs.1]
    · linarith [habs.2]
    · linarith [habs.2]

/-- **Л1 в конкретной, конечной сетке.** Узел берётся либо из семейства `{r_i}`
(`t = rmin`), либо из решётки `c + z·s` вокруг центра `c`, и номер узла `z` ограничен
радиусом сетки: `|z| ≤ R/s + ½`. Это и есть утверждение про **перебираемое конечное**
семейство, а не про абстрактное покрытие. -/
theorem lo_node_exists_grid {that rmin W s c Rad : ℝ} (hW : 0 < W) (hμ : that < rmin)
    (hs : 0 < s) (hstep : s ≤ W / 2) (hrange : |that + 3 * W / 4 - c| ≤ Rad) :
    ∃ t, that < t ∧ t ≤ that + W ∧ t ≤ rmin ∧
      (t = rmin ∨ ∃ z : ℤ, t = c + z * s ∧ |(z : ℝ)| ≤ Rad / s + 1 / 2) := by
  by_cases hcase : rmin ≤ that + W
  · exact ⟨rmin, hμ, hcase, le_refl _, Or.inl rfl⟩
  · rw [not_le] at hcase
    set x := that + 3 * W / 4 with hx
    set z : ℤ := round ((x - c) / s) with hz
    have hround := abs_sub_round ((x - c) / s)
    have hne : s ≠ 0 := ne_of_gt hs
    -- |(c + z·s) − x| ≤ s/2
    have hclose : |c + (z : ℝ) * s - x| ≤ s / 2 := by
      have hrw : c + (z : ℝ) * s - x = -(s * ((x - c) / s - (z : ℝ))) := by
        field_simp
        ring
      rw [hrw, abs_neg, abs_mul, abs_of_pos hs]
      calc s * |(x - c) / s - (z : ℝ)| ≤ s * (1 / 2) :=
            mul_le_mul_of_nonneg_left hround hs.le
        _ = s / 2 := by ring
    have habs := abs_le.mp hclose
    -- номер узла ограничен радиусом
    have hzbound : |(z : ℝ)| ≤ Rad / s + 1 / 2 := by
      have h1 : |(z : ℝ)| ≤ |(x - c) / s| + 1 / 2 := by
        have := abs_sub_abs_le_abs_sub ((x - c) / s) ((z : ℝ))
        cases' abs_cases ((x - c) / s - (z : ℝ)) with hc1 hc1 <;>
          cases' abs_cases ((x - c) / s) with hc2 hc2 <;>
          cases' abs_cases ((z : ℝ)) with hc3 hc3 <;> linarith [hround]
      have h2 : |(x - c) / s| ≤ Rad / s := by
        rw [abs_div, abs_of_pos hs]
        gcongr
      linarith
    refine ⟨c + (z : ℝ) * s, ?_, ?_, ?_, Or.inr ⟨z, rfl, hzbound⟩⟩
    · rw [hx] at habs; linarith [habs.1]
    · rw [hx] at habs; linarith [habs.2]
    · rw [hx] at habs; linarith [habs.2]

/-- Пул `{i : tβ_i ≤ m_i}` содержит `A`, если узел не выше точек `A`:
из `t ≤ r_i = m_i/β_i` и `β_i > 0` следует `tβ_i ≤ m_i`. -/
theorem pool_contains (hβ : ∀ i ∈ A, 0 < P.β i)
    (hr : ∀ i ∈ A, t ≤ P.m i / P.β i) : ∀ i ∈ A, t * P.β i ≤ P.m i := by
  intro i hi
  have hb := hβ i hi
  have := hr i hi
  rwa [le_div_iff₀ hb] at this

/-- **Шаг динамики «минимум `M`».** Гипотезы — ровно то, что доставляет динамика
`code/SPEC_LO.md` §3: округление целевой функции стоит `≤ εF`, первый момент
представителя не больше, чем у оптимума (и не меньше, чем на `Δ`), вес — в пределах
вдвое, узел удовлетворяет Лемме G. Вывод: `F(R) ≥ (1 − 33ε/8)F(A)`. -/
theorem lo_step {ε Δ : ℝ} (hε : 0 ≤ ε) (hΔ0 : 0 ≤ Δ)
    (hFA : 0 ≤ P.Fval A)
    (hnode : P.kappa A * (t - P.that A) ^ 2 ≤ ε * P.Fval A)
    (hthat : P.that A < t)
    (hQ : P.phi A t - ε * P.Fval A ≤ P.phi R t)
    (hMle : P.Mt R t ≤ P.Mt A t) (hMge : P.Mt A t - Δ ≤ P.Mt R t)
    (hΔ : 16 * Δ ^ 2 ≤ ε * P.Fval A * P.kappa A)
    (hκ : P.kappa A ≤ 2 * P.kappa R) :
    (1 - 33 * ε / 8) * P.Fval A ≤ P.Fval R := by
  have hκR : 0 < P.kappa R := kappa_pos
  have hκA : 0 < P.kappa A := kappa_pos
  have hMA : P.Mt A t < 0 := Mt_neg_of_gt_that hthat
  -- `|M_t(R)| ≤ |M_t(A)| + Δ`, поэтому `M_t(R)² ≤ (25/16)·εFκ`
  have hMAsq : (P.Mt A t) ^ 2 ≤ ε * P.Fval A * P.kappa A := abs_Mt_le hε hFA hnode
  have hMRsq : (P.Mt R t) ^ 2 ≤ (25 / 16) * (ε * P.Fval A * P.kappa A) := by
    have h1 : -(P.Mt R t) ≤ -(P.Mt A t) + Δ := by linarith
    have h2 : 0 ≤ -(P.Mt R t) := by linarith
    have h3 : (-(P.Mt A t)) ^ 2 ≤ ε * P.Fval A * P.kappa A := by nlinarith
    have h4 : 16 * Δ ^ 2 ≤ ε * P.Fval A * P.kappa A := hΔ
    nlinarith [sq_nonneg (-(P.Mt A t) - 4 * Δ), sq_nonneg (P.Mt A t), h1, h2, h3, h4]
  -- собираем `F(R) = φ_R(t) − M_t(R)²/κ(R)`
  have hFR : P.Fval R = P.phi R t - (P.Mt R t) ^ 2 / P.kappa R := Fval_eq_phi_sub t
  have hphiA : P.Fval A ≤ P.phi A t := by
    rw [phi_eq_completed_square]; nlinarith [sq_nonneg (t - P.that A), hκA.le]
  have hdiv : (P.Mt R t) ^ 2 / P.kappa R ≤ (25 / 8) * (ε * P.Fval A) := by
    rw [div_le_iff₀ hκR]
    nlinarith [hMRsq, hκ, hκR, hε, hFA]
  rw [hFR]
  linarith
