import SparseSharpe.Inertia

set_option linter.style.header false

/-!
# Long-only FPTAS: оценка потери от фильтра активных активов

В long-only версии алгоритм в точке сетки `t` оставляет только активы с `m_i − tβ_i > 0`.
Узел сетки берётся **сверху** от `t̂(A*)`, поэтому часть активов оптимального
носителя `A*` фильтр выбрасывает. Здесь доказано, что потеря мала.

Схема: пусть `A' ⊆ A`, `D := A ∖ A'`, `x := t̂(A) − t̂(A')`.

* `Fval_sub_le` — потеря равна ровно сумме вкладов выброшенных активов в `t̂(A')`;
* `centroid_shift` — точное тождество `κ(A)·x = Σ_{i∈D} β_i(m_i − t̂(A')β_i)/d_i`;
* `centroid_mono` — если выброшенные активы лежат правее центроида, то `x ≥ 0`;
* `filter_loss_bound` — если сверх того они лежат не дальше `d` правее `t̂(A)`, то
  `(κ(A) − U_D)·x ≤ U_D·d` и потеря не больше `U_D·(d + x)²`, где `U_D = Σ_{i∈D} β_i²/d_i`.

В применении `d = √(ε/(k+1))·|r_j − t̂(A)|` для самого тяжёлого актива `j`, откуда
`U_D ≤ κ(A) ≤ (k+1)u_j`, `κ(A) − U_D ≥ u_j`, значит `x ≤ (k+1)d`, и потеря не больше
`(k+1)u_j·(k+2)²d² = (k+2)²·ε·u_j(r_j − t̂(A))² ≤ (k+2)²·ε·F(A)`.
-/

namespace SparseSharpe

open Finset

variable {ι : Type*} [DecidableEq ι]

namespace OneFactor

variable {P : OneFactor ι} {A A' : Finset ι}

/-- Разбиение `φ` по носителю: `φ_A(s) = φ_{A'}(s) + Σ_{A∖A'} (m_i − sβ_i)²/d_i`. -/
lemma phi_split (h : A' ⊆ A) (s : ℝ) :
    P.phi A s = P.phi A' s + ∑ i ∈ A \ A', (P.m i - s * P.β i) ^ 2 / P.d i := by
  simp only [OneFactor.phi]
  rw [← Finset.sum_sdiff h]
  ring

/-- То же для суммарного веса: `κ(A) = κ(A') + Σ_{A∖A'} β_i²/d_i`. -/
lemma kappa_split (h : A' ⊆ A) :
    P.kappa A = P.kappa A' + ∑ i ∈ A \ A', (P.β i) ^ 2 / P.d i := by
  simp only [OneFactor.kappa]
  rw [← Finset.sum_sdiff h]
  ring

/-- То же для первого момента. -/
lemma Mt_split (h : A' ⊆ A) (s : ℝ) :
    P.Mt A s = P.Mt A' s + ∑ i ∈ A \ A', P.β i * (P.m i - s * P.β i) / P.d i := by
  simp only [OneFactor.Mt]
  rw [← Finset.sum_sdiff h]
  ring

/-- **Потеря от сужения носителя.** `F(A) − F(A') ≤ Σ_{i∈A∖A'} (m_i − t̂(A')β_i)²/d_i`. -/
theorem Fval_sub_le (h : A' ⊆ A) :
    P.Fval A - ∑ i ∈ A \ A', (P.m i - P.that A' * P.β i) ^ 2 / P.d i ≤ P.Fval A' := by
  have h1 : P.Fval A ≤ P.phi A (P.that A') := Fval_le_phi _
  have h2 := phi_split (P := P) h (P.that A')
  have h3 : P.phi A' (P.that A') = P.Fval A' := phi_that
  linarith

/-- **Сдвиг центроида.** `κ(A)·(t̂(A) − t̂(A')) = Σ_{i∈A∖A'} β_i(m_i − t̂(A')β_i)/d_i`. -/
theorem centroid_shift (h : A' ⊆ A) :
    P.kappa A * (P.that A - P.that A')
      = ∑ i ∈ A \ A', P.β i * (P.m i - P.that A' * P.β i) / P.d i := by
  have h1 : P.Mt A (P.that A') = P.kappa A * (P.that A - P.that A') := Mt_eq
  have h2 : P.Mt A' (P.that A') = 0 := by
    rw [Mt_eq, sub_self, mul_zero]
  have h3 := Mt_split (P := P) h (P.that A')
  rw [h2, zero_add] at h3
  linarith [h1, h3]

/-- Если каждый выброшенный актив лежит правее центроида `t̂(A')`
(`β_i > 0` и `m_i ≥ t̂(A')β_i`), то сужение носителя центроид не поднимает. -/
theorem centroid_mono (h : A' ⊆ A)
    (hD : ∀ i ∈ A \ A', 0 ≤ P.β i * (P.m i - P.that A' * P.β i)) :
    P.that A' ≤ P.that A := by
  have hsum : 0 ≤ ∑ i ∈ A \ A', P.β i * (P.m i - P.that A' * P.β i) / P.d i :=
    Finset.sum_nonneg fun i hi => div_nonneg (hD i hi) (P.hd i).le
  have h1 := centroid_shift (P := P) h
  have hκ : 0 < P.kappa A := kappa_pos
  nlinarith [h1, hsum, hκ]

/-- **Оценка потери от фильтра.** Пусть `A' ⊆ A`, `D = A ∖ A'`,
каждый выброшенный актив имеет `β_i > 0`, лежит правее `t̂(A')`
и не дальше `d` правее `t̂(A)`. Тогда, с `U_D := Σ_{i∈D} β_i²/d_i`
и `x := t̂(A) − t̂(A')`:

* `(κ(A) − U_D)·x ≤ U_D·d`  (сдвиг центроида мал),
* `F(A) − F(A') ≤ U_D·(d + x)²`  (потеря мала). -/
theorem filter_loss_bound {d : ℝ} (h : A' ⊆ A)
    (hβ : ∀ i ∈ A \ A', 0 < P.β i)
    (hlow : ∀ i ∈ A \ A', 0 ≤ P.m i - P.that A' * P.β i)
    (hup : ∀ i ∈ A \ A', P.m i - P.that A * P.β i ≤ d * P.β i) :
    (P.kappa A - ∑ i ∈ A \ A', (P.β i) ^ 2 / P.d i) * (P.that A - P.that A')
        ≤ (∑ i ∈ A \ A', (P.β i) ^ 2 / P.d i) * d
      ∧ P.Fval A - (∑ i ∈ A \ A', (P.β i) ^ 2 / P.d i)
            * (d + (P.that A - P.that A')) ^ 2 ≤ P.Fval A' := by
  set UD : ℝ := ∑ i ∈ A \ A', (P.β i) ^ 2 / P.d i with hUD
  set x : ℝ := P.that A - P.that A' with hx
  -- поточечно: `m_i − t̂(A')β_i ≤ (d + x)·β_i`
  have hpt : ∀ i ∈ A \ A', P.m i - P.that A' * P.β i ≤ (d + x) * P.β i := by
    intro i hi
    have h1 := hup i hi
    have : P.m i - P.that A' * P.β i
        = (P.m i - P.that A * P.β i) + x * P.β i := by rw [hx]; ring
    rw [this]
    nlinarith [h1]
  constructor
  · -- сдвиг центроида
    have hshift := centroid_shift (P := P) h
    have hb : ∑ i ∈ A \ A', P.β i * (P.m i - P.that A' * P.β i) / P.d i
        ≤ UD * (d + x) := by
      rw [hUD, Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      have hdi := P.hd i
      have h1 := hpt i hi
      have h2 := (hβ i hi).le
      have key : P.β i ^ 2 / P.d i * (d + x)
            - P.β i * (P.m i - P.that A' * P.β i) / P.d i
          = (P.β i * ((d + x) * P.β i - (P.m i - P.that A' * P.β i))) / P.d i := by
        field_simp
      rw [← sub_nonneg, key]
      exact div_nonneg (mul_nonneg h2 (by linarith)) hdi.le
    have hκ : P.kappa A = P.kappa A' + UD := kappa_split (P := P) h
    have hκ' : 0 < P.kappa A' := kappa_pos
    nlinarith [hshift, hb, hκ, hκ']
  · -- потеря
    have hloss : ∑ i ∈ A \ A', (P.m i - P.that A' * P.β i) ^ 2 / P.d i
        ≤ UD * (d + x) ^ 2 := by
      rw [hUD, Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      have hdi := P.hd i
      have h1 := hpt i hi
      have h0 := hlow i hi
      have key : P.β i ^ 2 / P.d i * (d + x) ^ 2
            - (P.m i - P.that A' * P.β i) ^ 2 / P.d i
          = (((d + x) * P.β i) ^ 2 - (P.m i - P.that A' * P.β i) ^ 2) / P.d i := by
        field_simp
      rw [← sub_nonneg, key]
      refine div_nonneg ?_ hdi.le
      nlinarith [h0, h1]
    have := Fval_sub_le (P := P) h
    linarith

end OneFactor

end SparseSharpe
