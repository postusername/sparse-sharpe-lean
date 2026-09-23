import SparseSharpe.Factor.State
import SparseSharpe.Factor.Rotation

set_option linter.style.header false

/-!
# Обогащённый ключ: две аддитивные величины сверх моментов

Теорема V (`Factor/Rotation.lean`) говорит: состояние `(Q_t, M_t, Κ_t)` — полный
набор инвариантов порядка `≤ 2` пары «строки, невязки» относительно поворотов
пространства индексов, а значение long-only таким инвариантом не является.
Значит ключ динамики обязан содержать величину, **не** инвариантную
относительно `O(m)`.

Самые дешёвые такие величины — моменты первого порядка самого облака точек:

    sumCf(U)_l = Σ_{i∈U} c_{il}          (координаты Крамера строк),
    sumRes(U)  = Σ_{i∈U} (y_i − ⟨a_i,t⟩) (невязки в узле).

Обе **аддитивны** по набору (значит годятся для динамики) и обе ограничены
без величин входа: `|sumCf| ≤ |U|` по правилу Крамера (`abs_cf_le_one`), а
`|sumRes| ≤ √(|U|·φ_U(t))` по Коши–Буняковскому — ровно та же форма, что у
`abs_momK_le`, то есть диапазон снова выражается через `Q`, а не через `m`, `B`,
`d`, `Σ_f`. Поэтому добавление этих `K+1` координат к ключу стоит полиномиально
много корзин и не ломает ни одну из оценок §6–§7 заметки.

Что это даёт. Для `sumRes` формально (`sumRes_rot`, `sumRes_rot_invariant_iff`,
`colsum_iff_rowsum`): при повороте `O` сумма невязок переходит в
`Σ_l (Σ_i O_il)·r_l`, и она сохраняется **при всех** правых частях тогда и только
тогда, когда у `O` все суммы по столбцам равны `1`, что для ортогональной `O`
равносильно `O𝟙 = 𝟙`. То есть среди поворотов добавленная координата оставляет
неразличимыми ровно стабилизатор вектора из единиц (подгруппу, изоморфную
`O(m−1)`); перестановки в него входят, и они же сохраняют значение long-only.
Для `sumCf` формально доказаны только аддитивность и диапазон: как она
преобразуется при повороте, здесь не формализовано (вместе со строками
поворачивается и базис `T`). Численно (`code/e24_stabilizer.py`, не Lean):
худшее отношение `F_LO(R)/F_LO(A*)` среди допущенных двойников растёт с
`0.000000` до `1.000000` при `m = 2, 3` и до `0.944` при `m = 4`.

**Чего это НЕ даёт.** Подгруппа `O(m−1)` при `m ≥ 4` всё ещё нетривиальна, и
каждый добавленный порядок моментов срезает лишь одну размерность. Поэтому
постоянного (по `k`) числа моментов не хватает, и вопрос «сколько нужно и нет
ли более умного неинварианта» остаётся открытым — `theory_note_v6.md`, §5.5.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {S : Finset ι} {T : κ → ι} {t : κ → ℝ}

/-- Первый момент строк в координатах максимально-объёмной `K`-ки. -/
noncomputable def sumCf (a : ι → κ → ℝ) (T : κ → ι) (U : Finset ι) : κ → ℝ :=
  fun l => ∑ i ∈ U, cf a T i l

/-- Первый момент невязок в узле. -/
noncomputable def sumRes (a : ι → κ → ℝ) (y : ι → ℝ) (U : Finset ι) (t : κ → ℝ) : ℝ :=
  ∑ i ∈ U, (y i - dotp (a i) t)

/-! ### Аддитивность: обе величины годятся для динамики -/

lemma sumCf_insert {U : Finset ι} {i : ι} (hi : i ∉ U) (l : κ) :
    sumCf a T (insert i U) l = sumCf a T U l + cf a T i l := by
  simp [sumCf, Finset.sum_insert hi, add_comm]

lemma sumRes_insert {U : Finset ι} {i : ι} (hi : i ∉ U) :
    sumRes a y (insert i U) t = sumRes a y U t + (y i - dotp (a i) t) := by
  simp [sumRes, Finset.sum_insert hi, add_comm]

/-! ### Диапазоны: в них нет величин входа -/

/-- Диапазон по `sumCf`: не больше `|U|`, потому что коэффициенты Крамера
максимально-объёмной `K`-ки не превосходят единицы. -/
theorem abs_sumCf_le (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0)
    {U : Finset ι} (hU : U ⊆ S) (l : κ) : |sumCf a T U l| ≤ (U.card : ℝ) := by
  calc |sumCf a T U l| ≤ ∑ i ∈ U, |cf a T i l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ U, (1:ℝ) := Finset.sum_le_sum fun i hi => abs_cf_le_one hmax hdet (hU hi) l
    _ = (U.card : ℝ) := by simp

omit [DecidableEq ι] [DecidableEq κ] in
/-- Диапазон по `sumRes`: `|Σ r_i| ≤ √(|U|·φ_U(t))` — та же форма, что у
`abs_momK_le`, то есть через `Q`, а не через величины входа. -/
theorem abs_sumRes_le (U : Finset ι) (t : κ → ℝ) :
    |sumRes a y U t| ≤ Real.sqrt ((U.card : ℝ) * phi a y U t) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq U (fun _ => (1:ℝ))
    (fun i => y i - dotp (a i) t)
  have hone : ∑ _i ∈ U, (1:ℝ) ^ 2 = (U.card : ℝ) := by simp
  have hphi : ∑ i ∈ U, (y i - dotp (a i) t) ^ 2 = phi a y U t := by
    rw [phi]; exact Finset.sum_congr rfl fun i _ => by ring
  have hsq : (sumRes a y U t) ^ 2 ≤ (U.card : ℝ) * phi a y U t := by
    calc (sumRes a y U t) ^ 2
        = (∑ i ∈ U, (1:ℝ) * (y i - dotp (a i) t)) ^ 2 := by
          rw [sumRes]; exact congrArg (· ^ 2) (Finset.sum_congr rfl fun i _ => by ring)
      _ ≤ (∑ _i ∈ U, (1:ℝ) ^ 2) * ∑ i ∈ U, (y i - dotp (a i) t) ^ 2 := hcs
      _ = (U.card : ℝ) * phi a y U t := by rw [hone, hphi]
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hsq

omit [DecidableEq ι] [DecidableEq κ] in
/-- Та же оценка через объемлющий набор: годится сразу для всех префиксов. -/
theorem abs_sumRes_le_of_subset {U : Finset ι} (hU : U ⊆ S) (t : κ → ℝ) :
    |sumRes a y U t| ≤ Real.sqrt ((S.card : ℝ) * phi a y S t) := by
  refine le_trans (abs_sumRes_le U t) (Real.sqrt_le_sqrt ?_)
  have h1 : (U.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hU
  have h2 : phi a y U t ≤ phi a y S t := phi_mono hU t
  have h3 : (0:ℝ) ≤ phi a y U t := phi_nonneg a y U t
  have h4 : (0:ℝ) ≤ (U.card : ℝ) := by positivity
  nlinarith

/-! ### Эти величины действительно не инвариантны относительно поворотов

Иначе добавлять их было бы бессмысленно: Теорема V применялась бы по-прежнему. -/

/-- Поворот на `−π/2` в двухэлементном пространстве индексов меняет сумму
правых частей: из `(1, 0)` получается `(0, −1)`, суммы `1` и `−1`. -/
example :
    (∑ i, rotTargets (Matrix.of ![![(0:ℝ), 1], ![-1, 0]]) (![(1:ℝ), 0]) i)
      ≠ ∑ i, (![(1:ℝ), 0]) i := by
  simp [rotTargets, Fin.sum_univ_two]
  norm_num

/-! ### Как `sumRes` преобразуется при повороте: стабилизатор вектора из единиц -/

section Rot

variable [Fintype ι] {O : Matrix ι ι ℝ}

omit [DecidableEq κ] in
/-- **Закон преобразования.** При повороте индексов сумма невязок переходит в
`Σ_l (Σ_i O_il)·r_l`. -/
theorem sumRes_rot (O : Matrix ι ι ℝ) (a : ι → κ → ℝ) (y : ι → ℝ) (t : κ → ℝ) :
    sumRes (rotRows O a) (rotTargets O y) Finset.univ t
      = ∑ l, (∑ i, O i l) * (y l - dotp (a l) t) := by
  have hres : ∀ i, rotTargets O y i - dotp (rotRows O a i) t
      = ∑ l, O i l * (y l - dotp (a l) t) := by
    intro i
    rw [rotTargets, dotp_rotRows, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [sumRes]
  rw [Finset.sum_congr rfl (fun i _ => hres i), Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => by rw [Finset.sum_mul]

omit [DecidableEq κ] in
/-- **Стабилизатор.** Сумма невязок сохраняется при повороте для **всех**
правых частей тогда и только тогда, когда у `O` все суммы по столбцам равны `1`. -/
theorem sumRes_rot_invariant_iff (O : Matrix ι ι ℝ) (a : ι → κ → ℝ) (t : κ → ℝ) :
    (∀ y : ι → ℝ, sumRes (rotRows O a) (rotTargets O y) Finset.univ t
        = sumRes a y Finset.univ t) ↔ ∀ l, ∑ i, O i l = 1 := by
  constructor
  · intro h l₀
    -- правые части, у которых вектор невязок — орт `e_{l₀}`
    have h0 := h (fun j => (if j = l₀ then 1 else 0) + dotp (a j) t)
    rw [sumRes_rot] at h0
    simp only [sumRes, add_sub_cancel_right] at h0
    simpa using h0
  · intro hcol y
    rw [sumRes_rot]
    simp only [hcol, one_mul, sumRes]

open Matrix in
/-- Для ортогональной `O` условие на суммы по столбцам (`Oᵀ𝟙 = 𝟙`) равносильно
условию на суммы по строкам (`O𝟙 = 𝟙`): это и есть стабилизатор вектора из
единиц. -/
theorem colsum_iff_rowsum (hO : Oᵀ * O = 1) :
    (∀ l, ∑ i, O i l = 1) ↔ ∀ i, ∑ l, O i l = 1 := by
  have hO' : O * Oᵀ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl ι)).mp hO
  have hrow : ∀ i j, (∑ l, O i l * O j l) = if i = j then (1:ℝ) else 0 := by
    intro i j
    have := congrFun (congrFun hO' i) j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using this
  have hcolm : ∀ l m, (∑ i, O i l * O i m) = if l = m then (1:ℝ) else 0 := by
    intro l m
    have := congrFun (congrFun hO l) m
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using this
  constructor
  · intro hc i
    calc ∑ l, O i l = ∑ l, O i l * ∑ j, O j l := by simp [hc]
      _ = ∑ j, ∑ l, O i l * O j l := by
          simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
      _ = 1 := by simp [hrow]
  · intro hr l
    calc ∑ i, O i l = ∑ i, O i l * ∑ m, O i m := by simp [hr]
      _ = ∑ m, ∑ i, O i l * O i m := by
          simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
      _ = 1 := by simp [hcolm]

/-- Непустота: у поворота на `−π/2` суммы по столбцам не равны `1`, и сумма
невязок действительно меняется при некоторых правых частях. -/
example : ¬ ∀ y : Fin 2 → ℝ,
    sumRes (rotRows (Matrix.of ![![(0:ℝ), 1], ![-1, 0]]) (fun (_ : Fin 2) (_ : Fin 1) => (0:ℝ)))
      (rotTargets (Matrix.of ![![(0:ℝ), 1], ![-1, 0]]) y) Finset.univ (fun _ => 0)
      = sumRes (fun (_ : Fin 2) (_ : Fin 1) => (0:ℝ)) y Finset.univ (fun _ => 0) := by
  rw [sumRes_rot_invariant_iff]
  intro h
  have := h 0
  simp [Fin.sum_univ_two] at this
  norm_num at this

end Rot

end SparseSharpe.Factor
