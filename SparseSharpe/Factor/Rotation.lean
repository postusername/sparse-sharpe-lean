import SparseSharpe.Factor.ActiveFilter

set_option linter.style.header false

/-!
# Теорема V: ключ из моментов не может определять значение long-only

Три сессии подряд полнота FPTAS для long-only упиралась в одно и то же:
у набора-носителя оптимума `A` находился набор `R` с **тем же ключом динамики**
`(Q_t, mom_t, gram)`, допущенный в том же узле, но с много меньшим значением
long-only. Этот файл объясняет, почему так происходит всегда, а не по
случайности.

**Источник — поворот пространства индексов.** Пусть `O` — ортогональная матрица
на множестве индексов активов, и пусть новые строки и правые части суть
линейные комбинации старых:

    a'_i = Σ_l O_{il} a_l ,    y'_i = Σ_l O_{il} y_l .

Тогда (теоремы ниже) при **любых** `t` и `v`

    gram a' v = gram a v ,   mom a' y' t v = mom a y t v ,   φ_{a'y'}(t) = φ_{ay}(t) ,

то есть совпадают **все** величины, из которых состоит состояние динамики, — и
совпадают они не только в узле, а в каждой точке. Отсюда же одна и та же
неподвижная точка (`IsNormal_rot`).

Причина проста: `gram`, `mom` и `φ` — это скалярные произведения векторов
`(⟨a_i,v⟩)_i` и `(y_i − ⟨a_i,t⟩)_i` в пространстве индексов, а ортогональное
преобразование скалярные произведения сохраняет. Иначе говоря, состояние
`(Q, M, Κ)` — это **полный набор инвариантов порядка ≤ 2** пары «строки, невязки»
относительно `O(m)`.

**А значение long-only инвариантом не является:** `psiC` строится из
**положительных частей** невязок, а положительная часть с поворотами не
коммутирует. Формальный свидетель — `rot_changes_psiC` (в конце файла):
отражение `O = [[3/5, 4/5], [4/5, −3/5]]`, строки `a = (3, 4)`, правые части
`y = (s, 0)`, `s > 0`. У исходного набора `min psiC = 0`, у повёрнутого
`psiC ≥ 16s²/25` всюду, а `gram`, `mom` и `φ` совпадают во всех точках.
Родственные, но не «поворотные» контрпримеры — `Factor/Ex135.lean` (потеря
`≥ 695/221` при сколь угодно малом запасе) и `Factor/Sticky.lean` (потеря почти
всего значения при сколь угодно малом зазоре узла).

> **Вывод (Теорема V).** Никакой ключ динамики, являющийся функцией от
> `(Q_t, mom_t, gram)`, не может определять значение long-only: существуют два
> набора с тождественно совпадающими `Q`, `mom` и `gram` (а значит и с
> совпадающим ключом при любом округлении), у одного из которых `min psiC = 0`,
> а у другого `psiC ≥ 16s²/25 > 0` во всех точках, при любом `s > 0`
> (`rot_changes_psiC`).

Что из этого следует практически, сказано в `theory_note_v6.md`, §5.6:
доказывать полноту «по одному узлу и одной корзине» нельзя в принципе; либо
состояние динамики надо расширить величиной, не инвариантной относительно
`O(m)`, либо доказательство обязано существенно пользоваться максимумом по
всем узлам (численно алгоритм именно так и выживает: `code/e22_adversarial.py`).
-/

namespace SparseSharpe.Factor

open Finset Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- Повёрнутые строки: `a'_i = Σ_l O_{il} a_l`. -/
noncomputable def rotRows (O : Matrix ι ι ℝ) (a : ι → κ → ℝ) : ι → κ → ℝ :=
  fun i j => ∑ l, O i l * a l j

/-- Повёрнутые правые части: `y'_i = Σ_l O_{il} y_l`. -/
noncomputable def rotTargets (O : Matrix ι ι ℝ) (y : ι → ℝ) : ι → ℝ :=
  fun i => ∑ l, O i l * y l

variable {O : Matrix ι ι ℝ} {a : ι → κ → ℝ} {y : ι → ℝ} {t v : κ → ℝ}

lemma dotp_rotRows (O : Matrix ι ι ℝ) (a : ι → κ → ℝ) (v : κ → ℝ) (i : ι) :
    dotp (rotRows O a i) v = ∑ l, O i l * dotp (a l) v := by
  simp only [dotp, rotRows, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Ортогональность сохраняет скалярные произведения в пространстве индексов.**
Из `Oᵀ O = 1` следует `Σ_i (Ox)_i (Oz)_i = Σ_i x_i z_i`. -/
lemma sum_rot_mul (hO : Oᵀ * O = 1) (x z : ι → ℝ) :
    (∑ i, (∑ l, O i l * x l) * ∑ l, O i l * z l) = ∑ i, x i * z i := by
  have hcol : ∀ l l' : ι, (∑ i, O i l * O i l') = if l = l' then (1:ℝ) else 0 := by
    intro l l'
    have := congrFun (congrFun hO l) l'
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using this
  calc (∑ i, (∑ l, O i l * x l) * ∑ l, O i l * z l)
      = ∑ i, ∑ l, ∑ l', (O i l * O i l') * (x l * z l') := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => by ring
    _ = ∑ l, ∑ l', (∑ i, O i l * O i l') * (x l * z l') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l' _ => by rw [← Finset.sum_mul]
    _ = ∑ l, x l * z l := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_congr rfl (fun l' _ => by rw [hcol l l'])]
        simp

/-- **Форма Грама не меняется при повороте индексов.** -/
theorem gram_rot (hO : Oᵀ * O = 1) (a : ι → κ → ℝ) (v : κ → ℝ) :
    gram (rotRows O a) Finset.univ v = gram a Finset.univ v := by
  simp only [gram, sq]
  rw [Finset.sum_congr rfl (fun i _ => by rw [dotp_rotRows])]
  exact sum_rot_mul hO (fun l => dotp (a l) v) (fun l => dotp (a l) v)

/-- **Первый момент не меняется при повороте индексов — в любой точке `t`.** -/
theorem mom_rot (hO : Oᵀ * O = 1) (a : ι → κ → ℝ) (y : ι → ℝ) (t v : κ → ℝ) :
    mom (rotRows O a) (rotTargets O y) Finset.univ t v = mom a y Finset.univ t v := by
  have hres : ∀ i, rotTargets O y i - dotp (rotRows O a i) t
      = ∑ l, O i l * (y l - dotp (a l) t) := by
    intro i
    rw [rotTargets, dotp_rotRows, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [mom]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hres i, dotp_rotRows])]
  exact sum_rot_mul hO (fun l => y l - dotp (a l) t) (fun l => dotp (a l) v)

/-- **Значение `φ` не меняется при повороте индексов — в любой точке `t`.**
В частности совпадают `Q` в узле и безусловное значение `F`. -/
theorem phi_rot (hO : Oᵀ * O = 1) (a : ι → κ → ℝ) (y : ι → ℝ) (t : κ → ℝ) :
    phi (rotRows O a) (rotTargets O y) Finset.univ t = phi a y Finset.univ t := by
  have hres : ∀ i, dotp (rotRows O a i) t - rotTargets O y i
      = ∑ l, O i l * (dotp (a l) t - y l) := by
    intro i
    rw [rotTargets, dotp_rotRows, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [phi, sq]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hres i])]
  exact sum_rot_mul hO (fun l => dotp (a l) t - y l) (fun l => dotp (a l) t - y l)

/-- **Неподвижная точка у повёрнутого набора та же.** -/
theorem isNormal_rot (hO : Oᵀ * O = 1) {th : κ → ℝ}
    (h : IsNormal a y Finset.univ th) :
    IsNormal (rotRows O a) (rotTargets O y) Finset.univ th := fun v => by
  rw [mom_rot hO]; exact h v

/-- **Теорема V, абстрактная часть.** Поворот индексов сохраняет всё состояние
динамики целиком и во всех точках сразу: форму Грама, первый момент, значение
`φ` и неподвижную точку. Значит два таких набора неотличимы никаким ключом,
построенным из `(Q_t, mom_t, gram)`, при любом округлении. -/
theorem rot_preserves_state (hO : Oᵀ * O = 1) (a : ι → κ → ℝ) (y : ι → ℝ) :
    (∀ v, gram (rotRows O a) Finset.univ v = gram a Finset.univ v)
    ∧ (∀ t v, mom (rotRows O a) (rotTargets O y) Finset.univ t v
                = mom a y Finset.univ t v)
    ∧ (∀ t, phi (rotRows O a) (rotTargets O y) Finset.univ t = phi a y Finset.univ t)
    ∧ (∀ th, IsNormal a y Finset.univ th →
              IsNormal (rotRows O a) (rotTargets O y) Finset.univ th) :=
  ⟨fun v => gram_rot hO a v, fun t v => mom_rot hO a y t v,
   fun t => phi_rot hO a y t, fun _ h => isNormal_rot hO h⟩

/-! ### Непустота: повороты, не равные тождественному, существуют

Иначе утверждение было бы бессодержательным: при `O = 1` всё совпадает даром. -/

/-- Поворот на `−π/2` в двухэлементном пространстве индексов ортогонален и
меняет набор по существу: строки переставляются со сменой знака у одной из них. -/
example :
    (Matrix.of ![![(0:ℝ), 1], ![-1, 0]])ᵀ * Matrix.of ![![(0:ℝ), 1], ![-1, 0]]
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Тот же поворот действительно меняет строки: из `a = (1, 0)` получается
`a' = (0, −1)`. Значит `rotRows` — не тождественное отображение. -/
example :
    rotRows (Matrix.of ![![(0:ℝ), 1], ![-1, 0]])
        (fun (i : Fin 2) (_ : Fin 1) => (![(1:ℝ), 0]) i)
      ≠ (fun (i : Fin 2) (_ : Fin 1) => (![(1:ℝ), 0]) i) := by
  intro h
  have hh := congrFun (congrFun h 0) 0
  simp [rotRows, Fin.sum_univ_two] at hh

/-! ### Свидетель: поворот меняет long-only значение

Отражение `O = [[3/5, 4/5], [4/5, −3/5]]` ортогонально (`OᵀO = 1`, всё
рационально). Строки `a = (3, 4)` (`K = 1`) переходят в `a' = (5, 0)`, правые
части `y = (s, 0)` — в `y' = (3s/5, 4s/5)`. У исходного набора обе нагрузки
положительны, и в точке `t = s/3` обе невязки неположительны: `psiC = 0`. У
повёрнутого вторая строка имеет нулевую нагрузку и правую часть `4s/5`, поэтому
её зажатая невязка равна `4s/5` в **любой** точке: `psiC ≥ 16s²/25`. При этом
`gram`, `mom`, `φ` и неподвижная точка у двух наборов совпадают всюду
(`rot_preserves_state`). -/

/-- Отражение `[[3/5, 4/5], [4/5, −3/5]]`. -/
noncomputable def reflO : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![![3/5, 4/5], ![4/5, -3/5]]

/-- Строки `a = (3, 4)` при `K = 1`. -/
def rowsV : Fin 2 → Fin 1 → ℝ := fun i _ => if i = 0 then 3 else 4

/-- Правые части `y = (s, 0)`. -/
def targetsV (s : ℝ) : Fin 2 → ℝ := fun i => if i = 0 then s else 0

lemma reflO_orth : reflOᵀ * reflO = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflO, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- **Теорема V, свидетель.** Поворот сохраняет всё состояние динамики, но
long-only значение меняет: у исходного набора оно `0`, у повёрнутого не меньше
`16s²/25 > 0` в любой точке (при `s > 0`). -/
theorem rot_changes_psiC {s : ℝ} (hs : 0 < s) :
    reflOᵀ * reflO = 1
    ∧ (∀ v, gram (rotRows reflO rowsV) Finset.univ v = gram rowsV Finset.univ v)
    ∧ (∀ t v, mom (rotRows reflO rowsV) (rotTargets reflO (targetsV s)) Finset.univ t v
                = mom rowsV (targetsV s) Finset.univ t v)
    ∧ (∀ t, phi (rotRows reflO rowsV) (rotTargets reflO (targetsV s)) Finset.univ t
                = phi rowsV (targetsV s) Finset.univ t)
    ∧ psiC rowsV (targetsV s) (fun _ => true) Finset.univ (fun _ => s / 3) = 0
    ∧ ∀ t, 16 * s ^ 2 / 25
        ≤ psiC (rotRows reflO rowsV) (rotTargets reflO (targetsV s)) (fun _ => true)
            Finset.univ t := by
  obtain ⟨h1, h2, h3, _⟩ := rot_preserves_state reflO_orth rowsV (targetsV s)
  refine ⟨reflO_orth, h1, h2, h3, ?_, fun t => ?_⟩
  · have e0 : targetsV s 0 - dotp (rowsV 0) (fun _ => s / 3) = 0 := by
      simp [targetsV, dotp, rowsV]; ring
    have e1 : targetsV s 1 - dotp (rowsV 1) (fun _ => s / 3) ≤ 0 := by
      simp [targetsV, dotp, rowsV]; linarith
    simp only [psiC, resC, Fin.sum_univ_two, ite_true, e0, max_eq_right e1, max_self]
    norm_num
  · have hrow1 : ∀ j, rotRows reflO rowsV 1 j = 0 := by
      intro j
      simp [rotRows, reflO, rowsV, Fin.sum_univ_two]
      norm_num
    have hy1 : rotTargets reflO (targetsV s) 1 = 4 * s / 5 := by
      simp [rotTargets, reflO, targetsV]; ring
    have hdot1 : dotp (rotRows reflO rowsV 1) t = 0 := by
      simp [dotp, hrow1]
    have hres1 : resC (rotRows reflO rowsV) (rotTargets reflO (targetsV s)) (fun _ => true) 1 t
        = 4 * s / 5 := by
      simp only [resC, ite_true, hdot1, hy1, sub_zero]
      exact max_eq_left (by linarith)
    have hsum : psiC (rotRows reflO rowsV) (rotTargets reflO (targetsV s)) (fun _ => true)
        Finset.univ t
        = resC (rotRows reflO rowsV) (rotTargets reflO (targetsV s)) (fun _ => true) 0 t ^ 2
          + (4 * s / 5) ^ 2 := by
      rw [psiC, Fin.sum_univ_two, hres1]
    rw [hsum]
    nlinarith [sq_nonneg (resC (rotRows reflO rowsV) (rotTargets reflO (targetsV s))
      (fun _ => true) 0 t)]

end SparseSharpe.Factor
