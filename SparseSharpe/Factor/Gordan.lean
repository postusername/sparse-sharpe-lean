import SparseSharpe.Factor.Cover
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Теорема Гордана и дихотомия «нагрузки в одном полупространстве»

Константа покрытия нарушителей (`AnchorCover`, `Factor/Cover.lean`) — это
максимум `|U|/δ_U` по наборам `U` из `≤ k` зажатых строк, которые могут
нарушать знак **одновременно**. Какие наборы могут, решает альтернатива
Гордана–Моцкина, и отсюда дихотомия.

* **Теорема Гордана** (`gordan`, `gordan_not_both`): для конечного набора
  векторов `a_i, i ∈ U` верно ровно одно — либо все они лежат в открытом
  полупространстве (`∃u, ⟨a_i,u⟩ > 0`), либо `0` — их выпуклая комбинация.
  Доказательство — отделимость нуля от выпуклой оболочки (Хан–Банах,
  `geometric_hahn_banach_point_closed`).
* **Аффинная форма** (`motzkin`, `motzkin_not_both`): набор `U` одновременно
  нарушает знак (`∃t, ⟨a_i,t⟩ > y_i` при всех `i ∈ U`) тогда и только тогда,
  когда нет сертификата `w ≥ 0`, `Σw = 1`, `Σw_ia_i = 0`, `Σw_iy_i ≥ 0`.
  Получается из теоремы Гордана в пространстве на единицу большей размерности.

**Дихотомия** (`anchorCover_iff_no_certificate`, `anchorCover_iff_halfspace_of_nonneg`,
`anchorCover_iff_all_of_halfspace`):

* если нагрузки **всех** зажатых строк лежат в одном открытом полупространстве,
  то одновременно нарушать знак может любой набор (при любых `y`), и
  ограничение на достижимость не даёт ничего: константа покрытия — максимум по
  **всем** наборам из `≤ k` строк;
* в общем случае из максимума выпадают ровно наборы с сертификатом Моцкина
  (`w ≥ 0`, `Σw = 1`, `Σw_ia_i = 0` **и** `Σw_iy_i ≥ 0`); одного отсутствия
  общего полупространства для этого мало — нужно ещё условие на `y`
  (пример: `a = (1, −1)`, `y = (−1, −1)`, обе строки нарушают знак в `t = 0`);
* при неотрицательных `y` (неотрицательные ожидаемые доходности) условие на `y`
  выполнено автоматически, и выпадают ровно те наборы, чьи нагрузки **не** лежат
  в открытом полупространстве.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ### Линейный функционал на `ℝ^K` — это скалярное произведение -/

lemma strongDual_eq_dotp (f : StrongDual ℝ (κ → ℝ)) (x : κ → ℝ) :
    f x = dotp x (fun l => f (Pi.single l 1)) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  simp only [dotp]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h : (Pi.single l (x l) : κ → ℝ) = x l • (Pi.single l 1 : κ → ℝ) := by
    ext j
    by_cases hj : j = l
    · subst hj; simp
    · simp [hj]
  rw [h, map_smul, smul_eq_mul]

/-! ### Теорема Гордана -/

/-- **Теорема Гордана.** Либо векторы `a_i, i ∈ U`, лежат в открытом
полупространстве, либо `0` — их выпуклая комбинация. -/
theorem gordan (a : ι → κ → ℝ) (U : Finset ι) :
    (∃ u : κ → ℝ, ∀ i ∈ U, 0 < dotp (a i) u) ∨
    (∃ w : ι → ℝ, (∀ i ∈ U, 0 ≤ w i) ∧ ∑ i ∈ U, w i = 1
      ∧ ∀ l, ∑ i ∈ U, w i * a i l = 0) := by
  classical
  let v : U → (κ → ℝ) := fun x => a x
  by_cases h0 : (0 : κ → ℝ) ∈ convexHull ℝ (Set.range v)
  · right
    rw [convexHull_range_eq_exists_affineCombination] at h0
    obtain ⟨s, w, hw0, hw1, hcomb⟩ := h0
    rw [Finset.affineCombination_eq_linear_combination s v w hw1] at hcomb
    let W : ι → ℝ := fun i => if h : i ∈ U then (if (⟨i, h⟩ : U) ∈ s then w ⟨i, h⟩ else 0)
      else 0
    have hWsub : ∀ x : U, W x = if x ∈ s then w x else 0 := by
      intro x
      simp [W]
    have hsumU : ∀ g : ι → ℝ, ∑ i ∈ U, W i * g i = ∑ x ∈ s, w x * g x := by
      intro g
      rw [← Finset.sum_coe_sort U]
      simp_rw [hWsub, ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    refine ⟨W, ?_, ?_, ?_⟩
    · intro i hi
      simp only [W, hi, dite_true]
      split_ifs with hs
      · exact hw0 _ hs
      · exact le_rfl
    · have := hsumU (fun _ => 1)
      simp only [mul_one] at this
      rw [this, hw1]
    · intro l
      rw [hsumU (fun i => a i l)]
      have := congrFun hcomb l
      simpa [Finset.sum_apply, v] using this
  · left
    obtain ⟨f, u, hf0, hfu⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
      (((Set.finite_range v).isCompact_convexHull ℝ).isClosed) h0
    refine ⟨fun l => f (Pi.single l 1), fun i hi => ?_⟩
    have hmem : a i ∈ convexHull ℝ (Set.range v) :=
      subset_convexHull ℝ _ ⟨⟨i, hi⟩, rfl⟩
    have h1 := hfu _ hmem
    rw [map_zero] at hf0
    rw [strongDual_eq_dotp f (a i)] at h1
    linarith

/-- Оба случая теоремы Гордана одновременно невозможны. -/
theorem gordan_not_both (a : ι → κ → ℝ) (U : Finset ι) :
    ¬ ((∃ u : κ → ℝ, ∀ i ∈ U, 0 < dotp (a i) u) ∧
      (∃ w : ι → ℝ, (∀ i ∈ U, 0 ≤ w i) ∧ ∑ i ∈ U, w i = 1
        ∧ ∀ l, ∑ i ∈ U, w i * a i l = 0)) := by
  rintro ⟨⟨u, hu⟩, ⟨w, hw0, hw1, hw⟩⟩
  -- `Σ w_i ⟨a_i,u⟩ = ⟨Σ w_i a_i, u⟩ = 0`, но слева — положительная сумма
  have hzero : ∑ i ∈ U, w i * dotp (a i) u = 0 := by
    simp only [dotp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    have := hw l
    calc ∑ i ∈ U, w i * (a i l * u l) = (∑ i ∈ U, w i * a i l) * u l := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [this, zero_mul]
  have hne : ∃ i ∈ U, 0 < w i := by
    by_contra hcon
    push Not at hcon
    have : ∑ i ∈ U, w i ≤ 0 := Finset.sum_nonpos hcon
    linarith
  obtain ⟨i₀, hi₀, hw₀⟩ := hne
  have hpos : 0 < ∑ i ∈ U, w i * dotp (a i) u :=
    Finset.sum_pos' (fun i hi => mul_nonneg (hw0 i hi) (hu i hi).le)
      ⟨i₀, hi₀, mul_pos hw₀ (hu i₀ hi₀)⟩
  linarith

/-! ### Аффинная форма: когда набор может нарушать знак одновременно -/

/-- Строки расширенной системы в `ℝ^{K+1}`: `e = (1, 0)` и `(−y_i, a_i)`. -/
def augRow (a : ι → κ → ℝ) (y : ι → ℝ) : Option ι → Option κ → ℝ
  | none, none => 1
  | none, some _ => 0
  | some i, none => -y i
  | some i, some l => a i l

lemma dotp_augRow_none (a : ι → κ → ℝ) (y : ι → ℝ) (u : Option κ → ℝ) :
    dotp (augRow a y none) u = u none := by
  simp [dotp, Fintype.sum_option, augRow]

lemma dotp_augRow_some (a : ι → κ → ℝ) (y : ι → ℝ) (i : ι) (u : Option κ → ℝ) :
    dotp (augRow a y (some i)) u = -y i * u none + ∑ l, a i l * u (some l) := by
  simp [dotp, Fintype.sum_option, augRow]

/-- **Альтернатива Моцкина.** Либо набор `U` одновременно нарушает знак в
какой-то точке, либо есть сертификат: `w ≥ 0`, `Σw = 1`, `Σw_ia_i = 0`,
`Σw_iy_i ≥ 0`. -/
theorem motzkin (a : ι → κ → ℝ) (y : ι → ℝ) (U : Finset ι) :
    (∃ t : κ → ℝ, ∀ i ∈ U, y i - dotp (a i) t < 0) ∨
    (∃ w : ι → ℝ, (∀ i ∈ U, 0 ≤ w i) ∧ ∑ i ∈ U, w i = 1
      ∧ (∀ l, ∑ i ∈ U, w i * a i l = 0) ∧ 0 ≤ ∑ i ∈ U, w i * y i) := by
  classical
  rcases gordan (augRow a y) (insertNone U) with ⟨u, hu⟩ | ⟨w, hw0, hw1, hw⟩
  · left
    have hτ : 0 < u none := by
      have := hu none (by simp)
      rwa [dotp_augRow_none] at this
    refine ⟨fun l => u (some l) / u none, fun i hi => ?_⟩
    have h := hu (some i) (by simpa using hi)
    rw [dotp_augRow_some] at h
    have hdot : dotp (a i) (fun l => u (some l) / u none)
        = (∑ l, a i l * u (some l)) / u none := by
      simp only [dotp]
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hdot, sub_neg, lt_div_iff₀ hτ]
    linarith
  · right
    -- координаты равенства `Σ w_o b_o = 0` и нормировка
    have hnone : w none = ∑ i ∈ U, w (some i) * y i := by
      have h := hw none
      rw [Finset.sum_insertNone] at h
      simp only [augRow, mul_one, mul_neg] at h
      rw [Finset.sum_neg_distrib] at h
      linarith
    have hsome : ∀ l, ∑ i ∈ U, w (some i) * a i l = 0 := by
      intro l
      have h := hw (some l)
      rw [Finset.sum_insertNone] at h
      simpa [augRow] using h
    have hsum : w none + ∑ i ∈ U, w (some i) = 1 := by
      rw [← Finset.sum_insertNone]; exact hw1
    have hw0' : ∀ i ∈ U, 0 ≤ w (some i) := fun i hi => hw0 (some i) (by simpa using hi)
    have hwn : 0 ≤ w none := hw0 none (by simp)
    set Ssum := ∑ i ∈ U, w (some i) with hS
    -- `Σ_U w > 0`: иначе все `w_i = 0`, значит и `w_none = Σ w_i y_i = 0`
    have hSpos : 0 < Ssum := by
      rcases (Finset.sum_nonneg hw0').lt_or_eq with h | h
      · exact h
      · exfalso
        have hall : ∀ i ∈ U, w (some i) = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg hw0').mp h.symm
        have : w none = 0 := by
          rw [hnone]; exact Finset.sum_eq_zero fun i hi => by rw [hall i hi, zero_mul]
        linarith
    refine ⟨fun i => w (some i) / Ssum, fun i hi => div_nonneg (hw0' i hi) hSpos.le,
      ?_, fun l => ?_, ?_⟩
    · rw [← Finset.sum_div, div_self hSpos.ne']
    · simp_rw [div_mul_eq_mul_div]
      rw [← Finset.sum_div, hsome l, zero_div]
    · simp_rw [div_mul_eq_mul_div]
      rw [← Finset.sum_div, ← hnone]
      exact div_nonneg hwn hSpos.le

/-- Оба случая альтернативы Моцкина одновременно невозможны. -/
theorem motzkin_not_both (a : ι → κ → ℝ) (y : ι → ℝ) (U : Finset ι) :
    ¬ ((∃ t : κ → ℝ, ∀ i ∈ U, y i - dotp (a i) t < 0) ∧
      (∃ w : ι → ℝ, (∀ i ∈ U, 0 ≤ w i) ∧ ∑ i ∈ U, w i = 1
        ∧ (∀ l, ∑ i ∈ U, w i * a i l = 0) ∧ 0 ≤ ∑ i ∈ U, w i * y i)) := by
  rintro ⟨⟨t, ht⟩, ⟨w, hw0, hw1, hw, hwy⟩⟩
  have hlin : ∑ i ∈ U, w i * dotp (a i) t = 0 := by
    simp only [dotp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    calc ∑ i ∈ U, w i * (a i l * t l) = (∑ i ∈ U, w i * a i l) * t l := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [hw l, zero_mul]
  have hne : ∃ i ∈ U, 0 < w i := by
    by_contra hcon
    push Not at hcon
    have : ∑ i ∈ U, w i ≤ 0 := Finset.sum_nonpos hcon
    linarith
  obtain ⟨i₀, hi₀, hw₀⟩ := hne
  have hneg : ∑ i ∈ U, w i * (y i - dotp (a i) t) < 0 :=
    Finset.sum_neg' (fun i hi => mul_nonpos_of_nonneg_of_nonpos (hw0 i hi) (ht i hi).le)
      ⟨i₀, hi₀, mul_neg_of_pos_of_neg hw₀ (ht i₀ hi₀)⟩
  have hexp : ∑ i ∈ U, w i * (y i - dotp (a i) t)
      = ∑ i ∈ U, w i * y i - ∑ i ∈ U, w i * dotp (a i) t := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- **Одновременное нарушение ⟺ нет сертификата.** -/
theorem violable_iff_no_certificate (a : ι → κ → ℝ) (y : ι → ℝ) (U : Finset ι) :
    (∃ t : κ → ℝ, ∀ i ∈ U, y i - dotp (a i) t < 0) ↔
    ¬ ∃ w : ι → ℝ, (∀ i ∈ U, 0 ≤ w i) ∧ ∑ i ∈ U, w i = 1
      ∧ (∀ l, ∑ i ∈ U, w i * a i l = 0) ∧ 0 ≤ ∑ i ∈ U, w i * y i := by
  constructor
  · intro h hc; exact motzkin_not_both a y U ⟨h, hc⟩
  · intro h
    rcases motzkin a y U with h1 | h2
    · exact h1
    · exact absurd h2 h

/-- **Полупространство ⟹ одновременное нарушение при любых `y`.** Достаточно
уйти далеко вдоль `u`. -/
theorem violable_of_halfspace {a : ι → κ → ℝ} {U : Finset ι} {u : κ → ℝ}
    (hu : ∀ i ∈ U, 0 < dotp (a i) u) (y : ι → ℝ) :
    ∃ t : κ → ℝ, ∀ i ∈ U, y i - dotp (a i) t < 0 := by
  classical
  -- `s = 1 + Σ_U |y_i|/⟨a_i,u⟩` годится для всех `i` сразу
  set s : ℝ := 1 + ∑ i ∈ U, |y i| / dotp (a i) u with hs
  refine ⟨s • u, fun i hi => ?_⟩
  rw [dotp_smul]
  have hpos := hu i hi
  have hterm : |y i| / dotp (a i) u ≤ ∑ j ∈ U, |y j| / dotp (a j) u :=
    Finset.single_le_sum (f := fun j => |y j| / dotp (a j) u)
      (fun j hj => div_nonneg (abs_nonneg _) (hu j hj).le) hi
  have hs1 : |y i| / dotp (a i) u + 1 ≤ s := by rw [hs]; linarith
  have hmul : (|y i| / dotp (a i) u + 1) * dotp (a i) u ≤ s * dotp (a i) u :=
    mul_le_mul_of_nonneg_right hs1 hpos.le
  have heq : (|y i| / dotp (a i) u + 1) * dotp (a i) u = |y i| + dotp (a i) u := by
    field_simp
  linarith [le_abs_self (y i)]

/-- **При `y ≥ 0` одновременное нарушение ⟺ полупространство.** Направление «⟹»
тривиально: сама точка нарушения и есть нужное направление. -/
theorem violable_iff_halfspace_of_nonneg {a : ι → κ → ℝ} {y : ι → ℝ} {U : Finset ι}
    (hy : ∀ i ∈ U, 0 ≤ y i) :
    (∃ t : κ → ℝ, ∀ i ∈ U, y i - dotp (a i) t < 0) ↔
      ∃ u : κ → ℝ, ∀ i ∈ U, 0 < dotp (a i) u := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, fun i hi => by linarith [ht i hi, hy i hi]⟩
  · rintro ⟨u, hu⟩
    exact violable_of_halfspace hu y

/-! ### Дихотомия для константы покрытия -/

variable [DecidableEq ι] {a : ι → κ → ℝ} {y : ι → ℝ} {cl : ι → Bool} {S base : Finset ι}

/-- Константа покрытия — это ровно максимум по одновременно нарушаемым
наборам (переписывание определения: точка нарушения существует, и больше от неё
ничего не требуется). -/
theorem anchorCover_iff_violable {k : ℕ} {c : ℝ} :
    AnchorCover a y cl S base k c ↔
      ∀ U ⊆ S, U.card ≤ k → (∀ j ∈ U, cl j) →
        (∃ t' : κ → ℝ, ∀ j ∈ U, y j - dotp (a j) t' < 0) →
        ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ (∀ v : κ → ℝ, d * gram a U v ≤ (1 - d) * gram a base v)
          ∧ (U.card : ℝ) ≤ c * d := by
  constructor
  · rintro h U hUS hUk hcl ⟨t', ht'⟩
    exact h t' U hUS hUk fun j hj => ⟨hcl j hj, ht' j hj⟩
  · intro h t' U hUS hUk hUv
    exact h U hUS hUk (fun j hj => (hUv j hj).1) ⟨t', fun j hj => (hUv j hj).2⟩

/-- **Дихотомия в общем виде (любые `y`).** Константа покрытия — максимум по
наборам **без** сертификата Моцкина; наборы с сертификатом из неё выпадают. -/
theorem anchorCover_iff_no_certificate {k : ℕ} {c : ℝ} :
    AnchorCover a y cl S base k c ↔
      ∀ U ⊆ S, U.card ≤ k → (∀ j ∈ U, cl j) →
        (¬ ∃ w : ι → ℝ, (∀ i ∈ U, 0 ≤ w i) ∧ ∑ i ∈ U, w i = 1
          ∧ (∀ l, ∑ i ∈ U, w i * a i l = 0) ∧ 0 ≤ ∑ i ∈ U, w i * y i) →
        ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ (∀ v : κ → ℝ, d * gram a U v ≤ (1 - d) * gram a base v)
          ∧ (U.card : ℝ) ≤ c * d := by
  rw [anchorCover_iff_violable]
  refine forall_congr' fun U => ?_
  simp only [violable_iff_no_certificate]

/-- **Дихотомия при неотрицательных `y`.** Из максимума выпадают ровно те
наборы, чьи нагрузки не лежат в открытом полупространстве. -/
theorem anchorCover_iff_halfspace_of_nonneg {k : ℕ} {c : ℝ}
    (hy : ∀ i ∈ S, cl i → 0 ≤ y i) :
    AnchorCover a y cl S base k c ↔
      ∀ U ⊆ S, U.card ≤ k → (∀ j ∈ U, cl j) →
        (∃ u : κ → ℝ, ∀ i ∈ U, 0 < dotp (a i) u) →
        ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ (∀ v : κ → ℝ, d * gram a U v ≤ (1 - d) * gram a base v)
          ∧ (U.card : ℝ) ≤ c * d := by
  rw [anchorCover_iff_violable]
  constructor
  · intro h U hUS hUk hcl hhalf
    exact h U hUS hUk hcl
      ((violable_iff_halfspace_of_nonneg fun i hi => hy i (hUS hi) (hcl i hi)).mpr hhalf)
  · intro h U hUS hUk hcl hviol
    exact h U hUS hUk hcl
      ((violable_iff_halfspace_of_nonneg fun i hi => hy i (hUS hi) (hcl i hi)).mp hviol)

/-- **Предел дихотомии: нагрузки в одном полупространстве — выигрыша нет.**
Если все зажатые строки вселенной лежат в одном открытом полупространстве, то
при **любых** `y` одновременно нарушать знак может любой набор, и константа
покрытия — максимум по **всем** наборам из `≤ k` зажатых строк. -/
theorem anchorCover_iff_all_of_halfspace {k : ℕ} {c : ℝ} {u : κ → ℝ}
    (hu : ∀ i ∈ S, cl i → 0 < dotp (a i) u) :
    AnchorCover a y cl S base k c ↔
      ∀ U ⊆ S, U.card ≤ k → (∀ j ∈ U, cl j) →
        ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ (∀ v : κ → ℝ, d * gram a U v ≤ (1 - d) * gram a base v)
          ∧ (U.card : ℝ) ≤ c * d := by
  rw [anchorCover_iff_violable]
  constructor
  · intro h U hUS hUk hcl
    exact h U hUS hUk hcl (violable_of_halfspace (fun i hi => hu i (hUS hi) (hcl i hi)) y)
  · intro h U hUS hUk hcl _
    exact h U hUS hUk hcl

/-! ### Непустота: обе стороны дихотомии на одном примере

`K = 1`, две строки с нагрузками `+1` и `−1` и `y = (1, 1)`: нагрузки **не**
лежат в одном полупространстве, сертификат `w = (1/2, 1/2)` (`Σw_ia_i = 0`,
`Σw_iy_i = 1 ≥ 0`), и пара одновременно знак не нарушает
(`t > 1` и `−t > 1` несовместны). Каждая строка по отдельности нарушает.
А у пары `(+1, +2)` полупространство есть (`u = 1`), и она нарушает знак
одновременно при любых `y`. -/

private def aG : Fin 2 → Fin 1 → ℝ := fun i _ => if i = 0 then 1 else -1
private def yG : Fin 2 → ℝ := fun _ => 1

example : ¬ ∃ t : Fin 1 → ℝ, ∀ i ∈ (Finset.univ : Finset (Fin 2)),
    yG i - dotp (aG i) t < 0 := by
  rw [violable_iff_no_certificate, not_not]
  refine ⟨fun _ => 1 / 2, fun _ _ => by norm_num, ?_, fun l => ?_, ?_⟩
  · simp
  · simp [Fin.sum_univ_two, aG]
  · simp [yG]

example : ∃ t : Fin 1 → ℝ, ∀ i ∈ ({0} : Finset (Fin 2)), yG i - dotp (aG i) t < 0 :=
  ⟨fun _ => 2, fun i hi => by
    rw [Finset.mem_singleton] at hi; subst hi; simp [dotp, aG, yG]⟩

example (y : Fin 2 → ℝ) : ∃ t : Fin 1 → ℝ, ∀ i ∈ (Finset.univ : Finset (Fin 2)),
    y i - dotp ((fun i _ => if i = 0 then 1 else 2 : Fin 2 → Fin 1 → ℝ) i) t < 0 :=
  violable_of_halfspace (u := fun _ => 1) (fun i _ => by fin_cases i <;> simp [dotp]) y

end SparseSharpe.Factor
