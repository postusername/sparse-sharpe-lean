import SparseSharpe.Factor.GuaranteeBlock
import Mathlib.Combinatorics.SetFamily.Shatter

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Достижимые множества нарушителей: их `O(M^K)`, и максимум по ним — константа покрытия

Нарушители в точке `t` — строки с `y_i − ⟨a_i,t⟩ < 0`. Множество
`W(t) = {i : y_i − ⟨a_i,t⟩ < 0}` — это знаковый паттерн набора из `M`
аффинных гиперплоскостей `⟨a_i,t⟩ = y_i` в `ℝ^K`. Таких паттернов не `2^M`:

> **Теорема** (`card_reachSets_le`, `card_reachSets_le_pow`). Достижимых множеств
> нарушителей не больше `Σ_{j≤K} C(M, j) ≤ (M+1)^K`.

Доказательство — через лемму Сауэра–Шелаха (в Mathlib:
`Finset.card_shatterer_le_sum_vcDim`) и оценку размерности
Вапника–Червоненкиса `vcDim ≤ K` (`vcDim_reachSets_le`): любые `K+1` строк
линейно зависимы, `Σ g_i a_i = 0`, поэтому `Σ g_i (y_i − ⟨a_i,t⟩)` не зависит от
`t`, и паттерны «нарушают ровно строки с `g_i > 0`» и «нарушают ровно строки с
`g_i < 0`» требуют от этой константы разных знаков — оба не реализуются
(`not_shatters_reachSets`). Оценка верна при любых данных, включая
вырожденные расположения гиперплоскостей (паттерны на гранях тоже считаются).

Покрытие нарушителей по этому семейству (`anchorCover_of_reachSets`,
`anchorCover_of_reachSets_sysVar`) даёт константу `c` как максимум по
`O(M^K)` множествам — это и есть величина, которую спецификация подставляет
вместо `γ`. Как перечислять семейство — `code/SPEC_LO_K3.md`, §9.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-! ### Семейство и его размерность Вапника–Червоненкиса -/

/-- Нарушители в точке `t`. -/
noncomputable def violAt (a : ι → κ → ℝ) (y : ι → ℝ) (t : κ → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => y i - dotp (a i) t < 0)

lemma mem_violAt {a : ι → κ → ℝ} {y : ι → ℝ} {t : κ → ℝ} {i : ι} :
    i ∈ violAt a y t ↔ y i - dotp (a i) t < 0 := by
  simp [violAt]

open Classical in
/-- Достижимые множества нарушителей. -/
noncomputable def reachSets (a : ι → κ → ℝ) (y : ι → ℝ) : Finset (Finset ι) :=
  Finset.univ.filter (fun W => ∃ t : κ → ℝ, violAt a y t = W)

lemma mem_reachSets {a : ι → κ → ℝ} {y : ι → ℝ} {W : Finset ι} :
    W ∈ reachSets a y ↔ ∃ t : κ → ℝ, violAt a y t = W := by
  simp [reachSets]

lemma violAt_mem_reachSets (a : ι → κ → ℝ) (y : ι → ℝ) (t : κ → ℝ) :
    violAt a y t ∈ reachSets a y :=
  mem_reachSets.mpr ⟨t, rfl⟩

/-- `Σ_{i∈s} g_i (y_i − ⟨a_i,t⟩)` не зависит от `t`, если `Σ g_i a_i = 0`. -/
lemma sum_res_eq_of_rel {a : ι → κ → ℝ} {y : ι → ℝ} {s : Finset ι} {G : ι → ℝ}
    (hG : ∀ l, ∑ i ∈ s, G i * a i l = 0) (t : κ → ℝ) :
    ∑ i ∈ s, G i * (y i - dotp (a i) t) = ∑ i ∈ s, G i * y i := by
  have hlin : ∑ i ∈ s, G i * dotp (a i) t = 0 := by
    simp only [dotp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    calc ∑ i ∈ s, G i * (a i l * t l) = (∑ i ∈ s, G i * a i l) * t l := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [hG l, zero_mul]
  have : ∑ i ∈ s, G i * (y i - dotp (a i) t)
      = ∑ i ∈ s, G i * y i - ∑ i ∈ s, G i * dotp (a i) t := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, hlin, sub_zero]

/-- Линейная зависимость с положительным коэффициентом запрещает раздробление:
паттерн «нарушают ровно `g > 0`» требует `Σ g_iy_i < 0`, а паттерн «нарушают
ровно `g < 0`» — `Σ g_iy_i ≥ 0`. -/
lemma not_shatters_of_rel {a : ι → κ → ℝ} {y : ι → ℝ} {s : Finset ι} {G : ι → ℝ}
    (hG : ∀ l, ∑ i ∈ s, G i * a i l = 0) (hpos : ∃ i ∈ s, 0 < G i) :
    ¬ (reachSets a y).Shatters s := by
  classical
  intro hsh
  set P := s.filter (fun i => 0 < G i) with hP
  set N := s.filter (fun i => G i < 0) with hN
  obtain ⟨u₁, hu₁, hs₁⟩ := hsh (Finset.filter_subset (fun i => 0 < G i) s)
  obtain ⟨u₂, hu₂, hs₂⟩ := hsh (Finset.filter_subset (fun i => G i < 0) s)
  obtain ⟨t₁, rfl⟩ := mem_reachSets.mp hu₁
  obtain ⟨t₂, rfl⟩ := mem_reachSets.mp hu₂
  -- на `s` нарушители в `t₁` — ровно `P`, в `t₂` — ровно `N`
  have hm₁ : ∀ i ∈ s, (y i - dotp (a i) t₁ < 0 ↔ 0 < G i) := by
    intro i hi
    have := congrArg (fun F => i ∈ F) hs₁
    simp only [Finset.mem_inter, mem_violAt, Finset.mem_filter] at this
    simpa [hi] using this
  have hm₂ : ∀ i ∈ s, (y i - dotp (a i) t₂ < 0 ↔ G i < 0) := by
    intro i hi
    have := congrArg (fun F => i ∈ F) hs₂
    simp only [Finset.mem_inter, mem_violAt, Finset.mem_filter] at this
    simpa [hi] using this
  -- в `t₁` сумма отрицательна
  have hneg : ∑ i ∈ s, G i * (y i - dotp (a i) t₁) < 0 := by
    obtain ⟨i₀, hi₀, hg₀⟩ := hpos
    refine Finset.sum_neg' (fun i hi => ?_) ⟨i₀, hi₀, ?_⟩
    · by_cases hg : 0 < G i
      · exact mul_nonpos_of_nonneg_of_nonpos hg.le ((hm₁ i hi).mpr hg).le
      · push Not at hg
        have hr : 0 ≤ y i - dotp (a i) t₁ := by
          by_contra hr; push Not at hr; exact absurd ((hm₁ i hi).mp hr) (not_lt.mpr hg)
        exact mul_nonpos_of_nonpos_of_nonneg hg hr
    · exact mul_neg_of_pos_of_neg hg₀ ((hm₁ i₀ hi₀).mpr hg₀)
  -- в `t₂` сумма неотрицательна
  have hnn : 0 ≤ ∑ i ∈ s, G i * (y i - dotp (a i) t₂) := by
    refine Finset.sum_nonneg fun i hi => ?_
    by_cases hg : G i < 0
    · exact mul_nonneg_of_nonpos_of_nonpos hg.le ((hm₂ i hi).mpr hg).le
    · push Not at hg
      have hr : 0 ≤ y i - dotp (a i) t₂ := by
        by_contra hr; push Not at hr; exact absurd ((hm₂ i hi).mp hr) (not_lt.mpr hg)
      exact mul_nonneg hg hr
  rw [sum_res_eq_of_rel hG] at hneg hnn
  linarith

/-- **Набор из `K+1` и более строк не раздробляется** семейством достижимых
множеств нарушителей. -/
theorem not_shatters_reachSets {a : ι → κ → ℝ} {y : ι → ℝ} {s : Finset ι}
    (hs : Fintype.card κ < s.card) : ¬ (reachSets a y).Shatters s := by
  classical
  have hdep : ¬ LinearIndependent ℝ (fun x : s => a x) := by
    intro hli
    have h := hli.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
    omega
  obtain ⟨g, hg, x₀, hx₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  -- перенос коэффициентов с подтипа на `ι`
  let G : ι → ℝ := fun i => if h : i ∈ s then g ⟨i, h⟩ else 0
  have hGs : ∀ x : s, G x = g x := fun x => by simp [G]
  have hrel : ∀ l, ∑ i ∈ s, G i * a i l = 0 := by
    intro l
    have h := congrFun hg l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [← Finset.sum_coe_sort s]
    simp_rw [hGs]
    exact h
  have hrel' : ∀ l, ∑ i ∈ s, (-G i) * a i l = 0 := by
    intro l
    simp_rw [neg_mul, Finset.sum_neg_distrib, hrel l, neg_zero]
  rcases lt_or_gt_of_ne hx₀ with hneg | hpos
  · refine not_shatters_of_rel hrel' ⟨x₀, x₀.2, ?_⟩
    rw [hGs]; linarith
  · exact not_shatters_of_rel hrel ⟨x₀, x₀.2, by rw [hGs]; exact hpos⟩

/-- **Размерность Вапника–Червоненкиса семейства не больше `K`.** -/
theorem vcDim_reachSets_le (a : ι → κ → ℝ) (y : ι → ℝ) :
    (reachSets a y).vcDim ≤ Fintype.card κ := by
  unfold Finset.vcDim
  refine Finset.sup_le fun s hs => ?_
  by_contra h
  push Not at h
  exact not_shatters_reachSets h (Finset.mem_shatterer.mp hs)

/-- **Достижимых множеств нарушителей не больше `Σ_{j≤K} C(M, j)`**
(лемма Сауэра–Шелаха). -/
theorem card_reachSets_le (a : ι → κ → ℝ) (y : ι → ℝ) :
    (reachSets a y).card
      ≤ ∑ j ∈ Finset.Iic (Fintype.card κ), (Fintype.card ι).choose j := by
  refine le_trans (Finset.card_le_card_shatterer _)
    (le_trans Finset.card_shatterer_le_sum_vcDim ?_)
  exact Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr (vcDim_reachSets_le a y))

/-- `Σ_{j≤K} C(M, j) ≤ (M+1)^K`. -/
lemma sum_choose_le_pow (M K : ℕ) : ∑ j ∈ Finset.Iic K, M.choose j ≤ (M + 1) ^ K := by
  rw [add_pow]
  have hI : Finset.Iic K = Finset.range (K + 1) := by
    ext j; simp
  rw [hI]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjK : j ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h1 : M.choose j ≤ M ^ j := Nat.choose_le_pow M j
  have h2 : 1 ≤ K.choose j := Nat.choose_pos hjK
  rw [one_pow, mul_one]
  exact le_trans h1 (Nat.le_mul_of_pos_right _ h2)

/-- **Итог: достижимых множеств нарушителей `O(M^K)`.** -/
theorem card_reachSets_le_pow (a : ι → κ → ℝ) (y : ι → ℝ) :
    (reachSets a y).card ≤ (Fintype.card ι + 1) ^ Fintype.card κ :=
  le_trans (card_reachSets_le a y) (sum_choose_le_pow _ _)

/-! ### Покрытие по семейству достижимых множеств, в языке задачи -/

variable [DecidableEq κ] {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- Строки **активов** (без якорей): `a_i = B_i/√d_i`. -/
noncomputable def assetRows (d : ι → ℝ) (B : ι → κ → ℝ) : ι → κ → ℝ :=
  fun i j => B i j / Real.sqrt (d i)

/-- Правые части активов: `y_i = m_i/√d_i`. -/
noncomputable def assetTargets (m d : ι → ℝ) : ι → ℝ := fun i => m i / Real.sqrt (d i)

lemma rowsK_inl (i : ι) : rowsK d B G (Sum.inl i) = assetRows d B i := by
  ext j; simp [rowsK, assetRows]

lemma targetsK_inl (i : ι) : targetsK (κ := κ) m d (Sum.inl i) = assetTargets m d i := by
  simp [targetsK, assetTargets]

/-- Зажатые одновременные нарушители набора строк лежат в образе множества
нарушителей-активов. -/
lemma subset_map_violAt {U : Finset (ι ⊕ κ)} {t' : κ → ℝ}
    (hUv : ∀ j ∈ U, (Sum.isLeft j) ∧ targetsK m d j - dotp (rowsK d B G j) t' < 0) :
    U ⊆ (violAt (assetRows d B) (assetTargets m d) t').map Function.Embedding.inl := by
  intro x hx
  obtain ⟨hl, hneg⟩ := hUv x hx
  rcases x with i | l
  · refine Finset.mem_map.mpr ⟨i, ?_, rfl⟩
    rw [mem_violAt, ← rowsK_inl (G := G), ← targetsK_inl (κ := κ)]
    exact hneg
  · simp at hl

/-- **Покрытие по достижимым множествам (точное блочное плечо).** Если у
каждого достижимого множества нарушителей-активов `W` есть `d_W` с
`d_W·gram_W ≤ (1−d_W)·gram_anch` и `min(|W|, k) ≤ c·d_W`, то `c` — константа
покрытия. Максимум берётся по `O(M^K)` множествам (`card_reachSets_le_pow`). -/
theorem anchorCover_of_reachSets {cand : Finset ι} {k : ℕ} {c : ℝ} (dW : Finset ι → ℝ)
    (hW : ∀ W ∈ reachSets (assetRows d B) (assetTargets m d),
      0 < dW W ∧ dW W ≤ 1
      ∧ (∀ v : κ → ℝ, dW W * gram (rowsK d B G) (W.map Function.Embedding.inl) v
          ≤ (1 - dW W) * gram (rowsK d B G) (anchorRows ι κ) v)
      ∧ (min W.card k : ℝ) ≤ c * dW W) :
    AnchorCover (rowsK d B G) (targetsK m d) (fun r => Sum.isLeft r) (barK (κ := κ) cand)
      (anchorRows ι κ) k c := by
  intro t' U hUS hUk hUv
  set W := violAt (assetRows d B) (assetTargets m d) t' with hWdef
  obtain ⟨hd0, hd1, hblock, hcard⟩ := hW W (violAt_mem_reachSets _ _ t')
  have hUW := subset_map_violAt (m := m) hUv
  refine ⟨dW W, hd0, hd1, fun v => ?_, ?_⟩
  · have h1 := gram_mono (a := rowsK d B G) hUW v
    nlinarith [hblock v, mul_le_mul_of_nonneg_left h1 hd0.le]
  · have hU1 : U.card ≤ W.card := by
      have := Finset.card_le_card hUW
      rwa [Finset.card_map] at this
    have hUc : (U.card : ℝ) ≤ (min W.card k : ℝ) := by
      have : U.card ≤ min W.card k := le_min hU1 hUk
      exact_mod_cast this
    linarith

/-- **Покрытие по достижимым множествам и плечам активов.** Если для каждого
достижимого `W` и каждого `U ⊆ W` мощности `≤ k` выполнено
`|U|·(1 + Σ_{i∈U} B_i'Σ_fB_i/d_i) ≤ c`, то `c` — константа покрытия.
Это вычислимо: для каждого `W` максимум достигается на `min(|W|,k)` активах `W`
с наибольшими `B_i'Σ_fB_i/d_i`. -/
theorem anchorCover_of_reachSets_sysVar (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {cand : Finset ι} {k : ℕ} {c : ℝ}
    (hW : ∀ W ∈ reachSets (assetRows d B) (assetTargets m d), ∀ U ⊆ W, U.card ≤ k →
      (U.card : ℝ) * (1 + ∑ i ∈ U, sysVar B Sf i / d i) ≤ c) :
    AnchorCover (rowsK d B G) (targetsK m d) (fun r => Sum.isLeft r) (barK (κ := κ) cand)
      (anchorRows ι κ) k c := by
  classical
  intro t' U hUS hUk hUv
  set W := violAt (assetRows d B) (assetTargets m d) t' with hWdef
  have hUW := subset_map_violAt (m := m) hUv
  -- `U = U₀.map inl`, `U₀ ⊆ W`
  set U₀ : Finset ι := W.filter (fun i => (Sum.inl i : ι ⊕ κ) ∈ U) with hU₀
  have hUeq : U = U₀.map Function.Embedding.inl := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp (hUW hx)
      exact Finset.mem_map.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hx⟩, rfl⟩
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      exact (Finset.mem_filter.mp hi).2
  have hU₀W : U₀ ⊆ W := Finset.filter_subset _ _
  have hcard : U₀.card = U.card := by rw [hUeq, Finset.card_map]
  have hc := hW W (violAt_mem_reachSets _ _ t') U₀ hU₀W (by rw [hcard]; exact hUk)
  set Ω := ∑ i ∈ U₀, sysVar B Sf i / d i with hΩ
  have hΩ0 : 0 ≤ Ω := Finset.sum_nonneg fun i _ =>
    div_nonneg (sysVar_nonneg hG hPS i) (hd i).le
  have hpos : 0 < 1 + Ω := by linarith
  refine ⟨1 / (1 + Ω), by positivity, ?_, fun v => ?_, ?_⟩
  · rw [div_le_one hpos]; linarith
  · have hgU : gram (rowsK d B G) U v ≤ Ω * gram (rowsK d B G) (anchorRows ι κ) v := by
      rw [hUeq, hΩ, Finset.sum_mul]
      simp only [gram, Finset.sum_map, Function.Embedding.inl_apply]
      exact Finset.sum_le_sum fun i _ => by
        simpa [gram] using sq_dotp_asset_le hd hG hPS i v
    have heq : 1 - 1 / (1 + Ω) = Ω * (1 / (1 + Ω)) := by field_simp; ring
    rw [heq]
    have hd0 : (0:ℝ) ≤ 1 / (1 + Ω) := by positivity
    calc 1 / (1 + Ω) * gram (rowsK d B G) U v
        ≤ 1 / (1 + Ω) * (Ω * gram (rowsK d B G) (anchorRows ι κ) v) :=
          mul_le_mul_of_nonneg_left hgU hd0
      _ = Ω * (1 / (1 + Ω)) * gram (rowsK d B G) (anchorRows ι κ) v := by ring
  · rw [← hcard, mul_one_div, le_div_iff₀ hpos]
    exact hc

/-! ### Непустота: оценка точна

`K = 1`, три строки `a = 1` с `y = 0, 1, 2`: гиперплоскости — точки `0, 1, 2`
на прямой, и достижимы ровно четыре множества нарушителей
`∅, {0}, {0,1}, {0,1,2}` (нарушители — строки с `t > y_i`), то есть
`1 + C(3,1) = 4` — граница `card_reachSets_le` достигается. -/

private def aR : Fin 3 → Fin 1 → ℝ := fun _ _ => 1
private def yR : Fin 3 → ℝ := fun i => (i : ℝ)

example : (reachSets aR yR).card ≤ 4 := by
  have h := card_reachSets_le aR yR
  simp only [Fintype.card_fin] at h
  have h4 : ∑ j ∈ Finset.Iic 1, (3 : ℕ).choose j = 4 := by decide
  omega

example : ({0, 1} : Finset (Fin 3)) ∈ reachSets aR yR := by
  have : violAt aR yR (fun _ => 3 / 2) = {0, 1} := by
    ext i
    fin_cases i <;> simp [mem_violAt, dotp, aR, yR] <;> norm_num
  rw [← this]
  exact violAt_mem_reachSets _ _ _

end SparseSharpe.Factor
