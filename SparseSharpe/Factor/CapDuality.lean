import SparseSharpe.Factor.Practical
import SparseSharpe.Factor.ClippedNode

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Ограничения на долю актива: двойственность и сертификат (задача L6 ТЗ, сессия 23)

Потолок на долю: `w ≥ 0`, `w_i ≤ c·Σ_j w_j` (`c = c_max ∈ [1/k, 1]`). Множество допустимых
весов — конус, поэтому масштабирование сохраняет потолок, и значение `max SR²` на нём — это
`max objLO` (`cap_exists_scaled`).

* `objLO_eq_defect_general` — тождество прямо-двойственного дефекта для **любого** веса:
  `objLO(S,w) = t'Σ_f⁻¹t − (Σ_fB_S'w − t)'Σ_f⁻¹(Σ_fB_S'w − t) + Σ_S(2(m_i − ⟨B_i,t⟩)w_i − d_iw_i²)`;
* `hub` — функция Хьюбера `h_d(r;C) = max_{0≤w≤C}(2rw − dw²)` (`hub_ge`);
* `cap_weak_duality` — **слабая двойственность с потолками (Теорема 4.1(b))**: для любых
  `t ∈ ℝ^K`, `ρ ∈ ℝ` и любого портфеля с потолком

      objLO(S,w) ≤ t'Σ_f⁻¹t + Σ_{i∈S} h_{d_i}(m_i + ρ − ⟨B_i,t⟩; c·W) − 2ρW,    W = Σ_S w_i;

* `objLO_cap_identity` — точное тождество для усечённых по потолку весов (Теорема 4.1(c)):
  при `w_i = clip((m_i+ρ−⟨B_i,t⟩)/d_i, 0, cW)`
  `objLO = t'Σ_f⁻¹t + Σ h_i − 2ρΣw_i − (Σ_fB'w − t)'Σ_f⁻¹(Σ_fB'w − t)`.

Сильная двойственность (равенство `F^cap_LO = min_{t,ρ≥0} sup_W`) проверена численно
(`code/check_perspective.py`), в Lean не формализована; динамика по `K+2` координатам — тоже.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ} {S : Finset ι} {w : ι → ℝ}

/-- Тождество дефекта для любого веса. -/
theorem objLO_eq_defect_general (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (S : Finset ι) (w : ι → ℝ) (t : κ → ℝ) :
    objLO m d B Sf S w
      = quadf P t - quadf P (tw Sf B S w - t)
        + ∑ i ∈ S, (2 * (m i - dotp (B i) t) * w i - d i * w i ^ 2) := by
  rw [objLO_eq, quadf_tw_sub hG hPS, Bw_dot]
  have : ∑ i ∈ S, (2 * (m i - dotp (B i) t) * w i - d i * w i ^ 2)
      = 2 * (∑ i ∈ S, m i * w i) - 2 * (∑ i ∈ S, w i * dotp (B i) t)
        - ∑ i ∈ S, d i * w i ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]; ring

/-- Проекция `r/d` на `[0,C]`: максимизатор `2rw − dw²` на отрезке. -/
noncomputable def capw (d r C : ℝ) : ℝ := max 0 (min C (r / d))

/-- Функция Хьюбера `h_d(r;C) = 2r·w* − d·w*²`, `w* = clip(r/d, 0, C)`. -/
noncomputable def hub (d r C : ℝ) : ℝ := 2 * r * capw d r C - d * capw d r C ^ 2

lemma capw_mem {d r C : ℝ} (hC : 0 ≤ C) : 0 ≤ capw d r C ∧ capw d r C ≤ C := by
  refine ⟨le_max_left _ _, max_le hC (min_le_left _ _)⟩

/-- `h_d(r;C) = max_{0≤w≤C}(2rw − dw²)`: верхняя граница для любого `w ∈ [0,C]`. -/
theorem hub_ge {d r C w : ℝ} (hd : 0 < d) (hC : 0 ≤ C) (hw0 : 0 ≤ w) (hwC : w ≤ C) :
    2 * r * w - d * w ^ 2 ≤ hub d r C := by
  unfold hub capw
  set q := r / d with hq
  have hr : r = d * q := by rw [hq]; field_simp
  rw [hr]
  -- `2dq·w − dw² = d(q² − (w−q)²)`
  have key : ∀ x : ℝ, 2 * (d * q) * x - d * x ^ 2 = d * (q ^ 2 - (x - q) ^ 2) := fun x => by ring
  rw [key, key]
  have hproj : ((max 0 (min C q)) - q) ^ 2 ≤ (w - q) ^ 2 := by
    rcases le_total q 0 with h1 | h1
    · have : min C q = q := min_eq_right (by linarith)
      rw [this, max_eq_left h1]; nlinarith
    · rcases le_total q C with h2 | h2
      · rw [min_eq_right h2, max_eq_right h1]; nlinarith [sq_nonneg (w - q)]
      · rw [min_eq_left h2, max_eq_right hC]; nlinarith
  have := mul_le_mul_of_nonneg_left (sub_le_sub_left hproj (q ^ 2)) hd.le
  linarith

/-- **Слабая двойственность с потолками (Теорема 4.1(b)).** -/
theorem cap_weak_duality (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {c : ℝ} (hw0 : ∀ i ∈ S, 0 ≤ w i) (hwc : ∀ i ∈ S, w i ≤ c * ∑ j ∈ S, w j)
    (t : κ → ℝ) (ρ : ℝ) :
    objLO m d B Sf S w
      ≤ quadf P t + ∑ i ∈ S, hub (d i) (m i + ρ - dotp (B i) t) (c * ∑ j ∈ S, w j)
        - 2 * ρ * ∑ j ∈ S, w j := by
  set W := ∑ j ∈ S, w j with hW
  rw [objLO_eq_defect_general (m := m) (d := d) (B := B) hG hPS S w t]
  have hdef := quadf_nonneg_of_root hG (tw Sf B S w - t)
  have hW0 : 0 ≤ W := Finset.sum_nonneg hw0
  have hitem : ∀ i ∈ S, 2 * (m i - dotp (B i) t) * w i - d i * w i ^ 2
      ≤ hub (d i) (m i + ρ - dotp (B i) t) (c * W) - 2 * ρ * w i := by
    intro i hi
    have hcW : 0 ≤ c * W := le_trans (hw0 i hi) (hwc i hi)
    have := hub_ge (r := m i + ρ - dotp (B i) t) (hd i) hcW (hw0 i hi) (hwc i hi)
    nlinarith
  have hsum := Finset.sum_le_sum hitem
  have hR : ∑ i ∈ S, (hub (d i) (m i + ρ - dotp (B i) t) (c * W) - 2 * ρ * w i)
      = ∑ i ∈ S, hub (d i) (m i + ρ - dotp (B i) t) (c * W) - 2 * ρ * W := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith

/-- **Точное тождество для усечённых по потолку весов (Теорема 4.1(c)).** -/
theorem objLO_cap_identity
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (S : Finset ι) (t : κ → ℝ) (ρ C : ℝ) :
    objLO m d B Sf S (fun i => capw (d i) (m i + ρ - dotp (B i) t) C)
      = quadf P t + ∑ i ∈ S, hub (d i) (m i + ρ - dotp (B i) t) C
        - 2 * ρ * ∑ i ∈ S, capw (d i) (m i + ρ - dotp (B i) t) C
        - quadf P (tw Sf B S (fun i => capw (d i) (m i + ρ - dotp (B i) t) C) - t) := by
  rw [objLO_eq_defect_general (m := m) (d := d) (B := B) hG hPS S _ t]
  have : ∑ i ∈ S, (2 * (m i - dotp (B i) t) * capw (d i) (m i + ρ - dotp (B i) t) C
      - d i * capw (d i) (m i + ρ - dotp (B i) t) C ^ 2)
      = ∑ i ∈ S, hub (d i) (m i + ρ - dotp (B i) t) C
        - 2 * ρ * ∑ i ∈ S, capw (d i) (m i + ρ - dotp (B i) t) C := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hub]; ring
  rw [this]; ring

/-! ### Конус: масштабирование сохраняет потолок -/

lemma cap_smul {c : ℝ} {μ : ℝ} (hμ : 0 ≤ μ) (hw0 : ∀ i ∈ S, 0 ≤ w i)
    (hwc : ∀ i ∈ S, w i ≤ c * ∑ j ∈ S, w j) :
    (∀ i ∈ S, 0 ≤ μ * w i) ∧ ∀ i ∈ S, μ * w i ≤ c * ∑ j ∈ S, μ * w j := by
  refine ⟨fun i hi => mul_nonneg hμ (hw0 i hi), fun i hi => ?_⟩
  rw [← Finset.mul_sum]
  have := mul_le_mul_of_nonneg_left (hwc i hi) hμ
  linarith

/-- Для портфеля с потолком и положительной дисперсией перенормировка сохраняет потолок
и даёт `objLO = sharpe²`: `OPT^cap = max SR²` на конусе. -/
theorem cap_exists_scaled
    {c : ℝ} (hw0 : ∀ i ∈ S, 0 ≤ w i) (hwc : ∀ i ∈ S, w i ≤ c * ∑ j ∈ S, w j)
    (hret : 0 < pRet m S w) (hv : 0 < pVar d B Sf S w) :
    ∃ w' : ι → ℝ, (∀ i ∈ S, 0 ≤ w' i) ∧ (∀ i ∈ S, w' i ≤ c * ∑ j ∈ S, w' j) ∧
      objLO m d B Sf S w' = sharpe m d B Sf S w ^ 2 := by
  have hμ : 0 ≤ pRet m S w / pVar d B Sf S w := div_nonneg hret.le hv.le
  obtain ⟨h1, h2⟩ := cap_smul (S := S) (w := w) (c := c) hμ hw0 hwc
  refine ⟨fun i => (pRet m S w / pVar d B Sf S w) * w i, h1, h2, ?_⟩
  rw [objLO_opt_scale S w hv, sharpe_sq S w hv]

end SparseSharpe.Factor
