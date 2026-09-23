import SparseSharpe.Factor.KBridge
import SparseSharpe.Factor.Clipped

set_option linter.style.header false

/-!
# Long-only при `K` факторах: точная формула значения

Задача: `F_LO(S) = max{ 2·m_S'w − w'V_S w : w ≥ 0 }`, `V = D + BΣ_fB'`.

Главный результат (`isGreatest_objLO`): если `w` удовлетворяет условиям ККТ на `S`,
то в точке `t̂ = Σ_f B'w`

    F_LO(S)  =  QLO(S, t̂),   QLO(S,t) = t'Σ_f⁻¹t + Σ_{i∈S} ((m_i − ⟨B_i,t⟩)_+)²/d_i.

Две половины:

* `objLO_le_QLO` — `QLO(S,t)` мажорирует цель для **любого** допустимого `w`
  и **любого** `t` (доказательство: `Σ_f⁻¹`-неравенство Юнга плюс поточечное
  `2rw − dw² ≤ (r)_+²/d`);
* `objLO_wclip` — «обрезанный» вес `w_i(t) = (m_i − ⟨B_i,t⟩)_+/d_i` автоматически
  допустим (`wclip_nonneg`) и даёт тождество

      objLO(w(t)) = Σ_{i∈S}((m_i−⟨B_i,t⟩)_+)²/d_i + 2⟨u,t⟩ − u'Σ_f u,  u = B'w(t).

Значение для алгоритма: в отличие от одномерного случая
(`SparseSharpe/LOFptas.lean`, где требовалась *самосогласованность* активного
множества), ограничение `w ≥ 0` здесь исчезает — любая точка `t` даёт
сертифицированное допустимое значение, и в правой части нет `Σ_f⁻¹`,
то есть она вычислима без обращения матриц и аддитивна по `S` при фиксированном `t`.
Это ровно структура `Q − ‖M‖²`, на которой построена динамика §4.

`QLO` — это `psiC` из `Factor/Clipped.lean` на строках `rowsK` с зажатием только
строк-активов (`QLO_eq_psiC`), поэтому к нему применимы `psiC_shift_ge`,
`psiC_le_phi` и `psiC_eq_phi_of_nonneg`.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ} {S : Finset ι} {w : ι → ℝ}
variable {t : κ → ℝ}

/-- Квадратичная форма с матрицей `C`: `x'Cx`. -/
noncomputable def quadf (C : κ → κ → ℝ) (x : κ → ℝ) : ℝ := ∑ j, ∑ j', C j j' * (x j * x j')

/-- Цель long-only `2·m_S'w − w'V_S w`. -/
noncomputable def objLO (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf : κ → κ → ℝ) (S : Finset ι)
    (w : ι → ℝ) : ℝ :=
  2 * (∑ i ∈ S, m i * w i) - ∑ i ∈ S, ∑ i' ∈ S, Vmat d B Sf i i' * (w i * w i')

/-- `QLO(S,t) = t'Σ_f⁻¹t + Σ_{i∈S}((m_i − ⟨B_i,t⟩)_+)²/d_i` (здесь `P = Σ_f⁻¹`). -/
noncomputable def QLO (m d : ι → ℝ) (B : ι → κ → ℝ) (P : κ → κ → ℝ) (S : Finset ι)
    (t : κ → ℝ) : ℝ :=
  quadf P t + ∑ i ∈ S, (max (m i - dotp (B i) t) 0) ^ 2 / d i

/-- Обрезанный вес `w_i(t) = (m_i − ⟨B_i,t⟩)_+/d_i`. -/
noncomputable def wclip (m d : ι → ℝ) (B : ι → κ → ℝ) (t : κ → ℝ) : ι → ℝ :=
  fun i => max (m i - dotp (B i) t) 0 / d i

/-- Обрезанный вес допустим для long-only. -/
lemma wclip_nonneg (hd : ∀ i, 0 < d i) (t : κ → ℝ) (i : ι) : 0 ≤ wclip m d B t i :=
  div_nonneg (le_max_right _ _) (hd i).le

/-! ### Перестановки в четырёхкратных суммах -/

/-- `∑_i∑_{i'}∑_j∑_{j'} = ∑_j∑_{j'}∑_i∑_{i'}`. -/
lemma sum_swap4 (S : Finset ι) (F : ι → ι → κ → κ → ℝ) :
    ∑ i ∈ S, ∑ i' ∈ S, ∑ j, ∑ j', F i i' j j'
      = ∑ j, ∑ j', ∑ i ∈ S, ∑ i' ∈ S, F i i' j j' := by
  have h1 : ∀ i ∈ S, ∑ i' ∈ S, ∑ j, ∑ j', F i i' j j'
      = ∑ j, ∑ i' ∈ S, ∑ j', F i i' j j' := fun _ _ => Finset.sum_comm
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 : ∀ i ∈ S, ∑ i' ∈ S, ∑ j', F i i' j j'
      = ∑ j', ∑ i' ∈ S, F i i' j j' := fun _ _ => Finset.sum_comm
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]

/-! ### Разложение цели -/

/-- `w'V_S w = Σ_i d_i w_i² + u'Σ_f u`, где `u = B'w`. Матрицы не обращаются. -/
lemma quad_Vmat (S : Finset ι) (w : ι → ℝ) :
    ∑ i ∈ S, ∑ i' ∈ S, Vmat d B Sf i i' * (w i * w i')
      = (∑ i ∈ S, d i * w i ^ 2) + quadf Sf (Bw B S w) := by
  have hrow : ∀ i ∈ S, ∑ i' ∈ S, Vmat d B Sf i i' * (w i * w i')
      = d i * w i ^ 2
        + ∑ i' ∈ S, (∑ j, ∑ j', B i j * (Sf j j' * B i' j')) * (w i * w i') := by
    intro i hi
    simp only [Vmat, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single i]
    · have hif : (if i = i then d i else 0) = d i := by simp
      rw [hif]; ring
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd hi h
  rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib]
  congr 1
  -- вторая половина собирается в `u'Σ_f u`
  have hpush : ∀ i ∈ S, ∑ i' ∈ S, (∑ j, ∑ j', B i j * (Sf j j' * B i' j')) * (w i * w i')
      = ∑ i' ∈ S, ∑ j, ∑ j', B i j * (Sf j j' * B i' j') * (w i * w i') := by
    intro i _
    refine Finset.sum_congr rfl fun i' _ => ?_
    simp only [Finset.sum_mul]
  rw [Finset.sum_congr rfl hpush, sum_swap4]
  simp only [quadf, Bw]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring

/-- Цель в терминах `u = B'w`: `objLO = 2Σm_iw_i − Σd_iw_i² − u'Σ_f u`. -/
lemma objLO_eq (S : Finset ι) (w : ι → ℝ) :
    objLO m d B Sf S w
      = 2 * (∑ i ∈ S, m i * w i) - (∑ i ∈ S, d i * w i ^ 2) - quadf Sf (Bw B S w) := by
  rw [objLO, quad_Vmat]; ring

/-- Цель зависит только от значений `w` на `S`. -/
lemma objLO_congr {w w' : ι → ℝ} (h : ∀ i ∈ S, w i = w' i) :
    objLO m d B Sf S w = objLO m d B Sf S w' := by
  simp only [objLO]
  congr 1
  · congr 1; exact Finset.sum_congr rfl fun i hi => by rw [h i hi]
  · exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun i' hi' => by
      rw [h i hi, h i' hi']

/-! ### Свойства `Σ_f⁻¹ = G'G` -/

/-- `∑_l∑_j∑_{j'} = ∑_j∑_{j'}∑_l`. -/
lemma sum_swap3 (F : κ → κ → κ → ℝ) :
    ∑ l, ∑ j, ∑ j', F l j j' = ∑ j, ∑ j', ∑ l, F l j j' := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- `x'Px = Σ_l ⟨G_l,x⟩²` — якорные строки реализуют `Σ_f⁻¹` как сумму квадратов. -/
lemma quadf_eq_sum_sq (hG : ∀ j j', ∑ l, G l j * G l j' = P j j') (x : κ → ℝ) :
    quadf P x = ∑ l, (dotp (G l) x) ^ 2 := by
  have h1 : ∀ l : κ, (dotp (G l) x) ^ 2
      = ∑ j, ∑ j', (G l j * G l j') * (x j * x j') := by
    intro l
    simp only [dotp, sq]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
  rw [Finset.sum_congr rfl fun l _ => h1 l, sum_swap3]
  simp only [quadf]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  rw [← hG j j', Finset.sum_mul]

/-- `x'Px ≥ 0`. -/
lemma quadf_nonneg_of_root (hG : ∀ j j', ∑ l, G l j * G l j' = P j j') (x : κ → ℝ) :
    0 ≤ quadf P x := by
  rw [quadf_eq_sum_sq hG]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Симметричность `P = G'G`. -/
lemma P_symm_of_root (hG : ∀ j j', ∑ l, G l j * G l j' = P j j') (j j' : κ) :
    P j j' = P j' j := by
  rw [← hG j j', ← hG j' j]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- Раскрытие `quadf P (s − t)`. -/
lemma quadf_sub (hPsymm : ∀ j j', P j j' = P j' j) (s t : κ → ℝ) :
    quadf P (s - t)
      = quadf P s - 2 * (∑ j, ∑ j', P j j' * (s j * t j')) + quadf P t := by
  have hcross : ∑ j, ∑ j', P j j' * (t j * s j') = ∑ j, ∑ j', P j j' * (s j * t j') := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by
      rw [hPsymm j' j]; ring
  simp only [quadf, Pi.sub_apply]
  have hexp : ∀ j j', P j j' * ((s j - t j) * (s j' - t j'))
      = P j j' * (s j * s j') - P j j' * (s j * t j') - P j j' * (t j * s j')
        + P j j' * (t j * t j') := fun _ _ => by ring
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hcross]
  ring

/-! ### Верхняя оценка: `objLO ≤ QLO` -/

/-- Поточечно: при `w ≥ 0` и `d > 0` имеем `2rw − dw² ≤ (r)_+²/d`. -/
lemma quad_item_le {r dd ww : ℝ} (hd : 0 < dd) (hw : 0 ≤ ww) :
    2 * r * ww - dd * ww ^ 2 ≤ (max r 0) ^ 2 / dd := by
  have hkey : 0 ≤ dd * (ww - max r 0 / dd) ^ 2 := by positivity
  have hexp : dd * (ww - max r 0 / dd) ^ 2
      = dd * ww ^ 2 - 2 * max r 0 * ww + (max r 0) ^ 2 / dd := by
    field_simp; ring
  have hr : r * ww ≤ max r 0 * ww := mul_le_mul_of_nonneg_right (le_max_left _ _) hw
  rw [hexp] at hkey
  linarith

/-- `⟨B'w, t⟩ = Σ_{i∈S} w_i⟨B_i,t⟩`. -/
lemma Bw_dot (S : Finset ι) (w : ι → ℝ) (t : κ → ℝ) :
    ∑ j, Bw B S w j * t j = ∑ i ∈ S, w i * dotp (B i) t := by
  simp only [Bw, dotp, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Неравенство Юнга в метрике `Σ_f`: `u'Σ_f u ≥ 2⟨u,t⟩ − t'Σ_f⁻¹t`. -/
lemma young_Sf (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (S : Finset ι) (w : ι → ℝ) (t : κ → ℝ) :
    2 * (∑ j, Bw B S w j * t j) - quadf P t ≤ quadf Sf (Bw B S w) := by
  set u := Bw B S w with hu
  set s := tw Sf B S w with hs
  have hPsymm := P_symm_of_root (P := P) (G := G) hG
  -- `∑_{j'} P j j' s_{j'} = u_j`
  have hPs : ∀ j, ∑ j', P j j' * s j' = u j := fun j => P_tw hPS j
  -- `quadf P s = quadf Sf u`
  have hquad_s : quadf P s = quadf Sf u := by
    have h1 : quadf P s = ∑ j, s j * u j := by
      simp only [quadf]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hPs j, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j' _ => by ring
    have h2 : quadf Sf u = ∑ j, u j * s j := by
      simp only [quadf, hs, tw]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j' _ => by ring
    rw [h1, h2]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- перекрёстный член
  have hcross : ∑ j, ∑ j', P j j' * (s j * t j') = ∑ j, u j * t j := by
    have hswap : ∑ j, ∑ j', P j j' * (s j * t j')
        = ∑ j', (∑ j, P j' j * s j) * t j' := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [hPsymm j j']; ring
    rw [hswap]
    exact Finset.sum_congr rfl fun j' _ => by rw [hPs j']
  have hnn := quadf_nonneg_of_root (P := P) (G := G) hG (s - t)
  rw [quadf_sub hPsymm s t, hquad_s, hcross] at hnn
  linarith

/-- **Верхняя оценка.** Для любого допустимого `w ≥ 0` и любого `t`: `objLO ≤ QLO(S,t)`. -/
theorem objLO_le_QLO (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hw : ∀ i ∈ S, 0 ≤ w i) (t : κ → ℝ) :
    objLO m d B Sf S w ≤ QLO m d B P S t := by
  have hyoung := young_Sf (B := B) (P := P) (G := G) hG hPS S w t
  have hdot := Bw_dot (B := B) S w t
  have hitems : ∑ i ∈ S, (2 * (m i - dotp (B i) t) * w i - d i * w i ^ 2)
      ≤ ∑ i ∈ S, (max (m i - dotp (B i) t) 0) ^ 2 / d i :=
    Finset.sum_le_sum fun i hi => quad_item_le (hd i) (hw i hi)
  have hsplit : ∑ i ∈ S, (2 * (m i - dotp (B i) t) * w i - d i * w i ^ 2)
      = 2 * (∑ i ∈ S, m i * w i) - 2 * (∑ j, Bw B S w j * t j) - ∑ i ∈ S, d i * w i ^ 2 := by
    rw [hdot]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit] at hitems
  rw [objLO_eq, QLO]
  linarith

/-! ### Нижняя оценка: тождество для обрезанного веса -/

/-- `(r)_+·(r − (r)_+) = 0`. -/
lemma max_mul_sub_max (r : ℝ) : max r 0 * (r - max r 0) = 0 := by
  rcases le_or_gt r 0 with h | h
  · rw [max_eq_right h]; ring
  · rw [max_eq_left h.le]; ring

/-- **Тождество для обрезанного веса.** Правая часть не содержит `Σ_f⁻¹`. -/
theorem objLO_wclip (hd : ∀ i, 0 < d i) (S : Finset ι) (t : κ → ℝ) :
    objLO m d B Sf S (wclip m d B t)
      = (∑ i ∈ S, (max (m i - dotp (B i) t) 0) ^ 2 / d i)
        + 2 * (∑ j, Bw B S (wclip m d B t) j * t j)
        - quadf Sf (Bw B S (wclip m d B t)) := by
  rw [objLO_eq, Bw_dot]
  have hitem : ∀ i ∈ S, 2 * (m i * wclip m d B t i) - d i * wclip m d B t i ^ 2
      = (max (m i - dotp (B i) t) 0) ^ 2 / d i
        + 2 * (wclip m d B t i * dotp (B i) t) := by
    intro i _
    have hdi := hd i
    have hne : d i ≠ 0 := ne_of_gt hdi
    have hz := max_mul_sub_max (m i - dotp (B i) t)
    simp only [wclip]
    field_simp
    nlinarith [hz]
  have hsum : 2 * (∑ i ∈ S, m i * wclip m d B t i) - ∑ i ∈ S, d i * wclip m d B t i ^ 2
      = (∑ i ∈ S, (max (m i - dotp (B i) t) 0) ^ 2 / d i)
        + 2 * ∑ i ∈ S, wclip m d B t i * dotp (B i) t := by
    have := Finset.sum_congr rfl hitem
    simp only [Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_sub_distrib] at this ⊢
    linarith [this]
  linarith [hsum]

/-! ### Условия ККТ и точное значение -/

/-- Условия ККТ для `max{2m'w − w'Vw : w ≥ 0}` на `S`. -/
structure IsKKT (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf : κ → κ → ℝ) (S : Finset ι)
    (w : ι → ℝ) : Prop where
  /-- Прямая допустимость. -/
  nonneg : ∀ i ∈ S, 0 ≤ w i
  /-- Двойственная допустимость `(V_Sw)_i ≥ m_i`. -/
  dual : ∀ i ∈ S, m i - dotp (B i) (tw Sf B S w) ≤ d i * w i
  /-- Дополняющая нежёсткость. -/
  slack : ∀ i ∈ S, 0 < w i → m i - dotp (B i) (tw Sf B S w) = d i * w i

/-- В точке ККТ обрезанный вес совпадает с самим `w` (на `S`). -/
theorem wclip_eq_of_kkt (hd : ∀ i, 0 < d i) (hk : IsKKT m d B Sf S w) :
    ∀ i ∈ S, wclip m d B (tw Sf B S w) i = w i := by
  intro i hi
  have hdi := hd i
  rcases lt_or_eq_of_le (hk.nonneg i hi) with hpos | hzero
  · have hne : d i ≠ 0 := ne_of_gt hdi
    have heq := hk.slack i hi hpos
    have hrpos : 0 < m i - dotp (B i) (tw Sf B S w) := by
      rw [heq]; exact mul_pos hdi hpos
    simp only [wclip, heq, max_eq_left (mul_pos hdi hpos).le]
    field_simp
  · have hw0 : w i = 0 := hzero.symm
    have hle : m i - dotp (B i) (tw Sf B S w) ≤ 0 := by
      have := hk.dual i hi; rw [hw0] at this; simpa using this
    simp only [wclip, max_eq_right hle, hw0]
    simp

/-- **Точное значение long-only.** В точке ККТ `objLO w = QLO(S, Σ_f B'w)`. -/
theorem objLO_eq_QLO_of_kkt (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hk : IsKKT m d B Sf S w) :
    objLO m d B Sf S w = QLO m d B P S (tw Sf B S w) := by
  set th := tw Sf B S w with hth
  have hwc := wclip_eq_of_kkt hd hk
  have hBw : Bw B S (wclip m d B th) = Bw B S w := by
    funext j
    simp only [Bw]
    exact Finset.sum_congr rfl fun i hi => by rw [hwc i hi]
  have hobj : objLO m d B Sf S w = objLO m d B Sf S (wclip m d B th) :=
    objLO_congr fun i hi => (hwc i hi).symm
  rw [hobj, objLO_wclip hd S th, hBw]
  -- `⟨u, t̂⟩ = u'Σ_f u` и `t̂'Σ_f⁻¹t̂ = u'Σ_f u`
  have hdotu : ∑ j, Bw B S w j * th j = quadf Sf (Bw B S w) := by
    simp only [quadf, hth, tw]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j' _ => by ring
  have hPsymm := P_symm_of_root (P := P) (G := G) hG
  have hquadP : quadf P th = quadf Sf (Bw B S w) := by
    have h1 : quadf P th = ∑ j, th j * Bw B S w j := by
      simp only [quadf]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← P_tw (Sf := Sf) (B := B) (S := S) (w := w) hPS j, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j' _ => by ring
    rw [h1, ← hdotu]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [QLO, hquadP, hdotu]
  ring

/-! ### Выбрасывание вдоль нулевого направления

Ключ к полноте LO-K′ (`theory_note_v5.md`, §11). Пусть `w` — оптимальный
long-only портфель на `S` (условие стационарности ККТ выполнено на всём `S`,
то есть `S` — носитель), а `μ ≥ 0` — **направление нулевой факторной экспозиции**:
`Σ_{i∈S} B_i μ_i = 0`. Тогда сдвиг вдоль `μ` стоит только второго порядка:

    objLO(w − θμ) = objLO(w) − θ²·Σ_{i∈S} d_i μ_i² .

Линейный член исчезает, потому что `Σμ_i(m_i − d_iw_i) = ⟨Σμ_iB_i, t̂⟩ = 0`.

Это снимает препятствие §4.2: прямое обнуление координаты стоит
`w_i²·V_ii = r_i(t̂)²(1 + ‖a_i‖²_{Σ_f})` с неограниченным множителем, а сдвиг
вдоль нулевого направления — нет. Выбрав `θ` так, что одна координата обращается
в ноль, получаем портфель на **меньшем** носителе почти той же стоимости.
Численно: `code/check_lo_nulldrop.py` — 0 нарушений, тождество точно до `9·10⁻¹⁶`,
наивная оценка дороже настоящей потери в медиане 4.8 раза и до 1207 раз. -/

/-- `Bw` линейно: экспозиция сдвинутого портфеля. -/
lemma Bw_sub_smul (S : Finset ι) (w μ : ι → ℝ) (θ : ℝ) (j : κ) :
    Bw B S (fun i => w i - θ * μ i) j = Bw B S w j - θ * Bw B S μ j := by
  simp only [Bw, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Тождество сдвига вдоль нулевого направления.** -/
theorem objLO_null_shift (hstat : ∀ i ∈ S, d i * w i + dotp (B i) (tw Sf B S w) = m i)
    {μ : ι → ℝ} (hnull : ∀ j, Bw B S μ j = 0) (θ : ℝ) :
    objLO m d B Sf S (fun i => w i - θ * μ i)
      = objLO m d B Sf S w - θ ^ 2 * ∑ i ∈ S, d i * μ i ^ 2 := by
  set th := tw Sf B S w with hth
  -- экспозиция не меняется
  have hBw : Bw B S (fun i => w i - θ * μ i) = Bw B S w := by
    funext j; rw [Bw_sub_smul, hnull j]; ring
  -- линейный член: `Σ μ_i (m_i − d_i w_i) = ⟨Σ μ_i B_i, t̂⟩ = 0`
  have hlin : ∑ i ∈ S, μ i * (m i - d i * w i) = 0 := by
    have hterm : ∀ i ∈ S, μ i * (m i - d i * w i) = μ i * dotp (B i) th := by
      intro i hi; rw [← hstat i hi]; ring
    rw [Finset.sum_congr rfl hterm, ← Bw_dot S μ th]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hnull j]; ring
  rw [objLO_eq, objLO_eq, hBw]
  have h1 : ∑ i ∈ S, m i * (w i - θ * μ i) = (∑ i ∈ S, m i * w i) - θ * ∑ i ∈ S, m i * μ i := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i ∈ S, d i * (w i - θ * μ i) ^ 2
      = (∑ i ∈ S, d i * w i ^ 2) - 2 * θ * (∑ i ∈ S, d i * w i * μ i)
        + θ ^ 2 * ∑ i ∈ S, d i * μ i ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : ∑ i ∈ S, m i * μ i = ∑ i ∈ S, d i * w i * μ i := by
    have hz : ∑ i ∈ S, (m i * μ i - d i * w i * μ i) = 0 := by
      rw [← hlin]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hsplit : ∑ i ∈ S, (m i * μ i - d i * w i * μ i)
        = (∑ i ∈ S, m i * μ i) - ∑ i ∈ S, d i * w i * μ i := Finset.sum_sub_distrib _ _
    linarith
  rw [h1, h2, h3]
  ring

/-- Сдвинутый портфель остаётся допустимым, если `0 ≤ θμ_i ≤ w_i`. -/
lemma sub_nonneg_of_le {μ : ι → ℝ} {θ : ℝ} (hle : ∀ i ∈ S, θ * μ i ≤ w i) :
    ∀ i ∈ S, 0 ≤ w i - θ * μ i := fun i hi => by linarith [hle i hi]

/-- **Оценка потери.** При `0 ≤ θμ_i ≤ w_i` потеря `θ²Σd_iμ_i²` не превосходит
`θ·Σ d_i w_i μ_i` — то есть `θ`, умноженного на «взвешенную» массу направления. -/
theorem null_shift_loss_le (hd : ∀ i, 0 < d i) {μ : ι → ℝ} {θ : ℝ}
    (hnn : ∀ i ∈ S, 0 ≤ θ * μ i) (hle : ∀ i ∈ S, θ * μ i ≤ w i) :
    θ ^ 2 * ∑ i ∈ S, d i * μ i ^ 2 ≤ θ * ∑ i ∈ S, d i * w i * μ i := by
  simp only [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have h0 := hnn i hi
  have h1 := hle i hi
  have hdi := (hd i).le
  nlinarith [mul_nonneg hdi h0, mul_nonneg hdi (sub_nonneg.mpr h1)]

/-- Портфель с нулевой координатой живёт на меньшем носителе. -/
lemma objLO_erase_of_zero [DecidableEq ι] {i₀ : ι} (hi : i₀ ∈ S) (hz : w i₀ = 0) :
    objLO m d B Sf S w = objLO m d B Sf (S.erase i₀) w := by
  have hsub : S.erase i₀ ⊆ S := Finset.erase_subset _ _
  have hlin : ∑ i ∈ S.erase i₀, m i * w i = ∑ i ∈ S, m i * w i := by
    refine Finset.sum_subset hsub fun x hx hnx => ?_
    have : x = i₀ := by
      by_contra h
      exact hnx (Finset.mem_erase.mpr ⟨h, hx⟩)
    rw [this, hz]; ring
  have hquad : ∑ i ∈ S.erase i₀, ∑ i' ∈ S.erase i₀, Vmat d B Sf i i' * (w i * w i')
      = ∑ i ∈ S, ∑ i' ∈ S, Vmat d B Sf i i' * (w i * w i') := by
    have hinner : ∀ i, ∑ i' ∈ S.erase i₀, Vmat d B Sf i i' * (w i * w i')
        = ∑ i' ∈ S, Vmat d B Sf i i' * (w i * w i') := by
      intro i
      refine Finset.sum_subset hsub fun x hx hnx => ?_
      have : x = i₀ := by
        by_contra h
        exact hnx (Finset.mem_erase.mpr ⟨h, hx⟩)
      rw [this, hz]; ring
    rw [Finset.sum_congr rfl fun i _ => hinner i]
    refine Finset.sum_subset hsub fun x hx hnx => ?_
    have : x = i₀ := by
      by_contra h
      exact hnx (Finset.mem_erase.mpr ⟨h, hx⟩)
    rw [this]
    refine Finset.sum_eq_zero fun i' _ => ?_
    rw [hz]; ring
  simp only [objLO, hlin, hquad]

/-! ### Непустота гипотез леммы о нулевом направлении

Два актива с противоположными нагрузками: `B₀ = (1)`, `B₁ = (−1)`, `d = 1`,
`Σ_f = 1`, `m = w = (1,1)`. Тогда `B'w = 0`, значит `t̂ = 0` и условие
стационарности `d_iw_i + ⟨B_i,t̂⟩ = m_i` выполнено, а `μ = (1,1)` — ненулевое
направление нулевой факторной экспозиции. Потеря `θ²Σd_iμ_i² = 2θ²` не равна
нулю, то есть заключение содержательно. -/

/-- Нагрузки двух активов: `+1` и `−1`. -/
private def Bex : Fin 2 → Fin 1 → ℝ := fun i _ => if i = 0 then 1 else -1

example :
    (∀ j : Fin 1, Bw Bex Finset.univ (fun _ => (1:ℝ)) j = 0)
    ∧ (∀ i ∈ (Finset.univ : Finset (Fin 2)),
        (1:ℝ) * (1:ℝ) + dotp (Bex i) (tw (fun _ _ => (1:ℝ)) Bex Finset.univ (fun _ => (1:ℝ)))
          = (1:ℝ))
    ∧ (∑ _i ∈ (Finset.univ : Finset (Fin 2)), (1:ℝ) * (1:ℝ) ^ 2) = 2 := by
  have hBw : ∀ j : Fin 1, Bw Bex Finset.univ (fun _ => (1:ℝ)) j = 0 := by
    intro j; simp [Bw, Bex, Fin.sum_univ_two]
  refine ⟨hBw, fun i _ => ?_, by simp⟩
  have ht : tw (fun _ _ => (1:ℝ)) Bex Finset.univ (fun _ => (1:ℝ)) = fun _ => 0 := by
    funext j; simp [tw, hBw]
  rw [ht]
  simp [dotp]

/-! ### Связь с зажатыми наименьшими квадратами -/

/-- `(x/c)_+ = (x)_+/c` при `c > 0`. -/
lemma max_div_of_pos {x c : ℝ} (hc : 0 < c) : max (x / c) 0 = max x 0 / c := by
  rcases le_or_gt x 0 with h | h
  · have h2 : (0 : ℝ) ≤ c⁻¹ := (inv_pos.mpr hc).le
    have hxc : x / c ≤ 0 := by rw [div_eq_mul_inv]; nlinarith
    rw [max_eq_right h, max_eq_right hxc, zero_div]
  · have hxc : 0 ≤ x / c := by positivity
    rw [max_eq_left h.le, max_eq_left hxc]

/-- **`QLO` — это `psiC` на строках `rowsK` с зажатием только строк-активов.**

Отсюда к `QLO` применимы `psiC_shift_ge` (односторонний сдвиг узла),
`psiC_le_phi` (`QLO(S,t) ≤ φ_{S̄}(t)`, то есть long-only не превосходит
безусловной задачи) и `psiC_eq_phi_of_nonneg` (совпадение при неотрицательных
невязках — это `F_LO(S) = F(S̄)` на самосогласованном активном множестве). -/
theorem QLO_eq_psiC (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (t : κ → ℝ) :
    psiC (rowsK d B G) (targetsK m d) (fun r => r.isLeft) (barK (κ := κ) S) t
      = QLO m d B P S t := by
  rw [psiC, barK, Finset.sum_disjSum, QLO]
  have hassets : ∑ i ∈ S, resC (rowsK d B G) (targetsK m d) (fun r => r.isLeft)
        (Sum.inl i : ι ⊕ κ) t ^ 2
      = ∑ i ∈ S, (max (m i - dotp (B i) t) 0) ^ 2 / d i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdi := hd i
    have hpos : 0 < Real.sqrt (d i) := Real.sqrt_pos.mpr hdi
    have hsq : Real.sqrt (d i) ^ 2 = d i := Real.sq_sqrt hdi.le
    have hdot : dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) t
        = dotp (B i) t / Real.sqrt (d i) := by
      simp only [rowsK, Sum.elim_inl, dotp, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [resC, Sum.isLeft_inl, ite_true, targetsK, Sum.elim_inl, hdot]
    rw [div_sub_div_same, max_div_of_pos hpos, div_pow, hsq]
  have hanchor : ∑ l : κ, resC (rowsK d B G) (targetsK m d) (fun r => r.isLeft)
        (Sum.inr l : ι ⊕ κ) t ^ 2 = quadf P t := by
    rw [quadf_eq_sum_sq hG]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [resC, Sum.isLeft_inr, ite_false, Bool.false_eq_true, targetsK,
      Sum.elim_inr, rowsK, zero_sub]
    ring
  rw [hassets, hanchor]
  ring

/-- **Итог: `QLO(S, Σ_f B'w)` — точное значение long-only задачи на `S`.** -/
theorem isGreatest_objLO (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hk : IsKKT m d B Sf S w) :
    IsGreatest {v : ℝ | ∃ w' : ι → ℝ, (∀ i ∈ S, 0 ≤ w' i) ∧ v = objLO m d B Sf S w'}
      (QLO m d B P S (tw Sf B S w)) := by
  constructor
  · exact ⟨w, hk.nonneg, (objLO_eq_QLO_of_kkt hd hG hPS hk).symm⟩
  · rintro v ⟨w', hw', rfl⟩
    exact objLO_le_QLO hd hG hPS hw' _

/-! ### Непустота гипотез

`lake build` и аудит аксиом не отличают верное утверждение от бессодержательного
(урок из `findings_v12.md`, §4a). Поэтому — явные примеры, где `IsKKT`, `hG` и `hPS`
выполнены одновременно, причём во втором ограничение `w ≥ 0` активно. -/

/-- `hG` и `hPS` совместимы: `Σ_f = P = G = 1`. -/
example :
    (∀ j j' : Fin 1, ∑ l : Fin 1, (fun _ _ : Fin 1 => (1 : ℝ)) l j
        * (fun _ _ : Fin 1 => (1 : ℝ)) l j' = (fun _ _ : Fin 1 => (1 : ℝ)) j j')
    ∧ (∀ j j' : Fin 1, ∑ l : Fin 1, (fun _ _ : Fin 1 => (1 : ℝ)) j l
        * (fun _ _ : Fin 1 => (1 : ℝ)) l j' = if j = j' then 1 else 0) := by
  refine ⟨fun j j' => by simp, fun j j' => ?_⟩
  simp [Subsingleton.elim j j']

/-- Невырожденный случай: `m = d = 1`, `B = 0` — оптимум `w = 1 > 0`, зажатие не активно. -/
example : IsKKT (ι := Fin 1) (κ := Fin 1) (fun _ => 1) (fun _ => 1) (fun _ _ => 0)
    (fun _ _ => 1) Finset.univ (fun _ => 1) := by
  refine ⟨fun i _ => by norm_num, fun i _ => ?_, fun i _ _ => ?_⟩ <;>
    simp [tw, Bw, dotp]

/-- Ограничение активно: при `m = −1` оптимум `w = 0`, и обрезка срабатывает. -/
example : IsKKT (ι := Fin 1) (κ := Fin 1) (fun _ => -1) (fun _ => 1) (fun _ _ => 0)
    (fun _ _ => 1) Finset.univ (fun _ => 0) := by
  refine ⟨fun i _ => le_refl 0, fun i _ => ?_, fun i _ h => absurd h (lt_irrefl 0)⟩
  simp [tw, Bw, dotp]

/-- В этом примере `QLO = 0`: обрезка убирает вклад актива с `m < 0`
(без неё значение было бы `1`). -/
example : QLO (ι := Fin 1) (κ := Fin 1) (fun _ => -1) (fun _ => 1) (fun _ _ => 0)
    (fun _ _ => 1) Finset.univ (fun _ => 0) = 0 := by
  simp [QLO, quadf, dotp]

/-! ### Главное тождество сдвига

`theory_note_v5.md`, §13.1. Лемма N (`objLO_null_shift`) и оценка §4.2 — два
крайних случая ОДНОГО тождества: в точке стационарности для **любого**
направления `μ`

    objLO(w − θμ) = objLO(w) − θ²·( Σ_{i∈S} d_iμ_i²  +  ‖Σ_{i∈S} B_iμ_i‖²_{Σ_f} ) .

При `Σ B_iμ_i = 0` это Лемма N (потеря без множителя `‖·‖_{Σ_f}`), при
`μ = e_{i₀}`, `θ = w_{i₀}` — прямое обнуление координаты с ценой `w_{i₀}²V_{i₀i₀}`.
Линейный член исчезает в обоих случаях по одной причине: `Σμ_i(m_i − d_iw_i)`
есть `⟨Σμ_iB_i, t̂⟩`, а `t̂ = Σ_f B'w`, и симметрия `Σ_f` склеивает это с
перекрёстным членом квадратичной формы. -/

/-- Билинейная форма `x'Cz`. -/
noncomputable def bilf (C : κ → κ → ℝ) (x z : κ → ℝ) : ℝ :=
  ∑ j, ∑ j', C j j' * (x j * z j')

/-- Раскрытие квадратичной формы на разности. -/
lemma quadf_sub_smul (C : κ → κ → ℝ) (x z : κ → ℝ) (θ : ℝ) :
    quadf C (fun j => x j - θ * z j)
      = quadf C x - θ * (bilf C x z + bilf C z x) + θ ^ 2 * quadf C z := by
  simp only [quadf, bilf, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring

/-- Симметричная матрица даёт симметричную билинейную форму. -/
lemma bilf_comm (hSf : ∀ j j', Sf j j' = Sf j' j) (x z : κ → ℝ) :
    bilf Sf x z = bilf Sf z x := by
  simp only [bilf]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by
    rw [hSf j' j]; ring

/-- **Главное тождество сдвига.** Обобщение `objLO_null_shift` на произвольное `μ`. -/
theorem objLO_shift (hSf : ∀ j j', Sf j j' = Sf j' j)
    (hstat : ∀ i ∈ S, d i * w i + dotp (B i) (tw Sf B S w) = m i) (μ : ι → ℝ) (θ : ℝ) :
    objLO m d B Sf S (fun i => w i - θ * μ i)
      = objLO m d B Sf S w
        - θ ^ 2 * ((∑ i ∈ S, d i * μ i ^ 2) + quadf Sf (Bw B S μ)) := by
  set th := tw Sf B S w with hth
  have hBw : Bw B S (fun i => w i - θ * μ i) = fun j => Bw B S w j - θ * Bw B S μ j := by
    funext j; rw [Bw_sub_smul]
  -- линейный член: `Σ μ_i(m_i − d_iw_i) = ⟨Σμ_iB_i, t̂⟩ = (B'μ)'Σ_f(B'w)`
  have hlin : ∑ i ∈ S, μ i * (m i - d i * w i) = bilf Sf (Bw B S μ) (Bw B S w) := by
    have hterm : ∀ i ∈ S, μ i * (m i - d i * w i) = μ i * dotp (B i) th := by
      intro i hi; rw [← hstat i hi]; ring
    rw [Finset.sum_congr rfl hterm, ← Bw_dot S μ th]
    simp only [hth, tw, bilf, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
  have hsum : (∑ i ∈ S, m i * μ i) - ∑ i ∈ S, d i * w i * μ i
      = bilf Sf (Bw B S μ) (Bw B S w) := by
    rw [← hlin, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hcomm := bilf_comm (Sf := Sf) hSf (Bw B S w) (Bw B S μ)
  rw [objLO_eq, objLO_eq, hBw, quadf_sub_smul]
  have h1 : ∑ i ∈ S, m i * (w i - θ * μ i) = (∑ i ∈ S, m i * w i) - θ * ∑ i ∈ S, m i * μ i := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i ∈ S, d i * (w i - θ * μ i) ^ 2
      = (∑ i ∈ S, d i * w i ^ 2) - 2 * θ * (∑ i ∈ S, d i * w i * μ i)
        + θ ^ 2 * ∑ i ∈ S, d i * μ i ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2]
  linear_combination (-2 * θ) * hsum + θ * hcomm

/-- **Цена прямого обнуления координаты — ровно `w_{i₀}²V_{i₀i₀}` (§4.2).**
Множитель `V_{i₀i₀} = d_{i₀} + ‖B_{i₀}‖²_{Σ_f}` не ограничен — именно это и было
препятствием §4.2. Настоящая (с переоптимизацией) цена меньше и равна
произведению невязок, см. `phi_erase_cost`. -/
theorem objLO_erase_cost (hSf : ∀ j j', Sf j j' = Sf j' j)
    (hstat : ∀ i ∈ S, d i * w i + dotp (B i) (tw Sf B S w) = m i) {i₀ : ι} (hi : i₀ ∈ S) :
    objLO m d B Sf (S.erase i₀) (fun i => w i - w i₀ * (if i = i₀ then 1 else 0))
      = objLO m d B Sf S w - w i₀ ^ 2 * Vmat d B Sf i₀ i₀ := by
  set μ : ι → ℝ := fun i => if i = i₀ then 1 else 0 with hμ
  have hz : (fun i => w i - w i₀ * μ i) i₀ = 0 := by simp [hμ]
  have herase := objLO_erase_of_zero (m := m) (d := d) (B := B) (Sf := Sf)
    (w := fun i => w i - w i₀ * μ i) hi hz
  have hshift := objLO_shift (m := m) (d := d) (B := B) (Sf := Sf) (S := S) (w := w)
    hSf hstat μ (w i₀)
  have hd : ∑ i ∈ S, d i * μ i ^ 2 = d i₀ := by
    simp only [hμ]
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd hi h
  have hBμ : Bw B S μ = B i₀ := by
    funext j
    simp only [Bw, hμ]
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd hi h
  have hV : quadf Sf (B i₀) = Vmat d B Sf i₀ i₀ - d i₀ := by
    have hVi : Vmat d B Sf i₀ i₀ = d i₀ + ∑ j, ∑ j', B i₀ j * (Sf j j' * B i₀ j') := by
      simp [Vmat]
    have hq : ∑ j, ∑ j', B i₀ j * (Sf j j' * B i₀ j')
        = ∑ j, ∑ j', Sf j j' * (B i₀ j * B i₀ j') :=
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
    rw [hVi, hq]
    simp only [quadf]
    ring
  rw [← herase, hshift, hd, hBμ, hV]
  ring

/-! ### Непустота и содержательность главного тождества

На том же примере (`Bex`: `B₀ = 1`, `B₁ = −1`, `d = 1`, `Σ_f = 1`, `m = w = (1,1)`)
возьмём `μ = e₀` — направление с НЕнулевой экспозицией. Тогда множитель потери
в (★★) равен `Σd_iμ_i² + ‖Σ B_iμ_i‖²_{Σ_f} = 1 + 1 = 2`, то есть заключение
`objLO_shift` не вырождено, а `objLO_erase_cost` даёт цену `w₀²V₀₀ = 2`,
тоже отличную от нуля. (Для сравнения: у направления `μ = (1,1)` из Леммы N
экспозиция нулевая, и второе слагаемое пропадает.) -/

/-- Множитель потери для `μ = e₀` равен `2`, а не нулю. -/
example :
    (∑ i ∈ (Finset.univ : Finset (Fin 2)), (1:ℝ) * (if i = 0 then (1:ℝ) else 0) ^ 2)
      + quadf (fun _ _ => (1:ℝ)) (Bw Bex Finset.univ (fun i => if i = 0 then (1:ℝ) else 0))
      = 2 := by
  have hBw : Bw Bex Finset.univ (fun i => if i = 0 then (1:ℝ) else 0) = fun _ => (1:ℝ) := by
    funext j; simp [Bw, Bex, Fin.sum_univ_two]
  rw [hBw]
  simp [quadf, Fin.sum_univ_two]
  norm_num

/-- Та же величина как диагональ `V`: `V₀₀ = d₀ + ‖B₀‖²_{Σ_f} = 2`. -/
example : Vmat (fun _ => (1:ℝ)) Bex (fun _ _ => (1:ℝ)) 0 0 = 2 := by
  simp [Vmat, Bex]
  norm_num

end SparseSharpe.Factor
