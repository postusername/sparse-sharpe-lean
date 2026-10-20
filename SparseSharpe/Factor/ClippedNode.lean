import SparseSharpe.Factor.Duality
import SparseSharpe.Factor.GuaranteeBlock

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Тождество прямо-двойственного дефекта и оценки в узле (задача L2 ТЗ, сессия 23)

В узле `τ ∈ ℝ^K` усечённый вес `w_i(τ) = (m_i − ⟨B_i,τ⟩)_+/d_i ≥ 0` допустим для long-only
при любом `τ`, и (`objLO_wclip_deficit`)

    objLO(S, w(τ)) = QLO(S, τ) − (Σ_f B_S'w(τ) − τ)'Σ_f⁻¹(Σ_f B_S'w(τ) − τ),

то есть значение допустимого портфеля — это двойственная функция минус **дефект** (неотрицательная
квадратичная форма). Дефект равен `‖Gτ − Σ_{i∈S} v_i(τ)‖²`, `v_i(τ) = w_i(τ)·GΣ_fB_i ∈ ℝ^K`
(`defect_eq_sum_sq`): он зависит от `S` только через `K` чисел `Σ_{i∈S} v_il(τ)`. Поэтому ни
матрица Грама, ни фильтр, ни константа покрытия в динамике не нужны (`Factor/ClippedDP.lean`).

Оценки в узле (`ν = 1 + Σ_{i∈S} B_i'Σ_fB_i/d_i`, `t*` — минимум `QLO(S,·)`, `F* = QLO(S,t*)`):

* `QLO_smooth` — неравенство гладкости: `QLO(τ+h) ≤ QLO(τ) + 2·(линейный член) + ν·h'Σ_f⁻¹h`;
* `QLO_sub_le_of_min` — `QLO(S,τ) − F* ≤ ν·(τ−t*)'Σ_f⁻¹(τ−t*)`;
* `defect_le` — `дефект(τ) ≤ ν·(QLO(S,τ) − F*)` (шаг по неотрицательному дефекту, гладкость
  применяется в точке `τ`, а не в `t*`: без неравенства треугольника);
* `objLO_wclip_ge_of_node` — `objLO(S, w(τ)) ≥ F* − ν²·(τ−t*)'Σ_f⁻¹(τ−t*)`.

Оценка точна: на «Примере A» (`K = k = 1`, `d = 1`, `B = A`, `m = 1`) потеря равна
`(1+ω)ωδ²`, дефект `(1+ω)²δ²` (`code/check_clipped_dp.py`).
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ} {S : Finset ι}

/-! ### Алгебра квадратичной формы -/

/-- `Σ_j Σ_j' P_jj' s_j t_j'` для `s = Σ_f B'w` — это `⟨B'w, t⟩`. -/
lemma cross_P_tw (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (S : Finset ι) (w : ι → ℝ) (t : κ → ℝ) :
    ∑ j, ∑ j', P j j' * (tw Sf B S w j * t j') = ∑ j, Bw B S w j * t j := by
  have hPsymm := P_symm_of_root (P := P) (G := G) hG
  have hswap : ∑ j, ∑ j', P j j' * (tw Sf B S w j * t j')
      = ∑ j', (∑ j, P j' j * tw Sf B S w j) * t j' := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [hPsymm j j']; ring
  rw [hswap]
  exact Finset.sum_congr rfl fun j' _ => by rw [P_tw hPS j']

/-- `s'Ps = u'Σ_f u` для `s = Σ_f u`, `u = B'w`. -/
lemma quadf_P_tw (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (S : Finset ι) (w : ι → ℝ) :
    quadf P (tw Sf B S w) = quadf Sf (Bw B S w) := by
  have hPs : ∀ j, ∑ j', P j j' * tw Sf B S w j' = Bw B S w j := fun j => P_tw hPS j
  have h1 : quadf P (tw Sf B S w) = ∑ j, tw Sf B S w j * Bw B S w j := by
    simp only [quadf]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hPs j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j' _ => by ring
  have h2 : quadf Sf (Bw B S w) = ∑ j, Bw B S w j * tw Sf B S w j := by
    simp only [quadf, tw]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j' _ => by ring
  rw [h1, h2]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `quadf P (s − t) = ...` для `s = Σ_f B'w`. -/
lemma quadf_tw_sub (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (S : Finset ι) (w : ι → ℝ) (t : κ → ℝ) :
    quadf P (tw Sf B S w - t)
      = quadf Sf (Bw B S w) - 2 * (∑ j, Bw B S w j * t j) + quadf P t := by
  have hPsymm := P_symm_of_root (P := P) (G := G) hG
  rw [quadf_sub hPsymm, quadf_P_tw hG hPS, cross_P_tw hG hPS]

/-- **Тождество прямо-двойственного дефекта (Теорема 3.1 ТЗ).** Для любого `S` и любой точки
`τ` обрезанный вес `w(τ)` даёт

    objLO(S, w(τ)) = QLO(S, τ) − (Σ_f B_S'w(τ) − τ)'Σ_f⁻¹(Σ_f B_S'w(τ) − τ).
-/
theorem objLO_wclip_deficit (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (S : Finset ι) (t : κ → ℝ) :
    objLO m d B Sf S (wclip m d B t)
      = QLO m d B P S t - quadf P (tw Sf B S (wclip m d B t) - t) := by
  rw [objLO_wclip hd, quadf_tw_sub hG hPS, QLO]
  ring

/-- Дефект неотрицателен (тривиальное следствие, но удобное). -/
lemma defect_nonneg (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (S : Finset ι) (w : ι → ℝ) (t : κ → ℝ) :
    0 ≤ quadf P (tw Sf B S w - t) := quadf_nonneg_of_root hG _

/-! ### Дефект в координатах `G`: `v_i(τ) = w_i·GΣ_fB_i` -/

/-- `v_il = w_i · Σ_j G_lj (Σ_f B_i)_j`: вклад актива `i` с весом `w_i` в `l`-ю координату `GΣ_fB'w`. -/
noncomputable def vcoord (G Sf : κ → κ → ℝ) (B : ι → κ → ℝ) (w : ι → ℝ) (i : ι) (l : κ) : ℝ :=
  w i * ∑ j, G l j * ∑ m, Sf j m * B i m

/-- `(G·Σ_f B_S'w)_l = Σ_{i∈S} v_il`. -/
lemma dotp_G_tw (S : Finset ι) (w : ι → ℝ) (l : κ) :
    dotp (G l) (tw Sf B S w) = ∑ i ∈ S, vcoord G Sf B w i l := by
  have h1 : dotp (G l) (tw Sf B S w)
      = ∑ j, ∑ j', ∑ i ∈ S, G l j * (Sf j j' * (B i j' * w i)) := by
    simp only [dotp, tw, Bw, Finset.mul_sum]
  have h2 : ∑ i ∈ S, vcoord G Sf B w i l
      = ∑ i ∈ S, ∑ j, ∑ j', G l j * (Sf j j' * (B i j' * w i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [vcoord, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
  rw [h1, h2]
  calc ∑ j, ∑ j', ∑ i ∈ S, G l j * (Sf j j' * (B i j' * w i))
      = ∑ j, ∑ i ∈ S, ∑ j', G l j * (Sf j j' * (B i j' * w i)) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i ∈ S, ∑ j, ∑ j', G l j * (Sf j j' * (B i j' * w i)) := Finset.sum_comm

lemma dotp_sub' (a u v : κ → ℝ) : dotp a (u - v) = dotp a u - dotp a v := by
  simp only [dotp, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- **Дефект как сумма квадратов:** `(Σ_f B_S'w − τ)'Σ_f⁻¹(Σ_f B_S'w − τ) = ‖Gτ − Σ_S v_i‖²`. -/
lemma defect_eq_sum_sq (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (S : Finset ι) (w : ι → ℝ) (t : κ → ℝ) :
    quadf P (tw Sf B S w - t)
      = ∑ l, (∑ i ∈ S, vcoord G Sf B w i l - dotp (G l) t) ^ 2 := by
  rw [quadf_eq_sum_sq hG]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [dotp_sub', dotp_G_tw]

/-- `Σ_l v_il² = w_i²·B_i'Σ_fB_i`. -/
lemma sum_sq_vcoord (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (w : ι → ℝ) (i : ι) :
    ∑ l, vcoord G Sf B w i l ^ 2 = w i ^ 2 * sysVar B Sf i := by
  simp only [vcoord, mul_pow]
  rw [← Finset.mul_sum, sum_sq_GSfB hG hPS i]

/-- Одна координата не больше всего вектора: `v_il² ≤ w_i²·B_i'Σ_fB_i`. -/
lemma vcoord_sq_le (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (w : ι → ℝ) (i : ι) (l : κ) :
    vcoord G Sf B w i l ^ 2 ≤ w i ^ 2 * sysVar B Sf i := by
  rw [← sum_sq_vcoord hG hPS]
  exact Finset.single_le_sum (f := fun l => vcoord G Sf B w i l ^ 2)
    (fun l _ => sq_nonneg _) (Finset.mem_univ l)

/-! ### Неравенство Коши–Буняковского в метрике `Σ_f⁻¹` и гладкость -/

/-- `⟨B_i, v⟩² ≤ (B_i'Σ_fB_i)·v'Σ_f⁻¹v`. -/
lemma sq_dotp_le_sysVar (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (i : ι) (v : κ → ℝ) :
    dotp (B i) v ^ 2 ≤ sysVar B Sf i * quadf P v := by
  have hBv : dotp (B i) v
      = ∑ l, (∑ j, G l j * (∑ m, Sf j m * B i m)) * (∑ j, G l j * v j) := by
    rw [sum_G_mul_G hG]
    simp only [dotp]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [← Finset.sum_mul, sum_SfB_mul_P hG hPS i j']
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun l => ∑ j, G l j * (∑ m, Sf j m * B i m)) (fun l => ∑ j, G l j * v j)
  rw [← hBv, sum_sq_GSfB hG hPS i] at hcs
  rw [quadf_eq_sum_sq hG]
  simpa [dotp] using hcs

/-- Плечо носителя `S`: `Σ_{i∈S} B_i'Σ_fB_i/d_i`. -/
noncomputable def levSum (d : ι → ℝ) (B : ι → κ → ℝ) (Sf : κ → κ → ℝ) (S : Finset ι) : ℝ :=
  ∑ i ∈ S, sysVar B Sf i / d i

lemma levSum_nonneg (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (S : Finset ι) :
    0 ≤ levSum d B Sf S :=
  Finset.sum_nonneg fun i _ => div_nonneg (sysVar_nonneg hG hPS i) (hd i).le

/-- `Σ_{i∈S} ⟨B_i,h⟩²/d_i ≤ levSum · h'Σ_f⁻¹h`. -/
lemma sum_sq_dotp_le (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (S : Finset ι) (h : κ → ℝ) :
    ∑ i ∈ S, dotp (B i) h ^ 2 / d i ≤ levSum d B Sf S * quadf P h := by
  rw [levSum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (sq_dotp_le_sysVar hG hPS i h) (hd i).le

/-- Поточечная гладкость `(x)_+²`: `(x)_+² ≤ (y)_+² + 2(y)_+(x−y) + (x−y)²`. -/
lemma pos_sq_le (x y : ℝ) :
    max x 0 ^ 2 ≤ max y 0 ^ 2 + 2 * max y 0 * (x - y) + (x - y) ^ 2 := by
  rcases le_total x 0 with hx | hx <;> rcases le_total y 0 with hy | hy
  · rw [max_eq_right hx, max_eq_right hy]; nlinarith [sq_nonneg (x - y)]
  · rw [max_eq_right hx, max_eq_left hy]; nlinarith [sq_nonneg x]
  · rw [max_eq_left hx, max_eq_right hy]; nlinarith [sq_nonneg (x - y), sq_nonneg y]
  · rw [max_eq_left hx, max_eq_left hy]; nlinarith

/-- `quadf P (τ + h) = quadf P τ + 2·ΣΣ P τ h + quadf P h`. -/
lemma quadf_add (hG : ∀ j j', ∑ l, G l j * G l j' = P j j') (τ h : κ → ℝ) :
    quadf P (τ + h)
      = quadf P τ + 2 * (∑ j, ∑ j', P j j' * (τ j * h j')) + quadf P h := by
  have hPsymm := P_symm_of_root (P := P) (G := G) hG
  have hcross : ∑ j, ∑ j', P j j' * (h j * τ j') = ∑ j, ∑ j', P j j' * (τ j * h j') := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by
      rw [hPsymm j' j]; ring
  simp only [quadf, Pi.add_apply]
  have hexp : ∀ j j', P j j' * ((τ j + h j) * (τ j' + h j'))
      = P j j' * (τ j * τ j') + P j j' * (τ j * h j') + P j j' * (h j * τ j')
        + P j j' * (h j * h j') := fun _ _ => by ring
  simp only [hexp, Finset.sum_add_distrib]
  rw [hcross]
  ring

lemma quadf_smul (c : ℝ) (x : κ → ℝ) : quadf P (c • x) = c ^ 2 * quadf P x := by
  simp only [quadf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring

/-- **Гладкость двойственной функции** в произвольной точке `τ`:

    QLO(S, τ+h) ≤ QLO(S, τ) + 2·(ΣΣ P_jj' τ_j h_j' − ⟨B_S'w(τ), h⟩) + (1 + levSum)·h'Σ_f⁻¹h. -/
theorem QLO_smooth (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (S : Finset ι) (τ h : κ → ℝ) :
    QLO m d B P S (τ + h)
      ≤ QLO m d B P S τ
        + 2 * ((∑ j, ∑ j', P j j' * (τ j * h j')) - ∑ j, Bw B S (wclip m d B τ) j * h j)
        + (1 + levSum d B Sf S) * quadf P h := by
  have hitem : ∀ i ∈ S,
      max (m i - dotp (B i) (τ + h)) 0 ^ 2 / d i
        ≤ max (m i - dotp (B i) τ) 0 ^ 2 / d i
          - 2 * (wclip m d B τ i * dotp (B i) h) + dotp (B i) h ^ 2 / d i := by
    intro i _
    have hdi := hd i
    have hxy : (m i - dotp (B i) (τ + h)) - (m i - dotp (B i) τ) = - dotp (B i) h := by
      simp only [dotp, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
    have hp := pos_sq_le (m i - dotp (B i) (τ + h)) (m i - dotp (B i) τ)
    rw [hxy] at hp
    have hw : wclip m d B τ i = max (m i - dotp (B i) τ) 0 / d i := rfl
    rw [hw]
    have : max (m i - dotp (B i) (τ + h)) 0 ^ 2 / d i
        ≤ (max (m i - dotp (B i) τ) 0 ^ 2 + 2 * max (m i - dotp (B i) τ) 0 * (- dotp (B i) h)
            + (- dotp (B i) h) ^ 2) / d i :=
      div_le_div_of_nonneg_right hp hdi.le
    refine le_trans this (le_of_eq ?_)
    field_simp
    ring
  have hsum := Finset.sum_le_sum hitem
  have hsplit : ∑ i ∈ S, (max (m i - dotp (B i) τ) 0 ^ 2 / d i
      - 2 * (wclip m d B τ i * dotp (B i) h) + dotp (B i) h ^ 2 / d i)
      = ∑ i ∈ S, max (m i - dotp (B i) τ) 0 ^ 2 / d i
        - 2 * ∑ j, Bw B S (wclip m d B τ) j * h j + ∑ i ∈ S, dotp (B i) h ^ 2 / d i := by
    rw [Bw_dot, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsplit] at hsum
  have hsq := sum_sq_dotp_le (B := B) (Sf := Sf) hd hG hPS S h
  have hq := quadf_add hG τ h
  rw [QLO, QLO, hq]
  nlinarith [hsum, hsq]

/-! ### Оценки в узле -/

/-- **Гладкость в точке минимума:** `QLO(S,τ) − F* ≤ ν·(τ − t*)'Σ_f⁻¹(τ − t*)`, `ν = 1 + levSum`. -/
theorem QLO_sub_le_of_min (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {S : Finset ι} {t₀ : κ → ℝ} (hmin : ∀ t, QLO m d B P S t₀ ≤ QLO m d B P S t) (τ : κ → ℝ) :
    QLO m d B P S τ - QLO m d B P S t₀ ≤ (1 + levSum d B Sf S) * quadf P (τ - t₀) := by
  have hsm := QLO_smooth (m := m) (d := d) (B := B) (Sf := Sf) hd hG hPS S t₀ (τ - t₀)
  have hτ : t₀ + (τ - t₀) = τ := by funext j; simp
  rw [hτ] at hsm
  -- линейный член обращается в ноль: `B'w(t₀) = Σ_f⁻¹ t₀`
  have hBw : ∀ j, Bw B S (wclip m d B t₀) j = ∑ j', P j j' * t₀ j' :=
    fun j => Bw_eq_of_min (G := G) hd hG hmin j
  have hlin : (∑ j, ∑ j', P j j' * (t₀ j * (τ - t₀) j'))
      - ∑ j, Bw B S (wclip m d B t₀) j * (τ - t₀) j = 0 := by
    have hPsymm := P_symm_of_root (P := P) (G := G) hG
    have h1 : ∑ j, Bw B S (wclip m d B t₀) j * (τ - t₀) j
        = ∑ j, ∑ j', P j j' * (t₀ j' * (τ - t₀) j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hBw j, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j' _ => by ring
    rw [h1, Finset.sum_comm]
    simp only [sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by
      rw [hPsymm j' j]
  rw [hlin] at hsm
  linarith

/-- **Дефект не больше `ν·(QLO(S,τ) − F)`** при любой нижней границе `F ≤ QLO(S,·)`.
Гладкость применена в точке `τ`, шаг `h = (Σ_f B'w(τ) − τ)/ν`. -/
theorem defect_le (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (S : Finset ι) {F : ℝ} (hF : ∀ t, F ≤ QLO m d B P S t) (τ : κ → ℝ) :
    quadf P (tw Sf B S (wclip m d B τ) - τ)
      ≤ (1 + levSum d B Sf S) * (QLO m d B P S τ - F) := by
  set ν := 1 + levSum d B Sf S with hν
  have hνpos : 0 < ν := by
    have := levSum_nonneg (B := B) hd hG hPS S
    rw [hν]; linarith
  set g : κ → ℝ := tw Sf B S (wclip m d B τ) - τ with hg
  set D := quadf P g with hD
  set h : κ → ℝ := ν⁻¹ • g with hh
  have hsm := QLO_smooth (m := m) (d := d) (B := B) (Sf := Sf) hd hG hPS S τ h
  have hPsymm := P_symm_of_root (P := P) (G := G) hG
  -- линейный член: `ΣΣ P τ h − ⟨B'w, h⟩ = −ν⁻¹·D`
  have hlin : (∑ j, ∑ j', P j j' * (τ j * h j'))
      - ∑ j, Bw B S (wclip m d B τ) j * h j = - ν⁻¹ * D := by
    have h1 : ∑ j, Bw B S (wclip m d B τ) j * h j
        = ∑ j, ∑ j', P j j' * (tw Sf B S (wclip m d B τ) j * h j') := by
      rw [cross_P_tw hG hPS]
    have h2 : (∑ j, ∑ j', P j j' * (τ j * h j'))
        - ∑ j, ∑ j', P j j' * (tw Sf B S (wclip m d B τ) j * h j')
        = - ∑ j, ∑ j', P j j' * (g j * h j') := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j' _ => ?_
      simp only [hg, Pi.sub_apply]; ring
    have h3 : ∑ j, ∑ j', P j j' * (g j * h j') = ν⁻¹ * D := by
      rw [hD, quadf, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      simp only [hh, Pi.smul_apply, smul_eq_mul]; ring
    rw [h1, h2, h3]; ring
  have hqh : quadf P h = ν⁻¹ ^ 2 * D := by rw [hh, quadf_smul]
  have hlow := hF (τ + h)
  rw [hlin, hqh] at hsm
  have hνne : ν ≠ 0 := hνpos.ne'
  -- `F ≤ QLO τ − 2ν⁻¹D + ν·ν⁻²·D = QLO τ − ν⁻¹D`
  have hcalc : 2 * (-ν⁻¹ * D) + ν * (ν⁻¹ ^ 2 * D) = - ν⁻¹ * D := by
    field_simp; ring
  have : F ≤ QLO m d B P S τ - ν⁻¹ * D := by
    have := le_trans hlow hsm
    linarith [hcalc]
  -- умножаем на `ν`
  have h5 : ν⁻¹ * D ≤ QLO m d B P S τ - F := by linarith
  calc D = ν * (ν⁻¹ * D) := by field_simp
    _ ≤ ν * (QLO m d B P S τ - F) := mul_le_mul_of_nonneg_left h5 hνpos.le

/-- **Значение усечённого веса в узле.** Если `t₀` минимизирует `QLO(S,·)`, то в любой точке `τ`

    objLO(S, w(τ)) ≥ F* − ν²·(τ − t₀)'Σ_f⁻¹(τ − t₀),    F* = QLO(S, t₀),  ν = 1 + levSum. -/
theorem objLO_wclip_ge_of_node (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {S : Finset ι} {t₀ : κ → ℝ} (hmin : ∀ t, QLO m d B P S t₀ ≤ QLO m d B P S t)
    (τ : κ → ℝ) :
    QLO m d B P S t₀ - (1 + levSum d B Sf S) ^ 2 * quadf P (τ - t₀)
      ≤ objLO m d B Sf S (wclip m d B τ) := by
  have hν : 0 ≤ 1 + levSum d B Sf S := by
    have := levSum_nonneg (B := B) hd hG hPS S
    linarith
  have hdef := defect_le (m := m) (B := B) (Sf := Sf) hd hG hPS S hmin τ
  have hgap := QLO_sub_le_of_min (m := m) (B := B) (Sf := Sf) hd hG hPS hmin τ
  rw [objLO_wclip_deficit hd hG hPS S τ]
  have hge := hmin τ
  have : (1 + levSum d B Sf S) * (QLO m d B P S τ - QLO m d B P S t₀)
      ≤ (1 + levSum d B Sf S) * ((1 + levSum d B Sf S) * quadf P (τ - t₀)) :=
    mul_le_mul_of_nonneg_left hgap hν
  nlinarith [this, hdef, hge]

end SparseSharpe.Factor
