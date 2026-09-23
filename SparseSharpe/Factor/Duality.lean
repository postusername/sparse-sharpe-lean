import SparseSharpe.Factor.Attain
import SparseSharpe.Factor.LongOnlyK

set_option linter.style.header false

/-!
# Сильная двойственность: то, что считает алгоритм, и есть long-only оптимум

Для практика вся цепочка имеет смысл только если величина, которую считает
динамика, — это в точности значение портфельной задачи

    F_LO(S)  =  max { 2·m_S'w − w'V_S w : w ≥ 0 },    V = D + BΣ_fB'.

Алгоритм же считает `QLO(S,t) = t'Σ_f⁻¹t + Σ_{i∈S}((m_i − ⟨B_i,t⟩)_+)²/d_i`
и минимизирует по `t`. Что `max = min`, до сих пор было известно **только при
гипотезе, что точка ККТ существует** (`isGreatest_objLO`). Здесь гипотеза снята.

Ход: минимум `QLO` достигается (`Factor/Attain.lean`, коэрцитивность по якорям);
в точке минимума активное множество удовлетворяет нормальным уравнениям
(Теорема X, `Factor/Reduction.lean`); переписав их в координатах задачи,
получаем `B'w = Σ_f⁻¹t₀` для обрезанного веса `w = w(t₀)`, откуда
`Σ_f B'w = t₀` и условия ККТ.

Итог — `isGreatest_objLO_isLeast_QLO`:

    max_{w ≥ 0} objLO(S,w)  =  min_t QLO(S,t) ,

и оба экстремума **достигаются**. Ни одна из гипотез не говорит о внутренних
объектах алгоритма: только `d > 0`, `G'G = Σ_f⁻¹`, `Σ_f⁻¹Σ_f = 1`.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ} {S : Finset ι} {w : ι → ℝ}

/-! ### Зажатый момент — это обычный момент активного множества -/

omit [Fintype ι] [DecidableEq κ] in
/-- `M_t(S)` по зажатым невязкам совпадает с обычным первым моментом активного
множества: вне `A(t)` зажатая невязка равна нулю, а внутри зажатие не действует. -/
lemma momC_eq_mom_activeSet (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (S : Finset ι)
    (t v : κ → ℝ) :
    momC a y cl S t v = mom a y (activeSet a y cl S t) t v := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (fun i => cl i → 0 < y i - dotp (a i) t) (fun i => resC a y cl i t * dotp (a i) v)
  have hzero : ∑ i ∈ S.filter (fun i => ¬ (cl i → 0 < y i - dotp (a i) t)),
      resC a y cl i t * dotp (a i) v = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    obtain ⟨hiS, hni⟩ := Finset.mem_filter.mp hi
    have : i ∉ activeSet a y cl S t := fun h => hni (mem_activeSet.mp h).2
    rw [resC_eq_zero_of_not_mem hiS this, zero_mul]
  have hact : ∑ i ∈ S.filter (fun i => cl i → 0 < y i - dotp (a i) t),
      resC a y cl i t * dotp (a i) v
      = mom a y (activeSet a y cl S t) t v := by
    rw [mom]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨_, hp⟩ := Finset.mem_filter.mp hi
    by_cases hc : cl i
    · have hpos : 0 < y i - dotp (a i) t := hp hc
      simp [resC, hc, max_eq_left hpos.le]
    · simp [resC, hc]
  rw [momC, ← hsplit, hzero, hact, add_zero]

/-! ### Нормальные уравнения активного множества в координатах задачи -/

/-- Вклад якорных строк в зажатый момент — это билинейная форма `−t'Σ_f⁻¹v`. -/
lemma anchor_part (hG : ∀ j j', ∑ l, G l j * G l j' = P j j') (t v : κ → ℝ) :
    ∑ l : κ, resC (rowsK d B G) (targetsK m d) (fun r => r.isLeft)
        (Sum.inr l : ι ⊕ κ) t * dotp (rowsK d B G (Sum.inr l : ι ⊕ κ)) v
      = -bilf P t v := by
  have h1 : ∀ l : κ, resC (rowsK d B G) (targetsK m d) (fun r => r.isLeft)
      (Sum.inr l : ι ⊕ κ) t * dotp (rowsK d B G (Sum.inr l : ι ⊕ κ)) v
      = -(∑ j, ∑ j', (G l j * G l j') * (t j * v j')) := by
    intro l
    simp only [resC, Sum.isLeft_inr, Bool.false_eq_true, ite_false, targetsK, rowsK,
      Sum.elim_inr, zero_sub, neg_mul, dotp]
    rw [Finset.sum_mul_sum]
    simp only [Finset.mul_sum, neg_inj]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
  rw [Finset.sum_congr rfl fun l _ => h1 l, Finset.sum_neg_distrib, bilf]
  congr 1
  rw [sum_swap3]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by
    rw [← Finset.sum_mul, hG j j']

/-- Вклад активов в зажатый момент — это `⟨B'w(t), v⟩` для обрезанного веса. -/
lemma asset_part (hd : ∀ i, 0 < d i) (S : Finset ι) (t v : κ → ℝ) :
    ∑ i ∈ S, resC (rowsK d B G) (targetsK m d) (fun r => r.isLeft)
        (Sum.inl i : ι ⊕ κ) t * dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) v
      = ∑ j, Bw B S (wclip m d B t) j * v j := by
  have hterm : ∀ i ∈ S, resC (rowsK d B G) (targetsK m d) (fun r => r.isLeft)
      (Sum.inl i : ι ⊕ κ) t * dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) v
      = ∑ j, (B i j * wclip m d B t i) * v j := by
    intro i _
    have hdi := hd i
    have hpos : 0 < Real.sqrt (d i) := Real.sqrt_pos.mpr hdi
    have hne : Real.sqrt (d i) ≠ 0 := ne_of_gt hpos
    have hsq : Real.sqrt (d i) * Real.sqrt (d i) = d i := Real.mul_self_sqrt hdi.le
    have hdot : ∀ u : κ → ℝ, dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) u
        = dotp (B i) u / Real.sqrt (d i) := by
      intro u
      simp only [rowsK, Sum.elim_inl, dotp, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hres : resC (rowsK d B G) (targetsK m d) (fun r => r.isLeft)
        (Sum.inl i : ι ⊕ κ) t = max (m i - dotp (B i) t) 0 / Real.sqrt (d i) := by
      simp only [resC, Sum.isLeft_inl, ite_true, targetsK, Sum.elim_inl, hdot]
      rw [← sub_div, max_div_of_pos hpos]
    rw [hres, hdot,
      show (∑ j, (B i j * wclip m d B t i) * v j) = wclip m d B t i * dotp (B i) v from by
        rw [dotp, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring,
      wclip, div_mul_div_comm, hsq]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [Bw, Finset.sum_mul]

/-- **Зажатый момент набора `S̄` в координатах задачи.** -/
theorem momC_barK_eq (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (S : Finset ι) (t v : κ → ℝ) :
    momC (rowsK d B G) (targetsK m d) (fun r => r.isLeft) (barK (κ := κ) S) t v
      = (∑ j, Bw B S (wclip m d B t) j * v j) - bilf P t v := by
  rw [momC, barK, Finset.sum_disjSum, asset_part (G := G) hd S t v,
    anchor_part (m := m) (d := d) (B := B) (P := P) hG t v]
  ring

/-! ### От минимума `QLO` к точке ККТ -/

/-- `Σ_f⁻¹·Σ_f = 1` влечёт `Σ_f·Σ_f⁻¹ = 1` (квадратные матрицы над коммутативным
кольцом: односторонняя обратимость двусторонняя). -/
lemma SP_of_PS (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) :
    ∀ j j', ∑ l, Sf j l * P l j' = if j = j' then 1 else 0 := by
  have hmat : (Matrix.of P) * (Matrix.of Sf) = 1 := by
    ext j j'
    simpa [Matrix.mul_apply, Matrix.one_apply] using hPS j j'
  have hcomm : (Matrix.of Sf) * (Matrix.of P) = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl κ)).mp hmat
  intro j j'
  have := congrFun (congrFun hcomm j) j'
  simpa [Matrix.mul_apply, Matrix.one_apply] using this

/-- Базисный орт в `ℝ^K`. -/
noncomputable def basisVec (j₀ : κ) : κ → ℝ := fun j => if j = j₀ then 1 else 0

/-- Билинейная форма против базисного орта: `bilf C t e_{j₀} = Σ_j C_{j j₀} t_j`. -/
lemma bilf_basisVec (C : κ → κ → ℝ) (t : κ → ℝ) (j₀ : κ) :
    bilf C t (basisVec j₀) = ∑ j, C j j₀ * t j := by
  simp only [bilf, basisVec]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j₀]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ j₀) h

lemma sum_mul_basisVec (u : κ → ℝ) (j₀ : κ) : (∑ j, u j * basisVec j₀ j) = u j₀ := by
  simp only [basisVec]
  rw [Finset.sum_eq_single j₀]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ j₀) h

/-- **Главный шаг.** В точке минимума `QLO` обрезанный вес `w(t₀)` даёт
`B'w = Σ_f⁻¹t₀`, то есть `t₀ = Σ_f B'w` — та самая точка, в которой
`isGreatest_objLO` считает значение. -/
theorem Bw_eq_of_min (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    {t₀ : κ → ℝ} (hmin : ∀ t, QLO m d B P S t₀ ≤ QLO m d B P S t) (j₀ : κ) :
    Bw B S (wclip m d B t₀) j₀ = ∑ j, P j₀ j * t₀ j := by
  classical
  have hpsi : ∀ t, psiC (rowsK d B G) (targetsK m d) (fun r => r.isLeft)
      (barK (κ := κ) S) t₀ ≤ psiC (rowsK d B G) (targetsK m d) (fun r => r.isLeft)
      (barK (κ := κ) S) t := by
    intro t
    rw [QLO_eq_psiC (P := P) hd hG, QLO_eq_psiC (P := P) hd hG]
    exact hmin t
  have hnorm := isNormal_activeSet_of_min (a := rowsK d B G) (y := targetsK m d)
    (cl := fun r => r.isLeft) (S := barK (κ := κ) S) (t₀ := t₀) hpsi
  have hzero : ∀ v, momC (rowsK d B G) (targetsK m d) (fun r => r.isLeft)
      (barK (κ := κ) S) t₀ v = 0 := by
    intro v
    rw [momC_eq_mom_activeSet]
    exact hnorm v
  have hid := momC_barK_eq (m := m) (B := B) (P := P) (G := G) hd hG S t₀ (basisVec j₀)
  rw [hzero, sum_mul_basisVec, bilf_basisVec] at hid
  have hsymm := P_symm_of_root (P := P) (G := G) hG
  have : Bw B S (wclip m d B t₀) j₀ = ∑ j, P j j₀ * t₀ j := by linarith
  rw [this]
  exact Finset.sum_congr rfl fun j _ => by rw [hsymm j j₀]

/-- В точке минимума `QLO` точка `Σ_f B'w(t₀)` — это сам `t₀`. -/
theorem tw_wclip_eq (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {t₀ : κ → ℝ} (hmin : ∀ t, QLO m d B P S t₀ ≤ QLO m d B P S t) :
    tw Sf B S (wclip m d B t₀) = t₀ := by
  have hSP := SP_of_PS (P := P) (Sf := Sf) hPS
  funext j
  simp only [tw]
  have hBw : ∀ j' : κ, Bw B S (wclip m d B t₀) j' = ∑ l, P j' l * t₀ l :=
    fun j' => Bw_eq_of_min (G := G) hd hG hmin j'
  rw [Finset.sum_congr rfl fun j' _ => by rw [hBw j']]
  have hswap : ∑ j' : κ, Sf j j' * ∑ l, P j' l * t₀ l
      = ∑ l, (∑ j', Sf j j' * P j' l) * t₀ l := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j' _ => by ring
  rw [hswap, Finset.sum_congr rfl fun l _ => by rw [hSP j l]]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **Точка ККТ существует и строится явно.** Если `t₀` доставляет минимум `QLO`,
то обрезанный вес `w_i = (m_i − ⟨B_i,t₀⟩)_+/d_i` удовлетворяет условиям ККТ
задачи `max{2m'w − w'Vw : w ≥ 0}`. -/
theorem isKKT_wclip_of_min (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {t₀ : κ → ℝ} (hmin : ∀ t, QLO m d B P S t₀ ≤ QLO m d B P S t) :
    IsKKT m d B Sf S (wclip m d B t₀) := by
  have htw : tw Sf B S (wclip m d B t₀) = t₀ := tw_wclip_eq (P := P) hd hG hPS hmin
  refine ⟨fun i _ => wclip_nonneg hd t₀ i, fun i _ => ?_, fun i _ hpos => ?_⟩
  · rw [htw]
    have hdi : d i ≠ 0 := ne_of_gt (hd i)
    have hdw : d i * wclip m d B t₀ i = max (m i - dotp (B i) t₀) 0 := by
      rw [wclip]; field_simp
    rw [hdw]; exact le_max_left _ _
  · rw [htw]
    have hdi : d i ≠ 0 := ne_of_gt (hd i)
    have hmax : 0 < max (m i - dotp (B i) t₀) 0 := by
      by_contra hcon
      push_neg at hcon
      have hz : max (m i - dotp (B i) t₀) 0 = 0 := le_antisymm hcon (le_max_right _ _)
      rw [wclip, hz, zero_div] at hpos
      exact lt_irrefl 0 hpos
    have hr : 0 < m i - dotp (B i) t₀ := by
      rcases max_cases (m i - dotp (B i) t₀) (0 : ℝ) with ⟨h1, _⟩ | ⟨h1, _⟩
      · rwa [h1] at hmax
      · rw [h1] at hmax; exact absurd hmax (lt_irrefl 0)
    rw [wclip, max_eq_left hr.le]
    field_simp

/-! ### Минимум достигается, и это и есть long-only оптимум -/

/-- Якорные строки как набор: `K` строк `Σ_f^{-1/2}` без активов. -/
noncomputable def anchorRows (ι : Type*) [DecidableEq ι] (κ : Type*) [Fintype κ]
    [DecidableEq κ] : Finset (ι ⊕ κ) := (∅ : Finset ι).disjSum Finset.univ

lemma inr_mem_anchorRows (l : κ) : (Sum.inr l : ι ⊕ κ) ∈ anchorRows ι κ := by
  simp [anchorRows, Finset.inr_mem_disjSum]

lemma anchorRows_subset_barK (S : Finset ι) : anchorRows ι κ ⊆ barK (κ := κ) S := by
  intro x hx
  rcases x with i | l
  · simp [anchorRows, Finset.inl_mem_disjSum] at hx
  · exact inr_mem_barK S l

lemma not_isLeft_of_mem_anchorRows {x : ι ⊕ κ} (hx : x ∈ anchorRows ι κ) : ¬ x.isLeft := by
  rcases x with i | l
  · simp [anchorRows, Finset.inl_mem_disjSum] at hx
  · simp

lemma targets_eq_zero_of_mem_anchorRows {x : ι ⊕ κ} (hx : x ∈ anchorRows ι κ) :
    targetsK m d x = 0 := by
  rcases x with i | l
  · simp [anchorRows, Finset.inl_mem_disjSum] at hx
  · simp [targetsK]

/-- **Минимум `QLO` достигается.** Гипотез о внутренних объектах алгоритма нет:
только `d > 0`, `G'G = Σ_f⁻¹` и `Σ_f⁻¹Σ_f = 1`. -/
theorem exists_min_QLO [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (S : Finset ι) :
    ∃ t₀ : κ → ℝ, ∀ t, QLO m d B P S t₀ ≤ QLO m d B P S t := by
  obtain ⟨t₀, hmin⟩ := exists_min_psiC (a := rowsK d B G) (y := targetsK m d)
    (cl := fun r => r.isLeft) (S := barK (κ := κ) S) (base := anchorRows ι κ)
    (Ta := fun l => (Sum.inr l : ι ⊕ κ))
    (anchorRows_subset_barK S) (fun _ hx => not_isLeft_of_mem_anchorRows hx)
    (fun _ hx => targets_eq_zero_of_mem_anchorRows hx)
    (fun l => inr_mem_anchorRows l)
    (det_anchor_ne_zero (d := d) (B := B) (P := P) (Sf := Sf) hG hPS)
  refine ⟨t₀, fun t => ?_⟩
  rw [← QLO_eq_psiC (P := P) hd hG, ← QLO_eq_psiC (P := P) hd hG]
  exact hmin t

/-- **Сильная двойственность для long-only.** Обе задачи разрешимы и значения равны:

    max { 2m'w − w'Vw : w ≥ 0 }  =  min_t [ t'Σ_f⁻¹t + Σ_i ((m_i−⟨B_i,t⟩)_+)²/d_i ] .

Слева — то, что нужно инвестору; справа — то, что считает динамика по ключу
`(Q, M, Κ)`. Гипотез существования нет: максимум даёт обрезанный вес в точке
минимума (`isKKT_wclip_of_min`), минимум — коэрцитивность по якорям
(`Factor/Attain.lean`). -/
theorem isGreatest_objLO_isLeast_QLO [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (S : Finset ι) :
    ∃ z : ℝ,
      IsLeast {u : ℝ | ∃ t, u = QLO m d B P S t} z ∧
      IsGreatest {v : ℝ | ∃ w : ι → ℝ, (∀ i ∈ S, 0 ≤ w i) ∧ v = objLO m d B Sf S w} z := by
  obtain ⟨t₀, hmin⟩ := exists_min_QLO (Sf := Sf) (G := G) hd hG hPS S
  refine ⟨QLO m d B P S t₀, ⟨⟨t₀, rfl⟩, ?_⟩, ?_⟩
  · rintro u ⟨t, rfl⟩; exact hmin t
  · have hk : IsKKT m d B Sf S (wclip m d B t₀) := isKKT_wclip_of_min (P := P) (G := G) hd hG hPS hmin
    have hgt := isGreatest_objLO (G := G) hd hG hPS hk
    rwa [tw_wclip_eq (P := P) (G := G) hd hG hPS hmin] at hgt

/-- То же в форме «значение зажатой задачи на строках = long-only оптимум»:
`min_t ψ_{S̄}(t)` — это в точности `max{2m'w − w'Vw : w ≥ 0}`. -/
theorem isGreatest_objLO_psiC [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (S : Finset ι) :
    ∃ t₀ : κ → ℝ,
      IsLeast {u : ℝ | ∃ t, u = psiC (rowsK d B G) (targetsK m d)
        (fun r => r.isLeft) (barK (κ := κ) S) t}
        (psiC (rowsK d B G) (targetsK m d) (fun r => r.isLeft) (barK (κ := κ) S) t₀) ∧
      IsGreatest {v : ℝ | ∃ w : ι → ℝ, (∀ i ∈ S, 0 ≤ w i) ∧ v = objLO m d B Sf S w}
        (psiC (rowsK d B G) (targetsK m d) (fun r => r.isLeft) (barK (κ := κ) S) t₀) := by
  obtain ⟨t₀, hmin⟩ := exists_min_QLO (Sf := Sf) (G := G) hd hG hPS S
  have hQ : ∀ t, psiC (rowsK d B G) (targetsK m d) (fun r => r.isLeft)
      (barK (κ := κ) S) t = QLO m d B P S t := fun t => QLO_eq_psiC (P := P) hd hG t
  refine ⟨t₀, ⟨⟨t₀, rfl⟩, ?_⟩, ?_⟩
  · rintro u ⟨t, rfl⟩; rw [hQ, hQ]; exact hmin t
  · rw [hQ]
    have hk : IsKKT m d B Sf S (wclip m d B t₀) := isKKT_wclip_of_min (P := P) (G := G) hd hG hPS hmin
    have hgt := isGreatest_objLO (G := G) hd hG hPS hk
    rwa [tw_wclip_eq (P := P) (G := G) hd hG hPS hmin] at hgt

/-! ### Непустота: ограничение `w ≥ 0` действительно активно

Инстанс `K = 1`, один актив: `m = −1`, `d = 1`, `B = 0`, `Σ_f = Σ_f⁻¹ = G = 1`.
Безусловный оптимум был бы `w = −1` со значением `1`; long-only даёт `0`.
Все гипотезы теоремы выполнены, и заключение нетривиально. -/

example : ∃ z : ℝ,
    IsLeast {u : ℝ | ∃ t, u = QLO (ι := Fin 1) (κ := Fin 1)
      (fun _ => -1) (fun _ => 1) (fun _ _ => 0) (fun _ _ => 1) Finset.univ t} z ∧
    IsGreatest {v : ℝ | ∃ w : Fin 1 → ℝ, (∀ i ∈ (Finset.univ : Finset (Fin 1)), 0 ≤ w i)
      ∧ v = objLO (ι := Fin 1) (κ := Fin 1)
        (fun _ => -1) (fun _ => 1) (fun _ _ => 0) (fun _ _ => 1) Finset.univ w} z :=
  isGreatest_objLO_isLeast_QLO (ι := Fin 1) (κ := Fin 1) (m := fun _ => -1) (d := fun _ => 1)
    (B := fun _ _ => 0) (Sf := fun _ _ => 1) (P := fun _ _ => 1) (G := fun _ _ => 1)
    (fun _ => one_pos)
    (fun j j' => by simp [Subsingleton.elim j j'])
    (fun j j' => by simp [Subsingleton.elim j j']) Finset.univ

end SparseSharpe.Factor
