import SparseSharpe.Factor.State

set_option linter.style.header false

/-!
# Мост: `K`-факторная разрежённая максимизация Шарпа — это задача наименьших квадратов

`V = D + B Σ_f B'`, `F(S) = m_S'V_S⁻¹m_S`. Утверждение (Лемма 1 для `K` факторов):

    F(S) = min_{t ∈ ℝ^K} [ t'Σ_f⁻¹t + Σ_{i∈S}(m_i − ⟨B_i,t⟩)²/d_i ],

и правая часть — это `phi` из `Factor/LeastSquares.lean` для набора строк

    a_i = B_i/√d_i,  y_i = m_i/√d_i   (активы),   a_{(l)} = G_l,  y = 0   (якорные строки),

где `G` — любой «корень» матрицы `Σ_f⁻¹` (`G'G = Σ_f⁻¹`; алгоритм берёт разложение Холецкого).

Доказывается напрямую: если `w` решает `V_S w = m_S`, то в точке `t̂ := Σ_f B'w`
выполнены нормальные уравнения (`isNormal_tw`) и `φ_S(t̂) = Σ_{i∈S} m_i w_i` (`phi_tw`),
а это и есть `m_S'V_S⁻¹m_S`. Матрицы нигде не обращаются: `Σ_f⁻¹` входит как `P`
с гипотезой `P·Σ_f = 1`.
-/

namespace SparseSharpe.Factor

open Finset Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ} {S : Finset ι} {w : ι → ℝ}

/-- Строки набора: активы (`inl`) и `K` якорных строк (`inr`). -/
noncomputable def rowsK (d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) : (ι ⊕ κ) → κ → ℝ :=
  Sum.elim (fun i j => B i j / Real.sqrt (d i)) (fun l j => G l j)

/-- Правые части: `m_i/√d_i` у активов, `0` у якорных строк. -/
noncomputable def targetsK (m d : ι → ℝ) : (ι ⊕ κ) → ℝ :=
  Sum.elim (fun i => m i / Real.sqrt (d i)) (fun _ => 0)

/-- `S̄` — активы `S` вместе со всеми `K` якорными строками. -/
noncomputable def barK (S : Finset ι) : Finset (ι ⊕ κ) := S.disjSum Finset.univ

/-- Якорные строки всегда в `S̄`. -/
lemma inr_mem_barK (S : Finset ι) (l : κ) : (Sum.inr l : ι ⊕ κ) ∈ barK S := by
  simp [barK, Finset.inr_mem_disjSum]

lemma inl_mem_barK {i : ι} (hi : i ∈ S) : (Sum.inl i : ι ⊕ κ) ∈ barK (κ := κ) S := by
  simp [barK, Finset.inl_mem_disjSum, hi]

/-- `B'w` — вклад портфеля в факторы. -/
noncomputable def Bw (B : ι → κ → ℝ) (S : Finset ι) (w : ι → ℝ) : κ → ℝ :=
  fun j => ∑ i ∈ S, B i j * w i

/-- `t̂ = Σ_f B'w` — точка, в которой достигается минимум. -/
noncomputable def tw (Sf : κ → κ → ℝ) (B : ι → κ → ℝ) (S : Finset ι) (w : ι → ℝ) : κ → ℝ :=
  fun j => ∑ j', Sf j j' * Bw B S w j'

/-- Матрица ковариаций `V = D + B Σ_f B'`. -/
noncomputable def Vmat (d : ι → ℝ) (B : ι → κ → ℝ) (Sf : κ → κ → ℝ) : ι → ι → ℝ :=
  fun i i' => (if i = i' then d i else 0) + ∑ j, ∑ j', B i j * (Sf j j' * B i' j')

/-- `(Vw)_i = d_i w_i + ⟨B_i, Σ_f B'w⟩` — то есть гипотеза `hw` ниже есть ровно `V_S w = m_S`. -/
lemma Vmat_mulVec (i : ι) (hi : i ∈ S) :
    ∑ i' ∈ S, Vmat d B Sf i i' * w i' = d i * w i + dotp (B i) (tw Sf B S w) := by
  have h1 : ∑ i' ∈ S, (if i = i' then d i else 0) * w i' = d i * w i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd hi h
  have h2 : ∑ i' ∈ S, (∑ j, ∑ j', B i j * (Sf j j' * B i' j')) * w i'
      = dotp (B i) (tw Sf B S w) := by
    simp only [dotp, tw, Bw, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun i' _ => by ring
  simp only [Vmat, add_mul, Finset.sum_add_distrib, h1, h2]

/-- `Σ_f⁻¹·(Σ_f B'w) = B'w`. -/
lemma P_tw (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (j : κ) :
    ∑ j', P j j' * tw Sf B S w j' = Bw B S w j := by
  simp only [tw, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ l, ∑ j', P j j' * (Sf j' l * Bw B S w l)
      = (∑ j', P j j' * Sf j' l) * Bw B S w l := by
    intro l; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j' _ => by ring
  rw [Finset.sum_congr rfl fun l _ => this l, Finset.sum_congr rfl fun l _ =>
    congrArg (· * Bw B S w l) (hPS j l)]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Специализация: `phi` на этих строках — это `t'Σ_f⁻¹t + Σ_{i∈S}(m_i − ⟨B_i,t⟩)²/d_i`. -/
theorem phiK_eq (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (t : κ → ℝ) :
    phi (rowsK d B G) (targetsK m d) (barK S) t
      = (∑ j, ∑ j', P j j' * (t j * t j')) + ∑ i ∈ S, (m i - dotp (B i) t) ^ 2 / d i := by
  rw [phi, barK, Finset.sum_disjSum]
  have hassets : ∑ i ∈ S, (dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) t - targetsK m d (Sum.inl i : ι ⊕ κ)) ^ 2
      = ∑ i ∈ S, (m i - dotp (B i) t) ^ 2 / d i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdi := hd i
    have hsq : Real.sqrt (d i) ^ 2 = d i := Real.sq_sqrt hdi.le
    have hne : Real.sqrt (d i) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hdi)
    have hdot : dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) t = dotp (B i) t / Real.sqrt (d i) := by
      simp only [rowsK, Sum.elim_inl, dotp, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hdot]
    simp only [targetsK, Sum.elim_inl]
    rw [div_sub_div_same, div_pow, hsq]
    congr 1
    ring
  have hanchor : ∑ l : κ, (dotp (rowsK d B G (Sum.inr l : ι ⊕ κ)) t - targetsK m d (Sum.inr l : ι ⊕ κ)) ^ 2
      = ∑ j, ∑ j', P j j' * (t j * t j') := by
    have hstep : ∀ l : κ, (dotp (rowsK d B G (Sum.inr l : ι ⊕ κ)) t - targetsK m d (Sum.inr l : ι ⊕ κ)) ^ 2
        = ∑ j, ∑ j', (G l j * G l j') * (t j * t j') := by
      intro l
      simp only [rowsK, targetsK, Sum.elim_inr, sub_zero, dotp, sq]
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
    rw [Finset.sum_congr rfl fun l _ => hstep l, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [← Finset.sum_mul, hG j j']
  rw [hassets, hanchor]
  ring

/-- **Нормальные уравнения в `t̂ = Σ_f B'w`** при `V_S w = m_S`. -/
theorem isNormal_tw (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPsymm : ∀ j j', P j j' = P j' j)
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hw : ∀ i ∈ S, d i * w i + dotp (B i) (tw Sf B S w) = m i) :
    IsNormal (rowsK d B G) (targetsK m d) (barK S) (tw Sf B S w) := by
  intro v
  rw [mom, barK, Finset.sum_disjSum]
  have hassets : ∑ i ∈ S, (targetsK m d (Sum.inl i : ι ⊕ κ)
        - dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) (tw Sf B S w))
        * dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) v = ∑ j, Bw B S w j * v j := by
    have hterm : ∀ i ∈ S, (targetsK m d (Sum.inl i : ι ⊕ κ)
        - dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) (tw Sf B S w))
        * dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) v = ∑ j, (B i j * w i) * v j := by
      intro i hi
      have hdi := hd i
      have hne : Real.sqrt (d i) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hdi)
      have hsq : Real.sqrt (d i) * Real.sqrt (d i) = d i := Real.mul_self_sqrt hdi.le
      have hdot : ∀ u : κ → ℝ, dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) u
          = dotp (B i) u / Real.sqrt (d i) := by
        intro u
        simp only [rowsK, Sum.elim_inl, dotp, Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hdot, hdot]
      simp only [targetsK, Sum.elim_inl]
      have hrew : m i - dotp (B i) (tw Sf B S w) = d i * w i := by
        have := hw i hi; linarith
      have hcomb : (m i / Real.sqrt (d i) - dotp (B i) (tw Sf B S w) / Real.sqrt (d i))
          * (dotp (B i) v / Real.sqrt (d i))
          = (m i - dotp (B i) (tw Sf B S w)) * dotp (B i) v / d i := by
        rw [div_sub_div_same, div_mul_div_comm, hsq]
      rw [hcomb, hrew]
      have hdne : d i ≠ 0 := ne_of_gt hdi
      have hcancel : d i * w i * dotp (B i) v / d i = w i * dotp (B i) v := by
        field_simp
      rw [hcancel]
      simp only [dotp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl hterm]
    simp only [Bw, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hanchor : ∑ l : κ, (targetsK m d (Sum.inr l : ι ⊕ κ)
        - dotp (rowsK d B G (Sum.inr l : ι ⊕ κ)) (tw Sf B S w))
        * dotp (rowsK d B G (Sum.inr l : ι ⊕ κ)) v = -∑ j, Bw B S w j * v j := by
    have hstep : ∀ l : κ, (targetsK m d (Sum.inr l : ι ⊕ κ)
        - dotp (rowsK d B G (Sum.inr l : ι ⊕ κ)) (tw Sf B S w))
        * dotp (rowsK d B G (Sum.inr l : ι ⊕ κ)) v
        = -∑ j, ∑ j', (G l j * G l j') * (tw Sf B S w j * v j') := by
      intro l
      simp only [rowsK, targetsK, Sum.elim_inr, zero_sub, dotp, neg_mul]
      rw [Finset.sum_mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
    have hswap : ∑ l : κ, ∑ j, ∑ j', (G l j * G l j') * (tw Sf B S w j * v j')
        = ∑ j, ∑ j', P j j' * (tw Sf B S w j * v j') := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [← Finset.sum_mul, hG j j']
    have hcollapse : ∑ j, ∑ j', P j j' * (tw Sf B S w j * v j')
        = ∑ j, Bw B S w j * v j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j' _ => ?_
      calc ∑ j, P j j' * (tw Sf B S w j * v j')
          = (∑ j, P j' j * tw Sf B S w j) * v j' := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun j _ => by rw [hPsymm j j']; ring
        _ = Bw B S w j' * v j' := by rw [P_tw hPS j']
    rw [Finset.sum_congr rfl fun l _ => hstep l, Finset.sum_neg_distrib, hswap, hcollapse]
  rw [hassets, hanchor]
  ring

/-! ### Невырожденность: у набора `S̄` всегда есть `K`-ка с ненулевым определителем -/

/-- Якорные строки образуют `K`-ку с ненулевым определителем: `G'G = Σ_f⁻¹`, а `Σ_f⁻¹`
обратима (`P·Σ_f = 1`), значит `det G ≠ 0`. -/
theorem det_anchor_ne_zero (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) :
    (rowMat (rowsK d B G) (fun l => (Sum.inr l : ι ⊕ κ))).det ≠ 0 := by
  classical
  have hPmat : (Matrix.of P) * (Matrix.of Sf) = 1 := by
    ext j j'
    simpa [Matrix.mul_apply, Matrix.one_apply] using hPS j j'
  have hPdet : (Matrix.of P).det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hPmat
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact one_ne_zero this.symm
  have hGmat : (Matrix.of G)ᵀ * (Matrix.of G) = Matrix.of P := by
    ext j j'
    simpa [Matrix.mul_apply, Matrix.transpose_apply] using hG j j'
  have hGdet : (Matrix.of G).det ≠ 0 := by
    intro h
    apply hPdet
    have := congrArg Matrix.det hGmat
    rw [Matrix.det_mul, Matrix.det_transpose, h, mul_zero] at this
    exact this.symm
  have hrow : rowMat (rowsK d B G) (fun l => (Sum.inr l : ι ⊕ κ)) = Matrix.of G := by
    ext l j; simp [rowMat, rowsK]
  rwa [hrow]

/-- Поэтому и у максимально-объёмной `K`-ки набора `S̄` определитель ненулевой:
она не хуже якорной. -/
theorem maxvol_det_ne_zero {T : κ → (ι ⊕ κ)}
    (hmax : MaxVol (rowsK d B G) (barK S) T)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) :
    (rowMat (rowsK d B G) T).det ≠ 0 := by
  have hanch := det_anchor_ne_zero (d := d) (B := B) (P := P) (Sf := Sf) hG hPS
  have hle := hmax.2 (fun l => (Sum.inr l : ι ⊕ κ)) (fun l => inr_mem_barK S l)
  intro h
  rw [h] at hle
  simp only [abs_zero] at hle
  exact hanch (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))

/-- И максимально-объёмная `K`-ка существует (якорная `K`-ка годится как свидетель). -/
theorem exists_maxvol_barK :
    ∃ T : κ → (ι ⊕ κ), MaxVol (rowsK d B G) (barK S) T :=
  exists_maxvol _ _ (fun l => (Sum.inr l : ι ⊕ κ)) (fun l => inr_mem_barK S l)

/-- Значение в точке `t̂ = Σ_f B'w` равно `Σ_{i∈S} m_i w_i`, то есть `m_S'V_S⁻¹m_S`. -/
theorem phi_tw (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hw : ∀ i ∈ S, d i * w i + dotp (B i) (tw Sf B S w) = m i) :
    phi (rowsK d B G) (targetsK m d) (barK S) (tw Sf B S w) = ∑ i ∈ S, m i * w i := by
  rw [phiK_eq (P := P) hd hG]
  -- якорная часть: `t̂'Σ_f⁻¹t̂ = Σ_j t̂_j (B'w)_j`
  have hanchor : ∑ j, ∑ j', P j j' * (tw Sf B S w j * tw Sf B S w j')
      = ∑ j, tw Sf B S w j * Bw B S w j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← P_tw (Sf := Sf) (B := B) (S := S) (w := w) hPS j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j' _ => by ring
  -- активы: невязка в оптимуме равна `d_i w_i`
  have hassets : ∑ i ∈ S, (m i - dotp (B i) (tw Sf B S w)) ^ 2 / d i
      = ∑ i ∈ S, d i * (w i) ^ 2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hrew : m i - dotp (B i) (tw Sf B S w) = d i * w i := by have := hw i hi; linarith
    have hdne : d i ≠ 0 := ne_of_gt (hd i)
    rw [hrew]
    field_simp
  -- условие стационарности, просуммированное с весами `w`
  have hstat : ∑ i ∈ S, m i * w i
      = (∑ i ∈ S, d i * (w i) ^ 2) + ∑ j, tw Sf B S w j * Bw B S w j := by
    have hsplit : ∑ i ∈ S, m i * w i
        = ∑ i ∈ S, (d i * w i + dotp (B i) (tw Sf B S w)) * w i :=
      Finset.sum_congr rfl fun i hi => by rw [hw i hi]
    have hmix : ∑ i ∈ S, dotp (B i) (tw Sf B S w) * w i
        = ∑ j, tw Sf B S w j * Bw B S w j := by
      simp only [dotp, Bw, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit]
    have : ∑ i ∈ S, (d i * w i + dotp (B i) (tw Sf B S w)) * w i
        = (∑ i ∈ S, d i * (w i) ^ 2) + ∑ i ∈ S, dotp (B i) (tw Sf B S w) * w i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hmix]
  rw [hanchor, hassets, hstat]
  ring

/-- **Лемма 1 для `K` факторов.** Если `w` решает `V_S w = m_S` (см. `Vmat_mulVec`), то
`t̂ = Σ_f B'w` минимизирует `φ_S`, и минимум равен `Σ_{i∈S} m_i w_i = m_S'V_S⁻¹m_S`.
Тем самым вся `Factor/*`-часть — про исходную задачу, а не про абстрактные строки. -/
theorem factor_lemma1 (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPsymm : ∀ j j', P j j' = P j' j)
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hw : ∀ i ∈ S, d i * w i + dotp (B i) (tw Sf B S w) = m i) :
    IsNormal (rowsK d B G) (targetsK m d) (barK S) (tw Sf B S w) ∧
    (∀ t, phi (rowsK d B G) (targetsK m d) (barK S) (tw Sf B S w)
        ≤ phi (rowsK d B G) (targetsK m d) (barK S) t) ∧
    phi (rowsK d B G) (targetsK m d) (barK S) (tw Sf B S w) = ∑ i ∈ S, m i * w i :=
  ⟨isNormal_tw hd hG hPsymm hPS hw,
   fun t => phi_min (isNormal_tw hd hG hPsymm hPS hw) t,
   phi_tw (P := P) hd hG hPS hw⟩

/-- **Теорема I для `K`-факторной модели, в одном утверждении.**
`w` решает `V_S w = m_S`, так что `F(S) = Σ_{i∈S} m_i w_i` (Лемма 1); `T` —
максимально-объёмная `K`-ка набора `S̄`; `t` — узел сетки, близкий к `t̂(S)` в её
координатах; `RB` — набор строк представителя динамики с тремя свойствами округления.
Вывод: `F_LS(RB) ≥ (1 − 17ε/8)·F(S)`, где слева — значение задачи наименьших квадратов
на строках представителя (минимум по `v` от `φ_{RB}(t+v)`). -/
theorem factor_fptas_at_node {T : κ → (ι ⊕ κ)} {RB : Finset (ι ⊕ κ)} {t : κ → ℝ}
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPsymm : ∀ j j', P j j' = P j' j)
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hw : ∀ i ∈ S, d i * w i + dotp (B i) (tw Sf B S w) = m i)
    (hmax : MaxVol (rowsK d B G) (barK S) T)
    {ε Δ ξ C : ℝ}
    (hC : (((barK (κ := κ) S).card : ℝ) * Fintype.card κ) ≤ C) (hCpos : 0 < C)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ^ 2 ≤ ε * (∑ i ∈ S, m i * w i) / 16)
    (hnode : gramK (rowsK d B G) T (t - tw Sf B S w) ≤ ε * (∑ i ∈ S, m i * w i) / C)
    (hQR : phi (rowsK d B G) (targetsK m d) (barK S) t
        ≤ phi (rowsK d B G) (targetsK m d) RB t)
    (hMclose : ∑ l, (momK (rowsK d B G) (targetsK m d) T RB t l
        - momK (rowsK d B G) (targetsK m d) T (barK S) t l) ^ 2 ≤ Δ ^ 2)
    (hξ0 : 0 ≤ ξ) (hξ : ξ * (Fintype.card κ : ℝ) ≤ 1 / 2)
    (hKclose : ∀ l l', |gramK2 (rowsK d B G) T RB l l'
        - gramK2 (rowsK d B G) T (barK S) l l'| ≤ ξ) (v : κ → ℝ) :
    (1 - 17 * ε / 8) * (∑ i ∈ S, m i * w i)
      ≤ phi (rowsK d B G) (targetsK m d) RB (t + v) := by
  have hval := phi_tw (P := P) hd hG hPS hw
  have hdet := maxvol_det_ne_zero hmax hG hPS
  have hnormal := isNormal_tw hd hG hPsymm hPS hw
  have := fptasK_at_grid_node hmax hdet hnormal hC hCpos hΔ0 (by rwa [hval])
    (by rwa [hval]) hQR hMclose hξ0 hξ hKclose v
  rwa [hval] at this

/-- **Следствие: оценка для значения задачи на носителе представителя.**
То же, что `factor_fptas_at_node`, но заключение выписано **для всякого** `t'`,
то есть для `F_LS(R) = min_{t'} φ_{R̄}(t')`, и носитель представителя — настоящее
множество активов `R` (строки `barK R`), а не произвольный набор строк. -/
theorem factor_fptas_value {T : κ → (ι ⊕ κ)} {R : Finset ι} {t : κ → ℝ}
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPsymm : ∀ j j', P j j' = P j' j)
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hw : ∀ i ∈ S, d i * w i + dotp (B i) (tw Sf B S w) = m i)
    (hmax : MaxVol (rowsK d B G) (barK S) T)
    {ε Δ ξ C : ℝ}
    (hC : (((barK (κ := κ) S).card : ℝ) * Fintype.card κ) ≤ C) (hCpos : 0 < C)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ^ 2 ≤ ε * (∑ i ∈ S, m i * w i) / 16)
    (hnode : gramK (rowsK d B G) T (t - tw Sf B S w) ≤ ε * (∑ i ∈ S, m i * w i) / C)
    (hQR : phi (rowsK d B G) (targetsK m d) (barK S) t
        ≤ phi (rowsK d B G) (targetsK m d) (barK R) t)
    (hMclose : ∑ l, (momK (rowsK d B G) (targetsK m d) T (barK R) t l
        - momK (rowsK d B G) (targetsK m d) T (barK S) t l) ^ 2 ≤ Δ ^ 2)
    (hξ0 : 0 ≤ ξ) (hξ : ξ * (Fintype.card κ : ℝ) ≤ 1 / 2)
    (hKclose : ∀ l l', |gramK2 (rowsK d B G) T (barK R) l l'
        - gramK2 (rowsK d B G) T (barK S) l l'| ≤ ξ) :
    ∀ t' : κ → ℝ, (1 - 17 * ε / 8) * (∑ i ∈ S, m i * w i)
      ≤ phi (rowsK d B G) (targetsK m d) (barK R) t' := by
  intro t'
  have h := factor_fptas_at_node (T := T) (RB := barK R) hd hG hPsymm hPS hw hmax
    hC hCpos hΔ0 hΔ hnode hQR hMclose hξ0 hξ hKclose (t' - t)
  have hid : t + (t' - t) = t' := by abel
  rwa [hid] at h

end SparseSharpe.Factor
