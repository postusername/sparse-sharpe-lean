import SparseSharpe.Factor.Guarantee

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Сквозная гарантия в `δ`-цепочке, в языке задачи

`lo_fptas_portfolio_opt` (`Factor/Guarantee.lean`) платит параметром `γ` —
блочным плечом **всех** активов вселенной относительно якорей. Здесь та же
гарантия выведена из `lo_fptas_block` (`Factor/DPRun.lean`), где вместо `γ`
стоит константа `c` покрытия нарушителей (`AnchorCover`, `Factor/Cover.lean`).

В языке задачи у этой константы есть явная и **честная** граница с обеих сторон.
Пусть `ω_i = B_i'Σ_fB_i/d_i` — отношение системной дисперсии актива к
идиосинкратической, так что `1 + ω_i = V_ii/d_i = 1/(1 − R²_i)`.

* **Сверху** (`sq_dotp_asset_le`, `anchorCover_of_sysVar`): плечо строки актива
  относительно якорей не больше `ω_i` (неравенство Коши–Буняковского в метрике
  `Σ_f⁻¹`), поэтому покрытие есть с `c = k(1 + kω)` для любой верхней границы
  `ω ≥ ω_i` на всех активах вселенной (в частности, `ω = max_i ω_i`). В этой
  константе **нет размера вселенной**: в отличие от `1/γ = 1 + λ_max(Σ_i …)`,
  где суммируются все `M` активов, здесь участвуют только наборы из `≤ k` строк.
* **Снизу** (`cover_const_ge_asset`): всякая константа покрытия не меньше
  `1 + ω_i` для каждого актива вселенной с `B_i'Σ_fB_i > 0`. То есть зависимость
  от худшего одиночного актива этим путём не снимается — она и есть предел
  рассуждения через покрытие.

Итог (`lo_fptas_portfolio_opt_rowLev`): гарантия `(1−2ε)` при калибровке
`c = k(1 + kω)`, в которую не входят ни `γ`, ни размер вселенной, ни то,
насколько нагрузки вселенной выстроены в одну сторону. Сама теорема — про
существование узла и результат динамики в нём; сколько это стоит, говорит
`lo_fptas_cost_block` (`Factor/Cost.lean`): число узлов и размер таблицы одного
запуска ограничены явными выражениями от `M`, `k`, `K`, `1/ε` и `c`. Утверждение
о времени работы в смысле модели вычислений здесь не формализовано — как и в
`γ`-цепочке (§16 заметки 7): вместе с перебором `K`-ок и догадок `V` эти две
границы дают полиномиальность по `M`, `k`, `1/ε` и `max_i V_ii/d_i` при
фиксированном `K`.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-! ### Якоря и плечо одного актива -/

/-- Системная дисперсия актива: `B_i'Σ_fB_i`. -/
noncomputable def sysVar (B : ι → κ → ℝ) (Sf : κ → κ → ℝ) (i : ι) : ℝ :=
  ∑ j, ∑ j', B i j * Sf j j' * B i j'

lemma card_anchorRows : (anchorRows ι κ).card = Fintype.card κ := by
  simp [anchorRows]

/-- Форма Грама якорей: `gram_anch(v) = Σ_l (Σ_j G_lj v_j)²`. -/
lemma gram_anchorRows (v : κ → ℝ) :
    gram (rowsK d B G) (anchorRows ι κ) v = ∑ l, (∑ j, G l j * v j) ^ 2 := by
  simp [gram, anchorRows, rowsK, dotp]

/-- `P = G'G` симметрична. -/
lemma P_symm (hG : ∀ j j', ∑ l, G l j * G l j' = P j j') (j j' : κ) : P j j' = P j' j := by
  rw [← hG, ← hG]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- `Σ_l (Σ_j G_lj s_j)(Σ_j G_lj u_j) = s'Pu`. -/
lemma sum_G_mul_G (hG : ∀ j j', ∑ l, G l j * G l j' = P j j') (s u : κ → ℝ) :
    ∑ l, (∑ j, G l j * s j) * (∑ j, G l j * u j) = ∑ j, ∑ j', s j * P j j' * u j' := by
  have hL : ∀ l, (∑ j, G l j * s j) * (∑ j, G l j * u j)
      = ∑ j, ∑ j', G l j * s j * (G l j' * u j') :=
    fun l => Finset.sum_mul_sum _ _ _ _
  simp_rw [hL]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [← hG, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- Вектор `s = Σ_f B_i` переводит `P` обратно в `B_i`: `Σ_j s_j P_jj' = B_ij'`. -/
lemma sum_SfB_mul_P (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (i : ι) (j' : κ) :
    ∑ j, (∑ l, Sf j l * B i l) * P j j' = B i j' := by
  have hswap : ∑ j, (∑ l, Sf j l * B i l) * P j j' = ∑ l, B i l * ∑ j, P j' j * Sf j l := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    rw [P_symm hG j j']; ring
  rw [hswap]
  simp_rw [hPS]
  simp

/-- `|G·Σ_fB_i|² = B_i'Σ_fB_i`. -/
lemma sum_sq_GSfB (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (i : ι) :
    ∑ l, (∑ j, G l j * (∑ m, Sf j m * B i m)) ^ 2 = sysVar B Sf i := by
  have h := sum_G_mul_G (G := G) (P := P) hG (fun j => ∑ m, Sf j m * B i m)
    (fun j => ∑ m, Sf j m * B i m)
  simp only [← sq] at h
  rw [h]
  -- `Σ_j Σ_j' s_j P_jj' s_j' = Σ_j' (Σ_j s_j P_jj') s_j' = Σ_j' B_ij' s_j'`
  have h2 : ∑ j, ∑ j', (∑ m, Sf j m * B i m) * P j j' * (∑ m, Sf j' m * B i m)
      = ∑ j', B i j' * (∑ m, Sf j' m * B i m) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [← Finset.sum_mul, sum_SfB_mul_P (B := B) hG hPS i j']
  rw [h2, sysVar]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

lemma sysVar_nonneg (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (i : ι) :
    0 ≤ sysVar B Sf i := by
  rw [← sum_sq_GSfB hG hPS i]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Плечо актива относительно якорей не больше `B_i'Σ_fB_i/d_i`.**
Неравенство Коши–Буняковского в метрике `Σ_f⁻¹`:
`(B_i'v)² = ⟨GΣ_fB_i, Gv⟩² ≤ |GΣ_fB_i|²·|Gv|² = (B_i'Σ_fB_i)·gram_anch(v)`. -/
theorem sq_dotp_asset_le (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (i : ι) (v : κ → ℝ) :
    (dotp (rowsK d B G (Sum.inl i)) v) ^ 2
      ≤ sysVar B Sf i / d i * gram (rowsK d B G) (anchorRows ι κ) v := by
  have hdi := hd i
  have hsq : Real.sqrt (d i) ^ 2 = d i := Real.sq_sqrt hdi.le
  have hne : Real.sqrt (d i) ≠ 0 := (Real.sqrt_pos.mpr hdi).ne'
  -- `⟨a_i,v⟩ = (B_i'v)/√d_i`
  have hdot : dotp (rowsK d B G (Sum.inl i)) v = (∑ j, B i j * v j) / Real.sqrt (d i) := by
    simp only [dotp, rowsK, Sum.elim_inl]
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- `B_i'v = Σ_l w_l u_l`, `w = GΣ_fB_i`, `u = Gv`
  have hBv : ∑ j, B i j * v j
      = ∑ l, (∑ j, G l j * (∑ m, Sf j m * B i m)) * (∑ j, G l j * v j) := by
    rw [sum_G_mul_G hG]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [← Finset.sum_mul, sum_SfB_mul_P hG hPS i j']
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun l => ∑ j, G l j * (∑ m, Sf j m * B i m)) (fun l => ∑ j, G l j * v j)
  rw [← hBv, sum_sq_GSfB hG hPS i] at hcs
  rw [hdot, div_pow, hsq, gram_anchorRows, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hdi]
  exact hcs

/-- В точке `v = Σ_fB_i` неравенство `sq_dotp_asset_le` обращается в равенство:
`⟨a_i,v⟩² = (B_i'Σ_fB_i)²/d_i` и `gram_anch(v) = B_i'Σ_fB_i`. -/
lemma dotp_asset_at_SfB (hd : ∀ i, 0 < d i) (i : ι) :
    (dotp (rowsK d B G (Sum.inl i)) (fun j => ∑ m, Sf j m * B i m)) ^ 2
      = sysVar B Sf i ^ 2 / d i := by
  have hdi := hd i
  have hsq : Real.sqrt (d i) ^ 2 = d i := Real.sq_sqrt hdi.le
  have hdot : dotp (rowsK d B G (Sum.inl i)) (fun j => ∑ m, Sf j m * B i m)
      = sysVar B Sf i / Real.sqrt (d i) := by
    simp only [dotp, rowsK, Sum.elim_inl, sysVar]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hdot, div_pow, hsq]

/-! ### Константа покрытия в языке задачи: граница сверху и предел снизу -/

/-- **Покрытие из плеч активов.** Если `B_i'Σ_fB_i/d_i ≤ ω` у всех активов
вселенной, то нарушители покрыты с константой `c = k(1 + kω)`. -/
theorem anchorCover_of_sysVar (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {cand : Finset ι} {k : ℕ} {ω : ℝ} (hω : 0 ≤ ω)
    (hsys : ∀ i ∈ cand, sysVar B Sf i / d i ≤ ω) :
    AnchorCover (rowsK d B G) (targetsK m d) (fun r => Sum.isLeft r) (barK (κ := κ) cand)
      (anchorRows ι κ) k ((k : ℝ) * (1 + (k : ℝ) * ω)) := by
  refine anchorCover_of_rowLev_uniform hω fun x hx hcl v => ?_
  rcases x with i | l
  · have hi : i ∈ cand := by simpa [barK, Finset.inl_mem_disjSum] using hx
    refine le_trans (sq_dotp_asset_le hd hG hPS i v) ?_
    exact mul_le_mul_of_nonneg_right (hsys i hi) (gram_nonneg _ _ _)
  · simp at hcl

/-- **Предел снизу, в языке задачи.** Всякая константа покрытия нарушителей
(при `k ≥ 1`) не меньше `1 + B_i'Σ_fB_i/d_i = V_ii/d_i` для каждого актива
вселенной с `B_i'Σ_fB_i > 0`. -/
theorem cover_const_ge_asset (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {cand : Finset ι} {k : ℕ} {c : ℝ}
    (hcov : AnchorCover (rowsK d B G) (targetsK m d) (fun r => Sum.isLeft r)
      (barK (κ := κ) cand) (anchorRows ι κ) k c) (hk : 1 ≤ k)
    {i : ι} (hi : i ∈ cand) (hsys : 0 < sysVar B Sf i) :
    1 + sysVar B Sf i / d i ≤ c := by
  -- строка актива ненулевая: иначе `B_i = 0` и `B_i'Σ_fB_i = 0`
  have hai : ∃ l, rowsK d B G (Sum.inl i) l ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hB : ∀ j, B i j = 0 := by
      intro j
      have h := hcon j
      simp only [rowsK, Sum.elim_inl] at h
      rcases div_eq_zero_iff.mp h with h | h
      · exact h
      · exact absurd h (Real.sqrt_pos.mpr (hd i)).ne'
    have : sysVar B Sf i = 0 := by simp [sysVar, hB]
    linarith
  have hgv : gram (rowsK d B G) (anchorRows ι κ) (fun j => ∑ m, Sf j m * B i m)
      = sysVar B Sf i := by
    rw [gram_anchorRows]; exact sum_sq_GSfB hG hPS i
  have h := cover_const_ge_row hcov hk (i := Sum.inl i)
    (by simpa [barK, Finset.inl_mem_disjSum] using hi) (by simp) hai
    (v := fun j => ∑ m, Sf j m * B i m) (by rw [hgv]; exact hsys)
  rw [hgv, dotp_asset_at_SfB hd] at h
  have hsimp : sysVar B Sf i ^ 2 / d i / sysVar B Sf i = sysVar B Sf i / d i := by
    field_simp
  rwa [hsimp] at h

/-! ### Сквозная теорема в языке задачи, `δ`-цепочка -/

/-- **FPTAS для long-only в `δ`-цепочке, в терминах портфеля.** То же, что
`lo_fptas_portfolio`, но калибровка через константу покрытия `c ≥ 1`
(`θ₀ = √(εV/(8c))`, `ε_g = ε/(32c)`) вместо `γ`, и без параметра `n`. -/
theorem lo_fptas_portfolio_block [Nonempty κ]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {cand A₀ : Finset ι} {La : List ι} {T : κ → (ι ⊕ κ)} {thA : κ → ℝ}
    {η ξ ε V C c s : ℝ} {k : ℕ}
    (hmax : MaxVol (rowsK d B G) (barK (κ := κ) A₀) T)
    (hdet : (rowMat (rowsK d B G) T).det ≠ 0)
    (hnormA : IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA)
    (hC : ((barK (κ := κ) A₀).card * Fintype.card κ : ℝ) ≤ C) (hCpos : 0 < C)
    (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hc : 1 ≤ c) (hV : 0 < V)
    (hVF : V ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA)
    (hFV : phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA ≤ 2 * V)
    (hKc : 0 < (Fintype.card κ : ℝ))
    (hs : s = 2 * Real.sqrt ((ε / (32 * c)) * V / ((Fintype.card κ : ℝ) * C)))
    (hselfA : ∀ x ∈ barK (κ := κ) A₀, (Sum.isLeft x) →
      0 ≤ targetsK m d x - dotp (rowsK d B G x) thA)
    (hη : 0 < η) (hξ : 0 < ξ)
    (hnd : La.Nodup) (hA₀La : A₀ ⊆ La.toFinset) (hLcand : ∀ i ∈ La, i ∈ cand)
    (hcov : AnchorCover (rowsK d B G) (targetsK m d) (fun r => Sum.isLeft r)
      (barK (κ := κ) cand) (anchorRows ι κ) k c)
    (hkA : A₀.card ≤ k) (hA₀cand : A₀ ⊆ cand)
    (hηθ : 8 * (Real.sqrt (Fintype.card κ : ℝ) * ((La.length : ℝ) * η))
      ≤ theta0B ε V c)
    (hζ8 : ((La.length : ℝ) * ξ) * (Fintype.card κ : ℝ) ≤ 1/8) :
    ∃ z : κ → ℤ,
      (∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C
        / (2 * (ε / (32 * c)))) + 1 / 2) ∧
      ∀ t : κ → ℝ, (∀ l, dotp (rowsK d B G (T l)) t
          = targetsK m d (T l) + s * (z l : ℝ)) →
        ∃ adm : (ι ⊕ κ) → Bool,
          (∀ x, adm x → -theta0B ε V c
            ≤ targetsK m d x - dotp (rowsK d B G x) t) ∧
          (∀ x ∈ barK (κ := κ) A₀, x ∉ anchorRows ι κ → adm x) ∧
          ∃ R ∈ survivors (fun W => phi (rowsK d B G) (targetsK m d) W t)
              (keyOf (rowsK d B G) (targetsK m d) T t η ξ) adm (anchorRows ι κ)
              (La.map Sum.inl),
            (assetsOf (κ := κ) R).card = A₀.card
            ∧ ∃ w : ι → ℝ, (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i)
              ∧ (1 - 2 * ε) * phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA
                ≤ objLO m d B Sf (assetsOf (κ := κ) R) w := by
  classical
  set a := rowsK d B G with ha
  set y := targetsK m d with hy
  set L : List (ι ⊕ κ) := La.map Sum.inl with hL
  have hndL : L.Nodup := hnd.map (fun _ _ h => by injection h)
  have hdisj : ∀ x ∈ L, x ∉ anchorRows ι κ := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    intro hc
    exact (not_isLeft_of_mem_anchorRows hc) (by simp)
  have hbA : anchorRows ι κ ⊆ barK (κ := κ) A₀ := anchorRows_subset_barK A₀
  have hAL : barK (κ := κ) A₀ ⊆ anchorRows ι κ ∪ L.toFinset := by
    intro x hx
    rcases x with i | l
    · refine Finset.mem_union_right _ ?_
      have hiA : i ∈ A₀ := by simpa [barK, Finset.inl_mem_disjSum] using hx
      refine List.mem_toFinset.mpr ?_
      exact List.mem_map.mpr ⟨i, List.mem_toFinset.mp (hA₀La hiA), rfl⟩
    · exact Finset.mem_union_left _ (inr_mem_anchorRows l)
  have hAS : barK (κ := κ) A₀ ⊆ barK (κ := κ) cand := by
    intro x hx
    rcases x with i | l
    · have : i ∈ A₀ := by simpa [barK, Finset.inl_mem_disjSum] using hx
      simpa [barK, Finset.inl_mem_disjSum] using hA₀cand this
    · exact inr_mem_barK cand l
  have hbaseS : anchorRows ι κ ⊆ barK (κ := κ) cand := anchorRows_subset_barK cand
  have hLS : ∀ x ∈ L.toFinset, x ∈ barK (κ := κ) cand := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    simpa [barK, Finset.inl_mem_disjSum] using hLcand i hi
  have hanchBase : anchorSet (fun r : ι ⊕ κ => Sum.isLeft r) (barK (κ := κ) cand)
      ⊆ anchorRows ι κ := by
    intro x hx
    obtain ⟨_, hx2⟩ := Finset.mem_filter.mp hx
    rcases x with i | l
    · simp at hx2
    · exact inr_mem_anchorRows l
  have hbaseAnch : ∀ x ∈ anchorRows ι κ, ¬ (Sum.isLeft x) :=
    fun _ hx => not_isLeft_of_mem_anchorRows hx
  have hk : (barK (κ := κ) A₀).card ≤ (anchorRows ι κ).card + k := by
    rw [card_barK, card_anchorRows]; omega
  obtain ⟨z, hz1, hz2⟩ := lo_fptas_block (a := a) (y := y) (cl := fun r => Sum.isLeft r)
    (S := barK (κ := κ) cand) (A := barK (κ := κ) A₀) (base := anchorRows ι κ)
    (T := T) (thA := thA) (η := η) (ξ := ξ) (ε := ε) (V := V) (C := C) (c := c) (s := s)
    (k := k) (L := L) (Tb := fun l => (Sum.inr l : ι ⊕ κ))
    hmax hdet hnormA hC hCpos hε hε1 hc hV hVF hFV hKc hs hselfA hη hξ
    hndL hdisj hbA hAL hAS hbaseS hLS hanchBase hbaseAnch hcov hk
    (fun l => inr_mem_anchorRows l)
    (det_anchor_ne_zero (d := d) (B := B) (P := P) (Sf := Sf) hG hPS)
    (by rwa [hL, List.length_map]) (by rwa [hL, List.length_map])
  refine ⟨z, hz1, fun t ht => ?_⟩
  obtain ⟨adm, hadm1, hadm2, R, hR, hcard, hval⟩ := hz2 t ht
  refine ⟨adm, hadm1, hadm2, R, hR, ?_, ?_⟩
  · have := card_assetsOf_eq (survivors_mem _ _ adm _ L R hR).1 hbA hcard
    rwa [assetsOf_barK] at this
  · set R₀ := assetsOf (κ := κ) R with hR₀
    have hReq : R = barK (κ := κ) R₀ :=
      barK_assetsOf (survivors_mem _ _ adm _ L R hR).1
    obtain ⟨zv, hleast, hgreat⟩ :=
      isGreatest_objLO_isLeast_QLO (Sf := Sf) (P := P) (G := G) hd hG hPS R₀
    obtain ⟨t₁, ht₁⟩ := hleast.1
    obtain ⟨w, hw, hwv⟩ := hgreat.1
    refine ⟨w, hw, ?_⟩
    rw [← hwv, ht₁, ← QLO_eq_psiC (P := P) hd hG]
    have := hval t₁
    rwa [hReq] at this

/-- **Гарантия относительно настоящего оптимума, `δ`-цепочка.** Портфель на
возвращённом носителе не хуже `(1−2ε)`-доли любого допустимого портфеля на
`Sopt`, носитель не длиннее `Sopt`; калибровка — через константу покрытия. -/
theorem lo_fptas_portfolio_opt_block [Nonempty κ]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {cand Sopt A₀ : Finset ι} {La : List ι} {T : κ → (ι ⊕ κ)} {thA : κ → ℝ}
    {η ξ ε V C c s : ℝ} {k : ℕ}
    (hopt : IsGreatest {v : ℝ | ∃ u : ι → ℝ, (∀ i ∈ Sopt, 0 ≤ u i)
        ∧ v = objLO m d B Sf Sopt u}
      (phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA))
    (hA₀Sopt : A₀ ⊆ Sopt)
    (hmax : MaxVol (rowsK d B G) (barK (κ := κ) A₀) T)
    (hdet : (rowMat (rowsK d B G) T).det ≠ 0)
    (hnormA : IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA)
    (hC : ((barK (κ := κ) A₀).card * Fintype.card κ : ℝ) ≤ C) (hCpos : 0 < C)
    (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hc : 1 ≤ c) (hV : 0 < V)
    (hVF : V ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA)
    (hFV : phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA ≤ 2 * V)
    (hKc : 0 < (Fintype.card κ : ℝ))
    (hs : s = 2 * Real.sqrt ((ε / (32 * c)) * V / ((Fintype.card κ : ℝ) * C)))
    (hselfA : ∀ x ∈ barK (κ := κ) A₀, (Sum.isLeft x) →
      0 ≤ targetsK m d x - dotp (rowsK d B G x) thA)
    (hη : 0 < η) (hξ : 0 < ξ)
    (hnd : La.Nodup) (hA₀La : A₀ ⊆ La.toFinset) (hLcand : ∀ i ∈ La, i ∈ cand)
    (hcov : AnchorCover (rowsK d B G) (targetsK m d) (fun r => Sum.isLeft r)
      (barK (κ := κ) cand) (anchorRows ι κ) k c)
    (hkS : Sopt.card ≤ k) (hA₀cand : A₀ ⊆ cand)
    (hηθ : 8 * (Real.sqrt (Fintype.card κ : ℝ) * ((La.length : ℝ) * η))
      ≤ theta0B ε V c)
    (hζ8 : ((La.length : ℝ) * ξ) * (Fintype.card κ : ℝ) ≤ 1/8) :
    ∃ z : κ → ℤ,
      (∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C
        / (2 * (ε / (32 * c)))) + 1 / 2) ∧
      ∀ t : κ → ℝ, (∀ l, dotp (rowsK d B G (T l)) t
          = targetsK m d (T l) + s * (z l : ℝ)) →
        ∃ adm : (ι ⊕ κ) → Bool,
          (∀ x ∈ barK (κ := κ) A₀, x ∉ anchorRows ι κ → adm x) ∧
          ∃ R ∈ survivors (fun W => phi (rowsK d B G) (targetsK m d) W t)
              (keyOf (rowsK d B G) (targetsK m d) T t η ξ) adm (anchorRows ι κ)
              (La.map Sum.inl),
            (assetsOf (κ := κ) R).card ≤ Sopt.card
            ∧ ∃ w : ι → ℝ, (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i)
              ∧ ∀ u : ι → ℝ, (∀ i ∈ Sopt, 0 ≤ u i) →
                  (1 - 2 * ε) * objLO m d B Sf Sopt u
                    ≤ objLO m d B Sf (assetsOf (κ := κ) R) w := by
  have hkA : A₀.card ≤ k := le_trans (Finset.card_le_card hA₀Sopt) hkS
  obtain ⟨z, hz1, hz2⟩ := lo_fptas_portfolio_block (P := P) hd hG hPS hmax hdet hnormA hC
    hCpos hε hε1 hc hV hVF hFV hKc hs hselfA hη hξ hnd hA₀La hLcand hcov hkA hA₀cand
    hηθ hζ8
  refine ⟨z, hz1, fun t ht => ?_⟩
  obtain ⟨adm, _hadm1, hadm2, R, hR, hcard, w, hw, hval⟩ := hz2 t ht
  refine ⟨adm, hadm2, R, hR, ?_, w, hw, fun u hu => ?_⟩
  · rw [hcard]; exact Finset.card_le_card hA₀Sopt
  · have hub : objLO m d B Sf Sopt u
        ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA :=
      hopt.2 ⟨u, hu, rfl⟩
    have hcoef : (0:ℝ) ≤ 1 - 2 * ε := by linarith
    have := mul_le_mul_of_nonneg_left hub hcoef
    linarith

/-- **Главная теорема в самой удобной форме.** Если у всех активов вселенной
`B_i'Σ_fB_i/d_i ≤ ω` (то есть `V_ii/d_i ≤ 1 + ω`), то годится константа покрытия
`c = k(1 + kω)`, и гарантия `lo_fptas_portfolio_opt_block` верна с ней.
Ни `γ`, ни размер вселенной в калибровку не входят. Время работы здесь не
утверждается: границы на число узлов и размер таблицы — `lo_fptas_cost_block`. -/
theorem lo_fptas_portfolio_opt_rowLev [Nonempty κ]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {cand Sopt A₀ : Finset ι} {La : List ι} {T : κ → (ι ⊕ κ)} {thA : κ → ℝ}
    {η ξ ε V C ω s : ℝ} {k : ℕ}
    (hopt : IsGreatest {v : ℝ | ∃ u : ι → ℝ, (∀ i ∈ Sopt, 0 ≤ u i)
        ∧ v = objLO m d B Sf Sopt u}
      (phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA))
    (hA₀Sopt : A₀ ⊆ Sopt)
    (hmax : MaxVol (rowsK d B G) (barK (κ := κ) A₀) T)
    (hdet : (rowMat (rowsK d B G) T).det ≠ 0)
    (hnormA : IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA)
    (hC : ((barK (κ := κ) A₀).card * Fintype.card κ : ℝ) ≤ C) (hCpos : 0 < C)
    (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hk1 : 1 ≤ k) (hω : 0 ≤ ω) (hV : 0 < V)
    (hsys : ∀ i ∈ cand, sysVar B Sf i / d i ≤ ω)
    (hVF : V ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA)
    (hFV : phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA ≤ 2 * V)
    (hKc : 0 < (Fintype.card κ : ℝ))
    (hs : s = 2 * Real.sqrt ((ε / (32 * ((k : ℝ) * (1 + (k : ℝ) * ω)))) * V
      / ((Fintype.card κ : ℝ) * C)))
    (hselfA : ∀ x ∈ barK (κ := κ) A₀, (Sum.isLeft x) →
      0 ≤ targetsK m d x - dotp (rowsK d B G x) thA)
    (hη : 0 < η) (hξ : 0 < ξ)
    (hnd : La.Nodup) (hA₀La : A₀ ⊆ La.toFinset) (hLcand : ∀ i ∈ La, i ∈ cand)
    (hkS : Sopt.card ≤ k) (hA₀cand : A₀ ⊆ cand)
    (hηθ : 8 * (Real.sqrt (Fintype.card κ : ℝ) * ((La.length : ℝ) * η))
      ≤ theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω)))
    (hζ8 : ((La.length : ℝ) * ξ) * (Fintype.card κ : ℝ) ≤ 1/8) :
    ∃ z : κ → ℤ,
      (∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C
        / (2 * (ε / (32 * ((k : ℝ) * (1 + (k : ℝ) * ω)))))) + 1 / 2) ∧
      ∀ t : κ → ℝ, (∀ l, dotp (rowsK d B G (T l)) t
          = targetsK m d (T l) + s * (z l : ℝ)) →
        ∃ adm : (ι ⊕ κ) → Bool,
          (∀ x ∈ barK (κ := κ) A₀, x ∉ anchorRows ι κ → adm x) ∧
          ∃ R ∈ survivors (fun W => phi (rowsK d B G) (targetsK m d) W t)
              (keyOf (rowsK d B G) (targetsK m d) T t η ξ) adm (anchorRows ι κ)
              (La.map Sum.inl),
            (assetsOf (κ := κ) R).card ≤ Sopt.card
            ∧ ∃ w : ι → ℝ, (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i)
              ∧ ∀ u : ι → ℝ, (∀ i ∈ Sopt, 0 ≤ u i) →
                  (1 - 2 * ε) * objLO m d B Sf Sopt u
                    ≤ objLO m d B Sf (assetsOf (κ := κ) R) w := by
  have hc : (1:ℝ) ≤ (k : ℝ) * (1 + (k : ℝ) * ω) := by
    have hk : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (k:ℝ)) hω]
  exact lo_fptas_portfolio_opt_block (P := P) hd hG hPS hopt hA₀Sopt hmax hdet hnormA hC
    hCpos hε hε1 hc hV hVF hFV hKc hs hselfA hη hξ hnd hA₀La hLcand
    (anchorCover_of_sysVar (m := m) hd hG hPS hω hsys) hkS hA₀cand hηθ hζ8

end SparseSharpe.Factor
