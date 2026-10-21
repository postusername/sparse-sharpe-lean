import SparseSharpe.Factor.ClippedTrading

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Теорема I из данных: long-short схема при фиксированном `K` (сессия 26, задача C0)

Long-short задача: веса любого знака, не больше `k` имён,

    F_LS(S) = max_w (2·m_S'w − w'V_S w),   OPT_LS(k) = max_{|S| ≤ k} F_LS(S).

Схема (`code/SPEC_FPTAS_K.md`, §§2–4): догадки `V = L·2^j`; перебор всех `K`-ок `T` строк
`S̄` (активы и `K` якорных строк гребня, `rowsK`); узлы решётки `s·ℤ^K` в невязках `T`
(Теорема H, `exists_grid_node`); в каждом узле — динамика с коробкой ключей
(`survivorsBox`: состояния с ключом вне коробки **отбрасываются**, спецификация §4);
кандидаты — носители всех выживших наборов.

* `objLO_le_phi_free`, `objLO_wfree_of_normal`, `isGreatest_objLO_free` — сильная
  двойственность long-short: `max_w (2m'w − w'Vw) = min_t φ_{S̄}(t)`, оба экстремума
  достигаются; гипотез, кроме данных, нет;
* `ls_one_guess` — при догадке `V ≤ OPT ≤ 2V` в таблице одного из узлов есть набор с
  `F_LS ≥ (1 − 17ε/8)·OPT` (Теорема H + `survivorsBox_spec` + `fptasK_step`);
* `card_lsCandidates_le` — размер семейства; **нет ни `ω`, ни величин входа, кроме
  числа догадок `J + 1`** (логарифм отношения `Σ_i m_i²/d_i` к значению `L = m_i²/V_ii`
  одиночного актива); `card_lsCandidates_poly` — та же граница в полиномиальной форме
  `4(J+1)(M+K)^K·N·(5K²N/ε)^K·(21KMN/ε)^K·(9KMN)^{K²}`, `N = k + K`;
* `main_theorem_ls` — **Теорема I из данных**: размер, `≤ k` имён у каждого кандидата,
  существование лучшей пары, гарантия `1 − 17ε/8` для значения и `√(1 − 17ε/8)` для
  коэффициента Шарпа портфеля `x = w*/Σ|w*_i|` (единичная валовая позиция).

Проверка спецификации на «дыру» `findings_v16.md` §1: в long-short спецификации правило
«состояния вне коробки отбрасываются» записано явно (§4), и здесь динамика — именно
`survivorsBox` с канонической коробкой `boxOf`; оценка таблицы `survivorsBox_card_le`
верна **при любом прогоне**, а коробка содержит ключи всех наборов, близких к префиксам
`S̄*` (`keyOf_mem_boxOf`: `|cf| ≤ 1` на `S̄*`, `|S̄*| ≤ k + K`, `φ_{S̄*}(τ) ≤ 4V`).
-/

namespace SparseSharpe.Factor

open Finset

section LongShortDuality

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- Поточечно, без знакового ограничения: `2rw − dw² ≤ r²/d`. -/
lemma quad_item_le_free {r dd ww : ℝ} (hd : 0 < dd) :
    2 * r * ww - dd * ww ^ 2 ≤ r ^ 2 / dd := by
  have hkey : 0 ≤ dd * (ww - r / dd) ^ 2 := by positivity
  have hexp : dd * (ww - r / dd) ^ 2 = dd * ww ^ 2 - 2 * r * ww + r ^ 2 / dd := by
    field_simp; ring
  linarith

/-- **Слабая двойственность long-short.** Для **любого** `w` (любого знака) и любого `t`:
`2m_S'w − w'V_Sw ≤ φ_{S̄}(t) = t'Σ_f⁻¹t + Σ_{i∈S}(m_i − ⟨B_i,t⟩)²/d_i`. -/
theorem objLO_le_phi_free (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (S : Finset ι) (w : ι → ℝ) (t : κ → ℝ) :
    objLO m d B Sf S w ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) S) t := by
  have hyoung := young_Sf (B := B) (P := P) (G := G) hG hPS S w t
  have hdot := Bw_dot (B := B) S w t
  have hitems : ∑ i ∈ S, (2 * (m i - dotp (B i) t) * w i - d i * w i ^ 2)
      ≤ ∑ i ∈ S, (m i - dotp (B i) t) ^ 2 / d i :=
    Finset.sum_le_sum fun i _ => quad_item_le_free (hd i)
  have hsplit : ∑ i ∈ S, (2 * (m i - dotp (B i) t) * w i - d i * w i ^ 2)
      = 2 * (∑ i ∈ S, m i * w i) - 2 * (∑ j, Bw B S w j * t j)
        - ∑ i ∈ S, d i * w i ^ 2 := by
    rw [hdot]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit] at hitems
  rw [objLO_eq, phiK_eq (P := P) hd hG]
  have hq : quadf P t = ∑ j, ∑ j', P j j' * (t j * t j') := rfl
  linarith

/-- Long-short вес в точке `t`: `w_i(t) = (m_i − ⟨B_i,t⟩)/d_i` (без обрезания). -/
noncomputable def wfree (m d : ι → ℝ) (B : ι → κ → ℝ) (t : κ → ℝ) : ι → ℝ :=
  fun i => (m i - dotp (B i) t) / d i

/-- **Первый момент набора `S̄` в координатах задачи:**
`mom_{S̄}(t, v) = ⟨B'w(t), v⟩ − t'Σ_f⁻¹v`. -/
lemma mom_barK_free (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (S : Finset ι) (t v : κ → ℝ) :
    mom (rowsK d B G) (targetsK m d) (barK (κ := κ) S) t v
      = (∑ j, Bw B S (wfree m d B t) j * v j) - bilf P t v := by
  rw [mom, barK, Finset.sum_disjSum]
  have hassets : ∑ i ∈ S, (targetsK m d (Sum.inl i : ι ⊕ κ)
        - dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) t)
        * dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) v
      = ∑ j, Bw B S (wfree m d B t) j * v j := by
    have hterm : ∀ i ∈ S, (targetsK m d (Sum.inl i : ι ⊕ κ)
        - dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) t)
        * dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) v
        = ∑ j, (B i j * wfree m d B t i) * v j := by
      intro i _
      have hdi := hd i
      have hsq : Real.sqrt (d i) * Real.sqrt (d i) = d i := Real.mul_self_sqrt hdi.le
      have hne : Real.sqrt (d i) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hdi)
      have hdot : ∀ u : κ → ℝ, dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) u
          = dotp (B i) u / Real.sqrt (d i) := by
        intro u
        simp only [rowsK, Sum.elim_inl, dotp, Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hdot, hdot]
      simp only [targetsK, Sum.elim_inl]
      have hrhs : ∑ j, (B i j * wfree m d B t i) * v j = wfree m d B t i * dotp (B i) v := by
        rw [dotp, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [hrhs, wfree, div_sub_div_same, div_mul_div_comm, hsq]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [Bw, Finset.sum_mul]
  have hanchor : ∑ l : κ, (targetsK m d (Sum.inr l : ι ⊕ κ)
        - dotp (rowsK d B G (Sum.inr l : ι ⊕ κ)) t)
        * dotp (rowsK d B G (Sum.inr l : ι ⊕ κ)) v = -bilf P t v := by
    have h1 : ∀ l : κ, (targetsK m d (Sum.inr l : ι ⊕ κ)
        - dotp (rowsK d B G (Sum.inr l : ι ⊕ κ)) t)
        * dotp (rowsK d B G (Sum.inr l : ι ⊕ κ)) v
        = -(∑ j, ∑ j', (G l j * G l j') * (t j * v j')) := by
      intro l
      simp only [targetsK, rowsK, Sum.elim_inr, zero_sub, neg_mul, dotp]
      rw [Finset.sum_mul_sum]
      simp only [neg_inj]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
    rw [Finset.sum_congr rfl fun l _ => h1 l, Finset.sum_neg_distrib, bilf]
    congr 1
    rw [sum_swap3]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by
      rw [← Finset.sum_mul, hG j j']
  rw [hassets, hanchor]
  ring

/-- В неподвижной точке `t̂` набора `S̄` вес `w(t̂)` даёт `B'w = Σ_f⁻¹t̂`. -/
theorem Bw_wfree_of_normal (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    {S : Finset ι} {th : κ → ℝ}
    (hnormal : IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th) (j₀ : κ) :
    Bw B S (wfree m d B th) j₀ = ∑ j, P j₀ j * th j := by
  have hid := mom_barK_free (m := m) (B := B) (P := P) (G := G) hd hG S th (basisVec j₀)
  rw [hnormal (basisVec j₀), sum_mul_basisVec, bilf_basisVec] at hid
  have hsymm := P_symm_of_root (P := P) (G := G) hG
  have : Bw B S (wfree m d B th) j₀ = ∑ j, P j j₀ * th j := by linarith
  rw [this]
  exact Finset.sum_congr rfl fun j _ => by rw [hsymm j j₀]

/-- В неподвижной точке `t̂` набора `S̄`: `Σ_f B'w(t̂) = t̂`. -/
theorem tw_wfree_of_normal (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {S : Finset ι} {th : κ → ℝ}
    (hnormal : IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th) :
    tw Sf B S (wfree m d B th) = th := by
  have hSP := SP_of_PS (P := P) (Sf := Sf) hPS
  funext j
  simp only [tw]
  have hBw : ∀ j' : κ, Bw B S (wfree m d B th) j' = ∑ l, P j' l * th l :=
    fun j' => Bw_wfree_of_normal (G := G) hd hG hnormal j'
  rw [Finset.sum_congr rfl fun j' _ => by rw [hBw j']]
  have hswap : ∑ j' : κ, Sf j j' * ∑ l, P j' l * th l
      = ∑ l, (∑ j', Sf j j' * P j' l) * th l := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j' _ => by ring
  rw [hswap, Finset.sum_congr rfl fun l _ => by rw [hSP j l]]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **Достижимость (long-short).** В неподвижной точке `t̂` набора `S̄` портфель
`w(t̂) = (m − Bt̂)/d` даёт `2m_S'w − w'V_Sw = φ_{S̄}(t̂)`. -/
theorem objLO_wfree_of_normal (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {S : Finset ι} {th : κ → ℝ}
    (hnormal : IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th) :
    objLO m d B Sf S (wfree m d B th)
      = phi (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th := by
  set w := wfree m d B th with hwdef
  have htw : tw Sf B S w = th := tw_wfree_of_normal (G := G) hd hG hPS hnormal
  have hw : ∀ i ∈ S, d i * w i + dotp (B i) (tw Sf B S w) = m i := by
    intro i _
    rw [htw, hwdef, wfree]
    have hne : d i ≠ 0 := ne_of_gt (hd i)
    field_simp
    ring
  have hphi := phi_tw (P := P) hd hG hPS hw
  rw [htw] at hphi
  have hquad : ∑ i ∈ S, ∑ i' ∈ S, Vmat d B Sf i i' * (w i * w i')
      = ∑ i ∈ S, m i * w i := by
    calc ∑ i ∈ S, ∑ i' ∈ S, Vmat d B Sf i i' * (w i * w i')
        = ∑ i ∈ S, w i * ∑ i' ∈ S, Vmat d B Sf i i' * w i' := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i' _ => by ring
      _ = ∑ i ∈ S, w i * (d i * w i + dotp (B i) (tw Sf B S w)) :=
          Finset.sum_congr rfl fun i hi => by rw [Vmat_mulVec i hi]
      _ = ∑ i ∈ S, m i * w i :=
          Finset.sum_congr rfl fun i hi => by rw [hw i hi]; ring
  rw [objLO, hquad, hphi]
  ring

/-- **Сильная двойственность long-short.** Для любого носителя `S` неподвижная точка `t̂`
набора `S̄` существует, и `φ_{S̄}(t̂) = max_w (2m_S'w − w'V_Sw)` (максимум по весам любого
знака достигается). Гипотезы — только данные. -/
theorem isGreatest_objLO_free (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (S : Finset ι) :
    ∃ th : κ → ℝ, IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th ∧
      IsGreatest {v : ℝ | ∃ w : ι → ℝ, v = objLO m d B Sf S w}
        (phi (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th) := by
  obtain ⟨th, hnormal⟩ := exists_isNormal_of_det (a := rowsK d B G) (V := barK (κ := κ) S)
    (Ta := fun l => (Sum.inr l : ι ⊕ κ)) (fun l => inr_mem_barK S l)
    (det_anchor_ne_zero (d := d) (B := B) (P := P) (Sf := Sf) hG hPS) (targetsK m d)
  refine ⟨th, hnormal, ⟨wfree m d B th, (objLO_wfree_of_normal (G := G) hd hG hPS hnormal).symm⟩,
    ?_⟩
  rintro v ⟨w, rfl⟩
  exact objLO_le_phi_free (G := G) hd hG hPS S w th

/-- **Оптимальный long-short носитель существует**: `S`, `|S| ≤ k`, с неподвижной точкой
`t̂` набора `S̄`, значение `φ_{S̄}(t̂)` которого достигается на `S` и не меньше значения
**любого** портфеля (любого знака) с не более чем `k` именами. -/
theorem exists_optimal_support_free (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (k : ℕ) :
    ∃ S : Finset ι, S.card ≤ k ∧ ∃ th : κ → ℝ,
      IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th
      ∧ IsGreatest {v : ℝ | ∃ u : ι → ℝ, v = objLO m d B Sf S u}
          (phi (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th)
      ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ,
          objLO m d B Sf S' u ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th := by
  classical
  have hval : ∀ S : Finset ι, ∃ th : κ → ℝ,
      IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th ∧
      IsGreatest {v : ℝ | ∃ w : ι → ℝ, v = objLO m d B Sf S w}
        (phi (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th) :=
    fun S => isGreatest_objLO_free (G := G) hd hG hPS S
  choose th hnorm hgreat using hval
  have hne : ((Finset.univ : Finset (Finset ι)).filter (fun S => S.card ≤ k)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image _
    (fun S => phi (rowsK d B G) (targetsK m d) (barK (κ := κ) S) (th S)) hne
  have hSk : S.card ≤ k := (Finset.mem_filter.mp hS).2
  refine ⟨S, hSk, th S, hnorm S, hgreat S, fun S' hS' u => ?_⟩
  have h1 := (hgreat S').2 ⟨u, rfl⟩
  have h2 := hmax S' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS'⟩)
  exact le_trans h1 h2

/-! ### Вилка для догадок без `ω` -/

/-- Одиночный актив: лучшая позиция (любого знака) в активе `i` даёт `m_i²/V_ii`. -/
lemma objLO_single_free (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {S : Finset ι} {i : ι} (hi : i ∈ S) :
    objLO m d B Sf S (fun j => if j = i then m i / Vmat d B Sf i i else 0)
      = m i ^ 2 / Vmat d B Sf i i := by
  have hV := Vmat_diag_pos (B := B) (Sf := Sf) hd hG hPS i
  rw [objLO_eq_ret_var, pRet_single hi, pVar_single hi]
  field_simp
  ring

/-- **Нижняя граница вилки.** Long-short оптимум не меньше `m_i²/V_ii` для каждого `i`. -/
lemma opt_ge_single_free (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {Fopt : ℝ}
    (hSopt : ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, objLO m d B Sf S' u ≤ Fopt)
    (i : ι) : m i ^ 2 / Vmat d B Sf i i ≤ Fopt := by
  have h := hSopt {i} (by simpa using hk1)
    (fun j => if j = i then m i / Vmat d B Sf i i else 0)
  rwa [objLO_single_free (B := B) hd hG hPS (Finset.mem_singleton_self i)] at h

/-- **Верхняя граница вилки (слабая двойственность в `t = 0`).** Значение любого портфеля
не больше `Σ_i m_i²/d_i` (сумма по всем активам). -/
lemma objLO_le_sum_sq_free (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (S : Finset ι) (w : ι → ℝ) :
    objLO m d B Sf S w ≤ ∑ i, m i ^ 2 / d i := by
  have h := objLO_le_phi_free (m := m) (B := B) (Sf := Sf) (P := P) (G := G) hd hG hPS S w
    (fun _ => 0)
  rw [phiK_eq (P := P) hd hG] at h
  have h0 : (∑ j, ∑ j', P j j' * ((fun _ : κ => (0:ℝ)) j * (fun _ : κ => (0:ℝ)) j'))
      + ∑ i ∈ S, (m i - dotp (B i) (fun _ => 0)) ^ 2 / d i = ∑ i ∈ S, m i ^ 2 / d i := by
    simp [dotp]
  rw [h0] at h
  refine le_trans h (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) ?_)
  intro i _ _
  have := hd i
  positivity

end LongShortDuality

/-! ### Параметры схемы, таблица и семейство кандидатов -/

section LongShortScheme

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- Константа зажима Теоремы H: `C = (k+K)·K`. -/
noncomputable def lsC (Kc k : ℕ) : ℝ := ((k + Kc : ℕ) : ℝ) * (Kc : ℝ)

/-- Шаг сетки при догадке `V`: `s = 2√(εV/(K·C))` (как в `exists_grid_node`). -/
noncomputable def lsStep (Kc k : ℕ) (ε V : ℝ) : ℝ :=
  2 * Real.sqrt (ε * V / ((Kc : ℝ) * lsC Kc k))

/-- Радиус коробки номеров узлов: `Z = ⌈√(K·C/(2ε)) + 1/2⌉`. Величин входа в нём нет. -/
noncomputable def lsZ (Kc k : ℕ) (ε : ℝ) : ℕ :=
  ⌈Real.sqrt ((Kc : ℝ) * lsC Kc k / (2 * ε)) + 1 / 2⌉₊

/-- Ширина корзины по `M̃`: `η = √(εV)/(4√K·M)`. -/
noncomputable def lsEta (Mc Kc : ℕ) (ε V : ℝ) : ℝ :=
  Real.sqrt (ε * V) / (4 * Real.sqrt (Kc : ℝ) * (Mc : ℝ))

/-- Ширина корзины по `Κ̃`: `ξ = 1/(2KM)`. -/
noncomputable def lsXi (Mc Kc : ℕ) : ℝ := 1 / (2 * (Kc : ℝ) * (Mc : ℝ))

/-- **Таблица long-short динамики** при догадке `V`, `K`-ке `T` и узле `t`: допускаются все
активы (`adm ≡ true`), значение — `Q = φ_U(t)`, ключ — округлённые `M̃`, `Κ̃` и мощность,
наборы с ключом вне канонической коробки `boxOf` **отбрасываются** после каждого шага. -/
noncomputable def lsTable (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ) (ε V : ℝ)
    (T : κ → (ι ⊕ κ)) (t : κ → ℝ) (La : List ι) : Finset (Finset (ι ⊕ κ)) :=
  survivorsBox (fun W => phi (rowsK d B G) (targetsK m d) W t)
    (keyOf (rowsK d B G) (targetsK m d) T t (lsEta (Fintype.card ι) (Fintype.card κ) ε V)
      (lsXi (Fintype.card ι) (Fintype.card κ)))
    (fun _ => true)
    (boxOf κ 1 V (lsEta (Fintype.card ι) (Fintype.card κ) ε V)
      (lsXi (Fintype.card ι) (Fintype.card κ)) (k + Fintype.card κ) (Fintype.card ι))
    (anchorRows ι κ) (La.map Sum.inl)

/-- **Семейство при одной догадке `V`**: носители выживших наборов по всем `K`-кам строк
`S̄` (их `(M+K)^K`) и всем узлам `z ∈ [−Z, Z]^K`. -/
noncomputable def lsFamily (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ) (ε V : ℝ)
    (La : List ι) : Finset (Finset ι) :=
  (Finset.univ : Finset (κ → (ι ⊕ κ))).biUnion fun T =>
    (nodeBox (κ := κ) (lsZ (Fintype.card κ) k ε)).biUnion fun z =>
      (lsTable m d B G k ε V T
        (nodePoint (rowsK d B G) (targetsK m d) T (lsStep (Fintype.card κ) k ε V) z) La).image
        (assetsOf (κ := κ))

/-- **Семейство кандидатов Теоремы I** по всем догадкам `V_j = L·2^j`, `j ≤ J`. -/
noncomputable def lsCandidates (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ)
    (ε L : ℝ) (J : ℕ) (La : List ι) : Finset (Finset ι) :=
  (Finset.range (J + 1)).biUnion (fun j => lsFamily m d B G k ε (L * 2 ^ j) La)

/-- Граница размера одной таблицы (мощность канонической коробки при `ρ = 1`):
`(2⌈8M√(K(k+K)/ε) + M⌉ + 1)^K·(2⌈2KM(k+K) + M⌉ + 1)^{K²}·(k + K + 1)`. -/
noncomputable def lsTableBound (Mc Kc k : ℕ) (ε : ℝ) : ℕ :=
  (2 * ⌈8 * (Mc : ℝ) * Real.sqrt ((Kc : ℝ) * ((k + Kc : ℕ) : ℝ) / ε) + (Mc : ℝ)⌉ + 1).toNat
      ^ Kc
    * ((2 * ⌈2 * (Kc : ℝ) * (Mc : ℝ) * ((k + Kc : ℕ) : ℝ) + (Mc : ℝ)⌉ + 1).toNat ^ (Kc * Kc)
      * (k + Kc + 1))

lemma lsEta_pos [Nonempty ι] [Nonempty κ] {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V) :
    0 < lsEta (Fintype.card ι) (Fintype.card κ) ε V := by
  have hK : (0:ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hM : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have h1 : 0 < Real.sqrt (ε * V) := Real.sqrt_pos.mpr (by positivity)
  have h2 : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr hK
  unfold lsEta
  positivity

lemma lsXi_pos [Nonempty ι] [Nonempty κ] : 0 < lsXi (Fintype.card ι) (Fintype.card κ) := by
  have hK : (0:ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hM : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold lsXi
  positivity

/-- **Мощность канонической коробки при параметрах схемы**: `V` сокращается. -/
lemma card_lsBox [Nonempty ι] [Nonempty κ] (k : ℕ) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V) :
    (boxOf κ 1 V (lsEta (Fintype.card ι) (Fintype.card κ) ε V)
      (lsXi (Fintype.card ι) (Fintype.card κ)) (k + Fintype.card κ) (Fintype.card ι)).card
      = lsTableBound (Fintype.card ι) (Fintype.card κ) k ε := by
  have hK : (0:ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hM : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  set Kc : ℝ := (Fintype.card κ : ℝ) with hKc
  set Mc : ℝ := (Fintype.card ι : ℝ) with hMc
  set N : ℝ := ((k + Fintype.card κ : ℕ) : ℝ) with hN
  have hN0 : 0 ≤ N := by positivity
  rw [card_boxOf zero_le_one (lsEta_pos hε hV) lsXi_pos, lsTableBound]
  have hsK : 0 < Real.sqrt Kc := Real.sqrt_pos.mpr hK
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have e1 : (1 * Real.sqrt (N * (4 * V)) + Mc * lsEta (Fintype.card ι) (Fintype.card κ) ε V)
      / lsEta (Fintype.card ι) (Fintype.card κ) ε V
      = 8 * Mc * Real.sqrt (Kc * N / ε) + Mc := by
    have hNV : Real.sqrt (N * (4 * V)) = 2 * Real.sqrt N * Real.sqrt V := by
      rw [show N * (4 * V) = 2 ^ 2 * (N * V) by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num), Real.sqrt_mul hN0]
      ring
    have hεV : Real.sqrt (ε * V) = Real.sqrt ε * Real.sqrt V := Real.sqrt_mul hε.le V
    have hKNε : Real.sqrt (Kc * N / ε) = Real.sqrt Kc * Real.sqrt N / Real.sqrt ε := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_mul hK.le]
    rw [lsEta, hNV, hεV, hKNε]
    field_simp
    ring
  have e2 : (N * 1 ^ 2 + Mc * lsXi (Fintype.card ι) (Fintype.card κ))
      / lsXi (Fintype.card ι) (Fintype.card κ) = 2 * Kc * Mc * N + Mc := by
    rw [lsXi]
    field_simp
    ring
  rw [e1, e2]

/-- Всякая таблица схемы не больше `lsTableBound + 1` (при любом узле, любой `K`-ке). -/
lemma card_lsTable_le [Nonempty ι] [Nonempty κ] (k : ℕ) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V)
    (T : κ → (ι ⊕ κ)) (t : κ → ℝ) (La : List ι) :
    (lsTable m d B G k ε V T t La).card
      ≤ lsTableBound (Fintype.card ι) (Fintype.card κ) k ε + 1 := by
  unfold lsTable
  refine le_trans (survivorsBox_card_le _ _ _ _ _ _) ?_
  rw [card_lsBox k hε hV]

/-- Размер семейства при одной догадке. -/
lemma card_lsFamily_le [Nonempty ι] [Nonempty κ] (k : ℕ) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V)
    (La : List ι) :
    (lsFamily m d B G k ε V La).card
      ≤ (Fintype.card ι + Fintype.card κ) ^ Fintype.card κ
        * ((2 * lsZ (Fintype.card κ) k ε + 1) ^ Fintype.card κ
          * (lsTableBound (Fintype.card ι) (Fintype.card κ) k ε + 1)) := by
  unfold lsFamily
  refine le_trans Finset.card_biUnion_le ?_
  have h2 : ∀ T ∈ (Finset.univ : Finset (κ → (ι ⊕ κ))),
      ((nodeBox (κ := κ) (lsZ (Fintype.card κ) k ε)).biUnion fun z =>
        (lsTable m d B G k ε V T
          (nodePoint (rowsK d B G) (targetsK m d) T (lsStep (Fintype.card κ) k ε V) z)
            La).image (assetsOf (κ := κ))).card
      ≤ (2 * lsZ (Fintype.card κ) k ε + 1) ^ Fintype.card κ
        * (lsTableBound (Fintype.card ι) (Fintype.card κ) k ε + 1) := by
    intro T _
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _
      (lsTableBound (Fintype.card ι) (Fintype.card κ) k ε + 1) (fun z _ => ?_)) ?_
    · exact le_trans Finset.card_image_le (card_lsTable_le k hε hV T _ La)
    · rw [card_nodeBox, smul_eq_mul]
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ h2) ?_
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_sum, smul_eq_mul]

/-- **Размер семейства кандидатов Теоремы I**:
`(J+1)·(M+K)^K·(2Z+1)^K·(lsTableBound + 1)`. -/
theorem card_lsCandidates_le [Nonempty ι] [Nonempty κ] (k : ℕ) {ε L : ℝ} (hε : 0 < ε)
    (hL0 : 0 < L) (J : ℕ) (La : List ι) :
    (lsCandidates m d B G k ε L J La).card
      ≤ (J + 1) * ((Fintype.card ι + Fintype.card κ) ^ Fintype.card κ
        * ((2 * lsZ (Fintype.card κ) k ε + 1) ^ Fintype.card κ
          * (lsTableBound (Fintype.card ι) (Fintype.card κ) k ε + 1))) := by
  unfold lsCandidates
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ (fun j _ =>
    card_lsFamily_le (m := m) (d := d) (B := B) (G := G) k hε (by positivity) La)) ?_
  rw [Finset.card_range, smul_eq_mul]

/-- У каждого члена таблицы не больше `k` активов. -/
lemma card_assetsOf_le_of_mem_lsTable {k : ℕ} {ε V : ℝ} {T : κ → (ι ⊕ κ)} {t : κ → ℝ}
    {La : List ι} {R : Finset (ι ⊕ κ)} (hR : R ∈ lsTable m d B G k ε V T t La) :
    (assetsOf (κ := κ) R).card ≤ k := by
  unfold lsTable at hR
  have hmem := survivorsBox_mem _ _ _ _ _ _ R hR
  have hbR : anchorRows ι κ ⊆ R := hmem.1
  have hRbar : R = barK (κ := κ) (assetsOf (κ := κ) R) := barK_assetsOf hbR
  rcases survivorsBox_key_mem _ _ _ _ _ _ R hR with hbase | hkey
  · have : assetsOf (κ := κ) R = ∅ := by
      rw [hbase]
      ext i
      simp [mem_assetsOf, anchorRows]
    rw [this]; simp
  · simp only [boxOf, keyBox, keyOf, Finset.mem_product, Finset.mem_range] at hkey
    have hcard : R.card ≤ k + Fintype.card κ := by omega
    have h2 := card_barK (κ := κ) (assetsOf (κ := κ) R)
    rw [← hRbar] at h2
    omega

/-- У каждого кандидата не больше `k` активов. -/
theorem card_le_of_mem_lsCandidates {k : ℕ} {ε L : ℝ} {J : ℕ} {La : List ι} {R : Finset ι}
    (hR : R ∈ lsCandidates m d B G k ε L J La) : R.card ≤ k := by
  unfold lsCandidates lsFamily at hR
  simp only [Finset.mem_biUnion, Finset.mem_image] at hR
  obtain ⟨j, _, T, _, z, _, R', hR', rfl⟩ := hR
  exact card_assetsOf_le_of_mem_lsTable hR'

end LongShortScheme

/-! ### Гарантия одной догадки и сквозная теорема -/

section LongShortGuarantee

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- **Одна догадка (шаг Теоремы I).** Пусть `S`, `|S| ≤ k`, — носитель с неподвижной точкой
`t̂` набора `S̄` и `V ≤ φ_{S̄}(t̂) ≤ 2V`, `0 < ε ≤ 1`. Тогда в семействе догадки `V` есть носитель
`R` с `φ_{R̄}(t') ≥ (1 − 17ε/8)·φ_{S̄}(t̂)` при **всех** `t'`, то есть
`F_LS(R) ≥ (1 − 17ε/8)·F_LS(S)`.

Ход: максимально-объёмная `K`-ка `T` набора `S̄` (`exists_maxvol_barK`, невырождена —
`maxvol_det_ne_zero`); узел решётки по Теореме H (`exists_grid_node`, `φ_{S̄}(τ) ≤ (1+ε)F`);
инвариант динамики с коробкой (`survivorsBox_spec`; коробка содержит нужные ключи —
`keyOf_mem_boxOf` с `|cf| ≤ 1`, `|S̄| ≤ k + K`, `φ_{S̄}(τ) ≤ 4V`); дрейф ключа `M` ширин корзины
переводится в гипотезы шага (`mom_close`, `gram_half_of_entrywise`), шаг — `fptasK_step`. -/
theorem ls_one_guess [Nonempty ι] [Nonempty κ]
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} {ε V : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {S : Finset ι} (hkS : S.card ≤ k) {th : κ → ℝ}
    (hnormal : IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th)
    (hV : 0 < V) (hVF : V ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th)
    (hFV : phi (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th ≤ 2 * V)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La) :
    ∃ R ∈ lsFamily m d B G k ε V La, ∀ t' : κ → ℝ,
      (1 - 17 * ε / 8) * phi (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th
        ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) R) t' := by
  classical
  set a := rowsK d B G with ha
  set y := targetsK m d with hy
  set A := barK (κ := κ) S with hA
  set F := phi a y A th with hF
  have hK0 : 0 < Fintype.card κ := Fintype.card_pos
  have hM0 : 0 < Fintype.card ι := Fintype.card_pos
  have hKc : (0:ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast hK0
  have hMc : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hM0
  -- максимально-объёмная `K`-ка набора `S̄`
  obtain ⟨T, hmax⟩ := exists_maxvol_barK (d := d) (B := B) (G := G) (S := S)
  have hdet := maxvol_det_ne_zero (P := P) (Sf := Sf) hmax hG hPS
  have hAcard : A.card ≤ k + Fintype.card κ := by rw [hA, card_barK]; omega
  have hC : (A.card * Fintype.card κ : ℝ) ≤ lsC (Fintype.card κ) k := by
    rw [lsC]
    have : (A.card : ℝ) ≤ ((k + Fintype.card κ : ℕ) : ℝ) := by exact_mod_cast hAcard
    exact mul_le_mul_of_nonneg_right this hKc.le
  have hCpos : 0 < lsC (Fintype.card κ) k := by
    rw [lsC]
    have : (0:ℝ) < ((k + Fintype.card κ : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < k + Fintype.card κ)
    positivity
  -- узел сетки (Теорема H)
  obtain ⟨z, hz1, hz2⟩ := exists_grid_node (a := a) (y := y) (s := lsStep (Fintype.card κ) k ε V)
    hmax hdet hnormal hC hCpos hε hV hVF hFV hKc rfl
  have hzbox : z ∈ nodeBox (κ := κ) (lsZ (Fintype.card κ) k ε) :=
    mem_nodeBox_of_abs_le fun l => le_trans (hz1 l) (Nat.le_ceil _)
  set t := nodePoint a y T (lsStep (Fintype.card κ) k ε V) z with ht
  have hQ : phi a y A t ≤ (1 + ε) * F :=
    hz2 t (fun l => nodePoint_spec (y := y) (s := lsStep (Fintype.card κ) k ε V) (z := z) hdet l)
  have hF0 : 0 ≤ F := phi_nonneg a y A th
  have hQ4 : phi a y A t ≤ 4 * V := by nlinarith
  -- динамика с коробкой
  set η := lsEta (Fintype.card ι) (Fintype.card κ) ε V with hη
  set ξ := lsXi (Fintype.card ι) (Fintype.card κ) with hξ
  have hηpos : 0 < η := lsEta_pos hε hV
  have hξpos : 0 < ξ := lsXi_pos
  set Lr : List (ι ⊕ κ) := La.map Sum.inl with hLr
  have hndL : Lr.Nodup := hnd.map (fun _ _ h => by injection h)
  have hLlen : Lr.length = Fintype.card ι := by
    rw [hLr, List.length_map]; exact length_of_nodup_complete hnd hall
  have hdisj : ∀ x ∈ Lr, x ∉ anchorRows ι κ := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    intro hc
    exact (not_isLeft_of_mem_anchorRows hc) (by simp)
  have hbA : anchorRows ι κ ⊆ A := anchorRows_subset_barK S
  have hAL : A ⊆ anchorRows ι κ ∪ Lr.toFinset := by
    intro x _
    rcases x with i | l
    · exact Finset.mem_union_right _
        (List.mem_toFinset.mpr (List.mem_map.mpr ⟨i, hall i, rfl⟩))
    · exact Finset.mem_union_left _ (inr_mem_anchorRows l)
  have hbox : ∀ U' ⊆ A, ∀ V' : Finset (ι ⊕ κ),
      KeyClose a y T t η ξ (Lr.length : ℝ) V' U' →
      keyOf a y T t η ξ V' ∈ boxOf κ 1 V η ξ (k + Fintype.card κ) (Fintype.card ι) :=
    fun U' hU' V' hV' => keyOf_mem_boxOf zero_le_one
      (fun x hx l => abs_cf_le_one hmax hdet hx l) hAcard hQ4 hηpos hξpos
      (by rw [hLlen]) hU' hV'
  obtain ⟨R, hR, hclose, hQR⟩ := survivorsBox_spec (a := a) (y := y) (T := T) (t := t)
    hηpos hξpos (fun _ => true) (boxOf κ 1 V η ξ (k + Fintype.card κ) (Fintype.card ι))
    (anchorRows ι κ) Lr hndL hdisj A hbA hAL (fun _ _ _ => rfl) hbox
  rw [hLlen] at hclose
  -- гипотезы шага из дрейфа ключа
  set Δ := Real.sqrt (Fintype.card κ : ℝ) * ((Fintype.card ι : ℝ) * η) with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  have hMclose : ∑ l, (momK a y T R t l - momK a y T A t l) ^ 2 ≤ Δ ^ 2 := by
    have hterm : ∀ l ∈ (Finset.univ : Finset κ),
        (momK a y T R t l - momK a y T A t l) ^ 2 ≤ ((Fintype.card ι : ℝ) * η) ^ 2 := by
      intro l _
      have h1 := hclose.mom l
      have h2 := abs_nonneg (momK a y T R t l - momK a y T A t l)
      nlinarith [sq_abs (momK a y T R t l - momK a y T A t l)]
    calc ∑ l, (momK a y T R t l - momK a y T A t l) ^ 2
        ≤ ∑ _l : κ, ((Fintype.card ι : ℝ) * η) ^ 2 := Finset.sum_le_sum hterm
      _ = (Fintype.card κ : ℝ) * ((Fintype.card ι : ℝ) * η) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = Δ ^ 2 := by
          rw [hΔ, show (Real.sqrt (Fintype.card κ : ℝ) * ((Fintype.card ι : ℝ) * η)) ^ 2
            = Real.sqrt (Fintype.card κ : ℝ) ^ 2 * ((Fintype.card ι : ℝ) * η) ^ 2 by ring,
            Real.sq_sqrt hKc.le]
  have hΔsq : Δ ^ 2 ≤ ε * F / 16 := by
    have hsK : Real.sqrt (Fintype.card κ : ℝ) ^ 2 = (Fintype.card κ : ℝ) :=
      Real.sq_sqrt hKc.le
    have hsεV : Real.sqrt (ε * V) ^ 2 = ε * V := Real.sq_sqrt (by positivity)
    have hsK0 : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr hKc
    have he : Δ ^ 2 = ε * V / 16 := by
      rw [hΔ, hη, lsEta]
      field_simp
      simp only [hsεV]
      ring
    rw [he]
    have : ε * V ≤ ε * F := mul_le_mul_of_nonneg_left hVF hε.le
    linarith
  have hξK : ((Fintype.card ι : ℝ) * ξ) * (Fintype.card κ : ℝ) ≤ 1 / 2 := by
    rw [hξ, lsXi]
    field_simp
    linarith
  have hKR : ∀ v, gram a A v / 2 ≤ gram a R v :=
    gram_half_of_entrywise hdet hmax.1 (by positivity) hξK hclose.gram
  have hM := mom_close (y := y) (t := t) hdet hmax.1 hΔ0 hMclose
  have hbR := (survivorsBox_mem _ _ _ _ _ _ R hR).1
  have hRbar : R = barK (κ := κ) (assetsOf (κ := κ) R) := barK_assetsOf hbR
  refine ⟨assetsOf (κ := κ) R, ?_, fun t' => ?_⟩
  · unfold lsFamily
    simp only [Finset.mem_biUnion, Finset.mem_image]
    exact ⟨T, Finset.mem_univ _, z, hzbox, R, hR, rfl⟩
  · have hstep := fptasK_step hnormal hΔ0 hΔsq hQ hQR hM hKR (t' - t)
    rw [show t + (t' - t) = t' by abel] at hstep
    rw [← hRbar]
    exact hstep

/-- **В семействе есть хороший кандидат** для любой вилки `L ≤ OPT ≤ 2^(J+1)·L`: носитель `R`
с портфелем `w` (любого знака) и `2m'w − w'Vw ≥ (1 − 17ε/8)·OPT`. -/
theorem exists_good_lsCandidate [Nonempty ι] [Nonempty κ]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} {ε L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hL0 : 0 < L) {J : ℕ}
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    {S : Finset ι} (hkS : S.card ≤ k) {th : κ → ℝ}
    (hnormal : IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th)
    (hLF : L ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th)
    (hFJ : phi (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th ≤ 2 ^ (J + 1) * L) :
    ∃ R ∈ lsCandidates m d B G k ε L J La, ∃ w : ι → ℝ,
      (1 - 17 * ε / 8) * phi (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th
        ≤ objLO m d B Sf R w := by
  obtain ⟨j, hjJ, hVF, hFV⟩ := exists_doubling_guess_succ J hL0 hLF hFJ
  have hV : 0 < L * 2 ^ j := by positivity
  obtain ⟨R, hR, hval⟩ := ls_one_guess (Sf := Sf) (P := P) hG hPS hε hε1 hkS hnormal hV
    hVF hFV hnd hall
  obtain ⟨thR, hnR, _⟩ := isGreatest_objLO_free (m := m) (B := B) (Sf := Sf) (P := P) (G := G)
    hd hG hPS R
  refine ⟨R, ?_, wfree m d B thR, ?_⟩
  · unfold lsCandidates
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (by omega), hR⟩
  · rw [objLO_wfree_of_normal (G := G) hd hG hPS hnR]
    exact hval thR

/-- **Лучшая пара (long-short) в любом непустом семействе существует**: носитель `R₀` и
портфель `w₀` (любого знака), значение которого не меньше значения любого портфеля на
любом носителе семейства. -/
theorem exists_best_free_of_family
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {Fam : Finset (Finset ι)} (hne : Fam.Nonempty) :
    ∃ R₀ ∈ Fam, ∃ w₀ : ι → ℝ,
      ∀ R ∈ Fam, ∀ w : ι → ℝ, objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀ := by
  classical
  have hval : ∀ R : Finset ι, ∃ th : κ → ℝ,
      IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) R) th ∧
      IsGreatest {v : ℝ | ∃ w : ι → ℝ, v = objLO m d B Sf R w}
        (phi (rowsK d B G) (targetsK m d) (barK (κ := κ) R) th) :=
    fun R => isGreatest_objLO_free (G := G) hd hG hPS R
  choose th hnorm hgreat using hval
  obtain ⟨R₀, hR₀, hmax⟩ := Finset.exists_max_image _
    (fun R => phi (rowsK d B G) (targetsK m d) (barK (κ := κ) R) (th R)) hne
  refine ⟨R₀, hR₀, wfree m d B (th R₀), fun R hR w => ?_⟩
  rw [objLO_wfree_of_normal (G := G) hd hG hPS (hnorm R₀)]
  exact le_trans ((hgreat R).2 ⟨w, rfl⟩) (hmax R hR)

/-- **Коэффициент Шарпа (long-short).** Если `Fopt > 0` ограничивает значение любого портфеля
с не более чем `k` именами, а `w₀` на `R` даёт `2m'w₀ − w₀'Vw₀ ≥ (1 − c)·Fopt`, `c < 1`, то
портфель `x = w₀/Σ_{i∈R}|w₀ i|` имеет единичную валовую позицию `Σ|x_i| = 1` и коэффициент
Шарпа не меньше `√(1 − c)` от коэффициента Шарпа **любого** портфеля с не более чем `k`
именами и положительной ожидаемой доходностью (`c < 1`; знак `c` не важен). -/
theorem best_pair_sharpe_free
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} {c : ℝ} (hc1 : c < 1) {Fopt : ℝ} (hFpos : 0 < Fopt)
    (hSopt : ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, objLO m d B Sf S' u ≤ Fopt)
    {R : Finset ι} {w₀ : ι → ℝ} (hval : (1 - c) * Fopt ≤ objLO m d B Sf R w₀) :
    ∑ i ∈ R, |(∑ j ∈ R, |w₀ j|)⁻¹ * w₀ i| = 1
    ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, 0 < pRet m S' u →
        Real.sqrt (1 - c) * sharpe m d B Sf S' u
          ≤ sharpe m d B Sf R (fun i => (∑ j ∈ R, |w₀ j|)⁻¹ * w₀ i) := by
  have hc : 0 < 1 - c := by linarith
  have hobjpos : 0 < objLO m d B Sf R w₀ := lt_of_lt_of_le (mul_pos hc hFpos) hval
  obtain ⟨hrw, _⟩ := obj_le_sharpe_sq (B := B) hd hG hPS hobjpos
  obtain ⟨i₀, hi₀, hwi₀⟩ := exists_ne_zero_of_pRet_pos hrw
  have hg : 0 < ∑ j ∈ R, |w₀ j| :=
    lt_of_lt_of_le (abs_pos.mpr hwi₀) (Finset.single_le_sum (f := fun j => |w₀ j|)
      (fun j _ => abs_nonneg _) hi₀)
  refine ⟨?_, fun S' hS' u hru => ?_⟩
  · have : ∀ i ∈ R, |(∑ j ∈ R, |w₀ j|)⁻¹ * w₀ i| = (∑ j ∈ R, |w₀ j|)⁻¹ * |w₀ i| := by
      intro i _
      rw [abs_mul, abs_of_pos (inv_pos.mpr hg)]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hg.ne'
  · rw [sharpe_smul R w₀ (inv_pos.mpr hg)]
    obtain ⟨i, hi, hui⟩ := exists_ne_zero_of_pRet_pos hru
    have hvu : 0 < pVar d B Sf S' u := pVar_pos (B := B) hd hG hPS hi hui
    have hopt := hSopt S' hS' (fun i => (pRet m S' u / pVar d B Sf S' u) * u i)
    rw [objLO_opt_scale S' u hvu] at hopt
    have hobj : (1 - 2 * (c / 2)) * (pRet m S' u ^ 2 / pVar d B Sf S' u)
        ≤ objLO m d B Sf R w₀ := by
      rw [show 1 - 2 * (c / 2) = 1 - c by ring]
      exact le_trans (mul_le_mul_of_nonneg_left hopt hc.le) hval
    have h := (sharpe_ge_of_obj_ge (B := B) hd hG hPS (by linarith) hru hobj).2.2
    rwa [show 1 - 2 * (c / 2) = 1 - c by ring] at h

/-- **Теорема I из данных (long-short, фиксированное `K`).**

Пусть `V = diag(d) + BΣ_fB'`, `d > 0`, `G'G = Σ_f⁻¹`, `K ≥ 1`, `k ≥ 1`, `0 < ε < 8/17`,
`L = m_i²/V_ii > 0` — значение одиночного актива (естественный выбор — лучший одиночный
актив, `L = max_i m_i²/V_ii`; максимальность не нужна), `J = ⌈log₂((Σ_i m_i²/d_i)/L)⌉`, `La` —
список всех активов без повторов (любой порядок). Тогда семейство `lsCandidates` обладает
свойствами: (1) размер не больше `(J+1)·(M+K)^K·(2Z+1)^K·(T_I + 1)`, где
`Z = ⌈K√((k+K)/(2ε)) + 1/2⌉` (`lsZ`) и
`T_I = (2⌈8M√(K(k+K)/ε) + M⌉ + 1)^K·(2⌈2KM(k+K) + M⌉ + 1)^{K²}·(k+K+1)`
(`lsTableBound`) — **нет `ω` и нет величин входа, кроме числа догадок `J + 1`**;
(2) у каждого кандидата не больше `k` имён; (3) лучшая пара (носитель, портфель любого знака)
существует; (4) для любой лучшей пары `(R₀, w₀)` значение `2m'w₀ − w₀'Vw₀` не меньше
`(1 − 17ε/8)·(2m'u − u'Vu)` для **любого** портфеля `u` с не более чем `k` именами, а портфель
`x = w₀/Σ|w₀_i|` (единичная валовая позиция) имеет коэффициент Шарпа не меньше
`√(1 − 17ε/8)` от коэффициента Шарпа любого такого портфеля с положительной доходностью. -/
theorem main_theorem_ls [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε L : ℝ} (hε : 0 < ε) (hε1 : 17 * ε < 8)
    (hL0 : 0 < L) (hLatt : ∃ i, m i ^ 2 / Vmat d B Sf i i = L)
    {J : ℕ} (hJ : J = ⌈Real.logb 2 ((∑ i, m i ^ 2 / d i) / L)⌉₊)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La) :
    (lsCandidates m d B G k ε L J La).card
        ≤ (J + 1) * ((Fintype.card ι + Fintype.card κ) ^ Fintype.card κ
          * ((2 * lsZ (Fintype.card κ) k ε + 1) ^ Fintype.card κ
            * (lsTableBound (Fintype.card ι) (Fintype.card κ) k ε + 1)))
    ∧ (∀ R ∈ lsCandidates m d B G k ε L J La, R.card ≤ k)
    ∧ (∃ R₀ ∈ lsCandidates m d B G k ε L J La, ∃ w₀ : ι → ℝ,
        ∀ R ∈ lsCandidates m d B G k ε L J La, ∀ w : ι → ℝ,
          objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀)
    ∧ ∀ R₀ ∈ lsCandidates m d B G k ε L J La, ∀ w₀ : ι → ℝ,
        (∀ R ∈ lsCandidates m d B G k ε L J La, ∀ w : ι → ℝ,
          objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀) →
        R₀.card ≤ k
        ∧ (∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ,
            (1 - 17 * ε / 8) * objLO m d B Sf S' u ≤ objLO m d B Sf R₀ w₀)
        ∧ ∑ i ∈ R₀, |(∑ j ∈ R₀, |w₀ j|)⁻¹ * w₀ i| = 1
        ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, 0 < pRet m S' u →
            Real.sqrt (1 - 17 * ε / 8) * sharpe m d B Sf S' u
              ≤ sharpe m d B Sf R₀ (fun i => (∑ j ∈ R₀, |w₀ j|)⁻¹ * w₀ i) := by
  have hε1' : ε ≤ 1 := by linarith
  -- оптимум long-short
  obtain ⟨S, hkS, th, hnormal, hFopt, hSopt⟩ := exists_optimal_support_free (m := m) (d := d)
    (B := B) (Sf := Sf) (P := P) (G := G) hd hG hPS k
  set Fopt := phi (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th with hFoptdef
  -- вилка `[L, 2^(J+1)L]` без `ω`
  obtain ⟨i₀, hi₀⟩ := hLatt
  have hLF : L ≤ Fopt := hi₀ ▸ opt_ge_single_free (B := B) hd hG hPS hk1 hSopt i₀
  have hFU : Fopt ≤ ∑ i, m i ^ 2 / d i := by
    obtain ⟨u, hu⟩ := hFopt.1
    rw [hu]
    exact objLO_le_sum_sq_free (G := G) (P := P) hd hG hPS S u
  have hq1 : (1:ℝ) ≤ (∑ i, m i ^ 2 / d i) / L := by
    rw [le_div_iff₀ hL0]; linarith
  obtain ⟨hJa, _⟩ := guess_count_spec hq1
  rw [← hJ] at hJa
  have hFJ : Fopt ≤ 2 ^ (J + 1) * L := by
    have h1 : ∑ i, m i ^ 2 / d i ≤ 2 ^ J * L := by
      rwa [div_le_iff₀ hL0] at hJa
    have h2 : (2:ℝ) ^ J * L ≤ 2 ^ (J + 1) * L := by
      rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) J]
    linarith
  obtain ⟨R, hR, w, hw⟩ := exists_good_lsCandidate (Sf := Sf) (P := P) hd hG hPS hε hε1' hL0
    hnd hall hkS hnormal hLF hFJ
  refine ⟨card_lsCandidates_le k hε hL0 J La, fun R hR => card_le_of_mem_lsCandidates hR,
    exists_best_free_of_family (P := P) (G := G) hd hG hPS ⟨R, hR⟩, ?_⟩
  intro R₀ hR₀ w₀ hbest
  have hval : (1 - 17 * ε / 8) * Fopt ≤ objLO m d B Sf R₀ w₀ := le_trans hw (hbest R hR w)
  have hc1 : 17 * ε / 8 < 1 := by linarith
  obtain ⟨hx1, hxs⟩ := best_pair_sharpe_free (B := B) hd hG hPS hc1
    (lt_of_lt_of_le hL0 hLF) hSopt hval
  refine ⟨card_le_of_mem_lsCandidates hR₀, fun S' hS' u => ?_, hx1, hxs⟩
  have hub := hSopt S' hS' u
  have hcoef : (0:ℝ) ≤ 1 - 17 * ε / 8 := by linarith
  linarith [mul_le_mul_of_nonneg_left hub hcoef]

end LongShortGuarantee

/-! ### Полиномиальная форма границы размера

С `N = k + K`, `0 < ε ≤ 1`: размер семейства Теоремы I не больше
`4(J+1)·(M+K)^K·N·(5K²N/ε)^K·(21KMN/ε)^K·(9KMN)^{K²}` — при фиксированном `K` полином от `M`,
`k` и `1/ε` (степени `K² + 2K`, `(K + 1)²` и `2K`), умноженный на число догадок `J + 1`. -/

section LongShortPoly

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {G : κ → κ → ℝ}

lemma sqrt_le_self_of_one_le {y : ℝ} (hy : 1 ≤ y) : Real.sqrt y ≤ y := by
  rw [Real.sqrt_le_iff]
  exact ⟨by linarith, by nlinarith⟩

/-- **Полиномиальная оценка размера семейства Теоремы I.** -/
theorem card_lsCandidates_poly [Nonempty ι] [Nonempty κ] {k : ℕ} (hk1 : 1 ≤ k) {ε L : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hL0 : 0 < L) (J : ℕ) (La : List ι) :
    ((lsCandidates m d B G k ε L J La).card : ℝ)
      ≤ 4 * ((J : ℝ) + 1) * ((Fintype.card ι : ℝ) + Fintype.card κ) ^ Fintype.card κ
        * ((k + Fintype.card κ : ℕ) : ℝ)
        * (5 * (Fintype.card κ : ℝ) ^ 2 * ((k + Fintype.card κ : ℕ) : ℝ) / ε) ^ Fintype.card κ
        * (21 * (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ) * ((k + Fintype.card κ : ℕ) : ℝ)
            / ε) ^ Fintype.card κ
        * (9 * (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ) * ((k + Fintype.card κ : ℕ) : ℝ))
            ^ (Fintype.card κ * Fintype.card κ) := by
  have hcard := card_lsCandidates_le (m := m) (d := d) (B := B) (G := G) k hε hL0 J La
  set K := Fintype.card κ with hKdef
  set M := Fintype.card ι with hMdef
  have hK1 : (1:ℝ) ≤ (K : ℝ) := by exact_mod_cast (Fintype.card_pos : 0 < K)
  have hM1 : (1:ℝ) ≤ (M : ℝ) := by exact_mod_cast (Fintype.card_pos : 0 < M)
  set N : ℝ := ((k + K : ℕ) : ℝ) with hNdef
  have hN2 : (2:ℝ) ≤ N := by
    have : 2 ≤ k + K := by have := (Fintype.card_pos : 0 < K); omega
    rw [hNdef]; exact_mod_cast this
  have hεinv : 1 ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
  -- узлы: `2Z + 1 ≤ 5K²N/ε`
  have hKK : (1:ℝ) ≤ (K : ℝ) * K := by nlinarith
  have hK2N : (2:ℝ) ≤ (K : ℝ) ^ 2 * N := by
    have := mul_le_mul hKK hN2 (by norm_num) (by positivity)
    nlinarith
  have h4 : 2 ≤ (K : ℝ) ^ 2 * N / ε := by
    rw [le_div_iff₀ hε]; nlinarith
  have hZ : 2 * (lsZ K k ε : ℝ) + 1 ≤ 5 * (K : ℝ) ^ 2 * N / ε := by
    set y := (K : ℝ) * lsC K k / (2 * ε) with hydef
    have hy' : y = (K : ℝ) ^ 2 * N / ε / 2 := by rw [hydef, lsC, ← hNdef]; ring
    have hy : 1 ≤ y := by rw [hy']; linarith
    have h1 : Real.sqrt y ≤ y := sqrt_le_self_of_one_le hy
    have h2 : (lsZ K k ε : ℝ) < Real.sqrt y + 1 / 2 + 1 := by
      rw [lsZ, ← hydef]; exact Nat.ceil_lt_add_one (by positivity)
    have e : 5 * (K : ℝ) ^ 2 * N / ε = 5 * ((K : ℝ) ^ 2 * N / ε) := by ring
    rw [e]
    linarith
  -- таблица: `T + 1 ≤ 4N(21KMN/ε)^K(9KMN)^{K²}`
  have hT : (lsTableBound M K k ε : ℝ) + 1
      ≤ 4 * N * (21 * (K : ℝ) * (M : ℝ) * N / ε) ^ K
        * (9 * (K : ℝ) * (M : ℝ) * N) ^ (K * K) := by
    set x := 8 * (M : ℝ) * Real.sqrt ((K : ℝ) * N / ε) + (M : ℝ) with hx
    set z := 2 * (K : ℝ) * (M : ℝ) * N + (M : ℝ) with hz
    have hx0 : 0 ≤ x := by positivity
    have hz0 : 0 ≤ z := by positivity
    have hA := Factor.cast_toNat_two_ceil_le hx0
    have hB := Factor.cast_toNat_two_ceil_le hz0
    have hKN : 1 ≤ (K : ℝ) * N / ε := by rw [le_div_iff₀ hε]; nlinarith
    have hsq := sqrt_le_self_of_one_le hKN
    have hA' : 2 * x + 3 ≤ 21 * (K : ℝ) * (M : ℝ) * N / ε := by
      have e : 21 * (K : ℝ) * (M : ℝ) * N / ε = 21 * (M : ℝ) * ((K : ℝ) * N / ε) := by ring
      rw [e, hx]
      nlinarith
    have hB' : 2 * z + 3 ≤ 9 * (K : ℝ) * (M : ℝ) * N := by
      have hKN2 : (2:ℝ) ≤ (K : ℝ) * N := by nlinarith
      have hKMN : 2 * (M : ℝ) ≤ (K : ℝ) * (M : ℝ) * N := by
        have := mul_le_mul_of_nonneg_left hKN2 (by positivity : (0:ℝ) ≤ (M : ℝ))
        linarith
      rw [hz]; linarith
    have hA1 : (1:ℝ) ≤ (((2 * ⌈x⌉ + 1).toNat : ℕ) : ℝ) := by
      have : (0:ℤ) ≤ ⌈x⌉ := Int.ceil_nonneg hx0
      have : 1 ≤ (2 * ⌈x⌉ + 1).toNat := by omega
      exact_mod_cast this
    have hB1 : (1:ℝ) ≤ (((2 * ⌈z⌉ + 1).toNat : ℕ) : ℝ) := by
      have : (0:ℤ) ≤ ⌈z⌉ := Int.ceil_nonneg hz0
      have : 1 ≤ (2 * ⌈z⌉ + 1).toNat := by omega
      exact_mod_cast this
    have hTdef : (lsTableBound M K k ε : ℝ)
        = (((2 * ⌈x⌉ + 1).toNat : ℕ) : ℝ) ^ K
          * ((((2 * ⌈z⌉ + 1).toNat : ℕ) : ℝ) ^ (K * K) * (N + 1)) := by
      rw [lsTableBound, hx, hz, hNdef]
      push_cast
      ring
    have hN1 : N + 1 ≤ 2 * N := by linarith
    have hP1 : (1:ℝ) ≤ (((2 * ⌈x⌉ + 1).toNat : ℕ) : ℝ) ^ K := one_le_pow₀ hA1
    have hP2 : (1:ℝ) ≤ (((2 * ⌈z⌉ + 1).toNat : ℕ) : ℝ) ^ (K * K) := one_le_pow₀ hB1
    have hT1 : (1:ℝ) ≤ (lsTableBound M K k ε : ℝ) := by
      rw [hTdef]
      have : (1:ℝ) ≤ N + 1 := by linarith
      have h12 : (1:ℝ) ≤ (((2 * ⌈z⌉ + 1).toNat : ℕ) : ℝ) ^ (K * K) * (N + 1) := by nlinarith
      nlinarith
    have hQ1 : (((2 * ⌈x⌉ + 1).toNat : ℕ) : ℝ) ^ K ≤ (21 * (K : ℝ) * (M : ℝ) * N / ε) ^ K :=
      pow_le_pow_left₀ (by positivity) (le_trans hA hA') K
    have hQ2 : (((2 * ⌈z⌉ + 1).toNat : ℕ) : ℝ) ^ (K * K)
        ≤ (9 * (K : ℝ) * (M : ℝ) * N) ^ (K * K) :=
      pow_le_pow_left₀ (by positivity) (le_trans hB hB') (K * K)
    have hstep : (lsTableBound M K k ε : ℝ)
        ≤ (21 * (K : ℝ) * (M : ℝ) * N / ε) ^ K * ((9 * (K : ℝ) * (M : ℝ) * N) ^ (K * K)
          * (2 * N)) := by
      rw [hTdef]
      exact mul_le_mul hQ1 (mul_le_mul hQ2 hN1 (by positivity) (by positivity))
        (by positivity) (by positivity)
    have e : 4 * N * (21 * (K : ℝ) * (M : ℝ) * N / ε) ^ K
        * (9 * (K : ℝ) * (M : ℝ) * N) ^ (K * K)
        = 2 * ((21 * (K : ℝ) * (M : ℝ) * N / ε) ^ K * ((9 * (K : ℝ) * (M : ℝ) * N) ^ (K * K)
          * (2 * N))) := by ring
    rw [e]
    linarith
  -- сборка
  have hcast : ((lsCandidates m d B G k ε L J La).card : ℝ)
      ≤ ((J : ℝ) + 1) * (((M : ℝ) + K) ^ K
        * ((2 * (lsZ K k ε : ℝ) + 1) ^ K * ((lsTableBound M K k ε : ℝ) + 1))) := by
    have := (Nat.cast_le (α := ℝ)).mpr hcard
    push_cast at this
    exact this
  refine le_trans hcast ?_
  have hZK : (2 * (lsZ K k ε : ℝ) + 1) ^ K ≤ (5 * (K : ℝ) ^ 2 * N / ε) ^ K :=
    pow_le_pow_left₀ (by positivity) hZ K
  have h1 : (2 * (lsZ K k ε : ℝ) + 1) ^ K * ((lsTableBound M K k ε : ℝ) + 1)
      ≤ (5 * (K : ℝ) ^ 2 * N / ε) ^ K * (4 * N * (21 * (K : ℝ) * (M : ℝ) * N / ε) ^ K
        * (9 * (K : ℝ) * (M : ℝ) * N) ^ (K * K)) :=
    mul_le_mul hZK hT (by positivity) (by positivity)
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ ((M : ℝ) + K) ^ K)
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ (J : ℝ) + 1)
  refine le_trans h3 (le_of_eq ?_)
  ring

end LongShortPoly

/-! ### Непустота

Одноактивный инстанс: `m = d = 1`, `B = 0`, `Σ_f = G = P = 1`, `k = 1`, `ε = 1/4`, `L = 1`,
`J = 0`, порядок `[0]`. Все гипотезы `main_theorem_ls` выполнены; заключение даёт портфель
с единичной валовой позицией и коэффициентом Шарпа не меньше `√(1 − 17/32) > 0`. -/

theorem ls_instance :
    ∃ R₀ ∈ lsCandidates (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1) (fun _ (_ : Unit) => 0)
        (fun _ _ => 1) 1 (1/4) 1 0 [0],
      ∃ x : Fin 1 → ℝ, ∑ i ∈ R₀, |x i| = 1
        ∧ Real.sqrt (1 - 17 * (1/4) / 8) ≤ sharpe (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1)
            (fun _ (_ : Unit) => 0) (fun _ _ => 1) R₀ x := by
  set m : Fin 1 → ℝ := fun _ => 1
  set d : Fin 1 → ℝ := fun _ => 1
  set B : Fin 1 → Unit → ℝ := fun _ _ => 0
  set Sf : Unit → Unit → ℝ := fun _ _ => 1
  set G : Unit → Unit → ℝ := fun _ _ => 1
  set P : Unit → Unit → ℝ := fun _ _ => 1
  have hd : ∀ i, 0 < d i := fun _ => one_pos
  have hG : ∀ j j' : Unit, ∑ l : Unit, G l j * G l j' = P j j' := by intro j j'; simp [G, P]
  have hPS : ∀ j j' : Unit, ∑ l : Unit, P j l * Sf l j' = if j = j' then 1 else 0 := by
    intro j j'; simp [P, Sf]
  have hVd : ∀ i, Vmat d B Sf i i = 1 := by intro i; simp [Vmat, d, B]
  have hLatt : ∃ i, m i ^ 2 / Vmat d B Sf i i = 1 := ⟨0, by simp [hVd, m]⟩
  have hJlog : (0:ℕ) = ⌈Real.logb 2 ((∑ i, m i ^ 2 / d i) / 1)⌉₊ := by simp [m, d]
  have hnd : ([0] : List (Fin 1)).Nodup := List.nodup_singleton 0
  have hall : ∀ i : Fin 1, i ∈ ([0] : List (Fin 1)) := by
    intro i; rw [List.mem_singleton]; exact Subsingleton.elim _ _
  have hsu : sharpe m d B Sf Finset.univ (fun _ => 1) = 1 := by
    simp [sharpe, pRet, pVar, Vmat, m, d, B]
  obtain ⟨_, _, ⟨R₀, hR₀, w₀, hbest⟩, h4⟩ := main_theorem_ls (G := G) (P := P) (Sf := Sf)
    hd hG hPS le_rfl (by norm_num : (0:ℝ) < 1/4) (by norm_num) one_pos hLatt hJlog hnd hall
  obtain ⟨_, _, hx1, hxsh⟩ := h4 R₀ hR₀ w₀ hbest
  have hsh := hxsh Finset.univ (by simp) (fun _ => 1) (by simp [pRet, m])
  refine ⟨R₀, hR₀, _, hx1, ?_⟩
  rw [hsu, mul_one] at hsh
  exact hsh

end SparseSharpe.Factor
