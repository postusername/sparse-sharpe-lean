import SparseSharpe.Factor.OnePassLower

set_option linter.style.header false

/-!
# Без `ω` при `K ≥ 3` нужно почти квадратичное время по `M`: разрыв от 3SUM

Задача 3SUM' (Gajentaan–Overmars): даны три набора целых `xa : Fin na → ℤ`, `xb : Fin nb → ℤ`,
`xc : Fin nc → ℤ`; есть ли `a, b, c` с `xa a + xb b = xc c`? Строим портфельную задачу: активы
`Fin na ⊕ Fin nb ⊕ Fin nc`, три фактора, `Σ_f = I`, `d = 1`, `m = 1`, нагрузки `A·(1, 0, xa a)`,
`A·(0, 1, xb b)`, `−A·(1, 1, xc c)`.

* «Да»: тройка `{a, b, c}` с весами `1` — точный хедж, цель `3` (`ts_yes`); больше `3` нет ни у
  какого носителя с не более чем тремя именами (`ts_le_three`).
* «Нет»: у любого носителя с не более чем тремя именами при любых весах (long-only или
  long-short) цель не больше `(2(1 + 3U)² + 9)/A²`, если `|xa|, |xb| ≤ U` (`ts_no`): слабая
  двойственность в точке, где все невязки носителя нулевые. Носитель без актива одного из трёх
  типов обнуляет невязки в точке нормы `≤ √5/A`; тройка `a, b, c` — в точке
  `((1 − 3xa/δ), (1 − 3xb/δ), 3/δ)/A`, `δ = xa + xb − xc`, `|δ| ≥ 1`.
* При `2(1 + 3U)² + 9 ≤ A²` цель «нет» не больше `1`, и любое `(1 − ε)`-приближение с `ε < 2/3`
  решает 3SUM' (`threesum_decide`). Факторы с нулевыми нагрузками ничего не меняют
  (`objLO_padZero`), так что то же при любом числе факторов `K ≥ 3` (`threesum_decide_pad`).

Вывод о времени (алгоритм за `T(M)` решает 3SUM за `T(3n) + O(n)`) — вне Lean.
-/

namespace SparseSharpe.Factor

open Finset

section PadZero

variable {ι κ κ' : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype κ'] [DecidableEq κ']

/-- Нагрузки, дополненные нулями по факторам `κ'`. -/
def padZero (B : ι → κ → ℝ) : ι → κ ⊕ κ' → ℝ := fun i => Sum.elim (B i) 0

omit [Fintype ι] in
/-- **Нулевые факторы ничего не меняют:** цель с нагрузками `padZero B` и `Σ_f = I` на `κ ⊕ κ'`
равна цели с `B` и `Σ_f = I` на `κ`. -/
theorem objLO_padZero (m d : ι → ℝ) (B : ι → κ → ℝ) (S : Finset ι) (w : ι → ℝ) :
    objLO m d (padZero (κ' := κ') B) (opI (κ ⊕ κ')) S w = objLO m d B (opI κ) S w := by
  have hV : ∀ i i', Vmat d (padZero (κ' := κ') B) (opI (κ ⊕ κ')) i i'
      = Vmat d B (opI κ) i i' := by
    intro i i'
    simp only [Vmat]
    rw [sum_opI_mul, sum_opI_mul]
    simp only [padZero, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero]
  simp only [objLO, hV]

end PadZero

section ThreeSum

variable {na nb nc : ℕ}

/-- Нагрузки: `A·(1, 0, xa a)`, `A·(0, 1, xb b)`, `−A·(1, 1, xc c)`. -/
noncomputable def tsB (A : ℝ) (xa : Fin na → ℤ) (xb : Fin nb → ℤ) (xc : Fin nc → ℤ) :
    Fin na ⊕ Fin nb ⊕ Fin nc → Fin 3 → ℝ
  | Sum.inl a => ![A, 0, A * xa a]
  | Sum.inr (Sum.inl b) => ![0, A, A * xb b]
  | Sum.inr (Sum.inr c) => ![-A, -A, -(A * xc c)]

/-- Ожидаемые избыточные доходности `m = 1`. -/
def tsm : Fin na ⊕ Fin nb ⊕ Fin nc → ℝ := fun _ => 1

/-- Идиосинкратические дисперсии `d = 1`. -/
def tsd : Fin na ⊕ Fin nb ⊕ Fin nc → ℝ := fun _ => 1

lemma ts_dot_a (A : ℝ) (xa : Fin na → ℤ) (xb : Fin nb → ℤ) (xc : Fin nc → ℤ) (a : Fin na)
    (t : Fin 3 → ℝ) :
    dotp (tsB A xa xb xc (Sum.inl a)) t = A * t 0 + A * xa a * t 2 := by
  simp only [dotp, tsB, Fin.sum_univ_three]
  simp

lemma ts_dot_b (A : ℝ) (xa : Fin na → ℤ) (xb : Fin nb → ℤ) (xc : Fin nc → ℤ) (b : Fin nb)
    (t : Fin 3 → ℝ) :
    dotp (tsB A xa xb xc (Sum.inr (Sum.inl b))) t = A * t 1 + A * xb b * t 2 := by
  simp only [dotp, tsB, Fin.sum_univ_three]
  simp

lemma ts_dot_c (A : ℝ) (xa : Fin na → ℤ) (xb : Fin nb → ℤ) (xc : Fin nc → ℤ) (c : Fin nc)
    (t : Fin 3 → ℝ) :
    dotp (tsB A xa xb xc (Sum.inr (Sum.inr c))) t = -(A * t 0) - A * t 1 - A * xc c * t 2 := by
  simp only [dotp, tsB, Fin.sum_univ_three]
  simp
  ring

/-- Двойственная функция примера: `Σ_{i∈S}(⟨B_i,t⟩ − 1)² + |t|²`. -/
lemma ts_phi (A : ℝ) (xa : Fin na → ℤ) (xb : Fin nb → ℤ) (xc : Fin nc → ℤ)
    (S : Finset (Fin na ⊕ Fin nb ⊕ Fin nc))
    (t : Fin 3 → ℝ) :
    phi (rowsK tsd (tsB A xa xb xc) (opI (Fin 3))) (targetsK tsm tsd) (barK S) t
      = ∑ i ∈ S, (dotp (tsB A xa xb xc i) t - 1) ^ 2 + ∑ l, t l ^ 2 := by
  simp only [phi, barK, Finset.sum_disjSum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [rowsK, targetsK, tsd, tsm, dotp]
  · refine Finset.sum_congr rfl fun l _ => ?_
    have : dotp (rowsK tsd (tsB A xa xb xc) (opI (Fin 3)) (Sum.inr l)) t = t l := by
      simp only [rowsK, Sum.elim_inr, dotp, opI]
      rw [Finset.sum_eq_single l]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    rw [this]; simp [targetsK]

/-- Слабая двойственность для примера (веса любого знака). -/
lemma ts_wd (A : ℝ) (xa : Fin na → ℤ) (xb : Fin nb → ℤ) (xc : Fin nc → ℤ)
    (S : Finset (Fin na ⊕ Fin nb ⊕ Fin nc))
    (w : Fin na ⊕ Fin nb ⊕ Fin nc → ℝ) (t : Fin 3 → ℝ) :
    objLO tsm tsd (tsB A xa xb xc) (opI (Fin 3)) S w
      ≤ ∑ i ∈ S, (dotp (tsB A xa xb xc i) t - 1) ^ 2 + ∑ l, t l ^ 2 := by
  have h := objLO_le_phi_free (m := tsm) (d := tsd) (B := tsB A xa xb xc)
    (Sf := opI (Fin 3)) (P := opI (Fin 3)) (G := opI (Fin 3))
    (fun _ => one_pos) (opI_hG _) (opI_hPS _) S w t
  rwa [ts_phi] at h

/-- **«Да»: точный хедж.** Если `xa a + xb b = xc c`, тройка с весами `1` имеет цель `3`. -/
theorem ts_yes (A : ℝ) (xa : Fin na → ℤ) (xb : Fin nb → ℤ) (xc : Fin nc → ℤ)
    {a : Fin na} {b : Fin nb} {c : Fin nc}
    (habc : xa a + xb b = xc c) :
    objLO tsm tsd (tsB A xa xb xc) (opI (Fin 3))
      {Sum.inl a, Sum.inr (Sum.inl b), Sum.inr (Sum.inr c)} (fun _ => 1) = 3 := by
  have hV : ∀ i i', Vmat tsd (tsB A xa xb xc) (opI (Fin 3)) i i'
      = (if i = i' then 1 else 0) + ∑ j, tsB A xa xb xc i j * tsB A xa xb xc i' j := by
    intro i i'; simp only [Vmat, tsd, sum_opI_mul]
  have hc : (xc c : ℝ) = xa a + xb b := by exact_mod_cast habc.symm
  have h1 : (Sum.inl a : Fin na ⊕ Fin nb ⊕ Fin nc) ∉
      ({Sum.inr (Sum.inl b), Sum.inr (Sum.inr c)} : Finset (Fin na ⊕ Fin nb ⊕ Fin nc)) := by simp
  have h2 : (Sum.inr (Sum.inl b) : Fin na ⊕ Fin nb ⊕ Fin nc) ∉
      ({Sum.inr (Sum.inr c)} : Finset (Fin na ⊕ Fin nb ⊕ Fin nc)) := by simp
  simp only [objLO, hV, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton, tsm]
  simp [tsB, Fin.sum_univ_three, hc]
  ring

/-- Больше `3` нет: в точке `t = 0` двойственная функция равна `|S| ≤ 3`. -/
theorem ts_le_three (A : ℝ) (xa : Fin na → ℤ) (xb : Fin nb → ℤ) (xc : Fin nc → ℤ)
    {S : Finset (Fin na ⊕ Fin nb ⊕ Fin nc)} (hS : S.card ≤ 3) (w : Fin na ⊕ Fin nb ⊕ Fin nc → ℝ) :
    objLO tsm tsd (tsB A xa xb xc) (opI (Fin 3)) S w ≤ 3 := by
  have hW := ts_wd A xa xb xc S w 0
  have h0 : ∀ i, dotp (tsB A xa xb xc i) 0 = 0 := fun i => by simp [dotp]
  simp only [h0, zero_sub, neg_one_sq, Finset.sum_const, nsmul_eq_mul, mul_one, Pi.zero_apply,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hW
  have : (S.card : ℝ) ≤ 3 := by exact_mod_cast hS
  linarith

lemma sq_one_sub_le {x δ U : ℝ} (hx : |x| ≤ U) (hδ : 1 ≤ |δ|) :
    (1 - 3 * x / δ) ^ 2 ≤ (1 + 3 * U) ^ 2 := by
  have hδ0 : 0 < |δ| := by linarith
  have hq : |x / δ| ≤ |x| := by
    rw [abs_div]; exact div_le_self (abs_nonneg x) hδ
  have h3 : |3 * x / δ| ≤ 3 * U := by
    rw [mul_div_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith
  have hU : 0 ≤ U := le_trans (abs_nonneg x) hx
  have hlo : -(1 + 3 * U) ≤ 1 - 3 * x / δ := by
    have := le_abs_self (3 * x / δ); linarith
  have hhi : 1 - 3 * x / δ ≤ 1 + 3 * U := by
    have := neg_abs_le (3 * x / δ); linarith
  exact sq_le_sq' hlo hhi

/-- **«Нет»: цель мала.** Если ни одна тройка не даёт `xa a + xb b = xc c`, то у любого носителя
с не более чем тремя именами при любых весах цель не больше `(2(1 + 3U)² + 9)/A²`. -/
theorem ts_no {U A : ℝ} (hA : 0 < A) (xa : Fin na → ℤ) (xb : Fin nb → ℤ) (xc : Fin nc → ℤ)
    (hUa : ∀ a, |(xa a : ℝ)| ≤ U) (hUb : ∀ b, |(xb b : ℝ)| ≤ U)
    (hno : ∀ a b c, xa a + xb b ≠ xc c)
    {S : Finset (Fin na ⊕ Fin nb ⊕ Fin nc)} (hS : S.card ≤ 3) (w : Fin na ⊕ Fin nb ⊕ Fin nc → ℝ) :
    objLO tsm tsd (tsB A xa xb xc) (opI (Fin 3)) S w ≤ (2 * (1 + 3 * U) ^ 2 + 9) / A ^ 2 := by
  have hA0 : A ≠ 0 := hA.ne'
  have hA2 : 0 < A ^ 2 := by positivity
  have h5 : 5 / A ^ 2 ≤ (2 * (1 + 3 * U) ^ 2 + 9) / A ^ 2 :=
    div_le_div_of_nonneg_right (by nlinarith) hA2.le
  have hsq : ∀ t : Fin 3 → ℝ, ∑ l, t l ^ 2 = t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 :=
    fun t => Fin.sum_univ_three _
  by_cases hSa : ∃ a, Sum.inl a ∈ S
  · by_cases hSb : ∃ b, Sum.inr (Sum.inl b) ∈ S
    · by_cases hSc : ∃ c, Sum.inr (Sum.inr c) ∈ S
      · -- тройка `a, b, c`
        obtain ⟨a, ha⟩ := hSa
        obtain ⟨b, hb⟩ := hSb
        obtain ⟨c, hc⟩ := hSc
        have hsub : ({Sum.inl a, Sum.inr (Sum.inl b), Sum.inr (Sum.inr c)} :
            Finset (Fin na ⊕ Fin nb ⊕ Fin nc)) ⊆ S := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
        have hcard : ({Sum.inl a, Sum.inr (Sum.inl b), Sum.inr (Sum.inr c)} :
            Finset (Fin na ⊕ Fin nb ⊕ Fin nc)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp), Finset.card_pair (by simp)]
        have hSeq : S = {Sum.inl a, Sum.inr (Sum.inl b), Sum.inr (Sum.inr c)} :=
          (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
        set δ : ℝ := (xa a : ℝ) + xb b - xc c with hδ
        have hδ1 : 1 ≤ |δ| := by
          have hz : xa a + xb b - xc c ≠ 0 := sub_ne_zero.mpr (hno a b c)
          have h1 : (1 : ℤ) ≤ |xa a + xb b - xc c| := Int.one_le_abs hz
          have h2 : (1 : ℝ) ≤ |((xa a + xb b - xc c : ℤ) : ℝ)| := by exact_mod_cast h1
          rw [hδ]; push_cast at h2; exact h2
        have hδ0 : δ ≠ 0 := by
          intro h; rw [h, abs_zero] at hδ1; linarith
        set t : Fin 3 → ℝ := ![(1 - 3 * xa a / δ) / A, (1 - 3 * xb b / δ) / A, 3 / δ / A]
          with ht
        have hW := ts_wd A xa xb xc S w t
        have h1 : (Sum.inl a : Fin na ⊕ Fin nb ⊕ Fin nc) ∉
            ({Sum.inr (Sum.inl b), Sum.inr (Sum.inr c)} : Finset (Fin na ⊕ Fin nb ⊕ Fin nc)) := by
          simp
        have h2 : (Sum.inr (Sum.inl b) : Fin na ⊕ Fin nb ⊕ Fin nc) ∉
            ({Sum.inr (Sum.inr c)} : Finset (Fin na ⊕ Fin nb ⊕ Fin nc)) := by simp
        rw [hSeq, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton,
          ts_dot_a, ts_dot_b, ts_dot_c, hsq] at hW
        have e0 : t 0 = (1 - 3 * xa a / δ) / A := rfl
        have e1 : t 1 = (1 - 3 * xb b / δ) / A := rfl
        have e2 : t 2 = 3 / δ / A := rfl
        have ra : A * t 0 + A * (xa a) * t 2 - 1 = 0 := by
          rw [e0, e2]; field_simp; ring
        have rb : A * t 1 + A * (xb b) * t 2 - 1 = 0 := by
          rw [e1, e2]; field_simp; ring
        have rc : -(A * t 0) - A * t 1 - A * (xc c) * t 2 - 1 = 0 := by
          rw [e0, e1, e2]; field_simp
          have : (xc c : ℝ) = xa a + xb b - δ := by rw [hδ]; ring
          rw [this]; ring
        rw [ra, rb, rc] at hW
        have hq0 : t 0 ^ 2 ≤ (1 + 3 * U) ^ 2 / A ^ 2 := by
          rw [e0, div_pow]
          exact div_le_div_of_nonneg_right (sq_one_sub_le (hUa a) hδ1) hA2.le
        have hq1 : t 1 ^ 2 ≤ (1 + 3 * U) ^ 2 / A ^ 2 := by
          rw [e1, div_pow]
          exact div_le_div_of_nonneg_right (sq_one_sub_le (hUb b) hδ1) hA2.le
        have hq2 : t 2 ^ 2 ≤ 9 / A ^ 2 := by
          rw [e2, div_pow]
          apply div_le_div_of_nonneg_right _ hA2.le
          rw [div_pow]
          have hδ2 : 1 ≤ δ ^ 2 := by
            have := mul_le_mul hδ1 hδ1 zero_le_one (abs_nonneg δ)
            rw [abs_mul_abs_self] at this; nlinarith
          rw [div_le_iff₀ (by positivity)]; nlinarith
        rw [hSeq]
        have : (2 * (1 + 3 * U) ^ 2 + 9) / A ^ 2
            = (1 + 3 * U) ^ 2 / A ^ 2 + (1 + 3 * U) ^ 2 / A ^ 2 + 9 / A ^ 2 := by ring
        rw [this]
        nlinarith
      · -- нет актива из `C`: точка `(1, 1, 0)/A`
        simp only [not_exists] at hSc
        set t : Fin 3 → ℝ := ![1 / A, 1 / A, 0] with ht
        have hW := ts_wd A xa xb xc S w t
        have hz : ∑ i ∈ S, (dotp (tsB A xa xb xc i) t - 1) ^ 2 = 0 := by
          refine Finset.sum_eq_zero fun i hi => ?_
          rcases i with a | b | c
          · rw [ts_dot_a]; simp [ht]; field_simp; ring
          · rw [ts_dot_b]; simp [ht]; field_simp; ring
          · exact absurd hi (hSc c)
        rw [hz, zero_add, hsq] at hW
        have : t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 = 2 / A ^ 2 := by
          simp [ht]; field_simp; ring
        rw [this] at hW
        have h2 : 2 / A ^ 2 ≤ 5 / A ^ 2 := div_le_div_of_nonneg_right (by norm_num) hA2.le
        linarith
    · -- нет актива из `B`: точка `(1, −2, 0)/A`
      simp only [not_exists] at hSb
      set t : Fin 3 → ℝ := ![1 / A, -2 / A, 0] with ht
      have hW := ts_wd A xa xb xc S w t
      have hz : ∑ i ∈ S, (dotp (tsB A xa xb xc i) t - 1) ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        rcases i with a | b | c
        · rw [ts_dot_a]; simp [ht]; field_simp; ring
        · exact absurd hi (hSb b)
        · rw [ts_dot_c]; simp [ht]; field_simp; ring
      rw [hz, zero_add, hsq] at hW
      have : t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 = 5 / A ^ 2 := by
        simp [ht]; field_simp; ring
      rw [this] at hW
      linarith
  · -- нет актива из `A`: точка `(−2, 1, 0)/A`
    simp only [not_exists] at hSa
    set t : Fin 3 → ℝ := ![-2 / A, 1 / A, 0] with ht
    have hW := ts_wd A xa xb xc S w t
    have hz : ∑ i ∈ S, (dotp (tsB A xa xb xc i) t - 1) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rcases i with a | b | c
      · exact absurd hi (hSa a)
      · rw [ts_dot_b]; simp [ht]; field_simp; ring
      · rw [ts_dot_c]; simp [ht]; field_simp; ring
    rw [hz, zero_add, hsq] at hW
    have : t 0 ^ 2 + t 1 ^ 2 + t 2 ^ 2 = 5 / A ^ 2 := by
      simp [ht]; field_simp; ring
    rw [this] at hW
    linarith

/-- При `2(1 + 3U)² + 9 ≤ A²` цель «нет» не больше `1`. -/
theorem ts_no_one {U A : ℝ} (hA : 0 < A) (hA2 : 2 * (1 + 3 * U) ^ 2 + 9 ≤ A ^ 2)
    (xa : Fin na → ℤ) (xb : Fin nb → ℤ) (xc : Fin nc → ℤ)
    (hUa : ∀ a, |(xa a : ℝ)| ≤ U) (hUb : ∀ b, |(xb b : ℝ)| ≤ U)
    (hno : ∀ a b c, xa a + xb b ≠ xc c)
    {S : Finset (Fin na ⊕ Fin nb ⊕ Fin nc)} (hS : S.card ≤ 3) (w : Fin na ⊕ Fin nb ⊕ Fin nc → ℝ) :
    objLO tsm tsd (tsB A xa xb xc) (opI (Fin 3)) S w ≤ 1 := by
  have h := ts_no hA xa xb xc hUa hUb hno hS w
  have hA2' : 0 < A ^ 2 := by positivity
  have : (2 * (1 + 3 * U) ^ 2 + 9) / A ^ 2 ≤ 1 := by rw [div_le_one hA2']; exact hA2
  linarith

/-- **Приближение решает 3SUM'.** Пусть `(S, w)`, `|S| ≤ 3`, — `(1 − ε)`-приближение, `ε < 2/3`
(не хуже `1 − ε` от любого long-only портфеля с не более чем тремя именами). Тогда тройка с
`xa a + xb b = xc c` существует тогда и только тогда, когда цель `(S, w)` больше `1`. -/
theorem threesum_decide {U A ε : ℝ} (hA : 0 < A)
    (hA2 : 2 * (1 + 3 * U) ^ 2 + 9 ≤ A ^ 2) (hε : ε < 2 / 3)
    (xa : Fin na → ℤ) (xb : Fin nb → ℤ) (xc : Fin nc → ℤ)
    (hUa : ∀ a, |(xa a : ℝ)| ≤ U) (hUb : ∀ b, |(xb b : ℝ)| ≤ U)
    {S : Finset (Fin na ⊕ Fin nb ⊕ Fin nc)} (hS : S.card ≤ 3) (w : Fin na ⊕ Fin nb ⊕ Fin nc → ℝ)
    (hgood : ∀ S' : Finset (Fin na ⊕ Fin nb ⊕ Fin nc), S'.card ≤ 3 →
      ∀ w' : Fin na ⊕ Fin nb ⊕ Fin nc → ℝ,
      (∀ i, 0 ≤ w' i) →
        (1 - ε) * objLO tsm tsd (tsB A xa xb xc) (opI (Fin 3)) S' w'
          ≤ objLO tsm tsd (tsB A xa xb xc) (opI (Fin 3)) S w) :
    (∃ a b c, xa a + xb b = xc c) ↔ 1 < objLO tsm tsd (tsB A xa xb xc) (opI (Fin 3)) S w := by
  constructor
  · rintro ⟨a, b, c, habc⟩
    have hcard : ({Sum.inl a, Sum.inr (Sum.inl b), Sum.inr (Sum.inr c)} :
        Finset (Fin na ⊕ Fin nb ⊕ Fin nc)).card ≤ 3 := by
      refine (Finset.card_insert_le _ _).trans ?_
      have := Finset.card_insert_le (Sum.inr (Sum.inl b) : Fin na ⊕ Fin nb ⊕ Fin nc)
        ({Sum.inr (Sum.inr c)} : Finset (Fin na ⊕ Fin nb ⊕ Fin nc))
      rw [Finset.card_singleton] at this
      omega
    have h := hgood _ hcard (fun _ => 1) (fun _ => zero_le_one)
    rw [ts_yes A xa xb xc habc] at h
    linarith
  · intro h1
    by_contra hcon
    simp only [not_exists] at hcon
    have := ts_no_one hA hA2 xa xb xc hUa hUb hcon hS w
    linarith

/-- **То же при любом числе факторов `K ≥ 3`:** добавлены факторы `κ'` с нулевыми нагрузками. -/
theorem threesum_decide_pad (κ' : Type*) [Fintype κ'] [DecidableEq κ'] {U A ε : ℝ}
    (hA : 0 < A) (hA2 : 2 * (1 + 3 * U) ^ 2 + 9 ≤ A ^ 2) (hε : ε < 2 / 3)
    (xa : Fin na → ℤ) (xb : Fin nb → ℤ) (xc : Fin nc → ℤ)
    (hUa : ∀ a, |(xa a : ℝ)| ≤ U) (hUb : ∀ b, |(xb b : ℝ)| ≤ U)
    {S : Finset (Fin na ⊕ Fin nb ⊕ Fin nc)} (hS : S.card ≤ 3) (w : Fin na ⊕ Fin nb ⊕ Fin nc → ℝ)
    (hgood : ∀ S' : Finset (Fin na ⊕ Fin nb ⊕ Fin nc), S'.card ≤ 3 →
      ∀ w' : Fin na ⊕ Fin nb ⊕ Fin nc → ℝ,
      (∀ i, 0 ≤ w' i) →
        (1 - ε) * objLO tsm tsd (padZero (κ' := κ') (tsB A xa xb xc)) (opI (Fin 3 ⊕ κ')) S' w'
          ≤ objLO tsm tsd (padZero (κ' := κ') (tsB A xa xb xc)) (opI (Fin 3 ⊕ κ')) S w) :
    (∃ a b c, xa a + xb b = xc c) ↔
      1 < objLO tsm tsd (padZero (κ' := κ') (tsB A xa xb xc)) (opI (Fin 3 ⊕ κ')) S w := by
  simp only [objLO_padZero] at hgood ⊢
  exact threesum_decide hA hA2 hε xa xb xc hUa hUb hS w hgood

/-- **Пример.** `xa = 1`, `xb = 2`, `A = 20`, `U = 2`: при `xc = 3` тройка даёт цель `3`, при
`xc = 4` у любого носителя с не более чем тремя именами цель не больше `1`. -/
theorem threesum_instance :
    objLO tsm tsd (tsB 20 (fun _ : Fin 1 => (1 : ℤ)) (fun _ : Fin 1 => (2 : ℤ))
        (fun _ : Fin 1 => (3 : ℤ))) (opI (Fin 3))
        {Sum.inl 0, Sum.inr (Sum.inl 0), Sum.inr (Sum.inr 0)} (fun _ => 1) = 3 ∧
    ∀ S : Finset (Fin 1 ⊕ Fin 1 ⊕ Fin 1), S.card ≤ 3 → ∀ w : Fin 1 ⊕ Fin 1 ⊕ Fin 1 → ℝ,
      objLO tsm tsd (tsB 20 (fun _ : Fin 1 => (1 : ℤ)) (fun _ : Fin 1 => (2 : ℤ))
        (fun _ : Fin 1 => (4 : ℤ))) (opI (Fin 3)) S w ≤ 1 := by
  refine ⟨ts_yes 20 _ _ _ (by norm_num), fun S hS w => ?_⟩
  refine ts_no_one (U := 2) (by norm_num) (by norm_num) _ _ _
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ _ _ => by norm_num) hS w

end ThreeSum

end SparseSharpe.Factor
