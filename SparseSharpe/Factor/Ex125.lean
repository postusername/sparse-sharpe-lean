import SparseSharpe.Factor.KBridge
import SparseSharpe.Factor.Clipped

set_option linter.style.header false

/-!
# Контрпример к вопросу §12.5: спуска по подмножествам не существует

`theory_note_v5.md`, §12.5 спрашивал: если носитель оптимума `A` самосогласован,
но в своей неподвижной точке у какого-то актива запас мал
(`min_i r_i(t̂(Ā)) < θ_O`), найдётся ли подмножество `A' ⊆ A` с **малой потерей**
и **большим запасом**?

Ответ — **нет**. Инстанс: `K = 2` фактора, два актива с ортогональными
нагрузками величины `M`,

    d = (1,1),   m = (1,1),   Σ_f = I,   B = M·I .

Тогда `V = I + M²I = (1+M²)I`, оптимальный портфель `w = (1,1)/(1+M²)`,
неподвижная точка `t̂ = (M,M)/(1+M²)`, и

* `F({0,1}) = 2/(1+M²)`;
* невязка каждого актива в `t̂` равна `1/(1+M²)`, то есть
  `r_i(t̂)² = F/(2(1+M²))` — при большом `M` сколь угодно мала по сравнению с `F`,
  а значит и с любым порогом вида `θ_O² = c·ε_g·V`;
* **любое** собственное подмножество даёт ровно `F/2` или `0`.

Требуемого `A'` нет ни при каком `M`: запас можно сделать сколь угодно малым,
а цена любого уменьшения носителя остаётся половиной оптимума.

Важно: ломается **маршрут доказательства**, а не алгоритм. На этом же инстансе
LO-K′ выдаёт ровно `OPT_LO` (`code/check_lo_12_5.py`), потому что допускающий узел
существует — он просто далёк от `t̂`.
-/

namespace SparseSharpe.Factor
namespace Ex125

open Finset

/-- Единичная матрица `2×2`. -/
def Id2 : Fin 2 → Fin 2 → ℝ := fun j j' => if j = j' then 1 else 0

/-- Нагрузки: `B = M·I` — два ортогональных фактора с загрузкой `M`. -/
def Bex (M : ℝ) : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then M else 0

/-- Идиосинкразия `d = 1`. -/
def dex : Fin 2 → ℝ := fun _ => 1

/-- Альфы `m = 1`. -/
def mex : Fin 2 → ℝ := fun _ => 1

/-- Оптимальный портфель на наборе `S`: `w_i = 1/(1+M²)` при `i ∈ S`. -/
noncomputable def wex (M : ℝ) (S : Finset (Fin 2)) : Fin 2 → ℝ :=
  fun i => if i ∈ S then 1 / (1 + M ^ 2) else 0

lemma one_add_sq_pos (M : ℝ) : (0:ℝ) < 1 + M ^ 2 := by positivity

lemma hd : ∀ i, (0:ℝ) < dex i := fun _ => by norm_num [dex]

lemma hG : ∀ j j', ∑ l, Id2 l j * Id2 l j' = Id2 j j' := by
  intro j j'
  fin_cases j <;> fin_cases j' <;> simp [Id2, Fin.sum_univ_two]

lemma hPsymm : ∀ j j', Id2 j j' = Id2 j' j := by
  intro j j'
  fin_cases j <;> fin_cases j' <;> simp [Id2]

lemma hPS : ∀ j j', ∑ l, Id2 j l * Id2 l j' = if j = j' then 1 else 0 := by
  intro j j'
  fin_cases j <;> fin_cases j' <;> simp [Id2, Fin.sum_univ_two]

/-- `t̂ = Σ_f B'w` — покоординатно `M·w_j`. -/
lemma tw_eq (M : ℝ) (S : Finset (Fin 2)) (j : Fin 2) :
    tw Id2 (Bex M) S (wex M S) j = M * wex M S j := by
  simp only [tw, Bw, Id2, Bex, Fin.sum_univ_two]
  fin_cases j <;> simp [wex]

/-- Условие стационарности `V_S w = m_S`. -/
lemma hw (M : ℝ) (S : Finset (Fin 2)) :
    ∀ i ∈ S, dex i * wex M S i + dotp (Bex M i) (tw Id2 (Bex M) S (wex M S)) = mex i := by
  intro i hi
  have hpos := one_add_sq_pos M
  have hdot : dotp (Bex M i) (tw Id2 (Bex M) S (wex M S)) = M * (M * wex M S i) := by
    simp only [dotp, Bex, Fin.sum_univ_two, tw_eq]
    fin_cases i <;> simp
  rw [hdot]
  simp only [dex, mex, wex, if_pos hi]
  field_simp

/-- **Значение набора `S`: `|S|/(1+M²)`, и минимум достигается в `t̂`.** -/
theorem value (M : ℝ) (S : Finset (Fin 2)) :
    IsNormal (rowsK dex (Bex M) Id2) (targetsK mex dex) (barK S)
        (tw Id2 (Bex M) S (wex M S))
    ∧ (∀ t, phi (rowsK dex (Bex M) Id2) (targetsK mex dex) (barK S)
        (tw Id2 (Bex M) S (wex M S))
          ≤ phi (rowsK dex (Bex M) Id2) (targetsK mex dex) (barK S) t)
    ∧ phi (rowsK dex (Bex M) Id2) (targetsK mex dex) (barK S)
        (tw Id2 (Bex M) S (wex M S)) = (S.card : ℝ) / (1 + M ^ 2) := by
  obtain ⟨h1, h2, h3⟩ := factor_lemma1 (P := Id2) (Sf := Id2) hd hG hPsymm hPS (hw M S)
  refine ⟨h1, h2, ?_⟩
  rw [h3]
  have hsum : ∑ i ∈ S, mex i * wex M S i = ∑ _i ∈ S, 1 / (1 + M ^ 2) :=
    Finset.sum_congr rfl fun i hi => by simp [mex, wex, if_pos hi]
  rw [hsum, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Невязка актива в неподвижной точке равна `1/(1+M²)`.** -/
theorem res_eq (M : ℝ) {S : Finset (Fin 2)} {i : Fin 2} (hi : i ∈ S) :
    targetsK mex dex (Sum.inl i : Fin 2 ⊕ Fin 2)
        - dotp (rowsK dex (Bex M) Id2 (Sum.inl i : Fin 2 ⊕ Fin 2))
            (tw Id2 (Bex M) S (wex M S))
      = 1 / (1 + M ^ 2) := by
  have hpos := one_add_sq_pos M
  have hdot : dotp (rowsK dex (Bex M) Id2 (Sum.inl i : Fin 2 ⊕ Fin 2))
      (tw Id2 (Bex M) S (wex M S)) = M * (M * wex M S i) := by
    simp only [rowsK, Sum.elim_inl, dotp, dex, Real.sqrt_one, div_one, Bex,
      Fin.sum_univ_two, tw_eq]
    fin_cases i <;> simp
  rw [hdot]
  simp only [targetsK, Sum.elim_inl, mex, dex, Real.sqrt_one, div_one, wex, if_pos hi]
  field_simp
  ring

/-- Значение набора как `IsLeast`: минимум по `t` существует и равен `|S|/(1+M²)`. -/
theorem isLeast_value (M : ℝ) (S : Finset (Fin 2)) :
    IsLeast {v : ℝ | ∃ t, v = phi (rowsK dex (Bex M) Id2) (targetsK mex dex) (barK S) t}
      ((S.card : ℝ) / (1 + M ^ 2)) := by
  obtain ⟨-, hmin, hval⟩ := value M S
  constructor
  · exact ⟨tw Id2 (Bex M) S (wex M S), hval.symm⟩
  · rintro b ⟨t, rfl⟩
    rw [← hval]
    exact hmin t

/-- Все наборы самосогласованы: невязка каждого актива в `t̂` равна `1/(1+M²) > 0`. -/
theorem selfcons (M : ℝ) (A : Finset (Fin 2)) :
    ∀ r ∈ barK (κ := Fin 2) A, (fun r : Fin 2 ⊕ Fin 2 => r.isLeft) r →
      0 ≤ targetsK mex dex r
          - dotp (rowsK dex (Bex M) Id2 r) (tw Id2 (Bex M) A (wex M A)) := by
  have hpos := one_add_sq_pos M
  rintro (i | l) hr hc
  · have hi : i ∈ A := by simpa [barK, Finset.inl_mem_disjSum] using hr
    rw [res_eq M hi]
    positivity
  · simp at hc

/-- **Значение long-only.** `F_LO(A) = |A|/(1+M²)` — как минимум зажатой функции
`psiC`, то есть ровно то, про что спрашивает §12.5 (а не безусловное `F`). -/
theorem isLeast_LO (M : ℝ) (A : Finset (Fin 2)) :
    IsLeast {v : ℝ | ∃ t, v = psiC (rowsK dex (Bex M) Id2) (targetsK mex dex)
        (fun r => r.isLeft) (barK A) t} ((A.card : ℝ) / (1 + M ^ 2)) := by
  have h := isLeast_psiC_of_selfconsistent (value M A).1 (selfcons M A)
  rwa [(value M A).2.2] at h

/-- **Ядро отрицательного ответа.** При `2p < M²` положим `θ := 2/(1+M²)`. Тогда:

* `F_LO({0,1}) = 2/(1+M²) = OPT_LO`, `F_LO(∅) = 0`;
* у **любого** непустого `A' ⊆ {0,1}` запас каждого актива равен `1/(1+M²) < θ`,
  то есть единственный набор с запасом `≥ θ` — пустой;
* `p·θ² < OPT_LO`, то есть пустой набор теряет БОЛЬШЕ, чем `p·θ²`.

Значит `A'` с `min_{i∈A'} r_i(t̂(Ā')) ≥ θ` и `F_LO(A') ≥ F_LO(A) − p·θ²` не
существует. -/
theorem no_good_subset_of {M p : ℝ} (hM0 : 0 < M) (hM2 : 2 * p < M ^ 2) :
    IsLeast {v : ℝ | ∃ t, v = psiC (rowsK dex (Bex M) Id2) (targetsK mex dex)
        (fun r => r.isLeft) (barK (univ : Finset (Fin 2))) t} (2 / (1 + M ^ 2))
    ∧ IsLeast {v : ℝ | ∃ t, v = psiC (rowsK dex (Bex M) Id2) (targetsK mex dex)
        (fun r => r.isLeft) (barK (∅ : Finset (Fin 2))) t} 0
    ∧ (∀ A : Finset (Fin 2), ∀ i ∈ A,
        targetsK mex dex (Sum.inl i : Fin 2 ⊕ Fin 2)
          - dotp (rowsK dex (Bex M) Id2 (Sum.inl i : Fin 2 ⊕ Fin 2))
              (tw Id2 (Bex M) A (wex M A)) < 2 / (1 + M ^ 2))
    ∧ p * (2 / (1 + M ^ 2)) ^ 2 < 2 / (1 + M ^ 2) := by
  have hpos := one_add_sq_pos M
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := isLeast_LO M (univ : Finset (Fin 2))
    have hc : (((univ : Finset (Fin 2)).card : ℝ)) = 2 := by simp
    rwa [hc] at h
  · have h := isLeast_LO M (∅ : Finset (Fin 2))
    have hc : (((∅ : Finset (Fin 2)).card : ℝ)) = 0 := by simp
    rw [hc, zero_div] at h
    exact h
  · intro A i hi
    rw [res_eq M hi]
    have hinv : (0:ℝ) < (1 + M ^ 2)⁻¹ := inv_pos.mpr hpos
    have h12 := mul_lt_mul_of_pos_right (show (1:ℝ) < 2 by norm_num) hinv
    simpa [div_eq_mul_inv] using h12
  · have hd : (0:ℝ) < (1 + M ^ 2) ^ 2 := by positivity
    have hnum : 4 * p < 2 * (1 + M ^ 2) := by nlinarith
    have h1 : p * (2 / (1 + M ^ 2)) ^ 2 = (4 * p) * ((1 + M ^ 2) ^ 2)⁻¹ := by
      field_simp; ring
    have h2 : (2:ℝ) / (1 + M ^ 2) = (2 * (1 + M ^ 2)) * ((1 + M ^ 2) ^ 2)⁻¹ := by
      field_simp
    rw [h1, h2]
    exact mul_lt_mul_of_pos_right hnum (inv_pos.mpr hd)

/-- **Ответ на вопрос §12.5 — отрицательный, с правильными кванторами.**

Для **любого** множителя `p` (роль `poly(k,K)·(c₁+1)²` из §12.5) найдётся инстанс
и порог `θ > 0`, при которых искомого `A'` нет вовсе. Порог `θ` свободен, потому
что любой `θ` представим в виде `θ_O = q·√(ε_g·V)`: достаточно взять
`ε_g := θ²/(q²V)`, а условие `p·θ² < OPT_LO` как раз и означает, что такое `ε_g`
мало́ (`ε_g < 1/(p·q²)`). Порядок кванторов именно тот, что нужен для
опровержения: сначала произвольный полином, потом инстанс. -/
theorem no_good_subset (p : ℝ) :
    ∃ θ M : ℝ, 0 < θ ∧ 0 < M
      ∧ IsLeast {v : ℝ | ∃ t, v = psiC (rowsK dex (Bex M) Id2) (targetsK mex dex)
          (fun r => r.isLeft) (barK (univ : Finset (Fin 2))) t} (2 / (1 + M ^ 2))
      ∧ IsLeast {v : ℝ | ∃ t, v = psiC (rowsK dex (Bex M) Id2) (targetsK mex dex)
          (fun r => r.isLeft) (barK (∅ : Finset (Fin 2))) t} 0
      ∧ (∀ A : Finset (Fin 2), ∀ i ∈ A,
          targetsK mex dex (Sum.inl i : Fin 2 ⊕ Fin 2)
            - dotp (rowsK dex (Bex M) Id2 (Sum.inl i : Fin 2 ⊕ Fin 2))
                (tw Id2 (Bex M) A (wex M A)) < θ)
      ∧ p * θ ^ 2 < 2 / (1 + M ^ 2) := by
  have hs0 : (0:ℝ) ≤ Real.sqrt (2 * |p| + 1) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (2 * |p| + 1) ^ 2 = 2 * |p| + 1 := Real.sq_sqrt (by positivity)
  set M : ℝ := Real.sqrt (2 * |p| + 1) + 1 with hMdef
  have hM0 : 0 < M := by rw [hMdef]; linarith
  have hM2 : 2 * p < M ^ 2 := by
    have hle : p ≤ |p| := le_abs_self p
    rw [hMdef]
    nlinarith [hsq, hs0, hle]
  obtain ⟨h1, h2, h3, h4⟩ := no_good_subset_of (p := p) hM0 hM2
  exact ⟨2 / (1 + M ^ 2), M, by positivity, hM0, h1, h2, h3, h4⟩

end Ex125
end SparseSharpe.Factor
