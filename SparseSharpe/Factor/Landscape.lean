import SparseSharpe.Factor.Duality

set_option linter.style.header false

/-!
# Ландшафт трудности: Предложения 3 и 4 (один фактор)

Оба утверждения — про модель `V = D + σ²ββ'` (`K = 1`), записанную как частный
случай `K`-факторной: `κ = Unit`, `B i () = β_i`, `Σ_f = σ²`. Цель
`objLO m d B Sf S w = 2m_S'w − w'V_Sw` (`Factor/LongOnlyK.lean`) — одна и та же для
long-short (любой `w`) и long-only (`w ≥ 0`).

## Предложение 4: NP-трудность уже при `β > 0`, `m > 0`, `D = I`

Редукция от задачи о `s`-подмножестве с заданной суммой (K-SUBSET SUM:
целые `a_i > 0`, `b > 0`; есть ли `S`, `|S| = s`, `Σ_S a_i = b`). Инстанс портфеля:

    d_i = 1,  β_i = a_i,  σ² = 2,  m_i = 1 + 2b·a_i .

Всё держится на точном тождестве (`subsetSum_obj_eq`)

    2m_S'w − w'V_Sw = |S| + 2b² − Σ_{i∈S}(w_i − 1)² − 2(Σ_{i∈S} a_iw_i − b)² ,

откуда:

* `subsetSum_obj_le` — при `|S| ≤ s` цель не больше `s + 2b²` при **любом** `w`;
* `subsetSum_obj_yes` — на ответе «да» значение `s + 2b²` достигается весом
  `w = 1_S ≥ 0`, то есть и в long-only, и в long-short;
* `subsetSum_obj_le_no` — на ответе «нет» (целые данные) цель не больше
  `s + 2b² − 1/(1 + 2Σ_i a_i²)` при **любом** `|S| ≤ s` и **любом** `w`.

Разрыв `1/(1 + 2Σa_i²)` — обратный полином от **величин** чисел, а не от длины
их записи: редукция слабая, как у рюкзака, и FPTAS она не исключает
(`1/ε` порядка `Σa_i²·(s + 2b²)` различает ответы — это псевдополиномиально).
Сама NP-полнота K-SUBSET SUM и полиномиальность построения инстанса — не
предмет формализации (в Mathlib нет модели вычислений); формально доказано
математическое содержание редукции: значение задачи различает ответы.

## Предложение 3: когда префикс EGP оптимален при кардинальности

При `β > 0` положим `r_i = m_i/β_i` (доходность на единицу беты) и
`q_i = m_i/√d_i` (на единицу остаточного риска). Если набор `T` «доминирует»
остальные активы — `r_i ≥ r_j` и `q_i ≥ q_j` для всех `i ∈ T`, `j ∉ T`, — то
`F_LO(S) ≤ F_LO(T)` для любого `S` с `|S| ≤ |T|` (`egp_prefix_optimal`).
Когда ранжирования по `r` и по `q` согласованы (`(r_i − r_j)(q_i − q_j) ≥ 0`),
таким `T` является префикс длины `k` сортировки по `r` с ничьими в пользу
большего `q`; это и есть формулировка заметки (`theory_note_longonly.md`).

Доказательство: поточечное доминирование `g_i(t) ≥ g_j(t)` при `t ≥ 0`,
`g_i(t) = ((m_i − tβ_i)_+)²/d_i` (`term_dominates`), обмен
(`sum_le_sum_of_dominates`), и то, что минимум двойственной функции набора `T`
лежит при `t ≥ 0` (`min_QLO_nonneg`); сильная двойственность —
`isGreatest_objLO_isLeast_QLO` (`Factor/Duality.lean`).
-/

namespace SparseSharpe.Factor

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

/-! ### Предложение 4 -/

/-- Инстанс редукции: `m_i = 1 + 2b·a_i`. -/
def ssM (a : ι → ℝ) (b : ℝ) : ι → ℝ := fun i => 1 + 2 * b * a i

/-- `d_i = 1`. -/
def ssD : ι → ℝ := fun _ => 1

/-- `β_i = a_i` (один фактор). -/
def ssB (a : ι → ℝ) : ι → Unit → ℝ := fun i _ => a i

/-- `σ² = 2`. -/
def ssSf : Unit → Unit → ℝ := fun _ _ => 2

/-- **Тождество редукции.** -/
theorem subsetSum_obj_eq (a : ι → ℝ) (b : ℝ) (S : Finset ι) (w : ι → ℝ) :
    objLO (ssM a b) ssD (ssB a) ssSf S w
      = S.card + 2 * b ^ 2 - ∑ i ∈ S, (w i - 1) ^ 2
          - 2 * (∑ i ∈ S, a i * w i - b) ^ 2 := by
  have hV : ∀ i i', Vmat ssD (ssB a) ssSf i i' = (if i = i' then 1 else 0) + 2 * (a i * a i') := by
    intro i i'
    simp only [Vmat, ssD, ssB, ssSf, Finset.univ_unique, Finset.sum_singleton]
    ring
  have hquad : ∑ i ∈ S, ∑ i' ∈ S, Vmat ssD (ssB a) ssSf i i' * (w i * w i')
      = ∑ i ∈ S, w i ^ 2 + 2 * (∑ i ∈ S, a i * w i) ^ 2 := by
    simp only [hV, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
    have h1 : ∀ i ∈ S, (∑ i' ∈ S, if i = i' then w i * w i' else 0) = w i ^ 2 := by
      intro i hi
      rw [Finset.sum_ite_eq S i (fun i' => w i * w i')]
      simp [hi, sq]
    rw [Finset.sum_congr rfl h1, sq (∑ i ∈ S, a i * w i), Finset.sum_mul_sum,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i' _ => by ring
  have hsq : ∑ i ∈ S, (w i - 1) ^ 2 = ∑ i ∈ S, w i ^ 2 - 2 * ∑ i ∈ S, w i + S.card := by
    have : ∀ i ∈ S, (w i - 1) ^ 2 = w i ^ 2 - 2 * w i + 1 := fun i _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    simp
  have hlin : ∑ i ∈ S, ssM a b i * w i = ∑ i ∈ S, w i + 2 * b * ∑ i ∈ S, a i * w i := by
    simp only [ssM, add_mul, one_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [objLO, hquad, hlin, hsq]
  ring

/-- Цель не больше `|S| + 2b²` при любом `w`. -/
theorem subsetSum_obj_le_card (a : ι → ℝ) (b : ℝ) (S : Finset ι) (w : ι → ℝ) :
    objLO (ssM a b) ssD (ssB a) ssSf S w ≤ S.card + 2 * b ^ 2 := by
  rw [subsetSum_obj_eq]
  have h1 : 0 ≤ ∑ i ∈ S, (w i - 1) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith [sq_nonneg (∑ i ∈ S, a i * w i - b)]

/-- **Предложение 4, верхняя граница.** При `|S| ≤ s` цель не больше `s + 2b²` —
при любом `w`, так что и для long-short, и для long-only. -/
theorem subsetSum_obj_le (a : ι → ℝ) (b : ℝ) {s : ℕ} {S : Finset ι} (hS : S.card ≤ s)
    (w : ι → ℝ) :
    objLO (ssM a b) ssD (ssB a) ssSf S w ≤ s + 2 * b ^ 2 := by
  have := subsetSum_obj_le_card a b S w
  have h : (S.card : ℝ) ≤ s := by exact_mod_cast hS
  linarith

/-- **Предложение 4, ответ «да».** Если `|S| = s` и `Σ_S a_i = b`, то вес `w = 1 ≥ 0`
даёт ровно `s + 2b²`. -/
theorem subsetSum_obj_yes (a : ι → ℝ) (b : ℝ) {s : ℕ} {S : Finset ι} (hS : S.card = s)
    (hsum : ∑ i ∈ S, a i = b) :
    objLO (ssM a b) ssD (ssB a) ssSf S (fun _ => 1) = s + 2 * b ^ 2 := by
  rw [subsetSum_obj_eq]
  simp [hsum, hS]

/-- Одномерная оценка: `U + 2(x+e)² ≥ 2e²/(1+2A)` при `x² ≤ A·U`, `U, A ≥ 0`. -/
lemma gap_scalar {U A x e : ℝ} (hU : 0 ≤ U) (hA : 0 ≤ A) (hx : x ^ 2 ≤ A * U) :
    2 * e ^ 2 / (1 + 2 * A) ≤ U + 2 * (x + e) ^ 2 := by
  have h12 : 0 < 1 + 2 * A := by linarith
  rw [div_le_iff₀ h12]
  rcases hA.lt_or_eq with hA' | hA'
  · -- `A·[(1+2A)(U + 2(x+e)²) − 2e²] ≥ ((1+2A)x + 2Ae)² ≥ 0`
    have key : A * ((U + 2 * (x + e) ^ 2) * (1 + 2 * A) - 2 * e ^ 2)
        ≥ ((1 + 2 * A) * x + 2 * A * e) ^ 2 := by
      nlinarith [hx]
    have : 0 ≤ A * ((U + 2 * (x + e) ^ 2) * (1 + 2 * A) - 2 * e ^ 2) :=
      le_trans (sq_nonneg _) key
    have h3 : 0 ≤ (U + 2 * (x + e) ^ 2) * (1 + 2 * A) - 2 * e ^ 2 := by
      by_contra hneg
      push Not at hneg
      nlinarith
    linarith
  · subst hA'
    have hx0 : x = 0 := by nlinarith [sq_nonneg x]
    subst hx0
    nlinarith

/-- **Разрыв.** При любом `w`:
`Σ_S(w_i − 1)² + 2(Σ_S a_iw_i − b)² ≥ 2(Σ_S a_i − b)²/(1 + 2Σ_S a_i²)`. -/
theorem subsetSum_gap (a : ι → ℝ) (b : ℝ) (S : Finset ι) (w : ι → ℝ) :
    2 * (∑ i ∈ S, a i - b) ^ 2 / (1 + 2 * ∑ i ∈ S, a i ^ 2)
      ≤ ∑ i ∈ S, (w i - 1) ^ 2 + 2 * (∑ i ∈ S, a i * w i - b) ^ 2 := by
  set U := ∑ i ∈ S, (w i - 1) ^ 2
  set A := ∑ i ∈ S, a i ^ 2
  set x := ∑ i ∈ S, a i * (w i - 1)
  have hU : 0 ≤ U := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hx : x ^ 2 ≤ A * U := Finset.sum_mul_sq_le_sq_mul_sq S a (fun i => w i - 1)
  have hsplit : ∑ i ∈ S, a i * w i - b = x + (∑ i ∈ S, a i - b) := by
    simp only [x, mul_sub, mul_one, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  exact gap_scalar hU hA hx

/-- **Предложение 4, ответ «нет».** Пусть `a_i`, `b` целые и нет `s`-подмножества с
суммой `b`. Тогда при любом `|S| ≤ s` и любом `w`
`2m_S'w − w'V_Sw ≤ s + 2b² − 1/(1 + 2Σ_i a_i²)`. -/
theorem subsetSum_obj_le_no (a : ι → ℤ) (b : ℤ) {s : ℕ}
    (hno : ∀ S : Finset ι, S.card = s → ∑ i ∈ S, a i ≠ b)
    {S : Finset ι} (hS : S.card ≤ s) (w : ι → ℝ) :
    objLO (ssM (fun i => (a i : ℝ)) b) ssD (ssB (fun i => (a i : ℝ))) ssSf S w
      ≤ s + 2 * (b : ℝ) ^ 2 - 1 / (1 + 2 * ∑ i, ((a i : ℝ)) ^ 2) := by
  set Atot := ∑ i, ((a i : ℝ)) ^ 2
  have hAtot : 0 ≤ Atot := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hden : 0 < 1 + 2 * Atot := by linarith
  have hsmall : 1 / (1 + 2 * Atot) ≤ 2 / (1 + 2 * ∑ i ∈ S, ((a i : ℝ)) ^ 2) := by
    have hAS : ∑ i ∈ S, ((a i : ℝ)) ^ 2 ≤ Atot :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun _ _ _ => sq_nonneg _)
    have h0 : 0 ≤ ∑ i ∈ S, ((a i : ℝ)) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc 1 / (1 + 2 * Atot) ≤ 2 / (1 + 2 * Atot) := by gcongr; norm_num
      _ ≤ 2 / (1 + 2 * ∑ i ∈ S, ((a i : ℝ)) ^ 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have hle1 : 1 / (1 + 2 * Atot) ≤ 1 := by
    rw [div_le_one hden]; linarith
  rw [subsetSum_obj_eq]
  rcases (Nat.lt_or_ge S.card s) with hlt | hge
  · -- `|S| < s`: разрыв не меньше `1`
    have hc : (S.card : ℝ) + 1 ≤ s := by exact_mod_cast hlt
    have h1 : 0 ≤ ∑ i ∈ S, (w i - 1) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith [sq_nonneg (∑ i ∈ S, ((a i : ℝ)) * w i - b)]
  · have hcard : S.card = s := le_antisymm hS hge
    have hne : ∑ i ∈ S, a i ≠ b := hno S hcard
    have hint : (1 : ℝ) ≤ (∑ i ∈ S, ((a i : ℝ)) - b) ^ 2 := by
      have : (∑ i ∈ S, a i - b) ≠ 0 := sub_ne_zero.mpr hne
      have h1 : (1 : ℤ) ≤ (∑ i ∈ S, a i - b) ^ 2 := by
        have := Int.one_le_abs this
        nlinarith [sq_abs (∑ i ∈ S, a i - b)]
      have h2 : ((∑ i ∈ S, a i - b : ℤ) : ℝ) = ∑ i ∈ S, ((a i : ℝ)) - b := by push_cast; ring
      have h3 : ((1 : ℤ) : ℝ) ≤ (((∑ i ∈ S, a i - b) ^ 2 : ℤ) : ℝ) := by exact_mod_cast h1
      rw [Int.cast_pow, h2] at h3
      simpa using h3
    have hgap := subsetSum_gap (fun i => (a i : ℝ)) (b : ℝ) S w
    have hAS0 : 0 ≤ ∑ i ∈ S, ((a i : ℝ)) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hge2 : 2 / (1 + 2 * ∑ i ∈ S, ((a i : ℝ)) ^ 2)
        ≤ 2 * (∑ i ∈ S, ((a i : ℝ)) - b) ^ 2 / (1 + 2 * ∑ i ∈ S, ((a i : ℝ)) ^ 2) := by
      apply div_le_div_of_nonneg_right (by linarith) (by linarith)
    have hc : (S.card : ℝ) = s := by exact_mod_cast hcard
    linarith

/-- **Предложение 4 одним утверждением** (целые данные): значение `s + 2b²`
достигается на `|S| ≤ s` неотрицательным весом тогда и только тогда, когда
у K-SUBSET SUM ответ «да»; и никакой вес (любого знака) его не превосходит. -/
theorem subsetSum_reduction (a : ι → ℤ) (b : ℤ) (s : ℕ) :
    (∀ S : Finset ι, S.card ≤ s → ∀ w : ι → ℝ,
        objLO (ssM (fun i => (a i : ℝ)) b) ssD (ssB (fun i => (a i : ℝ))) ssSf S w
          ≤ s + 2 * (b : ℝ) ^ 2) ∧
    ((∃ S : Finset ι, S.card ≤ s ∧ ∃ w : ι → ℝ, (∀ i ∈ S, 0 ≤ w i) ∧
        objLO (ssM (fun i => (a i : ℝ)) b) ssD (ssB (fun i => (a i : ℝ))) ssSf S w
          = s + 2 * (b : ℝ) ^ 2)
      ↔ ∃ S : Finset ι, S.card = s ∧ ∑ i ∈ S, a i = b) := by
  refine ⟨fun S hS w => subsetSum_obj_le _ _ hS w, ⟨?_, ?_⟩⟩
  · rintro ⟨S, hS, w, -, hval⟩
    by_contra hno
    push Not at hno
    have := subsetSum_obj_le_no a b hno hS w
    have hpos : 0 < 1 / (1 + 2 * ∑ i, ((a i : ℝ)) ^ 2) := by
      have : 0 ≤ ∑ i, ((a i : ℝ)) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      positivity
    linarith
  · rintro ⟨S, hS, hsum⟩
    refine ⟨S, hS.le, fun _ => 1, fun _ _ => zero_le_one, ?_⟩
    have := subsetSum_obj_yes (fun i => (a i : ℝ)) (b : ℝ) hS (by exact_mod_cast hsum)
    simpa using this

/-- Инстанс редукции лежит в классе Предложения 4: при `a > 0`, `b > 0` беты и
доходности положительны, `D = I`. -/
lemma subsetSum_instance_pos {a : ι → ℝ} {b : ℝ} (ha : ∀ i, 0 < a i) (hb : 0 < b) (i : ι) :
    0 < ssM a b i ∧ 0 < ssB a i () ∧ ssD i = (1 : ℝ) := by
  refine ⟨?_, ha i, rfl⟩
  simp only [ssM]
  have := ha i
  positivity

/-- Пример: `a = (1, 2, 3)`, `b = 5`, `s = 2` — ответ «да» (`{2, 3}`), значение
`2 + 2·25 = 52` достигается. -/
example : objLO (ssM (fun i : Fin 3 => ((i : ℕ) + 1 : ℝ)) 5) ssD
    (ssB (fun i : Fin 3 => ((i : ℕ) + 1 : ℝ))) ssSf {1, 2} (fun _ => 1) = 2 + 2 * 5 ^ 2 := by
  have h := subsetSum_obj_yes (fun i : Fin 3 => ((i : ℕ) + 1 : ℝ)) 5 (s := 2)
    (S := {1, 2}) (by decide) (by simp [Finset.sum_insert]; norm_num)
  simpa using h

/-! ### Предложение 3 -/

/-- **Поточечное доминирование.** Если `β_i, β_j > 0`, `r_j ≤ r_i` и `q_j ≤ q_i`, то
`((m_j − tβ_j)_+)²/d_j ≤ ((m_i − tβ_i)_+)²/d_i` при всех `t ≥ 0`. -/
theorem term_dominates {mi mj bi bj di dj t : ℝ} (hbi : 0 < bi) (hbj : 0 < bj)
    (hdi : 0 < di) (hdj : 0 < dj)
    (hr : mj / bj ≤ mi / bi) (hq : mj / Real.sqrt dj ≤ mi / Real.sqrt di) (ht : 0 ≤ t) :
    (max (mj - t * bj) 0) ^ 2 / dj ≤ (max (mi - t * bi) 0) ^ 2 / di := by
  rcases le_or_gt (mj - t * bj) 0 with hj | hj
  · rw [max_eq_right hj]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
    positivity
  · set si := Real.sqrt di with hsi
    set sj := Real.sqrt dj with hsj
    have hsipos : 0 < si := Real.sqrt_pos.mpr hdi
    have hsjpos : 0 < sj := Real.sqrt_pos.mpr hdj
    have hsi2 : si ^ 2 = di := Real.sq_sqrt hdi.le
    have hsj2 : sj ^ 2 = dj := Real.sq_sqrt hdj.le
    set rj := mj / bj with hrj
    have hmj : mj = rj * bj := by rw [hrj]; field_simp
    -- `0 ≤ t < r_j`
    have htr : t < rj := by
      have : t * bj < rj * bj := by rw [← hmj]; linarith
      exact lt_of_mul_lt_mul_right this hbj.le
    -- `m_i − β_i r_j ≥ 0`
    have hir : 0 ≤ mi - bi * rj := by
      have h1 : rj * bi ≤ mi := by
        have := mul_le_mul_of_nonneg_right hr hbi.le
        rwa [div_mul_cancel₀ _ hbi.ne'] at this
      linarith
    -- `m_j/s_j ≤ m_i/s_i` в виде `m_j·s_i ≤ m_i·s_j`
    have hq' : mj * si ≤ mi * sj := by
      rw [div_le_div_iff₀ hsjpos hsipos] at hq; linarith
    -- главное: `(m_j − tβ_j)·s_i ≤ (m_i − tβ_i)·s_j`
    have hmain : (mj - t * bj) * si ≤ (mi - t * bi) * sj := by
      have hrpos : 0 < rj := lt_of_le_of_lt ht htr
      -- `r_j·[(m_i − tβ_i)s_j − (m_j − tβ_j)s_i] = (r_j − t)(m_i s_j − m_j s_i) + t·s_j(m_i − β_i r_j)`
      have hid : rj * ((mi - t * bi) * sj - (mj - t * bj) * si)
          = (rj - t) * (mi * sj - mj * si) + t * sj * (mi - bi * rj) := by
        rw [hmj]; ring
      have h1 : 0 ≤ (rj - t) * (mi * sj - mj * si) :=
        mul_nonneg (by linarith) (by linarith)
      have h2 : 0 ≤ t * sj * (mi - bi * rj) := by positivity
      have h3 : 0 ≤ rj * ((mi - t * bi) * sj - (mj - t * bj) * si) := by rw [hid]; linarith
      have h4 : 0 ≤ (mi - t * bi) * sj - (mj - t * bj) * si := by
        by_contra hc; push Not at hc; nlinarith
      linarith
    have hipos : 0 < mi - t * bi := by
      have : 0 < (mj - t * bj) * si := mul_pos hj hsipos
      have : 0 < (mi - t * bi) * sj := lt_of_lt_of_le this hmain
      exact pos_of_mul_pos_left this hsjpos.le
    rw [max_eq_left hj.le, max_eq_left hipos.le, ← hsi2, ← hsj2,
      div_le_div_iff₀ (by positivity) (by positivity)]
    -- `(x_j s_i)² ≤ (x_i s_j)²`
    have h0 : 0 ≤ (mj - t * bj) * si := by positivity
    have := pow_le_pow_left₀ h0 hmain 2
    nlinarith [this]

/-- **Обмен.** Если каждый элемент `T` не хуже каждого элемента вне `T`, а `g ≥ 0`, то
сумма по любому `S` с `|S| ≤ |T|` не больше суммы по `T`. -/
theorem sum_le_sum_of_dominates {g : ι → ℝ} (hg : ∀ i, 0 ≤ g i) {S T : Finset ι}
    (hcard : S.card ≤ T.card) (hdom : ∀ i ∈ T, ∀ j ∉ T, g j ≤ g i) :
    ∑ i ∈ S, g i ≤ ∑ i ∈ T, g i := by
  have hS := Finset.sum_sdiff (s₁ := S ∩ T) (s₂ := S) (f := g) Finset.inter_subset_left
  have hT := Finset.sum_sdiff (s₁ := S ∩ T) (s₂ := T) (f := g) Finset.inter_subset_right
  have hc : (S \ (S ∩ T)).card ≤ (T \ (S ∩ T)).card := by
    rw [Finset.card_sdiff_of_subset Finset.inter_subset_left,
      Finset.card_sdiff_of_subset Finset.inter_subset_right]
    omega
  have hkey : ∑ i ∈ S \ (S ∩ T), g i ≤ ∑ i ∈ T \ (S ∩ T), g i := by
    rcases (T \ (S ∩ T)).eq_empty_or_nonempty with hE | hNE
    · rw [hE, Finset.card_empty, Nat.le_zero, Finset.card_eq_zero] at hc
      rw [hc, hE]
    · obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image _ g hNE
      have hi₀T : i₀ ∈ T := (Finset.mem_sdiff.mp hi₀).1
      have h1 : ∑ i ∈ S \ (S ∩ T), g i ≤ (S \ (S ∩ T)).card • g i₀ := by
        refine Finset.sum_le_card_nsmul _ _ _ fun j hj => ?_
        have hjT : j ∉ T := by
          intro hjT
          have := Finset.mem_sdiff.mp hj
          exact this.2 (Finset.mem_inter.mpr ⟨this.1, hjT⟩)
        exact hdom i₀ hi₀T j hjT
      have h2 : (T \ (S ∩ T)).card • g i₀ ≤ ∑ i ∈ T \ (S ∩ T), g i :=
        Finset.card_nsmul_le_sum _ _ _ fun i hi => hmin i hi
      have h3 : (S \ (S ∩ T)).card • g i₀ ≤ (T \ (S ∩ T)).card • g i₀ := by
        simp only [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hg i₀)
      linarith
  linarith

/-- Один фактор как `K`-факторная модель: `B i () = β_i`. -/
def oneB (β : ι → ℝ) : ι → Unit → ℝ := fun i _ => β i

/-- При `β ≥ 0` минимум двойственной функции лежит при `t ≥ 0`: в `t < 0` каждая
положительная часть не меньше, чем в `0`, а `t'Σ_f⁻¹t > 0`. -/
theorem min_QLO_nonneg {m d β : ι → ℝ} {P : Unit → Unit → ℝ} {S : Finset ι}
    (hd : ∀ i, 0 < d i) (hβ : ∀ i, 0 ≤ β i) (hP : 0 < P () ())
    {t₀ : Unit → ℝ} (hmin : ∀ t, QLO m d (oneB β) P S t₀ ≤ QLO m d (oneB β) P S t) :
    0 ≤ t₀ () := by
  by_contra hneg
  push Not at hneg
  have h0 := hmin (fun _ => 0)
  have hterm : ∀ i ∈ S, (max (m i - dotp (oneB β i) (fun _ => (0:ℝ))) 0) ^ 2 / d i
      ≤ (max (m i - dotp (oneB β i) t₀) 0) ^ 2 / d i := by
    intro i _
    have hdot0 : dotp (oneB β i) (fun _ => (0:ℝ)) = 0 := by simp [dotp]
    have hdot : dotp (oneB β i) t₀ = β i * t₀ () := by simp [dotp, oneB]
    rw [hdot0, hdot]
    have hle : m i - 0 ≤ m i - β i * t₀ () := by nlinarith [hβ i]
    have hmx : max (m i - 0) 0 ≤ max (m i - β i * t₀ ()) 0 := max_le_max hle le_rfl
    have hnn : 0 ≤ max (m i - 0) 0 := le_max_right _ _
    gcongr
    · exact (hd i).le
  have hsum := Finset.sum_le_sum hterm
  have hq0 : quadf P (fun _ => (0:ℝ)) = 0 := by simp [quadf]
  have hq : 0 < quadf P t₀ := by
    simp only [quadf, Finset.univ_unique, Finset.sum_singleton]
    have : 0 < t₀ () * t₀ () := mul_pos_of_neg_of_neg hneg hneg
    positivity
  simp only [QLO] at h0
  rw [hq0] at h0
  linarith

/-- **Предложение 3.** Один фактор, `β > 0`, `d > 0`, `Σ_f = G'G`-представление
(`hG`, `hPS`). Пусть `T` доминирует остальные активы: `r_j ≤ r_i` и `q_j ≤ q_i` для
`i ∈ T`, `j ∉ T` (`r = m/β`, `q = m/√d`). Тогда оптимальный long-only портфель на `T`
не хуже **любого** long-only портфеля на **любом** носителе `S` с `|S| ≤ |T|`. -/
theorem egp_prefix_optimal {m d β : ι → ℝ} {Sf P G : Unit → Unit → ℝ}
    (hd : ∀ i, 0 < d i) (hβ : ∀ i, 0 < β i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {T : Finset ι}
    (hdom : ∀ i ∈ T, ∀ j ∉ T, m j / β j ≤ m i / β i ∧
      m j / Real.sqrt (d j) ≤ m i / Real.sqrt (d i)) :
    ∃ wT : ι → ℝ, (∀ i ∈ T, 0 ≤ wT i) ∧
      ∀ S : Finset ι, S.card ≤ T.card → ∀ w : ι → ℝ, (∀ i ∈ S, 0 ≤ w i) →
        objLO m d (oneB β) Sf S w ≤ objLO m d (oneB β) Sf T wT := by
  obtain ⟨z, ⟨⟨t₀, hz⟩, hleast⟩, ⟨⟨wT, hwT, hwz⟩, -⟩⟩ :=
    isGreatest_objLO_isLeast_QLO (m := m) (B := oneB β) (Sf := Sf) (G := G) hd hG hPS T
  have hmin : ∀ t, QLO m d (oneB β) P T t₀ ≤ QLO m d (oneB β) P T t := by
    intro t; rw [← hz]; exact hleast ⟨t, rfl⟩
  have hP : 0 < P () () := by
    have h1 := hG () ()
    have h2 := hPS () ()
    simp only [Finset.univ_unique, Finset.sum_singleton, ite_true] at h1 h2
    have hne : P () () ≠ 0 := by intro h; rw [h, zero_mul] at h2; exact zero_ne_one h2
    rcases lt_or_gt_of_ne hne with h | h
    · nlinarith [sq_nonneg (G () ())]
    · exact h
  have ht₀ := min_QLO_nonneg hd (fun i => (hβ i).le) hP hmin
  refine ⟨wT, hwT, fun S hS w hw => ?_⟩
  have hweak := objLO_le_QLO (m := m) (B := oneB β) (S := S) hd hG hPS hw t₀
  have hdotp : ∀ i, dotp (oneB β i) t₀ = t₀ () * β i := by
    intro i; simp [dotp, oneB, mul_comm]
  have hcmp : QLO m d (oneB β) P S t₀ ≤ QLO m d (oneB β) P T t₀ := by
    simp only [QLO, hdotp]
    have := sum_le_sum_of_dominates (g := fun i => (max (m i - t₀ () * β i) 0) ^ 2 / d i)
      (fun i => by have := hd i; positivity) hS
      (fun i hi j hj => term_dominates (hβ i) (hβ j) (hd i) (hd j)
        (hdom i hi j hj).1 (hdom i hi j hj).2 ht₀)
    linarith
  rw [← hwz, hz]
  linarith

/-- Пример непустоты Предложения 3: два актива, `m = (2, 1)`, `β = (1, 1)`, `d = (1, 1)`;
`T = {0}` доминирует (`r = q = (2, 1)`), так что гипотеза `hdom` выполнима. -/
example : ∀ i ∈ ({0} : Finset (Fin 2)), ∀ j ∉ ({0} : Finset (Fin 2)),
    (![2, 1] : Fin 2 → ℝ) j / (![1, 1] : Fin 2 → ℝ) j
        ≤ (![2, 1] : Fin 2 → ℝ) i / (![1, 1] : Fin 2 → ℝ) i ∧
      (![2, 1] : Fin 2 → ℝ) j / Real.sqrt ((![1, 1] : Fin 2 → ℝ) j)
        ≤ (![2, 1] : Fin 2 → ℝ) i / Real.sqrt ((![1, 1] : Fin 2 → ℝ) i) := by
  intro i hi j hj
  simp only [Finset.mem_singleton] at hi hj
  subst hi
  fin_cases j
  · exact absurd rfl hj
  · norm_num

/-- **Контроль: без условия на `q` префикс по `r` не оптимален.** `k = 1`, `σ² = 1`,
`m = (1, 1)`, `β = (1/10, 1)`, `d = (100, 1/100)`: у актива `0` больше `r` (`10` против
`1`), но меньше `q` (`1/10` против `10`). Любой портфель на `{0}` даёт не больше `1/50`,
а портфель `w = 1` на `{1}` — `99/100`. -/
theorem egp_prefix_fails_without_q :
    (∀ w : Fin 2 → ℝ, objLO ![1, 1] ![100, 1/100] (oneB ![1/10, 1]) (fun _ _ => 1)
        {0} w ≤ 1 / 50) ∧
    objLO ![1, 1] ![100, 1/100] (oneB ![1/10, 1]) (fun _ _ => 1) {1} (fun _ => 1)
        = 99 / 100 := by
  constructor
  · intro w
    simp only [objLO, Vmat, oneB, Finset.sum_singleton, Finset.univ_unique]
    norm_num
    nlinarith [sq_nonneg (w 0 - 1 / 100)]
  · simp only [objLO, Vmat, oneB, Finset.sum_singleton, Finset.univ_unique]
    norm_num

/-! ### C.3: условие близости Вёгингера не выполнено

В рамке DP-benevolent (Woeginger 2000, условие C.3 — по пересказам Schieber и др. и
Doerr и др.; см. `litcheck_v20.md`) значение `G` должно меняться не более чем в `Δ^g`
раз, когда состояния покоординатно `Δ`-близки. Наша цель как функция состояния —
`G(A, κ, C) = C − A²/κ` (`Fval`); у **допустимых** состояний (`κ > 0`, `Cκ ≥ A²` —
неравенство Коши–Буняковского, которому удовлетворяет всякий носитель) она
неотрицательна. Условие ломается и на допустимых состояниях: при любом `Δ > 1` есть
покоординатно `Δ`-близкие допустимые состояния со значениями `0` и `(Δ − 1)/2 > 0`,
а мультипликативное сравнение с нулём невозможно. Поэтому общая теорема Вёгингера
неприменима буквально; FPTAS здесь строится иначе — аддитивным округлением моментов
в координатах, согласованных с геометрией узла (невязки `K`-ки), а не
мультипликативным огрублением состояния. -/

/-- Значение как функция состояния `(A, κ, C)`. -/
noncomputable def stateVal (A κ C : ℝ) : ℝ := C - A ^ 2 / κ

/-- Допустимое состояние: `κ > 0` и `Cκ ≥ A²` (так устроено состояние всякого
носителя: `F = C − A²/κ ≥ 0`). -/
def StateFeasible (A κ C : ℝ) : Prop := 0 < κ ∧ A ^ 2 ≤ C * κ

lemma stateVal_nonneg {A κ C : ℝ} (h : StateFeasible A κ C) : 0 ≤ stateVal A κ C := by
  obtain ⟨hκ, hAC⟩ := h
  simp only [stateVal, sub_nonneg]
  rw [div_le_iff₀ hκ]; exact hAC

/-- **Нарушение близости на допустимых состояниях.** При любом `Δ > 1` состояния
`(1, 1, C)` и `(1, 1, 1)` с `C = (1 + Δ)/2` допустимы, покоординатно `Δ`-близки
(`1 ≤ C ≤ Δ·1`), но значение первого `(Δ − 1)/2 > 0`, а второго — `0`: никакое
неравенство вида `G(s') ≥ Δ^{−g}·G(s)` не выполняется. -/
theorem stateVal_not_close {Δ : ℝ} (hΔ : 1 < Δ) :
    ∃ C : ℝ, StateFeasible 1 1 C ∧ StateFeasible 1 1 1 ∧ 1 ≤ C ∧ C ≤ Δ * 1 ∧
      0 < stateVal 1 1 C ∧ stateVal 1 1 1 = 0 := by
  refine ⟨(1 + Δ) / 2, ⟨one_pos, ?_⟩, ⟨one_pos, by norm_num⟩, ?_, ?_, ?_, ?_⟩
  · norm_num; linarith
  · linarith
  · linarith
  · simp only [stateVal]; norm_num; linarith
  · simp [stateVal]

end SparseSharpe.Factor
