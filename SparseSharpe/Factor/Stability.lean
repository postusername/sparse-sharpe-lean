import SparseSharpe.Factor.Reduction

set_option linter.style.header false

/-!
# Теорема W: устойчивость long-only при почти-самосогласованности

Теорема X (`Reduction.lean`) сводит long-only к безусловной задаче на
самосогласованных подмножествах, а `isLeast_psiC_of_selfconsistent` даёт точное
равенство `F_LO(S) = F(S)` при **точной** самосогласованности `r_i(t̂) ≥ 0`.
Динамика §4 проверяет знак не в неподвижной точке, а в узле сетки, поэтому она
может допустить набор, у которого невязки в `t̂` лишь **почти** неотрицательны:
`r_i(t̂) ≥ −θ`. Вопрос: насколько при этом `F_LO(S)` может провалиться под `F(S)`?

Ответ (`psiC_ge_of_slack`): зазор не больше `|S|θ² + 2θ√(|S|·gram_S(t−t̂))`,
а после исключения `t` через якорные строки (`psiC_ge_of_slack_anchor`)

    F_LO(S)  ≥  F(S) − |S|θ² − 4θ√(|S|·F(S)/γ),

где `γ` — **параметр обусловленности якоря**: любое число с
`γ·gram_S(v) ≤ gram_anch(v)` при всех `v`. Точное (наибольшее возможное) `γ` —
это наименьшее обобщённое собственное число пары `(Σ_f⁻¹, Κ(S̄))`; грубая, но
годная оценка снизу — `λ_min(Σ_f⁻¹)/λ_max(Κ(S̄))`. Так как якорные строки
входят в `S̄`, всегда можно считать `γ ≤ 1`. Следствие
`psiC_ge_one_sub_eps`: при `64|S|θ² ≤ ε²γF`, то есть при разрешении сетки

    θ  ≤  ε·√(γ·F) / (8·√|S|),

получаем `F_LO(S) ≥ (1−ε)·F(S)`. Это и есть калибровка узловой сетки для
long-only при `K ≥ 2`: она свободна от абсолютных масштабов входа (всё
выражено через само `F` и безразмерное `γ`). Сколько узлов этому отвечает —
считается не здесь, а в `Factor/GridFilter.lean`: там номера узлов ограничены
величиной `16|S̄|K/(ε√γ) + ½`, то есть узлов порядка `(32|S̄|K/(ε√γ))^K`.

Зависимость от `γ` не техническая: инстанс `Sticky.lean` (§4.4 заметки) —
это ровно `Σ_f = N⁴`, то есть `γ ≍ N^{-4}`, и там вытеснивший набор имеет
`F_LO(R) ≤ N^{-2}` при `F(R) ≈ 1`, хотя знаковый фильтр в узле пройден:
узел отстоит от неподвижной точки на `≍ 1/N ≫ ε√γ/√k ≍ ε/N²`, то есть
условие теоремы W нарушено ровно в том месте, где ломается алгоритм.
Вместе с Теоремой V (`Rotation.lean`) картина такая: моментный ключ в принципе
не различает `F_LO`, но при `θ ≲ ε√(γF)/√k` различать и не нужно — любой
сосед по корзине, прошедший знаковый фильтр, уже почти самосогласован.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype κ]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {cl : ι → Bool} {S : Finset ι} {t th : κ → ℝ}
variable {θ γ ε : ℝ}

/-! ### Вспомогательные неравенства -/

/-- Коши–Буняковский с единицами: `Σ|f| ≤ √(|S|·Σf²)`. -/
lemma sum_abs_le_sqrt_card_mul (S : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ S, |f i| ≤ Real.sqrt (S.card * ∑ i ∈ S, (f i) ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun i => |f i|)
  have hone : ∑ _i ∈ S, (1:ℝ) ^ 2 = (S.card : ℝ) := by
    simp
  have habs : ∀ i, (|f i|) ^ 2 = (f i) ^ 2 := fun i => sq_abs (f i)
  have hprod : ∑ i ∈ S, (1:ℝ) * |f i| = ∑ i ∈ S, |f i| := by
    exact Finset.sum_congr rfl fun i _ => one_mul _
  rw [hprod, hone] at hcs
  simp only [habs] at hcs
  have hnn : 0 ≤ ∑ i ∈ S, |f i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc ∑ i ∈ S, |f i| = Real.sqrt ((∑ i ∈ S, |f i|) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((S.card : ℝ) * ∑ i ∈ S, (f i) ^ 2) := Real.sqrt_le_sqrt hcs

/-- Параллелограмм: `gram(u − v) ≤ 2gram(u) + 2gram(v)`. -/
lemma gram_sub_le (a : ι → κ → ℝ) (S : Finset ι) (u v : κ → ℝ) :
    gram a S (u - v) ≤ 2 * gram a S u + 2 * gram a S v := by
  simp only [gram, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [dotp_sub]
  nlinarith [sq_nonneg (dotp (a i) u + dotp (a i) v)]

/-! ### Оценка зазора при зазоре знака `θ` -/

/-- **Потеря от зажатия при почти-самосогласованности.**
Если в неподвижной точке все зажатые невязки не меньше `−θ`, то в любой точке `t`

    φ_S(t) − ψ_S(t) ≤ |S|θ² + 2θ√(|S|·gram_S(t−t̂)) + gram_S(t−t̂). -/
theorem phi_sub_psiC_le_of_slack (hθ : 0 ≤ θ)
    (hslack : ∀ i ∈ S, cl i → -θ ≤ y i - dotp (a i) th) (t : κ → ℝ) :
    phi a y S t - psiC a y cl S t
      ≤ (S.card : ℝ) * θ ^ 2 + 2 * θ * Real.sqrt ((S.card : ℝ) * gram a S (t - th))
        + gram a S (t - th) := by
  have hitem : ∀ i ∈ S, (dotp (a i) t - y i) ^ 2 - resC a y cl i t ^ 2
      ≤ θ ^ 2 + 2 * θ * |dotp (a i) (t - th)| + dotp (a i) (t - th) ^ 2 := by
    intro i hi
    have habs : 0 ≤ |dotp (a i) (t - th)| := abs_nonneg _
    by_cases hc : cl i
    · simp only [resC, hc, ite_true]
      rcases le_or_gt 0 (y i - dotp (a i) t) with hx | hx
      · rw [max_eq_left hx]; nlinarith
      · rw [max_eq_right hx.le]
        have hsl := hslack i hi hc
        have hd : dotp (a i) (t - th) = dotp (a i) t - dotp (a i) th := dotp_sub _ _ _
        have hle : dotp (a i) t - dotp (a i) th ≤ |dotp (a i) (t - th)| := by
          rw [← hd]; exact le_abs_self _
        have hbound : -(y i - dotp (a i) t) ≤ θ + |dotp (a i) (t - th)| := by
          linarith
        nlinarith
    · simp only [resC, hc, ite_false, Bool.false_eq_true]
      nlinarith
  have hsum : ∑ i ∈ S, ((dotp (a i) t - y i) ^ 2 - resC a y cl i t ^ 2)
      ≤ ∑ i ∈ S, (θ ^ 2 + 2 * θ * |dotp (a i) (t - th)| + dotp (a i) (t - th) ^ 2) :=
    Finset.sum_le_sum hitem
  have hrhs : ∑ i ∈ S, (θ ^ 2 + 2 * θ * |dotp (a i) (t - th)| + dotp (a i) (t - th) ^ 2)
      = (S.card : ℝ) * θ ^ 2 + 2 * θ * (∑ i ∈ S, |dotp (a i) (t - th)|)
        + gram a S (t - th) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, gram, Finset.mul_sum]
  have hcs : ∑ i ∈ S, |dotp (a i) (t - th)|
      ≤ Real.sqrt ((S.card : ℝ) * gram a S (t - th)) := by
    simpa [gram] using sum_abs_le_sqrt_card_mul S (fun i => dotp (a i) (t - th))
  have hlhs : phi a y S t - psiC a y cl S t
      = ∑ i ∈ S, ((dotp (a i) t - y i) ^ 2 - resC a y cl i t ^ 2) := by
    simp only [phi, psiC, Finset.sum_sub_distrib]
  have hfin : 2 * θ * (∑ i ∈ S, |dotp (a i) (t - th)|)
      ≤ 2 * θ * Real.sqrt ((S.card : ℝ) * gram a S (t - th)) :=
    mul_le_mul_of_nonneg_left hcs (by linarith)
  rw [hlhs]
  calc ∑ i ∈ S, ((dotp (a i) t - y i) ^ 2 - resC a y cl i t ^ 2)
      ≤ ∑ i ∈ S, (θ ^ 2 + 2 * θ * |dotp (a i) (t - th)| + dotp (a i) (t - th) ^ 2) := hsum
    _ = (S.card : ℝ) * θ ^ 2 + 2 * θ * (∑ i ∈ S, |dotp (a i) (t - th)|)
          + gram a S (t - th) := hrhs
    _ ≤ (S.card : ℝ) * θ ^ 2 + 2 * θ * Real.sqrt ((S.card : ℝ) * gram a S (t - th))
          + gram a S (t - th) := by linarith

/-- **Теорема W (локальная форма).** При `r_i(t̂) ≥ −θ` значение зажатой задачи
в любой точке `t` не ниже `F(S)` минус `|S|θ² + 2θ√(|S|·gram_S(t−t̂))`. -/
theorem psiC_ge_of_slack (hnormal : IsNormal a y S th) (hθ : 0 ≤ θ)
    (hslack : ∀ i ∈ S, cl i → -θ ≤ y i - dotp (a i) th) (t : κ → ℝ) :
    phi a y S th
        - ((S.card : ℝ) * θ ^ 2 + 2 * θ * Real.sqrt ((S.card : ℝ) * gram a S (t - th)))
      ≤ psiC a y cl S t := by
  have hpyth : phi a y S t = phi a y S th + gram a S (t - th) := phi_eq_add hnormal t
  have hgap := phi_sub_psiC_le_of_slack (a := a) (y := y) (cl := cl) (S := S) (th := th) hθ
    hslack t
  linarith

/-! ### Якорные строки: исключение точки `t` -/

/-- Незажатые (якорные) строки набора. -/
def anchorSet (cl : ι → Bool) (S : Finset ι) : Finset ι := S.filter (fun i => ¬ cl i)

lemma anchorSet_subset : anchorSet cl S ⊆ S := Finset.filter_subset _ _

/-- На якорных строках `y = 0`, поэтому их вклад в `ψ_S(t)` — это `gram_anch(t)`. -/
lemma gram_anchor_le_psiC (hanch : ∀ i ∈ S, ¬ cl i → y i = 0) (t : κ → ℝ) :
    gram a (anchorSet cl S) t ≤ psiC a y cl S t := by
  have heq : gram a (anchorSet cl S) t = ∑ i ∈ anchorSet cl S, resC a y cl i t ^ 2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiS : i ∈ S := anchorSet_subset hi
    have hc : ¬ cl i := by
      have := Finset.mem_filter.mp hi
      simpa [anchorSet] using this.2
    have hy : y i = 0 := hanch i hiS hc
    simp only [resC, hc, ite_false, Bool.false_eq_true, hy]
    ring
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg anchorSet_subset fun _ _ _ => sq_nonneg _

/-- **Ограничение на сдвиг.** Если в точке `t` зажатое значение не выше `F(S)`,
то `gram_S(t−t̂) ≤ 4F(S)/γ`: дальше якорь не пускает. -/
theorem gram_sub_le_of_anchor (hγ : 0 < γ)
    (hanch : ∀ i ∈ S, ¬ cl i → y i = 0)
    (hcond : ∀ v : κ → ℝ, γ * gram a S v ≤ gram a (anchorSet cl S) v)
    (ht : psiC a y cl S t ≤ phi a y S th) :
    gram a S (t - th) ≤ 4 * phi a y S th / γ := by
  have h1 : γ * gram a S t ≤ phi a y S th :=
    le_trans (le_trans (hcond t) (gram_anchor_le_psiC hanch t)) ht
  have h2 : γ * gram a S th ≤ phi a y S th := by
    refine le_trans (le_trans (hcond th) (gram_anchor_le_psiC hanch th)) ?_
    exact psiC_le_phi a y cl S th
  have h3 := gram_sub_le a S t th
  rw [le_div_iff₀ hγ]
  nlinarith

/-- **Теорема W.** Long-only на почти-самосогласованном наборе:

    F_LO(S)  ≥  F(S) − |S|θ² − 4θ√(|S|·F(S)/γ).

`γ` — параметр обусловленности якоря, `θ` — допуск знакового фильтра. -/
theorem psiC_ge_of_slack_anchor (hnormal : IsNormal a y S th) (hθ : 0 ≤ θ) (hγ : 0 < γ)
    (hanch : ∀ i ∈ S, ¬ cl i → y i = 0)
    (hcond : ∀ v : κ → ℝ, γ * gram a S v ≤ gram a (anchorSet cl S) v)
    (hslack : ∀ i ∈ S, cl i → -θ ≤ y i - dotp (a i) th) (t : κ → ℝ) :
    phi a y S th
        - ((S.card : ℝ) * θ ^ 2 + 4 * θ * Real.sqrt ((S.card : ℝ) * phi a y S th / γ))
      ≤ psiC a y cl S t := by
  have hnn : 0 ≤ (S.card : ℝ) * θ ^ 2 + 4 * θ * Real.sqrt ((S.card : ℝ) * phi a y S th / γ) := by
    have h1 : (0:ℝ) ≤ (S.card : ℝ) * θ ^ 2 := by positivity
    have h2 : (0:ℝ) ≤ 4 * θ * Real.sqrt ((S.card : ℝ) * phi a y S th / γ) :=
      mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    linarith
  rcases le_or_gt (psiC a y cl S t) (phi a y S th) with ht | ht
  · have hg := gram_sub_le_of_anchor (a := a) (y := y) (cl := cl) (S := S) (th := th) (t := t)
      hγ hanch hcond ht
    have hbase := psiC_ge_of_slack (a := a) (y := y) (cl := cl) (S := S) (th := th) hnormal hθ
      hslack t
    have hstep : Real.sqrt ((S.card : ℝ) * gram a S (t - th))
        ≤ 2 * Real.sqrt ((S.card : ℝ) * phi a y S th / γ) := by
      have hmul : (S.card : ℝ) * gram a S (t - th)
          ≤ 4 * ((S.card : ℝ) * phi a y S th / γ) := by
        have hc : (0:ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
        have := mul_le_mul_of_nonneg_left hg hc
        calc (S.card : ℝ) * gram a S (t - th)
            ≤ (S.card : ℝ) * (4 * phi a y S th / γ) := this
          _ = 4 * ((S.card : ℝ) * phi a y S th / γ) := by ring
      calc Real.sqrt ((S.card : ℝ) * gram a S (t - th))
          ≤ Real.sqrt (4 * ((S.card : ℝ) * phi a y S th / γ)) := Real.sqrt_le_sqrt hmul
        _ = Real.sqrt 4 * Real.sqrt ((S.card : ℝ) * phi a y S th / γ) :=
            Real.sqrt_mul (by norm_num) _
        _ = 2 * Real.sqrt ((S.card : ℝ) * phi a y S th / γ) := by
            rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith [hbase, hstep, hθ]
  · linarith

/-- **Калибровка сетки.** Если допуск знакового фильтра удовлетворяет
`64|S|θ² ≤ ε²γF(S)` (то есть `θ ≤ ε√(γF)/(8√|S|)`), то long-only теряет
не более `ε`-доли безусловного значения. -/
theorem psiC_ge_one_sub_eps (hnormal : IsNormal a y S th) (hθ : 0 ≤ θ) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hanch : ∀ i ∈ S, ¬ cl i → y i = 0)
    (hcond : ∀ v : κ → ℝ, γ * gram a S v ≤ gram a (anchorSet cl S) v)
    (hslack : ∀ i ∈ S, cl i → -θ ≤ y i - dotp (a i) th)
    (hgrid : 64 * (S.card : ℝ) * θ ^ 2 ≤ ε ^ 2 * γ * phi a y S th) (t : κ → ℝ) :
    (1 - ε) * phi a y S th ≤ psiC a y cl S t := by
  have hF : 0 ≤ phi a y S th := phi_nonneg a y S th
  have hc : (0:ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  -- линейный член
  have hX : 0 ≤ 4 * θ * Real.sqrt ((S.card : ℝ) * phi a y S th / γ) :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have harg : 0 ≤ (S.card : ℝ) * phi a y S th / γ := by positivity
  have hsq : (4 * θ * Real.sqrt ((S.card : ℝ) * phi a y S th / γ)) ^ 2
      = 16 * θ ^ 2 * ((S.card : ℝ) * phi a y S th / γ) := by
    rw [mul_pow, Real.sq_sqrt harg]; ring
  have hlin : 4 * θ * Real.sqrt ((S.card : ℝ) * phi a y S th / γ) ≤ ε * phi a y S th / 2 := by
    have hY : 0 ≤ ε * phi a y S th / 2 := by positivity
    have hcmp : (4 * θ * Real.sqrt ((S.card : ℝ) * phi a y S th / γ)) ^ 2
        ≤ (ε * phi a y S th / 2) ^ 2 := by
      rw [hsq]
      have hkey : 16 * θ ^ 2 * ((S.card : ℝ) * phi a y S th / γ)
          = (16 * ((S.card : ℝ) * θ ^ 2) * phi a y S th) / γ := by
        field_simp
      rw [hkey, div_le_iff₀ hγ]
      nlinarith [mul_le_mul_of_nonneg_right hgrid hF, hF, hγ]
    nlinarith [hcmp, hX, hY]
  -- квадратичный член
  have hquad : (S.card : ℝ) * θ ^ 2 ≤ ε * phi a y S th / 2 := by
    have h1 : ε ^ 2 * γ ≤ ε := by
      have hstep : ε ^ 2 * γ ≤ ε ^ 2 * 1 := mul_le_mul_of_nonneg_left hγ1 (sq_nonneg ε)
      nlinarith [hε, hε1]
    have h2 : ε ^ 2 * γ * phi a y S th ≤ ε * phi a y S th :=
      mul_le_mul_of_nonneg_right h1 hF
    have h3 : (0:ℝ) ≤ ε * phi a y S th := by positivity
    linarith
  have hmain := psiC_ge_of_slack_anchor (a := a) (y := y) (cl := cl) (S := S) (th := th)
    hnormal hθ hγ hanch hcond hslack t
  linarith

/-! ### Знаковый фильтр в узле даёт зазор `θ = √(Q_t − F)` -/

/-- **Из знака в узле — почти-самосогласованность в неподвижной точке.**
Если в узле `t` все зажатые невязки неотрицательны, то в `t̂` они не меньше
`−√(φ_S(t) − φ_S(t̂))`. Величина под корнем — это в точности зазор `Q_t(S) − F(S)`,
то есть `‖M_t(S)‖²_{Κ(S)⁻¹}`: **то, что динамика §4 и так хранит в ключе**.

Отличие от `selfconsistent_of_phi_gap` (`Clipped.lean`): там требовался
строгий запас `ρ > 0` в узле и зазор `≤ ρ²`, и вывод был о точной
самосогласованности. Здесь запаса не требуется (фильтр LO-K″ проверяет
ровно `r_i(t) ≥ 0`), а вывод — приближённый, с явным `θ`. -/
theorem slack_of_node_sign (hnormal : IsNormal a y S th)
    (hsign : ∀ i ∈ S, cl i → 0 ≤ y i - dotp (a i) t) :
    ∀ i ∈ S, cl i → -Real.sqrt (phi a y S t - phi a y S th) ≤ y i - dotp (a i) th := by
  intro i hi hc
  have hgram : gram a S (t - th) = phi a y S t - phi a y S th := by
    rw [phi_eq_add hnormal t]; ring
  have hsq : (dotp (a i) (t - th)) ^ 2 ≤ gram a S (t - th) := sq_dotp_le_gram hi _
  have habs : |dotp (a i) (t - th)| ≤ Real.sqrt (gram a S (t - th)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  have hle : -dotp (a i) (t - th) ≤ |dotp (a i) (t - th)| := neg_le_abs _
  have hd : dotp (a i) (t - th) = dotp (a i) t - dotp (a i) th := dotp_sub _ _ _
  have hs := hsign i hi hc
  rw [← hgram]
  linarith

/-- **Теорема W в узловой форме.** Гипотезы проверяются динамикой:
знак невязок в узле и зазор `Q_t(S) − F(S) ≤ ε²γF(S)/(64|S|)`. Вывод —
long-only теряет не более `ε`-доли безусловного значения. -/
theorem psiC_ge_of_node_sign (hnormal : IsNormal a y S th) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hanch : ∀ i ∈ S, ¬ cl i → y i = 0)
    (hcond : ∀ v : κ → ℝ, γ * gram a S v ≤ gram a (anchorSet cl S) v)
    (hsign : ∀ i ∈ S, cl i → 0 ≤ y i - dotp (a i) t)
    (hgap : 64 * (S.card : ℝ) * (phi a y S t - phi a y S th) ≤ ε ^ 2 * γ * phi a y S th)
    (t' : κ → ℝ) :
    (1 - ε) * phi a y S th ≤ psiC a y cl S t' := by
  have hgap0 : 0 ≤ phi a y S t - phi a y S th := by
    have := phi_min hnormal t; linarith
  have hsq : Real.sqrt (phi a y S t - phi a y S th) ^ 2 = phi a y S t - phi a y S th :=
    Real.sq_sqrt hgap0
  refine psiC_ge_one_sub_eps (θ := Real.sqrt (phi a y S t - phi a y S th)) hnormal
    (Real.sqrt_nonneg _) hγ hγ1 hε hε1 hanch hcond
    (slack_of_node_sign hnormal hsign) ?_ t'
  rw [hsq]; exact hgap

/-! ### Вытеснение из корзины: закрыто без самосогласованности вытеснившего -/

/-- **Главное следствие.** Пусть в узле `t` набор `R` вытеснил `S` из корзины
(`Q_t(R) ≥ Q_t(S)`, первые моменты совпадают, формы Грама равны), причём

* `R` прошёл знаковый фильтр в узле: `r_i(t) ≥ 0` при `i ∈ R` (условие LO-K″);
* зазор **у `S`** (то есть у носителя оптимума, где его контролирует сетка)
  не больше `ε²γF(R)/(64|R|)`.

Тогда long-only-значение вытеснившего набора не меньше `(1−ε)·F(S̄)`, а значит
и не меньше `(1−ε)·F_LO(S)`. Самосогласованность `R` **не предполагается** —
именно она была недостающим звеном; её заменяют знак в узле (Теорема U даёт
его бесплатно для точных близнецов) и оценка Теоремы W.

Зазор переносится с `S` на `R` по `gap_eq_of_bucket`: у соседей по корзине он
один и тот же. -/
theorem psiC_ge_of_bucket_node_sign {thS thR : κ → ℝ} {R : Finset ι}
    (hQ : phi a y S t ≤ phi a y R t)
    (hMom : ∀ v, mom a y R t v = mom a y S t v)
    (hKeq : ∀ v, gram a R v = gram a S v)
    (hnormS : IsNormal a y S thS) (hnormR : IsNormal a y R thR)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hanchR : ∀ i ∈ R, ¬ cl i → y i = 0)
    (hcondR : ∀ v : κ → ℝ, γ * gram a R v ≤ gram a (anchorSet cl R) v)
    (hsignR : ∀ i ∈ R, cl i → 0 ≤ y i - dotp (a i) t)
    (hgapS : 64 * (R.card : ℝ) * (phi a y S t - phi a y S thS)
      ≤ ε ^ 2 * γ * phi a y R thR)
    (t' : κ → ℝ) :
    (1 - ε) * phi a y S thS ≤ psiC a y cl R t' := by
  have hgapR : phi a y R t - phi a y R thR = phi a y S t - phi a y S thS :=
    gap_eq_of_bucket hMom hKeq hnormS hnormR
  have hSR : phi a y S thS ≤ phi a y R thR :=
    phi_normal_le_of_bucket hQ hMom (fun v => le_of_eq (hKeq v).symm) hnormS
  have hmain := psiC_ge_of_node_sign (S := R) (th := thR) (t := t) hnormR hγ hγ1 hε hε1
    hanchR hcondR hsignR (by rw [hgapR]; exact hgapS) t'
  nlinarith [hmain, hSR, hε1]

/-! ### Ослабленный фильтр: он и допускает оптимум, и ограничивает вытеснившего

Строгий фильтр `r_i(t) ≥ 0` в узле имеет изъян: самосогласованный оптимум `A*`
его может **не пройти** — в узле, отстоящем от `t̂`, невязка активной строки
способна уйти чуть ниже нуля. Правильный порог — `−θ₀`, где `θ₀` берётся из
калибровки сетки. Тогда работают обе стороны:

* `node_filter_admits` — `A*` допущен в любом узле с зазором `≤ θ₀²`;
* `slack_of_node_slack` — любой допущенный набор почти самосогласован
  (`r_i(t̂) ≥ −2θ₀`), а значит к нему применима Теорема W. -/

/-- **Ослабленный фильтр допускает самосогласованный набор.** -/
theorem node_filter_admits (hnormal : IsNormal a y S th) {θ₀ : ℝ} (hθ₀ : 0 ≤ θ₀)
    (hself : ∀ i ∈ S, cl i → 0 ≤ y i - dotp (a i) th)
    (hgap : phi a y S t - phi a y S th ≤ θ₀ ^ 2) :
    ∀ i ∈ S, cl i → -θ₀ ≤ y i - dotp (a i) t := by
  intro i hi hc
  have hgram : gram a S (t - th) = phi a y S t - phi a y S th := by
    rw [phi_eq_add hnormal t]; ring
  have hsq : (dotp (a i) (t - th)) ^ 2 ≤ θ₀ ^ 2 := by
    have := sq_dotp_le_gram (a := a) (S := S) hi (t - th)
    rw [hgram] at this; linarith
  have habs : |dotp (a i) (t - th)| ≤ θ₀ := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hθ₀] at h
  have hle : dotp (a i) (t - th) ≤ |dotp (a i) (t - th)| := le_abs_self _
  have hd : dotp (a i) (t - th) = dotp (a i) t - dotp (a i) th := dotp_sub _ _ _
  have hs := hself i hi hc
  linarith

/-- **Допущенный набор почти самосогласован.** Порог `−θ₀` в узле при зазоре
`≤ θ₀²` даёт `r_i(t̂) ≥ −2θ₀`. -/
theorem slack_of_node_slack (hnormal : IsNormal a y S th) {θ₀ : ℝ} (hθ₀ : 0 ≤ θ₀)
    (hfilter : ∀ i ∈ S, cl i → -θ₀ ≤ y i - dotp (a i) t)
    (hgap : phi a y S t - phi a y S th ≤ θ₀ ^ 2) :
    ∀ i ∈ S, cl i → -(2 * θ₀) ≤ y i - dotp (a i) th := by
  intro i hi hc
  have hgram : gram a S (t - th) = phi a y S t - phi a y S th := by
    rw [phi_eq_add hnormal t]; ring
  have hsq : (dotp (a i) (t - th)) ^ 2 ≤ θ₀ ^ 2 := by
    have := sq_dotp_le_gram (a := a) (S := S) hi (t - th)
    rw [hgram] at this; linarith
  have habs : |dotp (a i) (t - th)| ≤ θ₀ := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hθ₀] at h
  have hle : -dotp (a i) (t - th) ≤ |dotp (a i) (t - th)| := neg_le_abs _
  have hd : dotp (a i) (t - th) = dotp (a i) t - dotp (a i) th := dotp_sub _ _ _
  have hs := hfilter i hi hc
  linarith

/-- **Шаг LO-K‴ целиком.** В узле `t` с ослабленным фильтром порога `θ₀`:

* `hgapS` — узел близок к неподвижной точке носителя оптимума `S`
  (зазор `≤ θ₀²`; это вывод Теоремы O о ближайшем узле сетки);
* `hfilterR` — вытеснивший `R` прошёл фильтр;
* `hcal` — калибровка `256|R|θ₀² ≤ ε²γF(R)`, то есть `θ₀ ≤ ε√(γF)/(16√|R|)`.

Вывод: `F_LO(R) ≥ (1−ε)·F(S̄) ≥ (1−ε)·F_LO(S)`. Вместе с `node_filter_admits`
(самосогласованный `A*` фильтр проходит) это замыкает шаг динамики для
long-only при любом `K`: и допуск оптимума, и безопасность вытеснения. -/
theorem psiC_ge_of_bucket_node_slack {thS thR : κ → ℝ} {R : Finset ι} {θ₀ : ℝ}
    (hQ : phi a y S t ≤ phi a y R t)
    (hMom : ∀ v, mom a y R t v = mom a y S t v)
    (hKeq : ∀ v, gram a R v = gram a S v)
    (hnormS : IsNormal a y S thS) (hnormR : IsNormal a y R thR)
    (hθ₀ : 0 ≤ θ₀) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hanchR : ∀ i ∈ R, ¬ cl i → y i = 0)
    (hcondR : ∀ v : κ → ℝ, γ * gram a R v ≤ gram a (anchorSet cl R) v)
    (hfilterR : ∀ i ∈ R, cl i → -θ₀ ≤ y i - dotp (a i) t)
    (hgapS : phi a y S t - phi a y S thS ≤ θ₀ ^ 2)
    (hcal : 256 * (R.card : ℝ) * θ₀ ^ 2 ≤ ε ^ 2 * γ * phi a y R thR)
    (t' : κ → ℝ) :
    (1 - ε) * phi a y S thS ≤ psiC a y cl R t' := by
  have hgapR : phi a y R t - phi a y R thR = phi a y S t - phi a y S thS :=
    gap_eq_of_bucket hMom hKeq hnormS hnormR
  have hgapR' : phi a y R t - phi a y R thR ≤ θ₀ ^ 2 := by rw [hgapR]; exact hgapS
  have hslackR := slack_of_node_slack (S := R) (th := thR) (t := t) hnormR hθ₀ hfilterR
    hgapR'
  have hSR : phi a y S thS ≤ phi a y R thR :=
    phi_normal_le_of_bucket hQ hMom (fun v => le_of_eq (hKeq v).symm) hnormS
  have hmain := psiC_ge_one_sub_eps (S := R) (th := thR) (θ := 2 * θ₀) hnormR
    (by linarith) hγ hγ1 hε hε1 hanchR hcondR hslackR (by nlinarith [hcal]) t'
  nlinarith [hmain, hSR, hε1]

/-! ### Непустота: гипотезы выполнимы, а оценка содержательна

Инстанс: `K = 1`, три строки — актив-нарушитель `a₀ = 0, y₀ = −1/100`
(зажатый), актив `a₁ = 1, y₁ = 1` (зажатый) и якорь `a₂ = 1, y₂ = 0`.
Неподвижная точка `t̂ = 1/2`, `F = φ(t̂) = 1/2 + 1/10000`, зазор знака `θ = 1/100`,
обусловленность `γ = 1/2`. Теорема W даёт **положительную** нижнюю оценку
long-only: `ψ_S(t) ≥ F − (3θ² + 4θ√(3F/γ)) > 2/5` при всех `t`
(истинное значение `F_LO = 1/2`, так что оценка не бессодержательна). -/

private def aW : Fin 3 → Fin 1 → ℝ := fun i _ => if i = 0 then 0 else 1

private noncomputable def yW : Fin 3 → ℝ := fun i => if i = 0 then -1/100 else if i = 1 then 1 else 0

private def clW : Fin 3 → Bool := fun i => i = 0 ∨ i = 1

private lemma normalW : IsNormal aW yW Finset.univ (fun _ => (1/2 : ℝ)) := by
  intro v
  simp [mom, aW, yW, dotp, Fin.sum_univ_three]
  ring

private lemma phiW : phi aW yW Finset.univ (fun _ => (1/2 : ℝ)) = 1/2 + 1/10000 := by
  simp [phi, aW, yW, dotp, Fin.sum_univ_three]
  norm_num

example (t : Fin 1 → ℝ) : (2:ℝ)/5 ≤ psiC aW yW clW Finset.univ t := by
  have hanch : ∀ i ∈ (Finset.univ : Finset (Fin 3)), ¬ clW i → yW i = 0 := by
    intro i _ hc
    fin_cases i <;> simp_all [clW, yW]
  have hcond : ∀ v : Fin 1 → ℝ,
      (1/2 : ℝ) * gram aW Finset.univ v ≤ gram aW (anchorSet clW Finset.univ) v := by
    intro v
    have hset : anchorSet clW (Finset.univ : Finset (Fin 3)) = {2} := by
      ext i; fin_cases i <;> simp [anchorSet, clW]
    rw [hset]
    simp [gram, aW, dotp, Fin.sum_univ_three]
    nlinarith [sq_nonneg (v 0)]
  have hslack : ∀ i ∈ (Finset.univ : Finset (Fin 3)), clW i →
      -(1/100 : ℝ) ≤ yW i - dotp (aW i) (fun _ => (1/2 : ℝ)) := by
    intro i _ hc
    fin_cases i <;> simp_all [aW, yW, clW, dotp, Fin.sum_univ_one] <;> norm_num
  have hmain := psiC_ge_of_slack_anchor (a := aW) (y := yW) (cl := clW)
    (S := Finset.univ) (th := fun _ => (1/2 : ℝ)) (θ := 1/100) (γ := 1/2)
    normalW (by norm_num) (by norm_num) hanch hcond hslack t
  rw [phiW] at hmain
  have hcard : ((Finset.univ : Finset (Fin 3)).card : ℝ) = 3 := by simp
  rw [hcard] at hmain
  have hsqrt : Real.sqrt (3 * (1/2 + 1/10000) / (1/2 : ℝ)) ≤ 2 := by
    have harg : (3 : ℝ) * (1/2 + 1/10000) / (1/2) ≤ 4 := by norm_num
    calc Real.sqrt (3 * (1/2 + 1/10000) / (1/2 : ℝ))
        ≤ Real.sqrt 4 := Real.sqrt_le_sqrt harg
      _ = 2 := by
          rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  nlinarith [hmain, hsqrt, Real.sqrt_nonneg (3 * (1/2 + 1/10000) / (1/2 : ℝ))]



/-! ### Непустота бакетной теоремы: вытеснивший набор, который НЕ самосогласован

Пример выше проверяет только `psiC_ge_of_slack_anchor`. Главное утверждение
файла — `psiC_ge_of_bucket_node_slack` — про случай `R ≠ S` с
несамосогласованным `R`, и для него нужен отдельный инстанс.

Построен он так (`K = 1`, пять строк: два актива `S`, два актива `R`, общий
якорь): `R` получен из `S` поворотом индексного пространства активов на угол
`(4/5, 3/5)` — по Теореме V (`Rotation.lean`) такой поворот сохраняет `gram`,
`mom` и `φ` во всех точках, то есть `S` и `R` — точные соседи по корзине с
`Q_t(R) = Q_t(S)`. Невязки поворачиваются вместе с ними:
`r_S = (4, 29/10)` переходит в `r_R = (247/50, −2/25)`. Вторая компонента
**отрицательна** — `R` не самосогласован, хотя `S` самосогласован.

Числа: `a = (1, 1, 7/5, 1/5, 1)`, `y = (109/10, 49/5, 73/5, 13/10, 0)`,
`S̄ = {0,1,4}`, `R̄ = {2,3,4}`, узел `t = t̂ = 69/10` (зазор ноль),
`γ = 1/3` (якорь `1` против `gram = 3`), `θ₀ = 2/25`, `ε = 1/2`,
`F(S̄) = 3601/50`. Калибровка: `256·3·(2/25)² = 3072/625 ≤ ε²γF = 3601/600`.

Вывод теоремы: `ψ_R(t') ≥ (1−ε)F(S̄) = 3601/100` при всех `t'`. -/

private noncomputable def aB : Fin 5 → Fin 1 → ℝ :=
  fun i _ => if i = 0 then 1 else if i = 1 then 1 else
    if i = 2 then 7/5 else if i = 3 then 1/5 else 1

private noncomputable def yB : Fin 5 → ℝ :=
  fun i => if i = 0 then 109/10 else if i = 1 then 49/5 else
    if i = 2 then 73/5 else if i = 3 then 13/10 else 0

private def clB : Fin 5 → Bool := fun i => i ≠ 4

private noncomputable def SB : Finset (Fin 5) := {0, 1, 4}
private noncomputable def RB : Finset (Fin 5) := {2, 3, 4}
private noncomputable def tB : Fin 1 → ℝ := fun _ => 69/10

private lemma sumSB (f : Fin 5 → ℝ) : ∑ i ∈ SB, f i = f 0 + f 1 + f 4 := by
  simp [SB, Finset.sum_insert, Finset.mem_insert]
  ring

private lemma sumRB (f : Fin 5 → ℝ) : ∑ i ∈ RB, f i = f 2 + f 3 + f 4 := by
  simp [RB, Finset.sum_insert, Finset.mem_insert]
  ring

/-- Точные соседи по корзине: формы Грама совпадают. -/
private lemma gramB (v : Fin 1 → ℝ) : gram aB RB v = gram aB SB v := by
  simp only [gram, sumSB, sumRB, dotp, aB, Fin.sum_univ_one]
  norm_num
  ring

/-- Первые моменты совпадают во всех направлениях. -/
private lemma momB (v : Fin 1 → ℝ) : mom aB yB RB tB v = mom aB yB SB tB v := by
  simp only [mom, sumSB, sumRB, dotp, aB, yB, tB, Fin.sum_univ_one]
  norm_num
  ring

/-- Значения в узле совпадают, значит `R` законно вытесняет `S`. -/
private lemma QB : phi aB yB SB tB ≤ phi aB yB RB tB := by
  simp only [phi, sumSB, sumRB, dotp, aB, yB, tB, Fin.sum_univ_one]
  norm_num

private lemma normalSB : IsNormal aB yB SB tB := by
  intro v
  simp only [mom, sumSB, dotp, aB, yB, tB, Fin.sum_univ_one]
  norm_num
  ring

private lemma normalRB : IsNormal aB yB RB tB := by
  intro v
  simp only [mom, sumRB, dotp, aB, yB, tB, Fin.sum_univ_one]
  norm_num
  ring

private lemma phiSB : phi aB yB SB tB = 3601/50 := by
  simp only [phi, sumSB, dotp, aB, yB, tB, Fin.sum_univ_one]
  norm_num

private lemma phiRB : phi aB yB RB tB = 3601/50 := by
  simp only [phi, sumRB, dotp, aB, yB, tB, Fin.sum_univ_one]
  norm_num

private lemma cardRB : RB.card = 3 := by decide

/-- `R` **не** самосогласован: невязка строки `3` в неподвижной точке равна `−2/25`. -/
private lemma not_selfcons_RB : ¬ (0 ≤ yB 3 - dotp (aB 3) tB) := by
  simp [yB, aB, tB, dotp, Fin.sum_univ_one]
  norm_num

/-- Вывод Теоремы Y на этом инстансе: у вытеснившего несамосогласованного `R`
long-only не меньше `(1−ε)F(S̄) = 3601/100`. -/
example (t' : Fin 1 → ℝ) : (3601:ℝ)/100 ≤ psiC aB yB clB RB t' := by
  have hanch : ∀ i ∈ RB, ¬ clB i → yB i = 0 := by
    intro i hi hc
    have : i = 4 := by
      by_contra h
      exact hc (by simp [clB, h])
    simp [yB, this]
  have hcond : ∀ v : Fin 1 → ℝ,
      (1/3 : ℝ) * gram aB RB v ≤ gram aB (anchorSet clB RB) v := by
    intro v
    have hset : anchorSet clB RB = {4} := by
      ext i; fin_cases i <;> simp [anchorSet, clB, RB]
    rw [hset]
    simp only [gram, sumRB, dotp, aB, Fin.sum_univ_one, Finset.sum_singleton]
    norm_num
    nlinarith [sq_nonneg (v 0)]
  have hfilter : ∀ i ∈ RB, clB i → -(2/25 : ℝ) ≤ yB i - dotp (aB i) tB := by
    intro i hi hc
    fin_cases i <;> simp_all [RB, clB, yB, aB, tB, dotp, Fin.sum_univ_one] <;> norm_num
  have hmain := psiC_ge_of_bucket_node_slack (a := aB) (y := yB) (cl := clB)
    (S := SB) (R := RB) (t := tB) (thS := tB) (thR := tB) (θ₀ := 2/25)
    (γ := 1/3) (ε := 1/2)
    QB momB gramB normalSB normalRB (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hanch hcond hfilter
    (by rw [phiSB]; norm_num)
    (by rw [phiRB, cardRB]; norm_num) t'
  rw [phiSB] at hmain
  norm_num at hmain
  linarith

end SparseSharpe.Factor
