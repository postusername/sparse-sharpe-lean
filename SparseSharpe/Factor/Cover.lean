import SparseSharpe.Factor.BlockLeverage

set_option linter.style.header false

/-!
# Покрытие нарушителей относительно якорей: что сквозная теорема берёт со входа

Теорема Z″ (`psiC_ge_of_approxBucket_calibrated_block`) требует покрытия
нарушителей `CoveredBy` для набора `R`, который **вернула динамика**, и блочное
плечо там меряется относительно `gram_R`. Этот набор заранее неизвестен: это
какой-то набор «якоря + не больше `k` активов». Поэтому во входных данных
честно выражается только плечо относительно **якорей**:

    d·gram_U(v) ≤ (1 − d)·gram_base(v)   при всех v.

Если это так, то для **любого** `R ⊇ base` и `U ⊆ R` из зажатых строк
`gram_U ≤ (1 − d)·gram_R` — потому что вне `U` в `R` лежат все якоря
(`coveredBy_of_anchorCover`). Плечо относительно всей вселенной (как в §22.4
заметки 7) для этого не годится: у большего набора плечо меньше, и
вернувшийся `R` может быть гораздо беднее вселенной.

**Определение** (`AnchorCover`). Для каждой точки `t'` и каждого набора `U`
из не более чем `k` зажатых строк вселенной, **одновременно** нарушающих знак
в `t'`, найдётся `d ∈ (0,1]` с `d·gram_U ≤ (1−d)·gram_base` и `|U| ≤ c·d`.
Константа `c` и есть то, что заменяет `1/γ` в калибровке:
`θ₀ = √(εV/(8c))` (`theta0B`, `Factor/GridFilter.lean`).

Три источника константы — все формальны:

* **старая гипотеза** на `γ` даёт покрытие с `c = k/γ` (`anchorCover_of_anchor_cond`):
  замена полна, ничего не теряется;
* **плечи строк** `⟨a_i,v⟩² ≤ ω_i·gram_base(v)` дают покрытие с
  `c = max_{|U|≤k} |U|·(1 + Σ_U ω_i) ≤ k(1 + kω)` (`anchorCover_of_rowLev`,
  `anchorCover_of_rowLev_uniform`). В приложении `ω_i = B_i'Σ_fB_i/d_i`, то есть
  `1 + ω_i = V_ii/d_i = 1/(1 − R²_i)`; в отличие от `1/γ` эта величина **не растёт
  с размером вселенной**;
* **семейство множеств**, покрывающее нарушителей (например, все достижимые
  множества нарушителей, их `O(M^K)` — `Factor/Reachable.lean`), даёт покрытие с
  `c = max_W min(|W|,k)/d_W` (`anchorCover_of_family`).

**Предел** (`cover_const_ge_single`, `cover_const_ge_row`): одна строка `{i}` —
тоже набор одновременных нарушителей, и всякая строка с `a_i ≠ 0` где-нибудь
нарушает знак. Поэтому **любая** константа покрытия не меньше
`1 + ⟨a_i,v⟩²/gram_base(v)` при всех `v`, то есть не меньше `1 + ω_i`. Покрытием
не снимается зависимость от худшего одиночного актива; снимается лишь
зависимость от размера вселенной и от «выстроенности» нагрузок.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype κ] [DecidableEq ι]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {cl : ι → Bool} {S R base : Finset ι}

/-! ### Определение и наследование на набор динамики -/

/-- **Покрытие нарушителей относительно якорей.** Для каждой точки `t'` и
каждого набора `U ⊆ S` из не более чем `k` зажатых строк, одновременно
нарушающих знак в `t'`, найдётся `d ∈ (0,1]` с `d·gram_U ≤ (1−d)·gram_base`
и `|U| ≤ c·d`. -/
def AnchorCover (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (S base : Finset ι)
    (k : ℕ) (c : ℝ) : Prop :=
  ∀ (t' : κ → ℝ) (U : Finset ι), U ⊆ S → U.card ≤ k →
    (∀ j ∈ U, cl j ∧ y j - dotp (a j) t' < 0) →
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ (∀ v : κ → ℝ, d * gram a U v ≤ (1 - d) * gram a base v)
      ∧ (U.card : ℝ) ≤ c * d

omit [DecidableEq ι] in
/-- Большая константа — тоже константа покрытия. -/
lemma AnchorCover.mono {k : ℕ} {c c' : ℝ} (h : AnchorCover a y cl S base k c) (hc : c ≤ c') :
    AnchorCover a y cl S base k c' := by
  intro t' U hUS hUk hUv
  obtain ⟨d, hd, hd1, hb, hcard⟩ := h t' U hUS hUk hUv
  exact ⟨d, hd, hd1, hb, le_trans hcard (mul_le_mul_of_nonneg_right hc hd.le)⟩

/-- **Покрытие вселенной наследуется набором динамики.** Если `base ⊆ R ⊆ S`,
якоря не зажаты, а зажатых строк в `R` не больше `k`, то нарушители `R`
покрыты в смысле `CoveredBy` (относительно `gram_R`) с калибровкой `c·θ² ≤ B`.

Суть: `U` — нарушители `R` в точке `t'`; вне `U` в `R` лежат все якоря, поэтому
`d·gram_U ≤ (1−d)·gram_base ≤ (1−d)·gram_{R∖U}`, а это и есть
`gram_U ≤ (1−d)·gram_R`. -/
theorem coveredBy_of_anchorCover {k : ℕ} {c θ B : ℝ}
    (hcov : AnchorCover a y cl S base k c)
    (hbR : base ⊆ R) (hRS : R ⊆ S) (hbase : ∀ i ∈ base, ¬ cl i)
    (hk : (clipSet cl R).card ≤ k) (hcal : c * θ ^ 2 ≤ B) :
    CoveredBy a y cl R θ B := by
  classical
  intro t'
  set U : Finset ι := R.filter (fun j => cl j ∧ y j - dotp (a j) t' < 0) with hU
  have hUR : U ⊆ R := filter_subset _ _
  have hUcl : U ⊆ clipSet cl R := by
    intro j hj
    have hj' := mem_filter.mp hj
    exact mem_filter.mpr ⟨hj'.1, hj'.2.1⟩
  have hUk : U.card ≤ k := le_trans (card_le_card hUcl) hk
  have hUv : ∀ j ∈ U, cl j ∧ y j - dotp (a j) t' < 0 := fun j hj => (mem_filter.mp hj).2
  obtain ⟨d, hd, hd1, hblock, hcard⟩ := hcov t' U (hUR.trans hRS) hUk hUv
  refine ⟨U, d, hUR, hd, hd1, ?_, ?_, ?_⟩
  · intro j hj hc hneg
    exact mem_filter.mpr ⟨hj, hc, hneg⟩
  · intro v
    have hsplit : gram a R v = gram a U v + gram a (R \ U) v := by
      simp only [gram]
      rw [← sum_union disjoint_sdiff, union_sdiff_of_subset hUR]
    have hbsub : base ⊆ R \ U := by
      intro i hi
      refine mem_sdiff.mpr ⟨hbR hi, fun hiU => hbase i hi ?_⟩
      exact (mem_filter.mp hiU).2.1
    have h1 : gram a base v ≤ gram a (R \ U) v := gram_mono hbsub v
    have h2 := hblock v
    have h3 : (1 - d) * gram a base v ≤ (1 - d) * gram a (R \ U) v :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    rw [hsplit]
    nlinarith [h2, h3]
  · have hdiv : (U.card : ℝ) / d ≤ c := by
      rw [div_le_iff₀ hd]; linarith [hcard]
    calc (U.card : ℝ) * θ ^ 2 / d = ((U.card : ℝ) / d) * θ ^ 2 := by ring
      _ ≤ c * θ ^ 2 := mul_le_mul_of_nonneg_right hdiv (sq_nonneg θ)
      _ ≤ B := hcal

/-- Зажатых строк в наборе, содержащем якоря, не больше «мощность минус якоря». -/
lemma card_clipSet_le_of_base (hbR : base ⊆ R) (hbase : ∀ i ∈ base, ¬ cl i) :
    (clipSet cl R).card + base.card ≤ R.card := by
  have hdisj : Disjoint (clipSet cl R) base := by
    rw [Finset.disjoint_left]
    intro i hi hib
    exact hbase i hib (mem_filter.mp hi).2
  rw [← card_union_of_disjoint hdisj]
  exact card_le_card (union_subset (filter_subset _ _) hbR)

/-! ### Источник 1: старая гипотеза на `γ` -/

/-- **Замена полна.** Якорное условие Теоремы W на вселенной `S` даёт покрытие
с `c = k/γ`: годится `d = γ` для любого набора зажатых строк. -/
theorem anchorCover_of_anchor_cond {k : ℕ} {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hanchBase : anchorSet cl S ⊆ base)
    (hcond : ∀ v : κ → ℝ, γ * gram a S v ≤ gram a (anchorSet cl S) v) :
    AnchorCover a y cl S base k ((k : ℝ) / γ) := by
  intro t' U hUS hUk hUv
  refine ⟨γ, hγ, hγ1, fun v => ?_, ?_⟩
  · have hUC : U ⊆ clipSet cl S := fun j hj => mem_filter.mpr ⟨hUS hj, (hUv j hj).1⟩
    have h1 : gram a U v ≤ gram a (clipSet cl S) v := gram_mono hUC v
    have hsplit := gram_split a cl S v
    have h2 := hcond v
    have h3 : gram a (anchorSet cl S) v ≤ gram a base v := gram_mono hanchBase v
    have h4 : (1 - γ) * gram a (anchorSet cl S) v ≤ (1 - γ) * gram a base v :=
      mul_le_mul_of_nonneg_left h3 (by linarith)
    nlinarith [h1, h2, h4, hγ.le]
  · rw [div_mul_cancel₀ _ hγ.ne']
    exact_mod_cast hUk

/-! ### Источник 2: плечи строк относительно якорей -/

omit [DecidableEq ι] in
/-- **Покрытие из плеч строк.** Пусть у каждой зажатой строки вселенной
`⟨a_i,v⟩² ≤ ω_i·gram_base(v)`. Тогда для набора `U` годится
`d_U = 1/(1 + Σ_U ω_i)`, и константа покрытия — любая `c` с
`|U|·(1 + Σ_U ω_i) ≤ c` для всех наборов зажатых строк мощности `≤ k`.
Одновременность нарушения здесь даже не используется. -/
theorem anchorCover_of_rowLev {k : ℕ} {c : ℝ} (ω : ι → ℝ) (hω : ∀ i ∈ S, cl i → 0 ≤ ω i)
    (hrow : ∀ i ∈ S, cl i → ∀ v : κ → ℝ, (dotp (a i) v) ^ 2 ≤ ω i * gram a base v)
    (hc : ∀ U ⊆ S, (∀ j ∈ U, cl j) → U.card ≤ k →
      (U.card : ℝ) * (1 + ∑ i ∈ U, ω i) ≤ c) :
    AnchorCover a y cl S base k c := by
  intro t' U hUS hUk hUv
  have hΩ : 0 ≤ ∑ i ∈ U, ω i :=
    sum_nonneg fun i hi => hω i (hUS hi) (hUv i hi).1
  set Ω := ∑ i ∈ U, ω i with hΩdef
  have hpos : 0 < 1 + Ω := by linarith
  refine ⟨1 / (1 + Ω), by positivity, ?_, fun v => ?_, ?_⟩
  · rw [div_le_one hpos]; linarith
  · -- `gram_U ≤ Ω·gram_base`, и `(1/(1+Ω))·Ω = 1 − 1/(1+Ω)`
    have hgU : gram a U v ≤ Ω * gram a base v := by
      rw [hΩdef, sum_mul]
      exact sum_le_sum fun i hi => hrow i (hUS hi) (hUv i hi).1 v
    have hgb := gram_nonneg a base v
    have heq : 1 - 1 / (1 + Ω) = Ω * (1 / (1 + Ω)) := by field_simp; ring
    rw [heq]
    have hd0 : (0:ℝ) ≤ 1 / (1 + Ω) := by positivity
    calc 1 / (1 + Ω) * gram a U v ≤ 1 / (1 + Ω) * (Ω * gram a base v) :=
          mul_le_mul_of_nonneg_left hgU hd0
      _ = Ω * (1 / (1 + Ω)) * gram a base v := by ring
  · have h := hc U hUS (fun j hj => (hUv j hj).1) hUk
    rw [← hΩdef] at h
    rw [mul_one_div, le_div_iff₀ hpos]
    exact h

omit [DecidableEq ι] in
/-- Удобная форма: одинаковая граница `ω` на плечи строк даёт `c = k·(1 + k·ω)`. -/
theorem anchorCover_of_rowLev_uniform {k : ℕ} {ω : ℝ} (hω : 0 ≤ ω)
    (hrow : ∀ i ∈ S, cl i → ∀ v : κ → ℝ, (dotp (a i) v) ^ 2 ≤ ω * gram a base v) :
    AnchorCover a y cl S base k ((k : ℝ) * (1 + (k : ℝ) * ω)) := by
  refine anchorCover_of_rowLev (fun _ => ω) (fun _ _ _ => hω) hrow ?_
  intro U _ _ hUk
  have hk : (U.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hUk
  rw [sum_const, nsmul_eq_mul]
  have h0 : (0:ℝ) ≤ (U.card : ℝ) := Nat.cast_nonneg _
  have h1 : 1 + (U.card : ℝ) * ω ≤ 1 + (k : ℝ) * ω := by nlinarith
  have h2 : (0:ℝ) ≤ 1 + (U.card : ℝ) * ω := by positivity
  calc (U.card : ℝ) * (1 + (U.card : ℝ) * ω) ≤ (k : ℝ) * (1 + (U.card : ℝ) * ω) :=
        mul_le_mul_of_nonneg_right hk h2
    _ ≤ (k : ℝ) * (1 + (k : ℝ) * ω) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)

/-! ### Источник 3: семейство множеств, покрывающее нарушителей -/

omit [DecidableEq ι] in
/-- **Покрытие из семейства множеств.** Если нарушители вселенной в каждой
точке лежат в каком-то `W` семейства, и у каждого `W` есть `d_W` с
`d_W·gram_W ≤ (1−d_W)·gram_base` и `min(|W|, k) ≤ c·d_W`, то это покрытие с
константой `c`. В приложении семейство — достижимые множества нарушителей,
их `O(M^K)` (`Factor/Reachable.lean`). -/
theorem anchorCover_of_family {k : ℕ} {c : ℝ} (𝒲 : Finset (Finset ι)) (dW : Finset ι → ℝ)
    (hcover : ∀ t' : κ → ℝ, ∃ W ∈ 𝒲,
      ∀ j ∈ S, cl j → y j - dotp (a j) t' < 0 → j ∈ W)
    (hd : ∀ W ∈ 𝒲, 0 < dW W ∧ dW W ≤ 1
      ∧ (∀ v : κ → ℝ, dW W * gram a W v ≤ (1 - dW W) * gram a base v)
      ∧ (min (W.card) k : ℝ) ≤ c * dW W) :
    AnchorCover a y cl S base k c := by
  intro t' U hUS hUk hUv
  obtain ⟨W, hW, hviol⟩ := hcover t'
  obtain ⟨hd0, hd1, hblock, hcard⟩ := hd W hW
  have hUW : U ⊆ W := fun j hj => hviol j (hUS hj) (hUv j hj).1 (hUv j hj).2
  refine ⟨dW W, hd0, hd1, fun v => ?_, ?_⟩
  · have h1 : gram a U v ≤ gram a W v := gram_mono hUW v
    have h2 := hblock v
    nlinarith [mul_le_mul_of_nonneg_left h1 hd0.le]
  · have hUc : (U.card : ℝ) ≤ (min (W.card) k : ℝ) := by
      have : U.card ≤ min W.card k := le_min (card_le_card hUW) hUk
      exact_mod_cast this
    linarith

/-! ### Предел: худший одиночный актив покрытием не снимается -/

omit [DecidableEq ι] in
/-- **Нижняя граница константы покрытия.** Одна строка `{i}` — тоже набор
одновременных нарушителей. Если зажатая строка `i` где-нибудь нарушает знак, то
всякая константа покрытия (при `k ≥ 1`) не меньше `1 + ⟨a_i,v⟩²/gram_base(v)`
при любом `v` с `gram_base(v) > 0`. -/
theorem cover_const_ge_single {k : ℕ} {c : ℝ} (hcov : AnchorCover a y cl S base k c)
    (hk : 1 ≤ k) {i : ι} (hiS : i ∈ S) (hci : cl i) {t' : κ → ℝ}
    (hviol : y i - dotp (a i) t' < 0) {v : κ → ℝ} (hv : 0 < gram a base v) :
    1 + (dotp (a i) v) ^ 2 / gram a base v ≤ c := by
  obtain ⟨d, hd, _hd1, hblock, hcard⟩ := hcov t' {i} (by simpa using hiS)
    (by simpa using hk) (fun j hj => by
      rw [Finset.mem_singleton] at hj
      subst hj
      exact ⟨hci, hviol⟩)
  have hb := hblock v
  simp only [gram, sum_singleton] at hb
  have hc1 : 1 ≤ c * d := by simpa using hcard
  -- `d·(x + g) ≤ g`, значит `1 + x/g = (g + x)/g ≤ 1/d ≤ c`
  set x := (dotp (a i) v) ^ 2
  set g := ∑ j ∈ base, (dotp (a j) v) ^ 2 with hg
  have hgpos : 0 < g := by simpa [gram] using hv
  have h1 : 1 + x / g ≤ 1 / d := by
    rw [show 1 + x / g = (g + x) / g by field_simp, div_le_div_iff₀ hgpos hd]
    nlinarith [hb]
  have h2 : 1 / d ≤ c := by
    rw [div_le_iff₀ hd]; linarith
  have : 1 + x / gram a base v = 1 + x / g := by simp [gram, hg]
  rw [this]
  linarith

omit [DecidableEq ι] in
/-- Всякая ненулевая строка где-нибудь нарушает знак: достаточно уйти вдоль неё. -/
lemma exists_viol_of_ne_zero {i : ι} (hai : ∃ l, a i l ≠ 0) :
    ∃ t' : κ → ℝ, y i - dotp (a i) t' < 0 := by
  obtain ⟨l₀, hl₀⟩ := hai
  set q := dotp (a i) (a i) with hq
  have hqpos : 0 < q := by
    rw [hq, dotp]
    have hle : a i l₀ * a i l₀ ≤ ∑ j, a i j * a i j :=
      Finset.single_le_sum (f := fun j => a i j * a i j)
        (fun j _ => mul_self_nonneg (a i j)) (Finset.mem_univ l₀)
    have hpos : 0 < a i l₀ * a i l₀ := mul_self_pos.mpr hl₀
    linarith
  refine ⟨((|y i| + 1) / q) • a i, ?_⟩
  rw [dotp_smul, ← hq, div_mul_cancel₀ _ hqpos.ne']
  linarith [le_abs_self (y i)]

omit [DecidableEq ι] in
/-- **Предел в форме, не требующей точки нарушения:** всякая зажатая строка
вселенной с `a_i ≠ 0` даёт `c ≥ 1 + ⟨a_i,v⟩²/gram_base(v)`. В приложении,
при `v = Σ_f B_i`, это `c ≥ 1 + B_i'Σ_fB_i/d_i = V_ii/d_i`. -/
theorem cover_const_ge_row {k : ℕ} {c : ℝ} (hcov : AnchorCover a y cl S base k c)
    (hk : 1 ≤ k) {i : ι} (hiS : i ∈ S) (hci : cl i) (hai : ∃ l, a i l ≠ 0)
    {v : κ → ℝ} (hv : 0 < gram a base v) :
    1 + (dotp (a i) v) ^ 2 / gram a base v ≤ c := by
  obtain ⟨t', ht'⟩ := exists_viol_of_ne_zero (y := y) hai
  exact cover_const_ge_single hcov hk hiS hci ht' hv

/-! ### Непустота: покрытие существует, и нижняя граница на нём достигается

`K = 1`: якорь `g = 1` (`gram_base(v) = v²`) и одна зажатая строка `a = 1`,
`y = 1`. Нарушители — только эта строка (при `t' > 1`), и для неё
`d·v² ≤ (1−d)·v²` ровно при `d ≤ 1/2`. Покрытие с `k = 1`, `c = 2` есть
(`anchorCover_ex`), а нижняя граница даёт `c ≥ 1 + 1/1 = 2` (`cover_ex_sharp`):
константа `2` точна, то есть определение не пусто и не завышено. -/

private def aC : Fin 2 → Fin 1 → ℝ := fun _ _ => 1
private def yC : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
private def clC : Fin 2 → Bool := fun i => decide (i = 0)
private def SC : Finset (Fin 2) := Finset.univ
private def baseC : Finset (Fin 2) := {1}

private lemma gram_baseC (v : Fin 1 → ℝ) : gram aC baseC v = (v 0) ^ 2 := by
  simp [gram, baseC, dotp, aC]

private lemma anchorCover_ex : AnchorCover aC yC clC SC baseC 1 2 := by
  intro t' U _ hUk hUv
  -- все строки `U` зажаты, значит `U ⊆ {0}`
  have hU0 : U ⊆ {0} := by
    intro j hj
    have := (hUv j hj).1
    fin_cases j
    · simp
    · simp [clC] at this
  refine ⟨1 / 2, by norm_num, by norm_num, fun v => ?_, ?_⟩
  · rw [gram_baseC]
    have hle : gram aC U v ≤ gram aC {0} v := gram_mono hU0 v
    have h0 : gram aC {0} v = (v 0) ^ 2 := by simp [gram, dotp, aC]
    rw [h0] at hle
    nlinarith [hle]
  · have : (U.card : ℝ) ≤ 1 := by exact_mod_cast hUk
    linarith

private lemma cover_ex_sharp {c : ℝ} (h : AnchorCover aC yC clC SC baseC 1 c) : 2 ≤ c := by
  have hv : 0 < gram aC baseC (fun _ => 1) := by rw [gram_baseC]; norm_num
  have := cover_const_ge_row (i := 0) h le_rfl (by simp [SC]) (by simp [clC])
    ⟨0, by simp [aC]⟩ hv
  rw [gram_baseC] at this
  simp [dotp, aC] at this
  linarith

/-- Покрытие с `c = 2` существует, и меньшей константы не бывает. -/
example : AnchorCover aC yC clC SC baseC 1 2
    ∧ ∀ c, AnchorCover aC yC clC SC baseC 1 c → 2 ≤ c :=
  ⟨anchorCover_ex, fun _ h => cover_ex_sharp h⟩

end SparseSharpe.Factor
