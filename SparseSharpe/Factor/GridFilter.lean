import SparseSharpe.Factor.Stability
import SparseSharpe.Factor.GridK

set_option linter.style.header false

/-!
# Связка «сетка → фильтр»: узел, в котором Теорема Y применима

Теорема Y (`Factor/Stability.lean`) требует от узла `t` двух вещей:

* сертификат `φ_S̄(t) − F(S̄) ≤ θ₀²` (зазор узла мал);
* чтобы порог фильтра был `−θ₀`, а не `0` — иначе сам оптимум может быть
  отвергнут.

Сетка Теоремы H/O (`Factor/GridK.lean`, `exists_grid_node`) даёт узел с
`φ_S̄(t) ≤ (1+ε_g)F(S̄)`, то есть с зазором `≤ ε_g·F ≤ 2ε_g·V`. Значит
достаточно взять

    ε_g = ε²γ/(512n),     θ₀ = ε√(γV)/(16√n),     n ≥ |S̄|,

и оба условия выполняются сразу (`exists_node_closing_step`). Номера узлов
при этом по-прежнему ограничены величиной, свободной от данных входа
(`exists_grid_node` возвращает эту оценку), только теперь она содержит `γ`:
шаг сетки уменьшился в `√(1/(ε γ))` раз по сравнению с безусловной задачей.
Это и есть та самая цена long-only — и единственная.

Итог файла (`psiC_ge_at_grid_node`): в найденном узле **любой** набор `R`,
прошедший фильтр порога `−θ₀` и вытеснивший `S̄` из корзины, удовлетворяет
`F_LO(R) ≥ (1−ε)F(S̄)`. Ни самосогласованность `R`, ни его близость к `S̄`
не предполагаются.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {cl : ι → Bool} {S R : Finset ι} {T : κ → ι}
variable {t th thR : κ → ℝ}

/-- Порог фильтра: `θ₀ = ε√(γV)/(16√n)`. -/
noncomputable def theta0 (ε γ V : ℝ) (n : ℕ) : ℝ :=
  ε * Real.sqrt (γ * V) / (16 * Real.sqrt (n : ℝ))

lemma theta0_nonneg {ε γ V : ℝ} {n : ℕ} (hε : 0 ≤ ε) : 0 ≤ theta0 ε γ V n := by
  unfold theta0
  positivity

lemma theta0_sq {ε γ V : ℝ} {n : ℕ} (hγV : 0 ≤ γ * V) (hn : 0 < n) :
    theta0 ε γ V n ^ 2 = ε ^ 2 * (γ * V) / (256 * (n : ℝ)) := by
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hg : Real.sqrt (γ * V) ^ 2 = γ * V := Real.sq_sqrt hγV
  have hsne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn0)
  unfold theta0
  field_simp
  rw [hs, hg]
  ring

/-- **Калибровка Теоремы Y выполняется автоматически.** -/
lemma cal_of_theta0 {ε γ V : ℝ} {n : ℕ} {F : ℝ} (hγ : 0 < γ) (hV : 0 < V)
    (hn : 0 < n) (hcard : (R.card : ℝ) ≤ (n : ℝ)) (hVF : V ≤ F) (hε : 0 ≤ ε) :
    256 * (R.card : ℝ) * theta0 ε γ V n ^ 2 ≤ ε ^ 2 * γ * F := by
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [theta0_sq (by positivity) hn]
  have hstep : 256 * (R.card : ℝ) * (ε ^ 2 * (γ * V) / (256 * (n : ℝ)))
      ≤ 256 * (n : ℝ) * (ε ^ 2 * (γ * V) / (256 * (n : ℝ))) := by
    have hnn : (0:ℝ) ≤ ε ^ 2 * (γ * V) / (256 * (n : ℝ)) := by positivity
    nlinarith [hcard, hnn]
  have heq : 256 * (n : ℝ) * (ε ^ 2 * (γ * V) / (256 * (n : ℝ))) = ε ^ 2 * (γ * V) := by
    field_simp
  have hlast : ε ^ 2 * (γ * V) ≤ ε ^ 2 * γ * F := by
    have : (0:ℝ) ≤ ε ^ 2 * γ := by positivity
    nlinarith [hVF, this]
  linarith [hstep, heq.le, hlast]

/-- **Узел, закрывающий шаг.** В решётке с шагом `s = 2√(ε_g V/(K·C))`,
`ε_g = ε²γ/(512n)`, есть узел, в котором одновременно

* зазор носителя оптимума не больше `θ₀²` (сертификат Теоремы Y);
* сам оптимум проходит фильтр порога `−θ₀` (`node_filter_admits`).

Номера узлов ограничены `√(K·C/(2ε_g)) + ½` — величиной без данных входа. -/
theorem exists_node_closing_step
    (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0) (hnormal : IsNormal a y S th)
    {ε γ V C s : ℝ} {n : ℕ}
    (hC : (S.card * Fintype.card κ : ℝ) ≤ C) (hCpos : 0 < C)
    (hε : 0 < ε) (hγ : 0 < γ) (hV : 0 < V)
    (hVF : V ≤ phi a y S th) (hFV : phi a y S th ≤ 2 * V)
    (hKc : 0 < (Fintype.card κ : ℝ)) (hn : 0 < n)
    (hs : s = 2 * Real.sqrt ((ε ^ 2 * γ / (512 * (n : ℝ))) * V
      / ((Fintype.card κ : ℝ) * C)))
    (hself : ∀ i ∈ S, cl i → 0 ≤ y i - dotp (a i) th) :
    ∃ z : κ → ℤ,
      (∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C
        / (2 * (ε ^ 2 * γ / (512 * (n : ℝ))))) + 1 / 2) ∧
      (∀ t : κ → ℝ, (∀ l, dotp (a (T l)) t = y (T l) + s * (z l : ℝ)) →
        phi a y S t - phi a y S th ≤ theta0 ε γ V n ^ 2
        ∧ (∀ i ∈ S, cl i → -theta0 ε γ V n ≤ y i - dotp (a i) t)) := by
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  set εg : ℝ := ε ^ 2 * γ / (512 * (n : ℝ)) with hεg
  have hεgpos : 0 < εg := by rw [hεg]; positivity
  obtain ⟨z, hz1, hz2⟩ := exists_grid_node hmax hdet hnormal hC hCpos hεgpos hV hVF hFV hKc hs
  refine ⟨z, hz1, fun t ht => ?_⟩
  have hphi := hz2 t ht
  have hgap : phi a y S t - phi a y S th ≤ theta0 ε γ V n ^ 2 := by
    rw [theta0_sq (by positivity) hn]
    have h1 : phi a y S t - phi a y S th ≤ εg * phi a y S th := by linarith
    have h2 : εg * phi a y S th ≤ εg * (2 * V) :=
      mul_le_mul_of_nonneg_left hFV hεgpos.le
    have h3 : εg * (2 * V) = ε ^ 2 * (γ * V) / (256 * (n : ℝ)) := by
      rw [hεg]; field_simp; ring
    linarith
  exact ⟨hgap, node_filter_admits hnormal (theta0_nonneg hε.le) hself hgap⟩

/-- **Узел с запасом.** То же, что `exists_node_closing_step`, но с шагом сетки,
вдвое более мелким по `ε_g` (`1024` вместо `512`): зазор получается не больше
`θ₀²/2`, и вторая половина `θ₀²` остаётся на цену округления ключа
(`bucketErr`, `Factor/Rounding.lean`). Именно эта версия нужна для сквозной
теоремы `lo_fptas` (`Factor/DPRun.lean`). -/
theorem exists_node_closing_step_half
    (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0) (hnormal : IsNormal a y S th)
    {ε γ V C s : ℝ} {n : ℕ}
    (hC : (S.card * Fintype.card κ : ℝ) ≤ C) (hCpos : 0 < C)
    (hε : 0 < ε) (hγ : 0 < γ) (hV : 0 < V)
    (hVF : V ≤ phi a y S th) (hFV : phi a y S th ≤ 2 * V)
    (hKc : 0 < (Fintype.card κ : ℝ)) (hn : 0 < n)
    (hs : s = 2 * Real.sqrt ((ε ^ 2 * γ / (1024 * (n : ℝ))) * V
      / ((Fintype.card κ : ℝ) * C)))
    (hself : ∀ i ∈ S, cl i → 0 ≤ y i - dotp (a i) th) :
    ∃ z : κ → ℤ,
      (∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C
        / (2 * (ε ^ 2 * γ / (1024 * (n : ℝ))))) + 1 / 2) ∧
      (∀ t : κ → ℝ, (∀ l, dotp (a (T l)) t = y (T l) + s * (z l : ℝ)) →
        phi a y S t - phi a y S th ≤ theta0 ε γ V n ^ 2 / 2
        ∧ (∀ i ∈ S, cl i → -theta0 ε γ V n ≤ y i - dotp (a i) t)) := by
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  set εg : ℝ := ε ^ 2 * γ / (1024 * (n : ℝ)) with hεg
  have hεgpos : 0 < εg := by rw [hεg]; positivity
  obtain ⟨z, hz1, hz2⟩ := exists_grid_node hmax hdet hnormal hC hCpos hεgpos hV hVF hFV hKc hs
  refine ⟨z, hz1, fun t ht => ?_⟩
  have hphi := hz2 t ht
  have hgap : phi a y S t - phi a y S th ≤ theta0 ε γ V n ^ 2 / 2 := by
    rw [theta0_sq (by positivity) hn]
    have h1 : phi a y S t - phi a y S th ≤ εg * phi a y S th := by linarith
    have h2 : εg * phi a y S th ≤ εg * (2 * V) :=
      mul_le_mul_of_nonneg_left hFV hεgpos.le
    have h3 : εg * (2 * V) = ε ^ 2 * (γ * V) / (256 * (n : ℝ)) / 2 := by
      rw [hεg]; field_simp; ring
    linarith
  have hgap' : phi a y S t - phi a y S th ≤ theta0 ε γ V n ^ 2 := by
    have : (0:ℝ) ≤ theta0 ε γ V n ^ 2 := sq_nonneg _
    linarith
  exact ⟨hgap, node_filter_admits hnormal (theta0_nonneg hε.le) hself hgap'⟩

/-- **Шаг динамики в найденном узле.** Сводка: в узле из
`exists_node_closing_step` любой набор `R`, вытеснивший `S̄` из корзины и
прошедший фильтр порога `−θ₀`, даёт `F_LO(R) ≥ (1−ε)·F(S̄)`. -/
theorem psiC_ge_at_grid_node
    {ε γ V : ℝ} {n : ℕ}
    (hnormS : IsNormal a y S th) (hnormR : IsNormal a y R thR)
    (hQ : phi a y S t ≤ phi a y R t)
    (hMom : ∀ v, mom a y R t v = mom a y S t v)
    (hKeq : ∀ v, gram a R v = gram a S v)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hV : 0 < V) (hn : 0 < n)
    (hcard : (R.card : ℝ) ≤ (n : ℝ)) (hVF : V ≤ phi a y S th)
    (hanchR : ∀ i ∈ R, ¬ cl i → y i = 0)
    (hcondR : ∀ v : κ → ℝ, γ * gram a R v ≤ gram a (anchorSet cl R) v)
    (hfilterR : ∀ i ∈ R, cl i → -theta0 ε γ V n ≤ y i - dotp (a i) t)
    (hgapS : phi a y S t - phi a y S th ≤ theta0 ε γ V n ^ 2)
    (t' : κ → ℝ) :
    (1 - ε) * phi a y S th ≤ psiC a y cl R t' := by
  have hFR : V ≤ phi a y R thR :=
    le_trans hVF (phi_normal_le_of_bucket hQ hMom (fun v => le_of_eq (hKeq v).symm) hnormS)
  exact psiC_ge_of_bucket_node_slack hQ hMom hKeq hnormS hnormR
    (theta0_nonneg hε.le) hγ hγ1 hε hε1 hanchR hcondR hfilterR hgapS
    (cal_of_theta0 hγ hV hn hcard hFR hε.le) t'

/-! ### Порог через константу покрытия (`δ`-цепочка)

В `δ`-цепочке (`Factor/Cover.lean`, `lo_fptas_block` в `Factor/DPRun.lean`)
калибровка Теоремы Z″ — это `c·(2θ₀)² ≤ ε·F`, где `c` — константа покрытия
нарушителей относительно якорей. Отсюда порог

    θ₀ = √(εV/(8c)),

а сетка — с `ε_g = ε/(32c)`, чтобы зазор узла не превышал `θ₀²/2` (вторая
половина `θ₀²` остаётся на цену округления ключа). По сравнению с `theta0`
(`θ₀² = ε²γV/(256n)`) здесь `ε` вместо `ε²` и `c` вместо `n/γ`; при `c = k/γ`
(старая гипотеза, `anchorCover_of_anchor_cond`) порог больше в `√(32n/(εk))` раз. -/

/-- Порог фильтра `δ`-цепочки: `θ₀ = √(εV/(8c))`. -/
noncomputable def theta0B (ε V c : ℝ) : ℝ := Real.sqrt (ε * V / (8 * c))

lemma theta0B_nonneg {ε V c : ℝ} : 0 ≤ theta0B ε V c := Real.sqrt_nonneg _

lemma theta0B_sq {ε V c : ℝ} (hε : 0 ≤ ε) (hV : 0 ≤ V) (hc : 0 ≤ c) :
    theta0B ε V c ^ 2 = ε * V / (8 * c) :=
  Real.sq_sqrt (by positivity)

omit [DecidableEq ι] in
/-- **Узел, закрывающий шаг, в `δ`-цепочке.** В решётке с шагом
`s = 2√(ε_g·V/(K·C))`, `ε_g = ε/(32c)`, есть узел, в котором зазор носителя
оптимума не больше `θ₀²/2` при `θ₀ = √(εV/(8c))`, и фильтр порога `−θ₀`
допускает все его зажатые строки. Номера узлов ограничены
`√(K·C/(2ε_g)) + ½ = 4√(K·C·c/ε) + ½` — величиной без данных входа. -/
theorem exists_node_closing_step_block
    (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0) (hnormal : IsNormal a y S th)
    {ε V C c s : ℝ}
    (hC : (S.card * Fintype.card κ : ℝ) ≤ C) (hCpos : 0 < C)
    (hε : 0 < ε) (hc : 0 < c) (hV : 0 < V)
    (hVF : V ≤ phi a y S th) (hFV : phi a y S th ≤ 2 * V)
    (hKc : 0 < (Fintype.card κ : ℝ))
    (hs : s = 2 * Real.sqrt ((ε / (32 * c)) * V / ((Fintype.card κ : ℝ) * C)))
    (hself : ∀ i ∈ S, cl i → 0 ≤ y i - dotp (a i) th) :
    ∃ z : κ → ℤ,
      (∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C
        / (2 * (ε / (32 * c)))) + 1 / 2) ∧
      (∀ t : κ → ℝ, (∀ l, dotp (a (T l)) t = y (T l) + s * (z l : ℝ)) →
        phi a y S t - phi a y S th ≤ theta0B ε V c ^ 2 / 2
        ∧ (∀ i ∈ S, cl i → -theta0B ε V c ≤ y i - dotp (a i) t)) := by
  set εg : ℝ := ε / (32 * c) with hεg
  have hεgpos : 0 < εg := by rw [hεg]; positivity
  obtain ⟨z, hz1, hz2⟩ := exists_grid_node hmax hdet hnormal hC hCpos hεgpos hV hVF hFV hKc hs
  refine ⟨z, hz1, fun t ht => ?_⟩
  have hphi := hz2 t ht
  have hgap : phi a y S t - phi a y S th ≤ theta0B ε V c ^ 2 / 2 := by
    rw [theta0B_sq hε.le hV.le hc.le]
    have h1 : phi a y S t - phi a y S th ≤ εg * phi a y S th := by linarith
    have h2 : εg * phi a y S th ≤ εg * (2 * V) :=
      mul_le_mul_of_nonneg_left hFV hεgpos.le
    have h3 : εg * (2 * V) = ε * V / (8 * c) / 2 := by
      rw [hεg]; field_simp; ring
    linarith
  have hgap' : phi a y S t - phi a y S th ≤ theta0B ε V c ^ 2 := by
    have : (0:ℝ) ≤ theta0B ε V c ^ 2 := sq_nonneg _
    linarith
  exact ⟨hgap, node_filter_admits hnormal theta0B_nonneg hself hgap'⟩

end SparseSharpe.Factor
