import SparseSharpe.Factor.Rounding

set_option linter.style.header false

/-!
# Теорема W″: оценка через блок нарушителей, а не через якоря

Теорема W (`Stability.lean`) платит параметром `γ`, определённым условием
`γ·gram_S(v) ≤ gram_anch(v)`. Это условие можно переписать иначе: поскольку
`gram_S = gram_anch + gram_{зажатые}`, оно равносильно

    gram_{зажатые}(v)  ≤  (1 − γ)·gram_S(v)     при всех v      (`gram_clip_iff`)

то есть **`γ` — это блочное плечо всего множества зажатых строк**: в матричной
записи `γ = 1 − λ_max(H_CC)`, где `H = XΚ⁻¹Xᵀ` — шляпная матрица набора, а `C` —
строки-активы (проверено численно, `code/check_blockleverage.py`).

Но в доказательство входят не все зажатые строки, а только **нарушители** —
те, у кого невязка в рассматриваемой точке отрицательна. Остальные зажатые
строки ведут себя как незажатые. Поэтому `γ` можно заменить на блочное плечо
одного лишь множества нарушителей:

> **Теорема W″** (`psiC_ge_of_slack_block`). Пусть `r_i(t̂) ≥ −θ` у зажатых
> строк, `W ⊆ S` содержит всех нарушителей в точке `t`, и
> `gram_W(v) ≤ (1−δ)·gram_S(v)` при всех `v`. Тогда
>
>     ψ_S(t)  ≥  F(S) − |W|·θ²/δ .

Старая оценка — частный случай `W =` все зажатые строки, `δ = γ`
(`psiC_ge_of_slack_block_anchor`). Новая **никогда не хуже** (`W` меньше,
поэтому `δ ≥ γ`) и на инстансах, где `γ` рушится, лучше на порядки: в семействе
с `Σ_f = N⁴` — медиана выигрыша `2.4·10⁴`, в семействе с подложенным соседом по
корзине — `6.9·10⁴` (`code/check_blockleverage.py`).

Форма оценки тоже лучше старой: `|W|θ²/δ` против `|S|θ² + 4θ√(|S|F/γ)`.
При калибровке это даёт `θ ≤ √(εδF/|W|)` вместо `θ ≤ ε√(γF)/(8√|S|)` — порог
больше в `8/√ε` раз даже при `δ = γ`, то есть узлов меньше в `(8/√ε)^K` раз.

**Где предел.** Множество нарушителей зависит от точки, а `F_LO` — это минимум
по всем точкам, поэтому в оценку входит максимум `|W|/δ_W` по всем **достижимым**
множествам нарушителей `W = {i : r_i(t) < 0}`. Достижимых множеств не `2^M`, а
`O(M^K)` (знаковые паттерны набора гиперплоскостей), и максимум по ним часто
много меньше значения при `W =` все активы. Но если существует направление, вдоль
которого **все** невязки уходят в минус, то `W =` все активы достижимо, и
выигрыша нет. Это ровно тот сценарий, который §11.2 заметки 6 называет
«зажатая задача убегает».
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype κ]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {cl : ι → Bool} {S W : Finset ι} {t th : κ → ℝ}
variable {θ δ γ : ℝ}
variable [DecidableEq ι]

/-! ### `γ` — это блочное плечо множества зажатых строк -/

/-- Зажатые строки набора. -/
def clipSet (cl : ι → Bool) (S : Finset ι) : Finset ι := S.filter (fun i => cl i)

lemma clipSet_subset : clipSet cl S ⊆ S := Finset.filter_subset _ _

/-- Набор разбивается на зажатые и якорные строки. -/
lemma gram_split (a : ι → κ → ℝ) (cl : ι → Bool) (S : Finset ι) (v : κ → ℝ) :
    gram a S v = gram a (clipSet cl S) v + gram a (anchorSet cl S) v := by
  simp only [gram, clipSet, anchorSet]
  exact (Finset.sum_filter_add_sum_filter_not S (fun i => cl i)
    (fun i => (dotp (a i) v) ^ 2)).symm

/-- Условие Теоремы W на якоре равносильно оценке блочного плеча зажатых строк:

    γ·gram_S(v) ≤ gram_anch(v)   ⟺   gram_{зажатые}(v) ≤ (1−γ)·gram_S(v). -/
lemma gram_clip_iff (a : ι → κ → ℝ) (cl : ι → Bool) (S : Finset ι) (γ : ℝ) :
    (∀ v : κ → ℝ, γ * gram a S v ≤ gram a (anchorSet cl S) v)
      ↔ (∀ v : κ → ℝ, gram a (clipSet cl S) v ≤ (1 - γ) * gram a S v) := by
  constructor
  · intro h v
    have hv := h v
    have hs := gram_split a cl S v
    linarith
  · intro h v
    have hv := h v
    have hs := gram_split a cl S v
    linarith

/-! ### Поточечная оценка через блок нарушителей -/

/-- Потеря на одной строке: вне `W` её нет, внутри — не больше `(θ + |⟨a_i,v⟩|)²`. -/
lemma sq_sub_resC_le_block {i : ι} (hiS : i ∈ S)
    (hslack : ∀ j ∈ S, cl j → -θ ≤ y j - dotp (a j) th)
    (hviol : ∀ j ∈ S, cl j → y j - dotp (a j) t < 0 → j ∈ W) :
    (dotp (a i) t - y i) ^ 2 - resC a y cl i t ^ 2
      ≤ (if i ∈ W then (θ + |dotp (a i) (t - th)|) ^ 2 else 0) := by
  have hnn : (0:ℝ) ≤ (if i ∈ W then (θ + |dotp (a i) (t - th)|) ^ 2 else 0) := by
    by_cases h : i ∈ W
    · rw [if_pos h]; positivity
    · rw [if_neg h]
  by_cases hc : cl i
  · by_cases hpos : 0 ≤ y i - dotp (a i) t
    · have hres : resC a y cl i t = y i - dotp (a i) t := by
        simp only [resC, hc, ite_true, max_eq_left hpos]
      have hz : (dotp (a i) t - y i) ^ 2 - resC a y cl i t ^ 2 = 0 := by
        rw [hres]; ring
      rw [hz]; exact hnn
    · push_neg at hpos
      have hiW : i ∈ W := hviol i hiS hc hpos
      have hres : resC a y cl i t = 0 := by
        simp only [resC, hc, ite_true, max_eq_right hpos.le]
      rw [hres, if_pos hiW]
      have hsl := hslack i hiS hc
      have hd : dotp (a i) (t - th) = dotp (a i) t - dotp (a i) th := dotp_sub (a i) t th
      have habs : dotp (a i) (t - th) ≤ |dotp (a i) (t - th)| :=
        le_abs_self (dotp (a i) (t - th))
      have hle : dotp (a i) t - y i ≤ θ + |dotp (a i) (t - th)| := by linarith
      have hnn2 : (0:ℝ) ≤ dotp (a i) t - y i := by linarith
      have hsq : (dotp (a i) t - y i) ^ 2 ≤ (θ + |dotp (a i) (t - th)|) ^ 2 :=
        pow_le_pow_left₀ hnn2 hle 2
      simpa using hsq
  · have hres : resC a y cl i t = y i - dotp (a i) t := by
      simp only [resC, hc, Bool.false_eq_true, ite_false]
    have hz : (dotp (a i) t - y i) ^ 2 - resC a y cl i t ^ 2 = 0 := by
      rw [hres]; ring
    rw [hz]; exact hnn

/-- Суммарная потеря: `φ_S(t) − ψ_S(t) ≤ |W|θ² + 2θΣ_W|⟨a_i,v⟩| + gram_W(v)`. -/
theorem phi_sub_psiC_le_block (hWS : W ⊆ S)
    (hslack : ∀ j ∈ S, cl j → -θ ≤ y j - dotp (a j) th)
    (hviol : ∀ j ∈ S, cl j → y j - dotp (a j) t < 0 → j ∈ W) :
    phi a y S t - psiC a y cl S t
      ≤ (W.card : ℝ) * θ ^ 2
        + 2 * θ * (∑ i ∈ W, |dotp (a i) (t - th)|)
        + gram a W (t - th) := by
  have hterm : phi a y S t - psiC a y cl S t
      ≤ ∑ i ∈ S, (if i ∈ W then (θ + |dotp (a i) (t - th)|) ^ 2 else 0) := by
    rw [phi, psiC, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i hi =>
      sq_sub_resC_le_block (th := th) (W := W) hi hslack hviol
  have hsel : ∑ i ∈ S, (if i ∈ W then (θ + |dotp (a i) (t - th)|) ^ 2 else 0)
      = ∑ i ∈ W, (θ + |dotp (a i) (t - th)|) ^ 2 := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hWS]
  have hpt : ∀ i ∈ W, (θ + |dotp (a i) (t - th)|) ^ 2
      = θ ^ 2 + (2 * θ * |dotp (a i) (t - th)| + dotp (a i) (t - th) ^ 2) := by
    intro i _
    have hsq : |dotp (a i) (t - th)| ^ 2 = dotp (a i) (t - th) ^ 2 := sq_abs _
    nlinarith [hsq]
  have hexp : ∑ i ∈ W, (θ + |dotp (a i) (t - th)|) ^ 2
      = (W.card : ℝ) * θ ^ 2 + 2 * θ * (∑ i ∈ W, |dotp (a i) (t - th)|)
        + gram a W (t - th) := by
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, gram]
    ring
  rw [hsel, hexp] at hterm
  exact hterm

/-! ### Теорема W″ -/

/-- Неравенство о средних в форме `2√(xy) ≤ x + y`. -/
lemma two_sqrt_mul_le {x z : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) :
    2 * Real.sqrt (x * z) ≤ x + z := by
  have h1 : x * z ≤ ((x + z) / 2) ^ 2 := by nlinarith [sq_nonneg (x - z)]
  have h2 : Real.sqrt (x * z) ≤ (x + z) / 2 := by
    calc Real.sqrt (x * z) ≤ Real.sqrt (((x + z) / 2) ^ 2) := Real.sqrt_le_sqrt h1
      _ = (x + z) / 2 := Real.sqrt_sq (by linarith)
  linarith

/-- **Теорема W″.** Если зажатые строки почти самосогласованы (`r_i(t̂) ≥ −θ`),
все нарушители в точке `t` лежат в `W ⊆ S`, и блочное плечо `W` не больше
`1 − δ` (то есть `gram_W(v) ≤ (1−δ)·gram_S(v)` при всех `v`), то

    ψ_S(t)  ≥  F(S) − |W|·θ²/δ .

Старая оценка (`psiC_ge_of_slack_anchor`) — частный случай `W =` все зажатые
строки, `δ = γ` (см. `gram_clip_iff`). Новая никогда не хуже, потому что
`W` меньше, и лучше по форме: `|W|θ²/δ` против `|S|θ² + 4θ√(|S|F/γ)`. -/
theorem psiC_ge_of_slack_block
    (hnormal : IsNormal a y S th) (hθ : 0 ≤ θ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hWS : W ⊆ S)
    (hslack : ∀ j ∈ S, cl j → -θ ≤ y j - dotp (a j) th)
    (hviol : ∀ j ∈ S, cl j → y j - dotp (a j) t < 0 → j ∈ W)
    (hblock : ∀ v : κ → ℝ, gram a W v ≤ (1 - δ) * gram a S v) :
    phi a y S th - (W.card : ℝ) * θ ^ 2 / δ ≤ psiC a y cl S t := by
  set v : κ → ℝ := t - th with hv
  set g : ℝ := gram a S v with hg
  set p : ℝ := gram a W v with hp
  have hgnn : 0 ≤ g := gram_nonneg a S v
  have hpnn : 0 ≤ p := gram_nonneg a W v
  have hpg : p ≤ (1 - δ) * g := hblock v
  have hpyth : phi a y S t = phi a y S th + g := phi_eq_add hnormal t
  have hloss := phi_sub_psiC_le_block (th := th) (W := W) hWS hslack hviol
  have hcs : (∑ i ∈ W, |dotp (a i) v|) ≤ Real.sqrt ((W.card : ℝ) * p) :=
    sum_abs_le_sqrt_card_mul W (fun i => dotp (a i) v)
  have hsqnn : 0 ≤ Real.sqrt ((W.card : ℝ) * p) := Real.sqrt_nonneg _
  -- достаточно показать `2θ·√(|W|p) ≤ (g − p) + |W|θ²(1−δ)/δ`
  have hmain : 2 * θ * Real.sqrt ((W.card : ℝ) * p)
      ≤ (g - p) + (W.card : ℝ) * θ ^ 2 * (1 - δ) / δ := by
    rcases eq_or_lt_of_le hδ1 with hone | hlt
    · -- `δ = 1`: тогда `p ≤ 0`, значит `p = 0`
      have hp0 : p = 0 := le_antisymm (by rw [← hone] at hpg; simpa using hpg) hpnn
      rw [hp0, ← hone]
      simp only [mul_zero, Real.sqrt_zero, mul_zero, sub_zero, sub_self, mul_zero,
        zero_div, add_zero]
      linarith
    · -- `δ < 1`: неравенство о средних с `β = δ/(1−δ)`
      set β : ℝ := δ / (1 - δ) with hβ
      have h1δ : 0 < 1 - δ := by linarith
      have hβpos : 0 < β := by rw [hβ]; positivity
      have hx : 0 ≤ β * p := by positivity
      have hz : 0 ≤ (W.card : ℝ) * θ ^ 2 / β := by positivity
      have ham := two_sqrt_mul_le hx hz
      have heq : (β * p) * ((W.card : ℝ) * θ ^ 2 / β) = θ ^ 2 * ((W.card : ℝ) * p) := by
        field_simp; try ring
      rw [heq] at ham
      have hs : Real.sqrt (θ ^ 2 * ((W.card : ℝ) * p))
          = θ * Real.sqrt ((W.card : ℝ) * p) := by
        rw [Real.sqrt_mul (sq_nonneg θ), Real.sqrt_sq hθ]
      rw [hs] at ham
      -- `βp ≤ δg ≤ g − p`
      have hβp : β * p ≤ g - p := by
        have h1 : β * p ≤ β * ((1 - δ) * g) := by nlinarith [hβpos.le, hpg]
        have h2 : β * ((1 - δ) * g) = δ * g := by rw [hβ]; field_simp
        have h3 : δ * g ≤ g - p := by nlinarith [hpg, hgnn]
        linarith
      have hcoef : (W.card : ℝ) * θ ^ 2 / β = (W.card : ℝ) * θ ^ 2 * (1 - δ) / δ := by
        rw [hβ]; field_simp; try ring
      rw [hcoef] at ham
      linarith
  have hfin : (W.card : ℝ) * θ ^ 2 + (W.card : ℝ) * θ ^ 2 * (1 - δ) / δ
      = (W.card : ℝ) * θ ^ 2 / δ := by field_simp; try ring
  nlinarith [hloss, hpyth, hcs, hmain, hfin, hθ, hsqnn,
    mul_le_mul_of_nonneg_left hcs (by positivity : (0:ℝ) ≤ 2 * θ)]

/-- **Согласование гипотез** со старой формой. Якорное условие Теоремы W
(`γ·gram_S(v) ≤ gram_anch(v)`) — это в точности блочная оценка для
`W =` все зажатые строки с `δ = γ`, поэтому Теорема W″ применима всюду, где
применима Теорема W.

Важно: это согласование **гипотез**, а не переформулировка старого вывода.
Заключение здесь другое и более сильное — `|clipSet|·θ²/γ` вместо
`|S|θ² + 4θ√(|S|F/γ)` у `psiC_ge_of_slack_anchor`; у той, кроме того, есть
лишняя гипотеза `hanch` (`y = 0` на якорях), а здесь она не нужна. -/
theorem psiC_ge_of_slack_clipSet
    (hnormal : IsNormal a y S th) (hθ : 0 ≤ θ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hslack : ∀ j ∈ S, cl j → -θ ≤ y j - dotp (a j) th)
    (hcond : ∀ v : κ → ℝ, γ * gram a S v ≤ gram a (anchorSet cl S) v) :
    phi a y S th - ((clipSet cl S).card : ℝ) * θ ^ 2 / γ ≤ psiC a y cl S t := by
  refine psiC_ge_of_slack_block (W := clipSet cl S) hnormal hθ hγ hγ1 clipSet_subset
    hslack (fun j hj hc _ => ?_) ((gram_clip_iff a cl S γ).mp hcond)
  exact Finset.mem_filter.mpr ⟨hj, by simpa using hc⟩

/-! ### Калибровка и шаг динамики в терминах `δ`

Множество нарушителей зависит от точки, а `F_LO(S) = min_t ψ_S(t)` — это минимум
по всем точкам. Поэтому калибровка формулируется через **покрытие**: для каждой
точки `t'` должны найтись своё `W(t')` и своё `δ(t')`, причём калибровка
проверяется для каждой пары отдельно.

Важно, что `W` и `δ` берутся **поточечно**, а не общими на все точки: общая
пара `(c, δ)` требовала бы `c ≥ max|W|` и `δ ≤ min δ_W` независимо, а это до
двух раз хуже (численно — `code/check_blockleverage.py`). Поточечная форма
строго сильнее и совпадает с тем, что меряется численно.

Старая якорная форма — частный случай `W ≡` все зажатые строки, `δ = γ`;
тогда покрытие тривиально (одно и то же `W` годится всюду). Выигрыш возникает,
когда достижимые множества нарушителей меньше: их `O(M^K)` штук, а не `2^M`
(это знаковые паттерны набора гиперплоскостей `⟨a_i,t⟩ = y_i`).
-/

/-- **Покрытие нарушителей с готовой калибровкой.** Для каждой точки `t'`
найдётся блок `W`, содержащий её нарушителей, с блочным плечом `≤ 1 − d` и
уже проверенной калибровкой `|W|·θ²/d ≤ B`. -/
def CoveredBy (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (S : Finset ι)
    (θ B : ℝ) : Prop :=
  ∀ t' : κ → ℝ, ∃ (W : Finset ι) (d : ℝ), W ⊆ S ∧ 0 < d ∧ d ≤ 1
    ∧ (∀ j ∈ S, cl j → y j - dotp (a j) t' < 0 → j ∈ W)
    ∧ (∀ v : κ → ℝ, gram a W v ≤ (1 - d) * gram a S v)
    ∧ (W.card : ℝ) * θ ^ 2 / d ≤ B

/-- **Калибровка в терминах `δ`.** Если нарушители покрыты блоками с калибровкой
`|W|θ²/d ≤ εF`, то `F_LO(S) ≥ (1−ε)·F(S)`.

Сравнение со старой формой `psiC_ge_one_sub_eps` (`64|S|θ² ≤ ε²γF`): при
`W =` все зажатые строки и `d = γ` здесь требуется лишь `|S|θ² ≤ εγF`, то есть
порог больше в `8/√ε` раз. -/
theorem psiC_ge_one_sub_eps_cover
    (hnormal : IsNormal a y S th) (hθ : 0 ≤ θ)
    (hslack : ∀ i ∈ S, cl i → -θ ≤ y i - dotp (a i) th)
    (hcov : CoveredBy a y cl S θ (ε * phi a y S th)) (t' : κ → ℝ) :
    (1 - ε) * phi a y S th ≤ psiC a y cl S t' := by
  obtain ⟨W, d, hWS, hd, hd1, hviol, hblock, hcal⟩ := hcov t'
  have hmain := psiC_ge_of_slack_block (W := W) (δ := d) (t := t') hnormal hθ hd hd1
    hWS hslack hviol hblock
  linarith

/-- Удобная форма с общими границами `c` и `δ`: она слабее поточечной, но её
проще предъявлять. -/
theorem coveredBy_of_uniform {c : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {B : ℝ}
    (hcover : ∀ t' : κ → ℝ, ∃ W : Finset ι, W ⊆ S ∧ (W.card : ℝ) ≤ c
      ∧ (∀ j ∈ S, cl j → y j - dotp (a j) t' < 0 → j ∈ W)
      ∧ (∀ v : κ → ℝ, gram a W v ≤ (1 - δ) * gram a S v))
    (hθ : 0 ≤ θ) (hcal : c * θ ^ 2 / δ ≤ B) :
    CoveredBy a y cl S θ B := by
  intro t'
  obtain ⟨W, hWS, hWc, hviol, hblock⟩ := hcover t'
  refine ⟨W, δ, hWS, hδ, hδ1, hviol, hblock, le_trans ?_ hcal⟩
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hWc (sq_nonneg θ)) hδ.le

/-- **Замена полна.** Старая якорная гипотеза Теоремы W всегда даёт покрытие:
годится одно и то же `W ≡ clipSet cl S` с `d = γ`. Значит утверждения в терминах
`δ` применимы всюду, где применимы их якорные предшественники, — цепочку можно
переводить на `δ` целиком, ничего не теряя. -/
theorem coveredBy_of_anchor_cond (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hθ : 0 ≤ θ) {B : ℝ}
    (hcond : ∀ v : κ → ℝ, γ * gram a S v ≤ gram a (anchorSet cl S) v)
    (hcal : ((clipSet cl S).card : ℝ) * θ ^ 2 / γ ≤ B) :
    CoveredBy a y cl S θ B :=
  coveredBy_of_uniform (c := ((clipSet cl S).card : ℝ)) hγ hγ1
    (fun _ => ⟨clipSet cl S, clipSet_subset, le_rfl,
      fun j hj hc _ => Finset.mem_filter.mpr ⟨hj, by simpa using hc⟩,
      (gram_clip_iff a cl S γ).mp hcond⟩) hθ hcal

/-- **Шаг динамики в терминах `δ` (Теорема Y″).** Тот же вывод, что у
`psiC_ge_of_bucket_node_slack`, но калибровка идёт через блочное плечо
нарушителей, а не через обусловленность якоря. Гипотеза `y = 0` на якорях
набора `R` здесь не нужна вовсе. -/
theorem psiC_ge_of_bucket_node_slack_block {thS thR : κ → ℝ} {R : Finset ι}
    {θ₀ : ℝ}
    (hQ : phi a y S t ≤ phi a y R t)
    (hMom : ∀ v, mom a y R t v = mom a y S t v)
    (hKeq : ∀ v, gram a R v = gram a S v)
    (hnormS : IsNormal a y S thS) (hnormR : IsNormal a y R thR)
    (hθ₀ : 0 ≤ θ₀) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfilterR : ∀ i ∈ R, cl i → -θ₀ ≤ y i - dotp (a i) t)
    (hgapS : phi a y S t - phi a y S thS ≤ θ₀ ^ 2)
    (hcov : CoveredBy a y cl R (2 * θ₀) (ε * phi a y R thR))
    (t' : κ → ℝ) :
    (1 - ε) * phi a y S thS ≤ psiC a y cl R t' := by
  have hgapR : phi a y R t - phi a y R thR = phi a y S t - phi a y S thS :=
    gap_eq_of_bucket hMom hKeq hnormS hnormR
  have hgapR' : phi a y R t - phi a y R thR ≤ θ₀ ^ 2 := by rw [hgapR]; exact hgapS
  have hslackR := slack_of_node_slack (S := R) (th := thR) (t := t) hnormR hθ₀
    hfilterR hgapR'
  have hSR : phi a y S thS ≤ phi a y R thR :=
    phi_normal_le_of_bucket hQ hMom (fun v => le_of_eq (hKeq v).symm) hnormS
  have hmain := psiC_ge_one_sub_eps_cover (S := R) (th := thR) (θ := 2 * θ₀)
    hnormR (by linarith) hslackR hcov t'
  nlinarith [hmain, hSR, hε1]

/-- Следствие: Теорема Y″ покрывает Теорему Y. Гипотезы — старые, калибровка
`|clipSet|·(2θ₀)²/γ ≤ εF` слабее старой `256|R|θ₀² ≤ ε²γF` в `64/ε` раз. -/
theorem psiC_ge_of_bucket_node_slack_anchor' {thS thR : κ → ℝ} {R : Finset ι}
    {θ₀ : ℝ}
    (hQ : phi a y S t ≤ phi a y R t)
    (hMom : ∀ v, mom a y R t v = mom a y S t v)
    (hKeq : ∀ v, gram a R v = gram a S v)
    (hnormS : IsNormal a y S thS) (hnormR : IsNormal a y R thR)
    (hθ₀ : 0 ≤ θ₀) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcondR : ∀ v : κ → ℝ, γ * gram a R v ≤ gram a (anchorSet cl R) v)
    (hfilterR : ∀ i ∈ R, cl i → -θ₀ ≤ y i - dotp (a i) t)
    (hgapS : phi a y S t - phi a y S thS ≤ θ₀ ^ 2)
    (hcal : ((clipSet cl R).card : ℝ) * (2 * θ₀) ^ 2 / γ ≤ ε * phi a y R thR)
    (t' : κ → ℝ) :
    (1 - ε) * phi a y S thS ≤ psiC a y cl R t' :=
  psiC_ge_of_bucket_node_slack_block hQ hMom hKeq hnormS hnormR hθ₀ hε hε1
    hfilterR hgapS (coveredBy_of_anchor_cond hγ hγ1 (by linarith) hcondR hcal) t'

/-! ### Теорема Z″: округлённый ключ в терминах `δ` -/

/-- **Теорема Z″.** То же, что `psiC_ge_of_approxBucket`, но калибровка идёт
через блочное плечо нарушителей. Это та форма, которой пользуется динамика:
ключ у неё округлён, поэтому соседи по корзине лишь приближённые. -/
theorem psiC_ge_of_approxBucket_block {thS thR : κ → ℝ} {R : Finset ι}
    {θ₀ η ζ : ℝ}
    (hb : ApproxBucket a y S R t η ζ)
    (hnormS : IsNormal a y S thS) (hnormR : IsNormal a y R thR)
    (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hζ2 : 2 * ζ < 1)
    (hθ₀ : 0 ≤ θ₀) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfilterR : ∀ i ∈ R, cl i → -θ₀ ≤ y i - dotp (a i) t)
    (hgapS : (phi a y S t - phi a y S thS)
      + bucketErr η ζ (phi a y S t - phi a y S thS) ≤ θ₀ ^ 2)
    (hcov : CoveredBy a y cl R (2 * θ₀) (ε * phi a y R thR))
    (t' : κ → ℝ) :
    (1 - ε) * (phi a y S thS - bucketErr η ζ (phi a y S t - phi a y S thS))
      ≤ psiC a y cl R t' := by
  have hgapR : phi a y R t - phi a y R thR ≤ θ₀ ^ 2 :=
    le_trans (gap_le_of_approxBucket hb hη hζ hζ2 hnormS hnormR) hgapS
  have hslackR := slack_of_node_slack (S := R) (th := thR) (t := t) hnormR hθ₀
    hfilterR hgapR
  have hSR := phi_normal_ge_of_approxBucket' hb hη hζ hζ2 hnormS hnormR
  have hmain := psiC_ge_one_sub_eps_cover (S := R) (th := thR) (θ := 2 * θ₀)
    hnormR (by linarith) hslackR hcov t'
  nlinarith [hmain, hSR, hε1]

/-- **Теорема Z″, итоговая форма:** `F_LO(R) ≥ (1 − 2ε)·F(S̄)`. Это то самое
утверждение, из которого собирается сквозная гарантия, — теперь без `γ`. -/
theorem psiC_ge_of_approxBucket_calibrated_block {thS thR : κ → ℝ} {R : Finset ι}
    {θ₀ η ζ : ℝ}
    (hb : ApproxBucket a y S R t η ζ)
    (hnormS : IsNormal a y S thS) (hnormR : IsNormal a y R thR)
    (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hζ2 : 2 * ζ < 1)
    (hθ₀ : 0 ≤ θ₀) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfilterR : ∀ i ∈ R, cl i → -θ₀ ≤ y i - dotp (a i) t)
    (hgapS : (phi a y S t - phi a y S thS)
      + bucketErr η ζ (phi a y S t - phi a y S thS) ≤ θ₀ ^ 2)
    (hcov : CoveredBy a y cl R (2 * θ₀) (ε * phi a y R thR))
    (hErr : bucketErr η ζ (phi a y S t - phi a y S thS) ≤ ε * phi a y S thS)
    (t' : κ → ℝ) :
    (1 - 2 * ε) * phi a y S thS ≤ psiC a y cl R t' := by
  have hmain := psiC_ge_of_approxBucket_block hb hnormS hnormR hη hζ hζ2 hθ₀
    hε hε1 hfilterR hgapS hcov t'
  have hg0 : 0 ≤ phi a y S t - phi a y S thS := by
    have := phi_min hnormS t; linarith
  have herr0 : 0 ≤ bucketErr η ζ (phi a y S t - phi a y S thS) :=
    bucketErr_nonneg hη hζ hζ2 hg0
  nlinarith [hmain, hErr, hε, hε1, phi_nonneg a y S thS, herr0]

/-- Точная корзина — частный случай Теоремы Z″ с `η = ζ = 0`: тогда
`bucketErr = 0`, и утверждение превращается в Теорему Y″. Самопроверка: обе
формулировки совпадают. -/
theorem psiC_ge_of_bucket_node_slack_block' {thS thR : κ → ℝ} {R : Finset ι}
    {θ₀ : ℝ}
    (hQ : phi a y S t ≤ phi a y R t)
    (hMom : ∀ v, mom a y R t v = mom a y S t v)
    (hKeq : ∀ v, gram a R v = gram a S v)
    (hnormS : IsNormal a y S thS) (hnormR : IsNormal a y R thR)
    (hθ₀ : 0 ≤ θ₀) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfilterR : ∀ i ∈ R, cl i → -θ₀ ≤ y i - dotp (a i) t)
    (hgapS : phi a y S t - phi a y S thS ≤ θ₀ ^ 2)
    (hcov : CoveredBy a y cl R (2 * θ₀) (ε * phi a y R thR))
    (t' : κ → ℝ) :
    (1 - ε) * phi a y S thS ≤ psiC a y cl R t' := by
  have hb := approxBucket_of_exact hQ hMom hKeq
  have hz := psiC_ge_of_approxBucket_block (η := 0) (ζ := 0) hb hnormS hnormR
    le_rfl le_rfl (by norm_num) hθ₀ hε hε1 hfilterR
    (by rw [bucketErr_zero]; linarith) hcov t'
  rw [bucketErr_zero] at hz
  simp only [sub_zero] at hz
  linarith

/-! ### Непустота: полный инстанс, где усиление существенно

Три строки с одинаковой нагрузкой `a = 1` в `ℝ¹`: якорная (`y = 0`) и две
зажатые с `y = −1` и `y = 5`. Неподвижная точка `t̂ = 4/3`, невязки там
`−4/3`, `−7/3`, `11/3`, поэтому годится `θ = 7/3`. В точке `t = 0` нарушитель
**один** — строка `1` (её невязка `−1 < 0`), у строки `2` невязка `5 > 0`.

Грамовы формы: `gram_S(v) = 3v²`, у всех зажатых строк `2v²` (значит
`γ ≤ 1/3`), у одной строки `1` — `v²` (значит годится `δ = 2/3`).

Итог: Теорема W″ с `W = {1}`, `δ = 2/3` даёт содержательную оценку
`ψ_S(0) ≥ 62/3 − 49/6 = 12.5` (и действительно `ψ_S(0) = 25`), тогда как та же
теорема с `W =` все зажатые строки и `δ = γ = 1/3` даёт `62/3 − 98/3 = −12`,
то есть **пусто**. Усиление меняет содержательность оценки, а не только
константу. -/

private def aB : Fin 3 → Fin 1 → ℝ := fun _ _ => 1
private def yB : Fin 3 → ℝ := fun i => if i = 1 then -1 else if i = 2 then 5 else 0
private def clB : Fin 3 → Bool := fun i => decide (i ≠ 0)
private noncomputable def thB : Fin 1 → ℝ := fun _ => 4 / 3
private def tB : Fin 1 → ℝ := fun _ => 0

private lemma dotpB (i : Fin 3) (v : Fin 1 → ℝ) : dotp (aB i) v = v 0 := by
  simp [dotp, aB]

private lemma normalB : IsNormal aB yB (Finset.univ : Finset (Fin 3)) thB := by
  intro v
  simp only [mom, Fin.sum_univ_three, dotpB, yB, thB]
  norm_num
  ring

private lemma slackB : ∀ j ∈ (Finset.univ : Finset (Fin 3)), clB j →
    -(7/3 : ℝ) ≤ yB j - dotp (aB j) thB := by
  intro j _ _
  fin_cases j <;> simp [dotpB, yB, thB] <;> norm_num

private lemma violB : ∀ j ∈ (Finset.univ : Finset (Fin 3)), clB j →
    yB j - dotp (aB j) tB < 0 → j ∈ ({1} : Finset (Fin 3)) := by
  intro j _ _ hlt
  fin_cases j
  · simp [dotpB, yB, tB] at hlt
  · simp
  · simp only [dotpB, yB, tB] at hlt; norm_num at hlt

private lemma blockB : ∀ v : Fin 1 → ℝ,
    gram aB ({1} : Finset (Fin 3)) v
      ≤ (1 - 2/3) * gram aB (Finset.univ : Finset (Fin 3)) v := by
  intro v
  simp only [gram, Finset.sum_singleton, Fin.sum_univ_three, dotpB]
  nlinarith [sq_nonneg (v 0)]

private lemma phiB : phi aB yB (Finset.univ : Finset (Fin 3)) thB = 62 / 3 := by
  simp only [phi, Fin.sum_univ_three, dotpB, yB, thB]
  norm_num

private lemma psiB : psiC aB yB clB (Finset.univ : Finset (Fin 3)) tB = 25 := by
  simp only [psiC, Fin.sum_univ_three, resC, clB, dotpB, yB, tB]
  norm_num

/-- **Теорема W″ на этом инстансе даёт содержательную оценку.** Все её гипотезы
проверены выше; вывод — `12.5 ≤ ψ_S(0)`, и это правда (`ψ_S(0) = 25`). -/
example : (25 : ℝ) / 2 ≤ psiC aB yB clB (Finset.univ : Finset (Fin 3)) tB := by
  have h := psiC_ge_of_slack_block (a := aB) (y := yB) (cl := clB)
    (S := (Finset.univ : Finset (Fin 3))) (W := ({1} : Finset (Fin 3)))
    (t := tB) (th := thB) (θ := 7/3) (δ := 2/3)
    normalB (by norm_num) (by norm_num) (by norm_num) (Finset.subset_univ _)
    slackB violB blockB
  rw [phiB] at h
  norm_num at h
  linarith

/-- А та же теорема с `W =` все зажатые строки и `δ = γ = 1/3` даёт `−12`,
то есть **пусто**: усиление меняет содержательность оценки, а не только
константу. -/
example : (62 : ℝ) / 3 - 2 * (7/3) ^ 2 / (1/3) = -12 := by norm_num

end SparseSharpe.Factor
