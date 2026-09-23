import SparseSharpe.Factor.Stability

set_option linter.style.header false

/-!
# Приближённые соседи по корзине: Теорема Y для округлённого ключа

Теоремы U и Y доказаны для **точных** соседей по корзине (`mom` и `gram`
совпадают в точности). Динамика хранит ключ округлённым, поэтому соседи
приближённые. Здесь это исправлено.

Допуск записан в **безразмерной** форме:

    |mom_R(t,v) − mom_S(t,v)| ≤ η·√(gram_S(v)),     |gram_R(v) − gram_S(v)| ≤ ζ·gram_S(v).

Это ровно то, что даёт округление ключа в координатах максимально-объёмной
`K`-ки: там `M` хранится как набор `K` чисел `M_l`, спаренных со строками
`a_{T_l}`, и `mom(t,v) = Σ_l M_l⟨a_{T_l},v⟩`; так как `⟨a_{T_l},v⟩² ≤ gram_S(v)`
для строк набора (`sq_dotp_le_gram`), округление `M` с шагом `η₀` даёт
`η = √K·η₀`, а округление `Κ` с шагом `ξ₀` даёт `ζ = K·ξ₀` — это доказано в
`Factor/KeyRounding.lean` (`approxBucket_of_keyOf_eq`). Абсолютных величин
входа в этих константах нет.

Главные утверждения:

* `phi_ge_of_approxBucket` — поточечно `φ_R ≥ φ_S − 2η√(gram_S) − ζ·gram_S`;
* `phi_normal_ge_of_approxBucket` — по значениям `F(R) ≥ F(S̄) − err`;
* `gap_le_of_approxBucket` — зазор переносится: `gap_R ≤ gap_S + err`;
* `psiC_ge_of_approxBucket` — Теорема Y целиком для округлённого ключа,

где

    err(η,ζ,g) = 2η²/(1−2ζ) + 2√2·η·√g + 2ζ·g,   g = gap_S = Q_t(S̄) − F(S̄).

При `η, ζ → 0` получается `err → 0` и старые точные утверждения. Обе
добавки устроены так, как и должно быть: квадратичная по `η` часть — цена
неопределённости первого момента, линейная по `ζ` — цена неопределённости
формы Грама, а перекрёстный член `η√g` исчезает вместе с зазором узла.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype κ]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {cl : ι → Bool} {S R : Finset ι}
variable {t thS thR : κ → ℝ} {η ζ ε γ : ℝ}

/-! ### Вспомогательное -/

lemma sqrt_add_le_of_nonneg {x z : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) :
    Real.sqrt (x + z) ≤ Real.sqrt x + Real.sqrt z := by
  have h : x + z ≤ (Real.sqrt x + Real.sqrt z) ^ 2 := by
    have hx' := Real.sq_sqrt hx
    have hz' := Real.sq_sqrt hz
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg z,
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg z)]
  calc Real.sqrt (x + z) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt z) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt x + Real.sqrt z :=
        Real.sqrt_sq (by positivity)

/-- Неравенство Юнга в нужной форме: `2√2·η·√W ≤ (1−2ζ)W + 2η²/(1−2ζ)`. -/
lemma young_sqrt {W c η : ℝ} (hW : 0 ≤ W) (hc : 0 < c) :
    2 * Real.sqrt 2 * η * Real.sqrt W ≤ c * W + 2 * η ^ 2 / c := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsW : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW
  have hexp : c * W + 2 * η ^ 2 / c - 2 * Real.sqrt 2 * η * Real.sqrt W
      = (c * Real.sqrt W - Real.sqrt 2 * η) ^ 2 / c := by
    field_simp
    nlinarith [hs2, hsW]
  have hpos : 0 ≤ (c * Real.sqrt W - Real.sqrt 2 * η) ^ 2 / c :=
    div_nonneg (sq_nonneg _) hc.le
  linarith [hexp, hpos]

/-! ### Приближённая корзина -/

/-- **Приближённые соседи по корзине.** `R` вытеснил `S` (значение в узле не
меньше), а первый момент и форма Грама совпадают с точностью `η` и `ζ`. -/
structure ApproxBucket (a : ι → κ → ℝ) (y : ι → ℝ) (S R : Finset ι) (t : κ → ℝ)
    (η ζ : ℝ) : Prop where
  /-- Вытеснение: значение в узле у `R` не меньше. -/
  Q : phi a y S t ≤ phi a y R t
  /-- Первый момент совпадает с точностью `η` (в безразмерной форме). -/
  mom : ∀ v, |mom a y R t v - mom a y S t v| ≤ η * Real.sqrt (gram a S v)
  /-- Форма Грама совпадает с относительной точностью `ζ`. -/
  gram : ∀ v, |gram a R v - gram a S v| ≤ ζ * gram a S v

/-- Цена округления ключа. -/
noncomputable def bucketErr (η ζ g : ℝ) : ℝ :=
  2 * η ^ 2 / (1 - 2 * ζ) + 2 * Real.sqrt 2 * η * Real.sqrt g + 2 * ζ * g

lemma bucketErr_nonneg {g : ℝ} (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hζ2 : 2 * ζ < 1) (hg : 0 ≤ g) :
    0 ≤ bucketErr η ζ g := by
  have h1 : (0:ℝ) ≤ 2 * η ^ 2 / (1 - 2 * ζ) := by
    apply div_nonneg (by positivity); linarith
  have h2 : (0:ℝ) ≤ 2 * Real.sqrt 2 * η * Real.sqrt g := by positivity
  have h3 : (0:ℝ) ≤ 2 * ζ * g := by positivity
  simp only [bucketErr]; linarith

/-- **Поточечно.** Разность `φ_R − φ_S` во всякой точке не меньше своей
величины в узле минус цена округления. Вытеснение (`hb.Q`) здесь не нужно —
оно добавится в следствиях. -/
theorem phi_ge_of_approxBucket (hb : ApproxBucket a y S R t η ζ) (v : κ → ℝ) :
    phi a y S (t + v) + (phi a y R t - phi a y S t)
        - 2 * η * Real.sqrt (gram a S v) - ζ * gram a S v
      ≤ phi a y R (t + v) := by
  have hR := phi_shift a y R t v
  have hS := phi_shift a y S t v
  have hm := abs_le.mp (hb.mom v)
  have hg := abs_le.mp (hb.gram v)
  rw [hR, hS]
  linarith [hm.1, hm.2, hg.1, hg.2]

/-- **По значениям, с сохранением вытеснения.**
`F(R) ≥ F(S̄) + (Q_t(R) − Q_t(S̄)) − err`. -/
theorem phi_normal_ge_of_approxBucket (hb : ApproxBucket a y S R t η ζ)
    (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hζ2 : 2 * ζ < 1)
    (hnormS : IsNormal a y S thS) (hnormR : IsNormal a y R thR) :
    phi a y S thS + (phi a y R t - phi a y S t)
      - bucketErr η ζ (phi a y S t - phi a y S thS) ≤ phi a y R thR := by
  set g : ℝ := phi a y S t - phi a y S thS with hgdef
  have hgram_g : gram a S (t - thS) = g := by rw [hgdef, phi_eq_add hnormS t]; ring
  have hg0 : 0 ≤ g := by rw [← hgram_g]; exact gram_nonneg _ _ _
  set W : ℝ := gram a S (thR - thS) with hWdef
  have hW0 : 0 ≤ W := gram_nonneg _ _ _
  -- разложение в точке `thR`
  have hid : t + (thR - t) = thR := by abel
  have hpt := phi_ge_of_approxBucket hb (thR - t)
  rw [hid] at hpt
  have hphiS : phi a y S thR = phi a y S thS + W := by
    rw [phi_eq_add hnormS thR, hWdef]
  -- `gram_S(thR − t) ≤ 2W + 2g`
  have hsplit : gram a S (thR - t) ≤ 2 * W + 2 * g := by
    have hsub : (thR - thS) - (t - thS) = thR - t := by abel
    have := gram_sub_le a S (thR - thS) (t - thS)
    rw [hsub, hgram_g] at this
    linarith
  have hgramnn : 0 ≤ gram a S (thR - t) := gram_nonneg _ _ _
  -- корень
  have hsq : Real.sqrt (gram a S (thR - t)) ≤ Real.sqrt 2 * (Real.sqrt W + Real.sqrt g) := by
    calc Real.sqrt (gram a S (thR - t)) ≤ Real.sqrt (2 * (W + g)) := by
          apply Real.sqrt_le_sqrt; linarith
      _ = Real.sqrt 2 * Real.sqrt (W + g) := Real.sqrt_mul (by norm_num) _
      _ ≤ Real.sqrt 2 * (Real.sqrt W + Real.sqrt g) := by
          have := sqrt_add_le_of_nonneg hW0 hg0
          nlinarith [Real.sqrt_nonneg 2]
  -- Юнг
  have hyoung : 2 * Real.sqrt 2 * η * Real.sqrt W ≤ (1 - 2 * ζ) * W + 2 * η ^ 2 / (1 - 2 * ζ) :=
    young_sqrt hW0 (by linarith)
  have hmul : 2 * η * Real.sqrt (gram a S (thR - t))
      ≤ 2 * Real.sqrt 2 * η * Real.sqrt W + 2 * Real.sqrt 2 * η * Real.sqrt g := by
    have h2 := mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ 2 * η)
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg W, Real.sqrt_nonneg g]
  have hzeta : ζ * gram a S (thR - t) ≤ 2 * ζ * W + 2 * ζ * g := by
    nlinarith [hsplit, hζ]
  have hfin : phi a y S thS + (phi a y R t - phi a y S t) - bucketErr η ζ g
      ≤ phi a y S thR + (phi a y R t - phi a y S t)
        - 2 * η * Real.sqrt (gram a S (thR - t)) - ζ * gram a S (thR - t) := by
    rw [hphiS]
    simp only [bucketErr]
    linarith
  linarith

/-- **`F(R) ≥ F(S̄) − err`.** Вытеснивший набор не хуже вытесненного с точностью
до цены округления. -/
theorem phi_normal_ge_of_approxBucket' (hb : ApproxBucket a y S R t η ζ)
    (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hζ2 : 2 * ζ < 1)
    (hnormS : IsNormal a y S thS) (hnormR : IsNormal a y R thR) :
    phi a y S thS - bucketErr η ζ (phi a y S t - phi a y S thS) ≤ phi a y R thR := by
  have h := phi_normal_ge_of_approxBucket hb hη hζ hζ2 hnormS hnormR
  linarith [hb.Q]

/-- **Перенос зазора.** `gap_R ≤ gap_S + err`. Это приближённая форма
`gap_eq_of_bucket`: сертификат по-прежнему достаточно проверять у `S̄`. -/
theorem gap_le_of_approxBucket (hb : ApproxBucket a y S R t η ζ)
    (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hζ2 : 2 * ζ < 1)
    (hnormS : IsNormal a y S thS) (hnormR : IsNormal a y R thR) :
    phi a y R t - phi a y R thR
      ≤ (phi a y S t - phi a y S thS)
        + bucketErr η ζ (phi a y S t - phi a y S thS) := by
  have hmain := phi_normal_ge_of_approxBucket hb hη hζ hζ2 hnormS hnormR
  linarith

/-! ### Теорема Y для округлённого ключа -/

/-- **Шаг динамики при округлённом ключе.** Всё как в
`psiC_ge_of_bucket_node_slack`, но соседи по корзине приближённые: моменты и
формы Грама совпадают с точностью `η` и `ζ`. Условие на зазор проверяется
по-прежнему у `S̄` — с добавкой `err`. -/
theorem psiC_ge_of_approxBucket {θ₀ : ℝ}
    (hb : ApproxBucket a y S R t η ζ)
    (hnormS : IsNormal a y S thS) (hnormR : IsNormal a y R thR)
    (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hζ2 : 2 * ζ < 1)
    (hθ₀ : 0 ≤ θ₀) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hanchR : ∀ i ∈ R, ¬ cl i → y i = 0)
    (hcondR : ∀ v : κ → ℝ, γ * gram a R v ≤ gram a (anchorSet cl R) v)
    (hfilterR : ∀ i ∈ R, cl i → -θ₀ ≤ y i - dotp (a i) t)
    (hgapS : (phi a y S t - phi a y S thS)
      + bucketErr η ζ (phi a y S t - phi a y S thS) ≤ θ₀ ^ 2)
    (hcal : 256 * (R.card : ℝ) * θ₀ ^ 2 ≤ ε ^ 2 * γ * phi a y R thR)
    (t' : κ → ℝ) :
    (1 - ε) * (phi a y S thS - bucketErr η ζ (phi a y S t - phi a y S thS))
      ≤ psiC a y cl R t' := by
  have hgapR : phi a y R t - phi a y R thR ≤ θ₀ ^ 2 :=
    le_trans (gap_le_of_approxBucket hb hη hζ hζ2 hnormS hnormR) hgapS
  have hslackR := slack_of_node_slack (S := R) (th := thR) (t := t) hnormR hθ₀ hfilterR hgapR
  have hSR := phi_normal_ge_of_approxBucket' hb hη hζ hζ2 hnormS hnormR
  have hmain := psiC_ge_one_sub_eps (S := R) (th := thR) (θ := 2 * θ₀) hnormR
    (by linarith) hγ hγ1 hε hε1 hanchR hcondR hslackR (by nlinarith [hcal]) t'
  nlinarith [hmain, hSR, hε1]

/-- **Цена округления мала при простом условии на допуски.**
`err ≤ 6η² + (3/2)g` при `ζ ≤ 1/4`, поэтому достаточно `12η² ≤ εF` и `3g ≤ εF`.
Второе выполняется автоматически: зазор узла в калибровке Теоремы Y и так
не больше `ε²γF/(256|R|)`. Значит единственное требование к округлению —
`η ≤ √(εF/12)`, то есть тот же порядок, что и в безусловной динамике. -/
theorem bucketErr_le_of_small {g F : ℝ} (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hζ4 : ζ ≤ 1/4)
    (hg : 0 ≤ g) (hηF : 12 * η ^ 2 ≤ ε * F) (hgF : 3 * g ≤ ε * F) :
    bucketErr η ζ g ≤ ε * F := by
  have hden : (0:ℝ) < 1 - 2 * ζ := by linarith
  have h1 : 2 * η ^ 2 / (1 - 2 * ζ) ≤ 4 * η ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg η]
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsg : Real.sqrt g ^ 2 = g := Real.sq_sqrt hg
  have h2 : 2 * Real.sqrt 2 * η * Real.sqrt g ≤ 2 * η ^ 2 + g := by
    nlinarith [sq_nonneg (Real.sqrt 2 * η - Real.sqrt g), hs2, hsg]
  have h3 : 2 * ζ * g ≤ g / 2 := by nlinarith
  simp only [bucketErr]
  linarith

/-- **Явное правило округления.** При `8η ≤ θ` и `ζ ≤ 1/8` цена округления
не съедает больше половины запаса `θ²`: `bucketErr η ζ g ≤ θ²/2` для любого
`g ≤ θ²/2`. Оценка `5θ²/12 ≤ θ²/2` — с запасом. -/
theorem bucketErr_le_half {g θ : ℝ} (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hθ : 0 ≤ θ)
    (hηθ : 8 * η ≤ θ) (hζ8 : ζ ≤ 1/8) (hg : 0 ≤ g) (hgθ : g ≤ θ ^ 2 / 2) :
    bucketErr η ζ g ≤ θ ^ 2 / 2 := by
  have hden : (0:ℝ) < 1 - 2 * ζ := by linarith
  have h1 : 2 * η ^ 2 / (1 - 2 * ζ) ≤ θ ^ 2 / 24 := by
    rw [div_le_div_iff₀ hden (by norm_num)]
    nlinarith [sq_nonneg η, sq_nonneg θ, hηθ, hζ, hη]
  have hsqrt : Real.sqrt 2 * Real.sqrt g ≤ θ := by
    have h2 : Real.sqrt g ≤ Real.sqrt (θ ^ 2 / 2) := Real.sqrt_le_sqrt hgθ
    have h3 : Real.sqrt 2 * Real.sqrt (θ ^ 2 / 2) = θ := by
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      have : (2:ℝ) * (θ ^ 2 / 2) = θ ^ 2 := by ring
      rw [this, Real.sqrt_sq hθ]
    calc Real.sqrt 2 * Real.sqrt g ≤ Real.sqrt 2 * Real.sqrt (θ ^ 2 / 2) := by
          exact mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 2)
      _ = θ := h3
  have h2 : 2 * Real.sqrt 2 * η * Real.sqrt g ≤ θ ^ 2 / 4 := by
    have hstep : 2 * Real.sqrt 2 * η * Real.sqrt g = 2 * η * (Real.sqrt 2 * Real.sqrt g) := by
      ring
    rw [hstep]
    have : 2 * η * (Real.sqrt 2 * Real.sqrt g) ≤ 2 * η * θ :=
      mul_le_mul_of_nonneg_left hsqrt (by linarith)
    nlinarith [hηθ, hη, hθ]
  have h3 : 2 * ζ * g ≤ θ ^ 2 / 8 := by nlinarith
  simp only [bucketErr]
  linarith

/-- **Итог с калибровкой.** Если цена округления не больше `ε·F(S̄)`, то
гарантия шага — `(1−2ε)·F(S̄)`. -/
theorem psiC_ge_of_approxBucket_calibrated {θ₀ : ℝ}
    (hb : ApproxBucket a y S R t η ζ)
    (hnormS : IsNormal a y S thS) (hnormR : IsNormal a y R thR)
    (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hζ2 : 2 * ζ < 1)
    (hθ₀ : 0 ≤ θ₀) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hanchR : ∀ i ∈ R, ¬ cl i → y i = 0)
    (hcondR : ∀ v : κ → ℝ, γ * gram a R v ≤ gram a (anchorSet cl R) v)
    (hfilterR : ∀ i ∈ R, cl i → -θ₀ ≤ y i - dotp (a i) t)
    (hgapS : (phi a y S t - phi a y S thS)
      + bucketErr η ζ (phi a y S t - phi a y S thS) ≤ θ₀ ^ 2)
    (hcal : 256 * (R.card : ℝ) * θ₀ ^ 2 ≤ ε ^ 2 * γ * phi a y R thR)
    (hErr : bucketErr η ζ (phi a y S t - phi a y S thS) ≤ ε * phi a y S thS)
    (t' : κ → ℝ) :
    (1 - 2 * ε) * phi a y S thS ≤ psiC a y cl R t' := by
  have hmain := psiC_ge_of_approxBucket hb hnormS hnormR hη hζ hζ2 hθ₀ hγ hγ1 hε hε1
    hanchR hcondR hfilterR hgapS hcal t'
  nlinarith [hmain, hErr, hε, hε1, phi_nonneg a y S thS]

/-! ### Непустота: точная корзина — частный случай

При `η = ζ = 0` структура `ApproxBucket` описывает ровно точных соседей
(с точностью до направления неравенства по `gram`), а `bucketErr 0 0 g = 0`,
так что `psiC_ge_of_approxBucket` переходит в `psiC_ge_of_bucket_node_slack`. -/

lemma bucketErr_zero (g : ℝ) : bucketErr 0 0 g = 0 := by
  simp [bucketErr]

/-- Точные соседи по корзине — это `ApproxBucket` с нулевыми допусками. -/
theorem approxBucket_of_exact (hQ : phi a y S t ≤ phi a y R t)
    (hMom : ∀ v, mom a y R t v = mom a y S t v)
    (hKeq : ∀ v, gram a R v = gram a S v) :
    ApproxBucket a y S R t 0 0 :=
  { Q := hQ
    mom := fun v => by simp [hMom v]
    gram := fun v => by simp [hKeq v] }

end SparseSharpe.Factor
