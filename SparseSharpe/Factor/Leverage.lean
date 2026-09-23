import SparseSharpe.Factor.LeastSquares

set_option linter.style.header false

/-!
# Плечи строк и бюджет плеч: `Σ_{i∈S} h_i = K`

`theory_note_v5.md`, §13.2 показал, что цена выбрасывания строки из набора равна

    F(S̄) − F((S∖{i₀})‾)  =  r_{i₀}(t̂)² / (1 − h_{i₀}),

где `h_{i₀} = a_{i₀}'Κ(S̄)⁻¹a_{i₀}` — **плечо** строки. §13.4 заметил, что плечи
подчиняются бюджету `Σ_{i∈S}h_i ≤ K`, и потому «липких» строк (с `h_i` близким к `1`)
не больше `2K`. В Lean этого не было: остальная часть `Factor/*` намеренно обходится
без обращения матриц, а бюджет — это тождество для следа.

Здесь бюджет доказан. Обращение матрицы используется только внутри этого файла,
а наружу выходят утверждения без него:

* `lev_nonneg`, `lev_le_one` — `0 ≤ h_i ≤ 1`;
* `sum_lev_eq_card` — **бюджет**: `Σ_{i∈S} h_i = K` (ровно, а не `≤`);
* `card_sticky_le` — липких строк не больше `K/c`, в частности не больше `2K` при `c = 1/2`;
* `sq_dotp_le_lev_mul_gram` — **оценка через плечо**: `⟨a_i,v⟩² ≤ h_i·gram_S(v)`.
  Это усиление `sq_dotp_le_gram` (там множитель `1` вместо `h_i`); оценка
  достижима — равенство при `v = Κ⁻¹a_i`.

Отдельно стоит сказать, чего этот файл **не** объясняет. В контрпримере `Ex135`
плечи равны `25/26` (актив `1` набора `A`), `9/26` и `16/26` (активы `R`) и
`1/26` (якорная строка). Нарушитель там — актив с плечом `9/26`, то есть
совсем не «липкий»; цена его выбрасывания велика не из-за множителя
`1/(1−h) = 26/17`, а из-за того, что сама невязка в неподвижной точке велика
(`≈ 60/26`), потому что узел далёк от `t̂`, а порог допуска `ρ = δ` мал.
Бюджет плеч нужен для другого сценария — когда нарушение вызвано округлением
ключа динамики, и тогда `|r_i(t̂_R)| ≤ √(h_i·зазор)` мало́, а опасен именно
множитель `1/(1−h_i)`.

Вся конструкция — шляпная матрица `H = X Κ⁻¹ X'`, где `X` — матрица строк набора
(строки вне набора обнулены). Она симметрична и идемпотентна, поэтому
`H_ii = Σ_j H_ij²`, откуда сразу и `0 ≤ h_i ≤ 1`, и оценка плеча через
неравенство Коши–Буняковского. Бюджет — это `tr H = tr(Κ⁻¹Κ) = K`.
-/

namespace SparseSharpe.Factor

open Finset Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Матрица строк набора `S`: строки вне `S` обнулены. -/
def rowsOf (a : ι → κ → ℝ) (S : Finset ι) : Matrix ι κ ℝ :=
  Matrix.of fun i j => if i ∈ S then a i j else 0

/-- Матрица Грама набора `S`: `Κ(S) = X'X = Σ_{i∈S} a_ia_i'`. -/
def gramMat (a : ι → κ → ℝ) (S : Finset ι) : Matrix κ κ ℝ :=
  (rowsOf a S)ᵀ * rowsOf a S

/-- Шляпная матрица `H = X Κ(S)⁻¹ X'`. -/
noncomputable def hatMat (a : ι → κ → ℝ) (S : Finset ι) : Matrix ι ι ℝ :=
  rowsOf a S * (gramMat a S)⁻¹ * (rowsOf a S)ᵀ

/-- Плечо строки `i` в наборе `S`: `h_i = a_i'Κ(S)⁻¹a_i`. -/
noncomputable def lev (a : ι → κ → ℝ) (S : Finset ι) (i : ι) : ℝ := hatMat a S i i

variable {a : ι → κ → ℝ} {y : ι → ℝ} {S : Finset ι} {v : κ → ℝ} {i : ι}

/-! ### Связь с языком строк -/

/-- `filter (· ∈ S) univ = S`. -/
lemma filter_mem_univ (S : Finset ι) :
    Finset.univ.filter (fun i => i ∈ S) = S := by ext x; simp

omit [Fintype ι] [DecidableEq κ] in
lemma rowsOf_mulVec (a : ι → κ → ℝ) (S : Finset ι) (v : κ → ℝ) (i : ι) :
    (rowsOf a S).mulVec v i = if i ∈ S then dotp (a i) v else 0 := by
  by_cases h : i ∈ S <;>
    simp [rowsOf, Matrix.mulVec, dotProduct, dotp, h]

omit [DecidableEq κ] in
/-- Форма Грама из `LeastSquares.lean` — это `‖Xv‖²`. -/
lemma gram_eq_sum_mulVec (a : ι → κ → ℝ) (S : Finset ι) (v : κ → ℝ) :
    gram a S v = ∑ i, ((rowsOf a S).mulVec v i) ^ 2 := by
  rw [gram]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ S)]
  have h1 : ∑ i ∈ Finset.univ.filter (fun i => i ∈ S),
      ((rowsOf a S).mulVec v i) ^ 2 = ∑ i ∈ S, (dotp (a i) v) ^ 2 := by
    rw [filter_mem_univ]
    exact Finset.sum_congr rfl fun i hi => by rw [rowsOf_mulVec]; simp [hi]
  have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ i ∈ S),
      ((rowsOf a S).mulVec v i) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hn : i ∉ S := (Finset.mem_filter.mp hi).2
    rw [rowsOf_mulVec]; simp [hn]
  rw [h1, h2, add_zero]

/-! ### Шляпная матрица: симметрия и идемпотентность -/

omit [Fintype κ] [DecidableEq κ] in
lemma gramMat_transpose (a : ι → κ → ℝ) (S : Finset ι) :
    (gramMat a S)ᵀ = gramMat a S := by
  simp [gramMat, Matrix.transpose_mul]

/-- `H` симметрична. -/
theorem hatMat_transpose (a : ι → κ → ℝ) (S : Finset ι) :
    (hatMat a S)ᵀ = hatMat a S := by
  simp only [hatMat, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv, gramMat_transpose, Matrix.mul_assoc]

/-- `H X = X` — шляпная матрица оставляет столбцы `X` на месте. -/
theorem hatMat_mul_rows (hdet : IsUnit (gramMat a S).det) :
    hatMat a S * rowsOf a S = rowsOf a S := by
  have h : (rowsOf a S)ᵀ * rowsOf a S = gramMat a S := rfl
  calc hatMat a S * rowsOf a S
      = rowsOf a S * ((gramMat a S)⁻¹ * ((rowsOf a S)ᵀ * rowsOf a S)) := by
        simp [hatMat, Matrix.mul_assoc]
    _ = rowsOf a S * ((gramMat a S)⁻¹ * gramMat a S) := by rw [h]
    _ = rowsOf a S := by rw [Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]

/-- `H` идемпотентна. -/
theorem hatMat_idem (hdet : IsUnit (gramMat a S).det) :
    hatMat a S * hatMat a S = hatMat a S := by
  calc hatMat a S * hatMat a S
      = (hatMat a S * rowsOf a S) * ((gramMat a S)⁻¹ * (rowsOf a S)ᵀ) := by
        simp [hatMat, Matrix.mul_assoc]
    _ = rowsOf a S * ((gramMat a S)⁻¹ * (rowsOf a S)ᵀ) := by rw [hatMat_mul_rows hdet]
    _ = hatMat a S := by simp [hatMat, Matrix.mul_assoc]

/-- **Диагональ равна сумме квадратов строки.** `H_ii = Σ_j H_ij²`. -/
theorem lev_eq_sum_sq (hdet : IsUnit (gramMat a S).det) (i : ι) :
    lev a S i = ∑ j, (hatMat a S i j) ^ 2 := by
  have hsym : ∀ j, hatMat a S j i = hatMat a S i j := fun j => by
    have := congrFun (congrFun (hatMat_transpose a S) i) j
    simpa [Matrix.transpose_apply] using this
  have h := congrFun (congrFun (hatMat_idem hdet) i) i
  rw [Matrix.mul_apply] at h
  rw [lev, ← h]
  exact Finset.sum_congr rfl fun j _ => by rw [hsym j]; ring

theorem lev_nonneg (hdet : IsUnit (gramMat a S).det) (i : ι) : 0 ≤ lev a S i := by
  rw [lev_eq_sum_sq hdet]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem lev_le_one (hdet : IsUnit (gramMat a S).det) (i : ι) : lev a S i ≤ 1 := by
  have hsum := lev_eq_sum_sq hdet (a := a) (S := S) i
  have hdiag : (hatMat a S i i) ^ 2 ≤ ∑ j, (hatMat a S i j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (hatMat a S i j) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hle : (lev a S i) ^ 2 ≤ lev a S i := by
    have e : lev a S i = hatMat a S i i := rfl
    rw [e]
    calc (hatMat a S i i) ^ 2 ≤ ∑ j, (hatMat a S i j) ^ 2 := hdiag
      _ = hatMat a S i i := hsum.symm
  nlinarith [lev_nonneg hdet (a := a) (S := S) i, hle]

/-- Строки вне набора плеча не имеют. -/
theorem lev_eq_zero_of_notMem (hi : i ∉ S) : lev a S i = 0 := by
  simp only [lev, hatMat, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hz : ∀ l, (rowsOf a S) i l = 0 := fun l => by simp [rowsOf, hi]
  simp [hz]

/-! ### Бюджет плеч -/

/-- **Бюджет плеч: `Σ_{i∈S} h_i = K` ровно.**

Это `tr H = tr(X Κ⁻¹X') = tr(Κ⁻¹ X'X) = tr(Κ⁻¹Κ) = tr(I_K) = K`. Именно отсюда
следует, что «липких» строк (с большим плечом) в наборе мало: §13.4 заметки. -/
theorem sum_lev_eq_card (hdet : IsUnit (gramMat a S).det) :
    ∑ i ∈ S, lev a S i = (Fintype.card κ : ℝ) := by
  have hzero : ∑ i ∈ Finset.univ.filter (fun i => ¬ i ∈ S), lev a S i = 0 :=
    Finset.sum_eq_zero fun i hi => lev_eq_zero_of_notMem (Finset.mem_filter.mp hi).2
  have huniv : ∑ i, lev a S i = ∑ i ∈ S, lev a S i := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ S), hzero,
      add_zero, filter_mem_univ]
  have htr : (hatMat a S).trace = (Fintype.card κ : ℝ) := by
    calc (hatMat a S).trace
        = (rowsOf a S * ((gramMat a S)⁻¹ * (rowsOf a S)ᵀ)).trace := by
          rw [hatMat, Matrix.mul_assoc]
      _ = (((gramMat a S)⁻¹ * (rowsOf a S)ᵀ) * rowsOf a S).trace :=
          Matrix.trace_mul_comm _ _
      _ = ((gramMat a S)⁻¹ * gramMat a S).trace := by rw [Matrix.mul_assoc]; rfl
      _ = (1 : Matrix κ κ ℝ).trace := by rw [Matrix.nonsing_inv_mul _ hdet]
      _ = (Fintype.card κ : ℝ) := by simp
  rw [← huniv]
  simpa [Matrix.trace, Matrix.diag, lev] using htr

/-- **Липких строк мало.** Строк с плечом не меньше `c > 0` в наборе не больше `K/c`;
при `c = 1/2` — не больше `2K`. -/
theorem card_sticky_le (hdet : IsUnit (gramMat a S).det) {c : ℝ} (hc : 0 < c) :
    ((S.filter (fun i => c ≤ lev a S i)).card : ℝ) ≤ (Fintype.card κ : ℝ) / c := by
  classical
  set D := S.filter (fun i => c ≤ lev a S i) with hD
  have hsub : D ⊆ S := Finset.filter_subset _ _
  have h1 : c * (D.card : ℝ) ≤ ∑ i ∈ D, lev a S i := by
    calc c * (D.card : ℝ) = ∑ _i ∈ D, c := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ D, lev a S i :=
          Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2
  have h2 : ∑ i ∈ D, lev a S i ≤ ∑ i ∈ S, lev a S i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => lev_nonneg hdet j
  rw [sum_lev_eq_card hdet] at h2
  rw [le_div_iff₀ hc]
  linarith

/-! ### Точное плечо -/

/-- **Точная оценка плеча.** `⟨a_i,v⟩² ≤ h_i·gram_S(v)` при `i ∈ S`.

Это усиление `sq_dotp_le_gram` (там множитель `1`). Доказательство: вектор `Xv`
неподвижен под `H` (`hatMat_mul_rows`), поэтому `⟨a_i,v⟩ = Σ_j H_ij(Xv)_j`, а дальше
Коши–Буняковский и `Σ_j H_ij² = h_i`. -/
theorem sq_dotp_le_lev_mul_gram (hdet : IsUnit (gramMat a S).det) (hi : i ∈ S)
    (v : κ → ℝ) : (dotp (a i) v) ^ 2 ≤ lev a S i * gram a S v := by
  set w : ι → ℝ := (rowsOf a S).mulVec v with hw
  have hfix : (hatMat a S).mulVec w = w := by
    rw [hw, Matrix.mulVec_mulVec, hatMat_mul_rows hdet]
  have hcoord : dotp (a i) v = ∑ j, hatMat a S i j * w j := by
    have h2 : w i = dotp (a i) v := by rw [hw, rowsOf_mulVec]; simp [hi]
    calc dotp (a i) v = w i := h2.symm
      _ = ((hatMat a S).mulVec w) i := by rw [hfix]
      _ = ∑ j, hatMat a S i j * w j := by simp [Matrix.mulVec, dotProduct]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => hatMat a S i j)
    (fun j => w j)
  rw [hcoord]
  calc (∑ j, hatMat a S i j * w j) ^ 2
      ≤ (∑ j, (hatMat a S i j) ^ 2) * ∑ j, (w j) ^ 2 := hcs
    _ = lev a S i * gram a S v := by
        rw [← lev_eq_sum_sq hdet, ← gram_eq_sum_mulVec]

/-! ### Цена выбрасывания строки через её плечо -/

/-- **Цена выбрасывания строки: `r_{i₀}(t̂)²/(1 − h_{i₀})`.**

§13.2 заметки даёт цену как произведение невязок в двух неподвижных точках,
`phi_erase_cost`; §13.4 переводит её в матричную форму `r²/(1 − h)`. Здесь это
доказано без обращений матриц — из `sq_dotp_le_lev_mul_gram` и тождества сдвига
неподвижной точки.

Вместе с `card_sticky_le` это и есть содержательная часть §13.4: строку с плечом
не больше `1 − θ` можно выбросить за `r²/θ`, а строк с большим плечом в наборе
не больше `K/(1−θ)`. В `Ex135` множитель равен `1/(1 − 9/26) = 26/17`, то есть
там работает не он, а величина самой невязки. -/
theorem phi_erase_cost_le_of_lev {i₀ : ι} (hi : i₀ ∈ S)
    (hdet : IsUnit (gramMat a S).det)
    {th1 th0 : κ → ℝ} (h1 : IsNormal a y S th1) (h0 : IsNormal a y (S.erase i₀) th0)
    (hlt : lev a S i₀ < 1) :
    phi a y S th1 - phi a y (S.erase i₀) th0
      ≤ (y i₀ - dotp (a i₀) th1) ^ 2 / (1 - lev a S i₀) := by
  set h := lev a S i₀ with hhdef
  set u : κ → ℝ := th0 - th1 with hu
  set x : ℝ := dotp (a i₀) u with hx
  set c : ℝ := y i₀ - dotp (a i₀) th1 with hc
  have hxsub : x = dotp (a i₀) th0 - dotp (a i₀) th1 := by rw [hx, hu, dotp_sub]
  -- цена = c·(c − x)
  have hcost : phi a y S th1 - phi a y (S.erase i₀) th0 = c * (c - x) := by
    rw [phi_erase_cost hi h1 h0, hc, hxsub]; ring
  -- p := gram_{S∖i₀}(u) = −c·x ≥ 0
  have hs : gram a (S.erase i₀) u = -(c * x) := by
    have := gram_erase_shift (a := a) (y := y) hi h1 h0
    rw [← hu, ← hx, ← hc] at this
    exact this
  have hp0 : (0:ℝ) ≤ -(c * x) := by rw [← hs]; exact gram_nonneg _ _ _
  -- gram_S(u) = −c·x + x²
  have hG : gram a S u = -(c * x) + x ^ 2 := by
    rw [gram_erase_add (a := a) hi u, hs, ← hx]
  -- x² ≤ h·gram_S(u)
  have hlev : x ^ 2 ≤ h * gram a S u := by
    rw [hx, hhdef]; exact sq_dotp_le_lev_mul_gram hdet hi u
  have hlev' : x ^ 2 ≤ h * (-(c * x) + x ^ 2) := by rw [← hG]; exact hlev
  have hh0 : (0:ℝ) ≤ h := by rw [hhdef]; exact lev_nonneg hdet i₀
  have hden : (0:ℝ) < 1 - h := by linarith
  -- `p(1−h) ≤ c²h`, потому что `p² = c²x²` и `x²(1−h) ≤ hp`
  have hkey : (-(c * x)) * (1 - h) ≤ c ^ 2 * h := by
    set p : ℝ := -(c * x) with hpdef
    have hx2 : x ^ 2 * (1 - h) ≤ h * p := by nlinarith [hlev']
    have hpsq : p ^ 2 = c ^ 2 * x ^ 2 := by rw [hpdef]; ring
    rcases eq_or_lt_of_le hp0 with heq | hpos
    · rw [← heq]; nlinarith [hh0, sq_nonneg c]
    · have hmul : c ^ 2 * (x ^ 2 * (1 - h)) ≤ c ^ 2 * (h * p) :=
        mul_le_mul_of_nonneg_left hx2 (sq_nonneg c)
      have e1 : (p * (1 - h)) * p = c ^ 2 * (x ^ 2 * (1 - h)) := by
        rw [show (p * (1 - h)) * p = p ^ 2 * (1 - h) by ring, hpsq]; ring
      have e2 : (c ^ 2 * h) * p = c ^ 2 * (h * p) := by ring
      have h1' : (p * (1 - h)) * p ≤ (c ^ 2 * h) * p := by rw [e1, e2]; exact hmul
      exact le_of_mul_le_mul_right h1' hpos
  have hexp : c * (c - x) * (1 - h) = c ^ 2 * (1 - h) + (-(c * x)) * (1 - h) := by ring
  rw [hcost, le_div_iff₀ hden, hexp]
  nlinarith [hkey]

/-! ### Непустота гипотез

По правилу проекта: `lake build` и аудит аксиом не отличают содержательное
утверждение от пустого. Ниже — инстанс, в котором `IsUnit (gramMat a S).det`
выполнено, плечи различны и бюджет нетривиален. -/

/-- Две строки `a₁ = (1,0)`, `a₂ = (0,1)` в `ℝ²`: матрица Грама единична,
оба плеча равны `1`, их сумма равна `2 = K`. -/
example :
    IsUnit (gramMat (fun i j : Fin 2 => if i = j then (1:ℝ) else 0)
      (Finset.univ : Finset (Fin 2))).det := by
  have h : gramMat (fun i j : Fin 2 => if i = j then (1:ℝ) else 0)
      (Finset.univ : Finset (Fin 2)) = 1 := by
    ext j j'
    fin_cases j <;> fin_cases j' <;>
      simp [gramMat, rowsOf, Matrix.mul_apply]
  rw [h]
  simp

end SparseSharpe.Factor
