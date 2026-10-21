import SparseSharpe.Factor.ClippedNode

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Схема без ω: леммы шага (задача C1 ТЗ v26, `code/SPEC_C1.md`)

Строки `a : ι → κ → ℝ`, цели `y`, маска обрезания `cl` (в приложении: `rowsK`, `targetsK`,
`isLeft`; активы обрезаются, якоря — нет), `ψ_X(x) = psiC a y cl X x`. `T : κ → ι` — `K`-ка
строк с `det ≠ 0`, `ρ_l(x) = y_{T l} − ⟨a_{T l}, x⟩` (`rhoT`) — координаты невязок,
`c_{jl} = cf a T j l` — координаты Крамера (`a_j = Σ_l c_{jl}a_{T l}`).

* **Лемма 1 (узел)** `sf_node`, `sf_node_maxvol`: `ψ_S(x) − F_LO(S) ≤ C·‖ρ(x) − ρ(x₀)‖²`,
  `C = |S|·K` при максимальном объёме (`F_LO(S) = ψ_S(x₀)`).
* **Лемма 2 (свидетель Крамера)** `cramer_witness`: веса `resC_j(x)` вне `T` и веса строк `T`
  `ω_T = −Σ_{j∈X∖T} resC_j(x)c_j` (`omegaT`, полный вектор — `wCr`) стационарны, и
  `obj(X, ω) = ψ̃_X(x) − ‖ω_T − ρ(x)‖²` (`rowObj_wCr`), где `ψ̃` — то же `ψ`, но строки `T`
  не обрезаны (`clOff`); при активных в `x` строках `T` это `ψ_X(x) − ‖ω_T − r_T(x)‖²`
  (`rowObj_wCr_active`); `ω_T − ρ = −½∇_ρψ̃_X`, `ω_T − r_T = −½∇_ρψ_X`. В портфельных
  координатах: `objLO_cramer`, `objLO_eq_rowObj` (вес актива `w_i = ω_i/√d_i`), а вес якоря —
  его невязка в точке ККТ `t̂ = Σ_fB'w` (`anchor_weight_eq`).
* **Лемма 3 (градиент без ν)** `sf_grad`, `sf_grad'`, `sf_grad_maxvol`:
  `¼‖∇_ρψ_S(x)‖² ≤ |S|K·(ψ_S(x) − F_LO(S))`; `psiC_rho_taylor` — что `∇_ρψ = 2κ_S`
  действительно градиент в координатах `ρ` (двусторонняя оценка Тейлора).
* **Лемма 4 (ключ)** `omegaT_union` (линейность свидетеля в точной сумме `κ`),
  `abs_kap_sub_lt_of_key_eq` (`|κ_X − κ_S|_∞ < kη` при равных ключах `keyC` и мощностях),
  `abs_kapC_le_sqrt`, `abs_kapC_le_sqrt_psiC` (коробка `|κ_U| ≤ Σ_U resC ≤ √(k·ψ_X(x))`).
* **Лемма 5 (шаг)** `sf_step_grad` (`F_LO(X) ≥ ψ̃_S(x) − δ − (½‖∇_ρψ̃_S‖ + Δ)²`),
  `sf_step_grad_active` (то же с `ψ`, если строки `T` активны в `x`), `sf_step`,
  `sf_step_maxvol` (`F_LO(X) ≥ F_LO(S) − δ − (|S|K·‖Δρ‖ + Δ)²`), `sf_step_eps`
  (`≥ (1 − 5ε)F_LO(S)` при шаге решётки `√(εF̂)/(C√K)`, `η = √(εF̂)/(k√K)`, `δ ≤ εF̂`).
* **Лемма 7 (одна тугая строка)** `sf_signs_one_tight`, `sf_signs_no_tight`, `exists_corner`,
  `active_of_margin`. Порог нетугих строк — `kη + k·K·‖Δρ‖_∞` (не больше порога спецификации
  `kη + kK‖Δρ‖_∞√K`). **Точка остановки:** в формулировке `SPEC_C1.md` (п. 7) нужна
  дополнительная гипотеза — строки `S̄∖T`, активные в `x₀`, остаются активными в узле (`hact`);
  без неё утверждение ложно (`spec7_counterexample`, `spec7_fails`). Достаточное условие —
  запас `r_j(x₀) ≥ K·‖Δρ‖_∞` у всех активов, кроме тугой строки (`active_of_margin`), то есть
  класс «у оптимума не больше одной тугой строки **среди всех его активов**»
  (`Factor/ScaleFreeScheme.lean`).
* Лемма 6 (липкость) для этого не нужна и не формализована.
-/

namespace SparseSharpe.Factor

open Finset

section RowForm

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {cl : ι → Bool} {T : κ → ι}

/-! ### Координаты невязок `K`-ки и координаты Крамера -/

/-- Строки `K`-ки как множество. -/
def rowsT (T : κ → ι) : Finset ι := Finset.univ.image T

lemma mem_rowsT (T : κ → ι) (l : κ) : T l ∈ rowsT T :=
  Finset.mem_image_of_mem T (Finset.mem_univ l)

lemma card_rowsT (hdet : (rowMat a T).det ≠ 0) : (rowsT T).card = Fintype.card κ := by
  rw [rowsT, Finset.card_image_of_injective _ (injective_of_det_ne_zero hdet), Finset.card_univ]

/-- Координаты невязок `K`-ки: `ρ_l(x) = y_{T l} − ⟨a_{T l}, x⟩`. -/
noncomputable def rhoT (a : ι → κ → ℝ) (y : ι → ℝ) (T : κ → ι) (x : κ → ℝ) (l : κ) : ℝ :=
  y (T l) - dotp (a (T l)) x

/-- Координаты Крамера строки самой `K`-ки — единичные векторы. -/
lemma cf_self (hdet : (rowMat a T).det ≠ 0) (l l' : κ) :
    cf a T (T l) l' = if l = l' then 1 else 0 := by
  unfold cf
  by_cases h : l = l'
  · subst h
    rw [ite_eq_left rfl, Function.update_eq_self, div_self hdet]
  · rw [ite_eq_right h]
    have hz : (rowMat a (Function.update T l' (T l))).det = 0 := by
      refine Matrix.det_zero_of_row_eq h ?_
      funext j
      simp [rowMat, Function.update_apply, h]
    rw [hz, zero_div]

/-- Невязка любой строки через координаты невязок `K`-ки:
`r_j(x) − r_j(x') = Σ_l c_{jl}(ρ_l(x) − ρ_l(x'))`. -/
lemma res_sub_eq_sum_cf (hdet : (rowMat a T).det ≠ 0) (j : ι) (x x' : κ → ℝ) :
    (y j - dotp (a j) x) - (y j - dotp (a j) x')
      = ∑ l, cf a T j l * (rhoT a y T x l - rhoT a y T x' l) := by
  have h := dotp_eq_sum_cf hdet j (x' - x)
  rw [dotp_sub] at h
  have e : ∀ l, rhoT a y T x l - rhoT a y T x' l = dotp (a (T l)) (x' - x) := by
    intro l; simp only [rhoT, dotp_sub]; ring
  simp_rw [e]
  rw [← h]
  ring

/-- `gram_T(x − x₀) = ‖ρ(x) − ρ(x₀)‖²`. -/
lemma gramK_sub_eq (x x₀ : κ → ℝ) :
    gramK a T (x - x₀) = ∑ l, (rhoT a y T x l - rhoT a y T x₀ l) ^ 2 := by
  unfold gramK
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [dotp_sub]; simp only [rhoT]; ring

/-! ### Точная сумма Крамера, свидетель и маска без строк `T` -/

/-- Точная сумма Крамера набора строк `U` в точке `x`: `κ_U(x)_l = Σ_{j∈U} resC_j(x)·c_{jl}`. -/
noncomputable def kapC (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (T : κ → ι) (U : Finset ι)
    (x : κ → ℝ) (l : κ) : ℝ :=
  ∑ j ∈ U, resC a y cl j x * cf a T j l

/-- Градиент `ψ_U` по координатам `ρ`: `∇_ρψ_U(x) = 2κ_U(x)` (см. `psiC_rho_taylor`). -/
noncomputable def gradRho (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (T : κ → ι)
    (U : Finset ι) (x : κ → ℝ) (l : κ) : ℝ :=
  2 * kapC a y cl T U x l

/-- **Свидетель Крамера, веса строк `T`:** `ω_T(X)(x) = −Σ_{j∈X∖T} resC_j(x)·c_j`
(решение `Σ_l ω_l a_{T l} = −Σ_{j∈X∖T} resC_j(x)a_j`). -/
noncomputable def omegaT (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (T : κ → ι)
    (X : Finset ι) (x : κ → ℝ) (l : κ) : ℝ :=
  -kapC a y cl T (X \ rowsT T) x l

/-- Маска, в которой строки `T` не обрезаются (`ψ̃`). -/
def clOff (cl : ι → Bool) (T : κ → ι) : ι → Bool := fun j => cl j && decide (j ∉ rowsT T)

lemma resC_clOff_of_not_mem {j : ι} (hj : j ∉ rowsT T) (x : κ → ℝ) :
    resC a y (clOff cl T) j x = resC a y cl j x := by
  simp [resC, clOff, hj]

lemma resC_clOff_T (l : κ) (x : κ → ℝ) :
    resC a y (clOff cl T) (T l) x = rhoT a y T x l := by
  simp [resC, clOff, mem_rowsT, rhoT]

/-- Чем меньше обрезаний, тем больше `ψ`. -/
lemma psiC_le_of_clip_imp {cl' : ι → Bool} (h : ∀ j, cl' j → cl j) (S : Finset ι)
    (x : κ → ℝ) : psiC a y cl S x ≤ psiC a y cl' S x := by
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hc : cl j
  · by_cases hc' : cl' j
    · simp [resC, hc, hc']
    · simp only [resC, hc, hc', ite_true, ite_false, Bool.false_eq_true]
      rcases le_or_gt 0 (y j - dotp (a j) x) with h0 | h0
      · rw [max_eq_left h0]
      · rw [max_eq_right h0.le]; nlinarith
  · have hc' : ¬ cl' j = true := fun h' => hc (h j h')
    simp [resC, hc, hc']

lemma psiC_le_psiC_clOff (S : Finset ι) (x : κ → ℝ) :
    psiC a y cl S x ≤ psiC a y (clOff cl T) S x :=
  psiC_le_of_clip_imp (fun j h => by simp [clOff] at h; exact h.1) S x

/-- `Σ_{j∈U} resC_j(x)⟨a_j,h⟩ = Σ_l κ_U(x)_l ⟨a_{T l},h⟩`. -/
lemma sum_resC_dotp_eq (hdet : (rowMat a T).det ≠ 0) (U : Finset ι) (x h : κ → ℝ) :
    ∑ j ∈ U, resC a y cl j x * dotp (a j) h
      = ∑ l, kapC a y cl T U x l * dotp (a (T l)) h := by
  simp only [kapC, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dotp_eq_sum_cf hdet j h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- `κ_X = κ_{X∖T} + resC_T`: вклад строки `T l` в `l`-ю координату — её собственная невязка. -/
lemma kapC_split (hdet : (rowMat a T).det ≠ 0) {X : Finset ι} (hTX : rowsT T ⊆ X)
    (cl' : ι → Bool) (x : κ → ℝ) (l : κ) :
    kapC a y cl' T X x l = kapC a y cl' T (X \ rowsT T) x l + resC a y cl' (T l) x := by
  have hinj := injective_of_det_ne_zero hdet
  have hsplit := Finset.sum_sdiff hTX (f := fun j => resC a y cl' j x * cf a T j l)
  have hT : ∑ j ∈ rowsT T, resC a y cl' j x * cf a T j l = resC a y cl' (T l) x := by
    rw [rowsT, Finset.sum_image (fun l₁ _ l₂ _ h => hinj h)]
    rw [Finset.sum_eq_single l]
    · rw [cf_self hdet, ite_eq_left rfl, mul_one]
    · intro b _ hb; rw [cf_self hdet, ite_eq_right hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ l) h
  simp only [kapC]
  rw [← hsplit, hT]

/-! ### Лемма 1: узел -/

/-- **Лемма 1 (узел), зажим общего вида.** Если `x₀` — точка нормальных уравнений набора `S`,
в которой все обрезаемые строки активны, то в любой точке `x`

    ψ_S(x) − ψ_S(x₀) ≤ C·‖ρ(x) − ρ(x₀)‖²,

а `ψ_S(x₀) = min ψ_S = F_LO(S)` (`psiC_min_of_normal_of_nonneg`). Обрезание только уменьшает
`ψ` (`psiC_le_phi`), поэтому оценка — это `phi_eq_add` и зажим `gram_S ≤ C·gram_T`. -/
theorem sf_node {S : Finset ι} {C : ℝ} {x₀ : κ → ℝ}
    (hclamp : ∀ v, gram a S v ≤ C * gramK a T v) (hnormal : IsNormal a y S x₀)
    (hself : ∀ j ∈ S, cl j → 0 ≤ y j - dotp (a j) x₀) (x : κ → ℝ) :
    psiC a y cl S x - psiC a y cl S x₀
      ≤ C * ∑ l, (rhoT a y T x l - rhoT a y T x₀ l) ^ 2 := by
  have h1 := psiC_le_phi a y cl S x
  have h2 := phi_eq_add hnormal x
  have h3 : psiC a y cl S x₀ = phi a y S x₀ := psiC_eq_phi_of_nonneg hself
  have h4 := hclamp (x - x₀)
  rw [gramK_sub_eq (y := y)] at h4
  linarith

/-- **Лемма 1 при максимальном объёме:** `C = |S|·K`. -/
theorem sf_node_maxvol {S : Finset ι} {x₀ : κ → ℝ} (hmax : MaxVol a S T)
    (hdet : (rowMat a T).det ≠ 0) (hnormal : IsNormal a y S x₀)
    (hself : ∀ j ∈ S, cl j → 0 ≤ y j - dotp (a j) x₀) (x : κ → ℝ) :
    psiC a y cl S x - psiC a y cl S x₀
      ≤ (S.card * Fintype.card κ : ℝ) * ∑ l, (rhoT a y T x l - rhoT a y T x₀ l) ^ 2 :=
  sf_node (fun v => gram_le_card_mul_gramK hmax hdet v) hnormal hself x

/-! ### Гладкость в координатах `ρ` и Лемма 3 -/

/-- Поточечная гладкость: `ψ_S(x+h) ≤ ψ_S(x) − 2Σ_j resC_j(x)⟨a_j,h⟩ + gram_S(h)`. -/
lemma psiC_add_le (S : Finset ι) (x h : κ → ℝ) :
    psiC a y cl S (x + h)
      ≤ psiC a y cl S x - 2 * ∑ j ∈ S, resC a y cl j x * dotp (a j) h + gram a S h := by
  simp only [psiC, gram, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have hd : dotp (a j) (x + h) = dotp (a j) x + dotp (a j) h := dotp_add _ _ _
  by_cases hc : cl j
  · simp only [resC, hc, ite_true, hd]
    have := pos_sq_le (y j - (dotp (a j) x + dotp (a j) h)) (y j - dotp (a j) x)
    have e : y j - (dotp (a j) x + dotp (a j) h) - (y j - dotp (a j) x) = -dotp (a j) h := by
      ring
    rw [e] at this
    nlinarith [this]
  · simp only [resC, hc, ite_false, Bool.false_eq_true, hd]
    nlinarith

/-- **`∇_ρψ_S = 2κ_S` — градиент в координатах невязок `K`-ки.** Для любых `x, x'` с
`δ = ρ(x') − ρ(x)`:

    ⟨∇_ρψ_S(x), δ⟩ ≤ ψ_S(x') − ψ_S(x) ≤ ⟨∇_ρψ_S(x), δ⟩ + C‖δ‖²

(слева — выпуклость, `psiC_shift_ge`; справа — гладкость и зажим). -/
theorem psiC_rho_taylor (hdet : (rowMat a T).det ≠ 0) {S : Finset ι} {C : ℝ}
    (hclamp : ∀ v, gram a S v ≤ C * gramK a T v) (x x' : κ → ℝ) :
    ∑ l, gradRho a y cl T S x l * (rhoT a y T x' l - rhoT a y T x l)
        ≤ psiC a y cl S x' - psiC a y cl S x
      ∧ psiC a y cl S x' - psiC a y cl S x
        ≤ ∑ l, gradRho a y cl T S x l * (rhoT a y T x' l - rhoT a y T x l)
          + C * ∑ l, (rhoT a y T x' l - rhoT a y T x l) ^ 2 := by
  set h : κ → ℝ := x' - x with hh
  have hx' : x + h = x' := by rw [hh]; abel
  have hlin : ∑ l, gradRho a y cl T S x l * (rhoT a y T x' l - rhoT a y T x l)
      = -2 * ∑ j ∈ S, resC a y cl j x * dotp (a j) h := by
    rw [sum_resC_dotp_eq hdet S x h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have : rhoT a y T x' l - rhoT a y T x l = -dotp (a (T l)) h := by
      simp only [rhoT, hh, dotp_sub]; ring
    rw [this, gradRho]; ring
  have hq : gramK a T h = ∑ l, (rhoT a y T x' l - rhoT a y T x l) ^ 2 := by
    rw [hh]; exact gramK_sub_eq x' x
  constructor
  · have hsh := psiC_shift_ge a y cl S x h
    rw [hx'] at hsh
    have hg := gramC_nonneg a y cl S x h
    have hm : momC a y cl S x h = ∑ j ∈ S, resC a y cl j x * dotp (a j) h := rfl
    rw [hlin]; linarith
  · have hup := psiC_add_le (a := a) (y := y) (cl := cl) S x h
    rw [hx'] at hup
    have hc := hclamp h
    rw [hq] at hc
    rw [hlin]; linarith

/-- **Лемма 3 (градиент без `ν`).** Если `F ≤ ψ_S` всюду и `gram_S ≤ C·gram_T`, то

    ¼‖∇_ρψ_S(x)‖² = ‖κ_S(x)‖² ≤ C·(ψ_S(x) − F).

Доказательство — шаг гладкости в координатах `ρ` длины `κ/C` (как `defect_le`, но константа
— зажим `C`, а не `ν = 1 + Σ ω_i`). -/
theorem sf_grad (hdet : (rowMat a T).det ≠ 0) {S : Finset ι} {C F : ℝ}
    (hclamp : ∀ v, gram a S v ≤ C * gramK a T v) (hC : 0 < C)
    (hF : ∀ x', F ≤ psiC a y cl S x') (x : κ → ℝ) :
    ∑ l, kapC a y cl T S x l ^ 2 ≤ C * (psiC a y cl S x - F) := by
  set Q := ∑ l, kapC a y cl T S x l ^ 2 with hQ
  set g : κ → ℝ := fun l => kapC a y cl T S x l / C with hg
  obtain ⟨h, hh⟩ := exists_point_with_residuals hdet g
  have hup := psiC_add_le (a := a) (y := y) (cl := cl) S x h
  rw [sum_resC_dotp_eq hdet S x h] at hup
  have hlin : ∑ l, kapC a y cl T S x l * dotp (a (T l)) h = Q / C := by
    rw [hQ, Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hh l, hg]; ring
  have hgK : gramK a T h = ∑ l, g l ^ 2 := by
    simp only [gramK, hh]
  have hq : C * ∑ l, g l ^ 2 = Q / C := by
    rw [hQ, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hg]; field_simp
  have hgr := hclamp h
  rw [hgK, hq] at hgr
  rw [hlin] at hup
  have hlow := hF (x + h)
  have h2 : Q / C ≤ psiC a y cl S x - F := by linarith
  calc Q = C * (Q / C) := by field_simp
    _ ≤ C * (psiC a y cl S x - F) := mul_le_mul_of_nonneg_left h2 hC.le

/-- Лемма 3 в обозначениях спецификации: `¼‖∇_ρψ_S(x)‖² ≤ C·(ψ_S(x) − F)`. -/
theorem sf_grad' (hdet : (rowMat a T).det ≠ 0) {S : Finset ι} {C F : ℝ}
    (hclamp : ∀ v, gram a S v ≤ C * gramK a T v) (hC : 0 < C)
    (hF : ∀ x', F ≤ psiC a y cl S x') (x : κ → ℝ) :
    (1 / 4) * ∑ l, gradRho a y cl T S x l ^ 2 ≤ C * (psiC a y cl S x - F) := by
  have h := sf_grad hdet hclamp hC hF x
  have e : (1 / 4) * ∑ l, gradRho a y cl T S x l ^ 2 = ∑ l, kapC a y cl T S x l ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [gradRho]; ring
  rw [e]; exact h

/-- **Лемма 3 в форме спецификации:** при максимальном объёме `T` и `F_LO(S) = ψ_S(x₀)`
(нормальные уравнения, все обрезаемые строки активны в `x₀`)
`¼‖∇_ρψ_S(x)‖² ≤ |S|·K·(ψ_S(x) − F_LO(S))`. -/
theorem sf_grad_maxvol {S : Finset ι} {x₀ : κ → ℝ} (hmax : MaxVol a S T)
    (hdet : (rowMat a T).det ≠ 0) (hnormal : IsNormal a y S x₀)
    (hself : ∀ j ∈ S, cl j → 0 ≤ y j - dotp (a j) x₀) (x : κ → ℝ) :
    (1 / 4) * ∑ l, gradRho a y cl T S x l ^ 2
      ≤ (S.card * Fintype.card κ : ℝ) * (psiC a y cl S x - psiC a y cl S x₀) := by
  rcases Nat.eq_zero_or_pos (S.card * Fintype.card κ) with h0 | hpos
  · -- `S = ∅` или `K = 0`: тогда `∇ = 0`
    have hK : ∀ l : κ, gradRho a y cl T S x l = 0 := by
      intro l
      rcases Nat.mul_eq_zero.mp h0 with hS | hK
      · have : S = ∅ := Finset.card_eq_zero.mp hS
        simp [gradRho, kapC, this]
      · exact absurd (Fintype.card_pos_iff.mpr ⟨l⟩) (by omega)
    simp [hK]
    have := psiC_min_of_normal_of_nonneg hnormal hself x
    have hc : (S.card * Fintype.card κ : ℝ) = 0 := by exact_mod_cast h0
    rw [hc]; simp
  · exact sf_grad' hdet (fun v => gram_le_card_mul_gramK hmax hdet v)
      (by exact_mod_cast hpos) (psiC_min_of_normal_of_nonneg hnormal hself) x

/-! ### Лемма 2: свидетель Крамера -/

/-- Цель в строчной форме: `obj(X, ω) = Σ_{j∈X}(2y_jω_j − ω_j²)`. Для набора активов `X` и
стационарных весов строк `barK X` это `objLO` (`objLO_eq_rowObj`). -/
noncomputable def rowObj (y : ι → ℝ) (X : Finset ι) (ω : ι → ℝ) : ℝ :=
  ∑ j ∈ X, (2 * y j * ω j - ω j ^ 2)

/-- Стационарность весов строк: `Σ_{j∈X} ω_j a_j = 0`. -/
def RowStat (a : ι → κ → ℝ) (X : Finset ι) (ω : ι → ℝ) : Prop :=
  ∀ v : κ → ℝ, ∑ j ∈ X, ω j * dotp (a j) v = 0

/-- При стационарности `obj(X, ω) = Σ_{j∈X}(r_j(x)² − (ω_j − r_j(x))²)` в любой точке `x`. -/
lemma rowObj_eq_of_stat {X : Finset ι} {ω : ι → ℝ} (h : RowStat a X ω) (x : κ → ℝ) :
    rowObj y X ω
      = ∑ j ∈ X, ((y j - dotp (a j) x) ^ 2 - (ω j - (y j - dotp (a j) x)) ^ 2) := by
  have h0 := h x
  have e : ∑ j ∈ X, ((y j - dotp (a j) x) ^ 2 - (ω j - (y j - dotp (a j) x)) ^ 2)
      = rowObj y X ω - 2 * ∑ j ∈ X, ω j * dotp (a j) x := by
    simp only [rowObj, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, h0]; ring

/-- **Строчная слабая двойственность:** стационарные веса, неотрицательные на обрезаемых
строках, дают `obj(X, ω) ≤ ψ_X(x')` при любом `x'`, то есть `obj(X, ω) ≤ F_LO(X)`. -/
lemma rowObj_le_psiC {X : Finset ι} {ω : ι → ℝ} (h : RowStat a X ω)
    (hω : ∀ j ∈ X, cl j → 0 ≤ ω j) (x' : κ → ℝ) : rowObj y X ω ≤ psiC a y cl X x' := by
  rw [rowObj_eq_of_stat h x', psiC]
  refine Finset.sum_le_sum fun j hj => ?_
  by_cases hc : cl j
  · have hw := hω j hj hc
    simp only [resC, hc, ite_true]
    have := quad_item_le (r := y j - dotp (a j) x') (dd := 1) one_pos hw
    rw [div_one] at this
    nlinarith [this]
  · simp only [resC, hc, ite_false, Bool.false_eq_true]
    nlinarith [sq_nonneg (ω j - (y j - dotp (a j) x'))]

/-- **Свидетель Крамера** — веса всех строк: `resC_j(x)` вне `T`, `ω_T(X)(x)` на строках `T`. -/
noncomputable def wCr (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (T : κ → ι) (X : Finset ι)
    (x : κ → ℝ) (j : ι) : ℝ :=
  if j ∈ rowsT T then ∑ l, (if T l = j then omegaT a y cl T X x l else 0) else resC a y cl j x

lemma wCr_T (hinj : Function.Injective T) (X : Finset ι) (x : κ → ℝ) (l : κ) :
    wCr a y cl T X x (T l) = omegaT a y cl T X x l := by
  rw [wCr, ite_eq_left (mem_rowsT T l)]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb; rw [ite_eq_right (fun h => hb (hinj h))]
  · intro h; exact absurd (Finset.mem_univ l) h

lemma wCr_of_not_mem {j : ι} (hj : j ∉ rowsT T) (X : Finset ι) (x : κ → ℝ) :
    wCr a y cl T X x j = resC a y cl j x := by
  rw [wCr, ite_eq_right hj]

/-- Свидетель Крамера стационарен: `Σ_{j∈X} ω^Cr_j a_j = 0`. -/
lemma isStat_wCr (hdet : (rowMat a T).det ≠ 0) {X : Finset ι} (hTX : rowsT T ⊆ X)
    (x : κ → ℝ) : RowStat a X (wCr a y cl T X x) := by
  intro v
  have hinj := injective_of_det_ne_zero hdet
  have hsplit := Finset.sum_sdiff hTX (f := fun j => wCr a y cl T X x j * dotp (a j) v)
  have h1 : ∑ j ∈ X \ rowsT T, wCr a y cl T X x j * dotp (a j) v
      = ∑ l, kapC a y cl T (X \ rowsT T) x l * dotp (a (T l)) v := by
    rw [← sum_resC_dotp_eq hdet]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [wCr_of_not_mem (Finset.mem_sdiff.mp hj).2]
  have h2 : ∑ j ∈ rowsT T, wCr a y cl T X x j * dotp (a j) v
      = ∑ l, omegaT a y cl T X x l * dotp (a (T l)) v := by
    rw [rowsT, Finset.sum_image (fun l₁ _ l₂ _ h => hinj h)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [wCr_T hinj]
  rw [← hsplit, h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun l _ => ?_
  simp only [omegaT]; ring

/-- `r² − (resC − r)² = resC²` для любой строки. -/
lemma sq_sub_sq_resC (j : ι) (x : κ → ℝ) :
    (y j - dotp (a j) x) ^ 2 - (resC a y cl j x - (y j - dotp (a j) x)) ^ 2
      = resC a y cl j x ^ 2 := by
  by_cases hc : cl j
  · simp only [resC, hc, ite_true]
    rcases le_or_gt 0 (y j - dotp (a j) x) with h | h
    · rw [max_eq_left h]; ring
    · rw [max_eq_right h.le]; ring
  · simp only [resC, hc, ite_false, Bool.false_eq_true]; ring

/-- **Тождество Леммы 2.** `obj(X, ω^Cr) = ψ̃_X(x) − ‖ω_T(X)(x) − ρ(x)‖²`; строки `T` в `ψ̃`
не обрезаны (`clOff`), поэтому активность строк `T` в узле не нужна. -/
theorem rowObj_wCr (hdet : (rowMat a T).det ≠ 0) {X : Finset ι} (hTX : rowsT T ⊆ X)
    (x : κ → ℝ) :
    rowObj y X (wCr a y cl T X x)
      = psiC a y (clOff cl T) X x - ∑ l, (omegaT a y cl T X x l - rhoT a y T x l) ^ 2 := by
  have hinj := injective_of_det_ne_zero hdet
  rw [rowObj_eq_of_stat (isStat_wCr hdet hTX x) x, psiC]
  have hA := Finset.sum_sdiff hTX (f := fun j => (y j - dotp (a j) x) ^ 2
    - (wCr a y cl T X x j - (y j - dotp (a j) x)) ^ 2)
  have hB := Finset.sum_sdiff hTX (f := fun j => resC a y (clOff cl T) j x ^ 2)
  have h1 : ∑ j ∈ X \ rowsT T, ((y j - dotp (a j) x) ^ 2
        - (wCr a y cl T X x j - (y j - dotp (a j) x)) ^ 2)
      = ∑ j ∈ X \ rowsT T, resC a y (clOff cl T) j x ^ 2 := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := (Finset.mem_sdiff.mp hj).2
    rw [wCr_of_not_mem hj', resC_clOff_of_not_mem hj', sq_sub_sq_resC]
  have h2 : ∑ j ∈ rowsT T, ((y j - dotp (a j) x) ^ 2
        - (wCr a y cl T X x j - (y j - dotp (a j) x)) ^ 2)
      = ∑ l, (rhoT a y T x l ^ 2 - (omegaT a y cl T X x l - rhoT a y T x l) ^ 2) := by
    rw [rowsT, Finset.sum_image (fun l₁ _ l₂ _ h => hinj h)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [wCr_T hinj]; rfl
  have h3 : ∑ j ∈ rowsT T, resC a y (clOff cl T) j x ^ 2 = ∑ l, rhoT a y T x l ^ 2 := by
    rw [rowsT, Finset.sum_image (fun l₁ _ l₂ _ h => hinj h)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [resC_clOff_T]
  rw [← hA, ← hB, h1, h2, h3, Finset.sum_sub_distrib]; ring

/-- **Лемма 2, градиент:** `ω_T(X)(x) − ρ(x) = −κ̃_X(x) = −½∇_ρψ̃_X(x)` (маска `clOff`). -/
lemma omegaT_sub_rhoT (hdet : (rowMat a T).det ≠ 0) {X : Finset ι} (hTX : rowsT T ⊆ X)
    (x : κ → ℝ) (l : κ) :
    omegaT a y cl T X x l - rhoT a y T x l = -kapC a y (clOff cl T) T X x l := by
  rw [kapC_split hdet hTX (clOff cl T) x l, resC_clOff_T]
  have : kapC a y (clOff cl T) T (X \ rowsT T) x l = kapC a y cl T (X \ rowsT T) x l := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [resC_clOff_of_not_mem (Finset.mem_sdiff.mp hj).2]
  rw [this, omegaT]; ring

/-- То же при обрезанных строках `T`: `ω_T(X)(x) − r_T(x) = −κ_X(x) = −½∇_ρψ_X(x)`. -/
lemma omegaT_sub_resC (hdet : (rowMat a T).det ≠ 0) {X : Finset ι} (hTX : rowsT T ⊆ X)
    (x : κ → ℝ) (l : κ) :
    omegaT a y cl T X x l - resC a y cl (T l) x = -kapC a y cl T X x l := by
  rw [kapC_split hdet hTX cl x l, omegaT]; ring

/-- Если строки `T` активны в `x`, то `ψ̃_X(x) = ψ_X(x)`. -/
lemma psiC_clOff_eq_of_active {X : Finset ι} {x : κ → ℝ}
    (hact : ∀ l, cl (T l) → 0 ≤ rhoT a y T x l) :
    psiC a y (clOff cl T) X x = psiC a y cl X x := by
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j ∈ rowsT T
  · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hj
    rw [resC_clOff_T]
    by_cases hc : cl (T l)
    · have h0 : 0 ≤ y (T l) - dotp (a (T l)) x := hact l hc
      simp only [resC, hc, ite_true, rhoT]
      rw [max_eq_left h0]
    · simp only [resC, hc, ite_false, Bool.false_eq_true, rhoT]
  · rw [resC_clOff_of_not_mem hj]

/-- Свидетель неотрицателен на обрезаемых строках, если неотрицательны веса строк `T`. -/
lemma wCr_nonneg {X : Finset ι} {x : κ → ℝ} (hinj : Function.Injective T)
    (hsign : ∀ l, cl (T l) → 0 ≤ omegaT a y cl T X x l) :
    ∀ j ∈ X, cl j → 0 ≤ wCr a y cl T X x j := by
  intro j _ hc
  by_cases hj : j ∈ rowsT T
  · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hj
    rw [wCr_T hinj]; exact hsign l hc
  · rw [wCr_of_not_mem hj]; exact resC_nonneg_of_clip hc

/-- **Лемма 2 целиком (строчная форма).** Для `X ⊇ T` и узла `x`:
(i) свидетель `ω^Cr` стационарен; (ii) на строках `T` он равен `ω_T(X)(x)`, вне `T` — `resC(x)`;
(iii) `obj(X, ω^Cr) = ψ̃_X(x) − ‖ω_T − ρ(x)‖²`; (iv) `ω_T − ρ = −½∇_ρψ̃_X(x)`;
(v) `ω_T − r_T = −½∇_ρψ_X(x)`; (vi) при `ω_T ≥ 0` на обрезаемых строках `T`
`obj(X, ω^Cr) ≤ ψ_X(x')` для любого `x'`, то есть `obj(X, ω^Cr) ≤ F_LO(X)`. -/
theorem cramer_witness (hdet : (rowMat a T).det ≠ 0) {X : Finset ι} (hTX : rowsT T ⊆ X)
    (x : κ → ℝ) :
    RowStat a X (wCr a y cl T X x)
    ∧ (∀ l, wCr a y cl T X x (T l) = omegaT a y cl T X x l)
    ∧ (∀ j, j ∉ rowsT T → wCr a y cl T X x j = resC a y cl j x)
    ∧ rowObj y X (wCr a y cl T X x)
        = psiC a y (clOff cl T) X x - ∑ l, (omegaT a y cl T X x l - rhoT a y T x l) ^ 2
    ∧ (∀ l, omegaT a y cl T X x l - rhoT a y T x l
        = -(1 / 2) * gradRho a y (clOff cl T) T X x l)
    ∧ (∀ l, omegaT a y cl T X x l - resC a y cl (T l) x = -(1 / 2) * gradRho a y cl T X x l)
    ∧ ((∀ l, cl (T l) → 0 ≤ omegaT a y cl T X x l) →
        ∀ x', rowObj y X (wCr a y cl T X x) ≤ psiC a y cl X x') := by
  have hinj := injective_of_det_ne_zero hdet
  refine ⟨isStat_wCr hdet hTX x, fun l => wCr_T hinj X x l,
    fun j hj => wCr_of_not_mem hj X x, rowObj_wCr hdet hTX x, fun l => ?_, fun l => ?_,
    fun hsign x' => rowObj_le_psiC (isStat_wCr hdet hTX x) (wCr_nonneg hinj hsign) x'⟩
  · rw [omegaT_sub_rhoT hdet hTX x l, gradRho]; ring
  · rw [omegaT_sub_resC hdet hTX x l, gradRho]; ring

/-- Лемма 2 в форме спецификации: при активных в `x` строках `T`
`obj(X, ω^Cr) = ψ_X(x) − ‖ω_T − r_T(x)‖²`. -/
theorem rowObj_wCr_active (hdet : (rowMat a T).det ≠ 0) {X : Finset ι} (hTX : rowsT T ⊆ X)
    {x : κ → ℝ} (hact : ∀ l, cl (T l) → 0 ≤ rhoT a y T x l) :
    rowObj y X (wCr a y cl T X x)
      = psiC a y cl X x - ∑ l, (omegaT a y cl T X x l - resC a y cl (T l) x) ^ 2 := by
  rw [rowObj_wCr hdet hTX x, psiC_clOff_eq_of_active hact]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 2
  by_cases hc : cl (T l)
  · have h0 : 0 ≤ y (T l) - dotp (a (T l)) x := hact l hc
    simp only [resC, hc, ite_true, rhoT]; rw [max_eq_left h0]
  · simp only [resC, hc, ite_false, Bool.false_eq_true, rhoT]

/-! ### Лемма 4: ключ Крамера -/

/-- **Линейность свидетеля в точной сумме.** При `X = base ∪ U`, `base ⊇ T`, `U ∩ base = ∅`:
`ω_T(base ∪ U) = ω_T(base) − κ_U`; поэтому `ω_T(X) − ω_T(S) = −(κ_{U_X} − κ_{U_S})`. -/
lemma omegaT_union {base U : Finset ι} (hdisj : Disjoint base U) (hTb : rowsT T ⊆ base)
    (x : κ → ℝ) (l : κ) :
    omegaT a y cl T (base ∪ U) x l = omegaT a y cl T base x l - kapC a y cl T U x l := by
  have hU : Disjoint U (rowsT T) := Finset.disjoint_of_subset_right hTb hdisj.symm
  have e : (base ∪ U) \ rowsT T = (base \ rowsT T) ∪ U := by
    rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_self_of_disjoint hU]
  have hd2 : Disjoint (base \ rowsT T) U :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset hdisj
  simp only [omegaT, kapC]
  rw [e, Finset.sum_union hd2]; ring

/-- Ключ строки в узле: `⌊resC_i(x)·c_i/η⌋ ∈ ℤ^K`. -/
noncomputable def keyC (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (T : κ → ι) (η : ℝ)
    (x : κ → ℝ) (i : ι) : κ → ℤ :=
  fun l => ⌊resC a y cl i x * cf a T i l / η⌋

/-- Остаток округления вниз: `0 ≤ v − η⌊v/η⌋ < η`. -/
lemma floor_rem_mem {v η : ℝ} (hη : 0 < η) :
    0 ≤ v - η * ⌊v / η⌋ ∧ v - η * ⌊v / η⌋ < η := by
  have h1 := Int.floor_le (v / η)
  have h2 := Int.lt_floor_add_one (v / η)
  constructor
  · have : η * (⌊v / η⌋ : ℝ) ≤ η * (v / η) := mul_le_mul_of_nonneg_left h1 hη.le
    rw [mul_div_cancel₀ _ hη.ne'] at this; linarith
  · have : η * (v / η) < η * ((⌊v / η⌋ : ℝ) + 1) := mul_lt_mul_of_pos_left h2 hη
    rw [mul_div_cancel₀ _ hη.ne'] at this; linarith

/-- **Равные суммы округлений ⇒ близкие точные суммы.** При `|U| = |V| ≤ k`, `k ≥ 1`:
`Σ_U⌊f/η⌋ = Σ_V⌊f/η⌋ ⇒ |Σ_U f − Σ_V f| < kη`. -/
lemma abs_sum_sub_lt_of_floor_eq {U V : Finset ι} {f : ι → ℝ} {η : ℝ} {k : ℕ} (hη : 0 < η)
    (hk : 0 < k) (hUk : U.card ≤ k) (hcard : U.card = V.card)
    (hfl : ∑ i ∈ U, ⌊f i / η⌋ = ∑ i ∈ V, ⌊f i / η⌋) :
    |∑ i ∈ U, f i - ∑ i ∈ V, f i| < k * η := by
  set e : Finset ι → ℝ := fun W => ∑ i ∈ W, (f i - η * ⌊f i / η⌋) with he
  have hsum : ∀ W : Finset ι, ∑ i ∈ W, f i = η * ((∑ i ∈ W, ⌊f i / η⌋ : ℤ) : ℝ) + e W := by
    intro W
    simp only [he, Int.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have he0 : ∀ W, 0 ≤ e W := fun W => Finset.sum_nonneg fun i _ => (floor_rem_mem hη).1
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  rcases Nat.eq_zero_or_pos U.card with h0 | hpos
  · have hU : U = ∅ := Finset.card_eq_zero.mp h0
    have hV : V = ∅ := Finset.card_eq_zero.mp (hcard ▸ h0)
    subst hU; subst hV
    simp only [Finset.sum_empty, sub_self, abs_zero]
    positivity
  · have hUne : U.Nonempty := Finset.card_pos.mp hpos
    have hVne : V.Nonempty := Finset.card_pos.mp (hcard ▸ hpos)
    have heU : e U < U.card * η := by
      calc e U < ∑ _i ∈ U, η :=
            Finset.sum_lt_sum_of_nonempty hUne fun i _ => (floor_rem_mem hη).2
        _ = U.card * η := by simp
    have heV : e V < U.card * η := by
      calc e V < ∑ _i ∈ V, η :=
            Finset.sum_lt_sum_of_nonempty hVne fun i _ => (floor_rem_mem hη).2
        _ = U.card * η := by rw [hcard]; simp
    have hdiff : ∑ i ∈ U, f i - ∑ i ∈ V, f i = e U - e V := by
      rw [hsum U, hsum V, hfl]; ring
    have hk' : (U.card : ℝ) * η ≤ k * η :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hUk) hη.le
    rw [hdiff, abs_lt]
    constructor <;> linarith [he0 U, he0 V]

/-- **Лемма 4, ключ:** равенство ключей `Σ_U keyC = Σ_V keyC` при `|U| = |V| ≤ k`, `k ≥ 1`,
даёт `|κ_U − κ_V|_∞ < kη`, где `κ_U = Σ_{i∈U} resC_i(x)c_i` — точная сумма. -/
theorem abs_kap_sub_lt_of_key_eq {U V : Finset ι} {η : ℝ} {k : ℕ} {x : κ → ℝ} (hη : 0 < η)
    (hk : 0 < k) (hUk : U.card ≤ k) (hcard : U.card = V.card)
    (hkey : ∑ i ∈ U, keyC a y cl T η x i = ∑ i ∈ V, keyC a y cl T η x i) (l : κ) :
    |kapC a y cl T U x l - kapC a y cl T V x l| < k * η := by
  have hl := congrFun hkey l
  simp only [Finset.sum_apply, keyC] at hl
  exact abs_sum_sub_lt_of_floor_eq hη hk hUk hcard hl

/-- **Лемма 4, коробка ключа без `ω`:** у обрезаемых строк с `|c_{il}| ≤ 1`
`|κ_U(x)_l| ≤ Σ_U resC_i(x) ≤ √(|U|·Σ_U resC_i(x)²)`. -/
theorem abs_kapC_le_sqrt {U : Finset ι} {l : κ} (hcl : ∀ i ∈ U, cl i)
    (hcf : ∀ i ∈ U, |cf a T i l| ≤ 1) (x : κ → ℝ) :
    |kapC a y cl T U x l| ≤ Real.sqrt (U.card * ∑ i ∈ U, resC a y cl i x ^ 2) := by
  have h1 : |kapC a y cl T U x l| ≤ ∑ i ∈ U, resC a y cl i x := by
    calc |kapC a y cl T U x l| ≤ ∑ i ∈ U, |resC a y cl i x * cf a T i l| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ U, resC a y cl i x := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hr := resC_nonneg_of_clip (a := a) (y := y) (t := x) (hcl i hi)
          rw [abs_mul, abs_of_nonneg hr]
          exact mul_le_of_le_one_right hr (hcf i hi)
  have h2 : (∑ i ∈ U, resC a y cl i x) ^ 2 ≤ U.card * ∑ i ∈ U, resC a y cl i x ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h0 : 0 ≤ ∑ i ∈ U, resC a y cl i x :=
    Finset.sum_nonneg fun i hi => resC_nonneg_of_clip (hcl i hi)
  calc |kapC a y cl T U x l| ≤ ∑ i ∈ U, resC a y cl i x := h1
    _ = Real.sqrt ((∑ i ∈ U, resC a y cl i x) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt (U.card * ∑ i ∈ U, resC a y cl i x ^ 2) := Real.sqrt_le_sqrt h2

/-- Коробка ключа в форме спецификации: `|κ_U(x)_l| ≤ √(k·ψ_X(x))` при `U ⊆ X`, `|U| ≤ k`. -/
theorem abs_kapC_le_sqrt_psiC {U X : Finset ι} {l : κ} {k : ℕ} (hUX : U ⊆ X)
    (hUk : U.card ≤ k) (hcl : ∀ i ∈ U, cl i) (hcf : ∀ i ∈ U, |cf a T i l| ≤ 1) (x : κ → ℝ) :
    |kapC a y cl T U x l| ≤ Real.sqrt (k * psiC a y cl X x) := by
  refine le_trans (abs_kapC_le_sqrt hcl hcf x) (Real.sqrt_le_sqrt ?_)
  have h1 : ∑ i ∈ U, resC a y cl i x ^ 2 ≤ psiC a y cl X x :=
    Finset.sum_le_sum_of_subset_of_nonneg hUX fun _ _ _ => sq_nonneg _
  have h2 : (U.card : ℝ) ≤ k := by exact_mod_cast hUk
  have h3 : 0 ≤ ∑ i ∈ U, resC a y cl i x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h4 : 0 ≤ psiC a y cl X x := psiC_nonneg a y cl X x
  nlinarith

/-! ### Лемма 5: шаг без `ω` -/

/-- Неравенство треугольника для евклидовой нормы в `ℝ^K`. -/
lemma sqrt_sum_sq_add_le (u v : κ → ℝ) :
    Real.sqrt (∑ l, (u l + v l) ^ 2)
      ≤ Real.sqrt (∑ l, u l ^ 2) + Real.sqrt (∑ l, v l ^ 2) := by
  have hu0 : (0:ℝ) ≤ ∑ l, u l ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hv0 : (0:ℝ) ≤ ∑ l, v l ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hu2 := Real.sq_sqrt hu0
  have hv2 := Real.sq_sqrt hv0
  have hcs := sum_mul_le_sqrt u v
  have hexp : ∑ l, (u l + v l) ^ 2
      = ∑ l, u l ^ 2 + 2 * ∑ l, u l * v l + ∑ l, v l ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hle : ∑ l, (u l + v l) ^ 2
      ≤ (Real.sqrt (∑ l, u l ^ 2) + Real.sqrt (∑ l, v l ^ 2)) ^ 2 := by
    rw [hexp]; nlinarith [hcs]
  calc Real.sqrt (∑ l, (u l + v l) ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ l, u l ^ 2) + Real.sqrt (∑ l, v l ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = Real.sqrt (∑ l, u l ^ 2) + Real.sqrt (∑ l, v l ^ 2) :=
        Real.sqrt_sq (by positivity)

/-- **Лемма 5, форма с градиентом.** Пусть `X, S ⊇ T`; в узле `x` набор `X` не хуже `S` по
счёту с допуском `δ` (`ψ̃_S(x) ≤ ψ̃_X(x) + δ`), свидетели близки (`‖ω_T(X) − ω_T(S)‖ ≤ Δ`), и
`ω_T(X) ≥ 0` на обрезаемых строках `T`. Тогда при любом `x'`

    ψ_X(x') ≥ ψ̃_S(x) − δ − (½‖∇_ρψ̃_S(x)‖ + Δ)²,

то есть `F_LO(X) ≥ ψ̃_S(x) − δ − (½‖∇_ρψ̃_S(x)‖ + Δ)²` — без `ω`. -/
theorem sf_step_grad (hdet : (rowMat a T).det ≠ 0) {S X : Finset ι} {δ Δ : ℝ} {x : κ → ℝ}
    (hTS : rowsT T ⊆ S) (hTX : rowsT T ⊆ X)
    (hscore : psiC a y (clOff cl T) S x ≤ psiC a y (clOff cl T) X x + δ)
    (hΔ : 0 ≤ Δ) (hkey : ∑ l, (omegaT a y cl T X x l - omegaT a y cl T S x l) ^ 2 ≤ Δ ^ 2)
    (hsign : ∀ l, cl (T l) → 0 ≤ omegaT a y cl T X x l) (x' : κ → ℝ) :
    psiC a y (clOff cl T) S x - δ
        - (Real.sqrt (∑ l, ((1 / 2) * gradRho a y (clOff cl T) T S x l) ^ 2) + Δ) ^ 2
      ≤ psiC a y cl X x' := by
  have hinj := injective_of_det_ne_zero hdet
  have hdual := rowObj_le_psiC (y := y) (isStat_wCr hdet hTX x) (wCr_nonneg hinj hsign) x'
  rw [rowObj_wCr hdet hTX x] at hdual
  -- `ω_T(X) − ρ = (ω_T(X) − ω_T(S)) + (−κ̃_S)`
  set u : κ → ℝ := fun l => omegaT a y cl T X x l - omegaT a y cl T S x l with hu
  set g : κ → ℝ := fun l => (1 / 2) * gradRho a y (clOff cl T) T S x l with hg
  have hsplit : ∀ l, omegaT a y cl T X x l - rhoT a y T x l = u l + (-g l) := by
    intro l
    have := omegaT_sub_rhoT (y := y) (cl := cl) hdet hTS x l
    simp only [hu, hg, gradRho]
    linarith
  have htri := sqrt_sum_sq_add_le u (fun l => -g l)
  have hneg : ∑ l, (-g l) ^ 2 = ∑ l, g l ^ 2 := Finset.sum_congr rfl fun l _ => by ring
  rw [hneg] at htri
  have hu' : Real.sqrt (∑ l, u l ^ 2) ≤ Δ := by
    rw [show Δ = Real.sqrt (Δ ^ 2) from (Real.sqrt_sq hΔ).symm]
    exact Real.sqrt_le_sqrt hkey
  have hE : Real.sqrt (∑ l, (omegaT a y cl T X x l - rhoT a y T x l) ^ 2)
      ≤ Real.sqrt (∑ l, g l ^ 2) + Δ := by
    have e : ∑ l, (omegaT a y cl T X x l - rhoT a y T x l) ^ 2 = ∑ l, (u l + -g l) ^ 2 :=
      Finset.sum_congr rfl fun l _ => by rw [hsplit l]
    rw [e]; linarith
  have hE0 : (0:ℝ) ≤ ∑ l, (omegaT a y cl T X x l - rhoT a y T x l) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq : ∑ l, (omegaT a y cl T X x l - rhoT a y T x l) ^ 2
      ≤ (Real.sqrt (∑ l, g l ^ 2) + Δ) ^ 2 := by
    have h1 := Real.sq_sqrt hE0
    have h2 : 0 ≤ Real.sqrt (∑ l, (omegaT a y cl T X x l - rhoT a y T x l) ^ 2) :=
      Real.sqrt_nonneg _
    nlinarith [hE, h1, h2]
  linarith

/-- **Лемма 5 (шаг без `ω`).** `S` — набор строк оптимума (`T ⊆ S`, все обрезаемые строки
активны в `x₀`, нормальные уравнения), `gram_S ≤ C·gram_T`; `X` — представитель корзины:
счёт не хуже с допуском `δ`, свидетели `Δ`-близки, `ω_T(X) ≥ 0`. Тогда при любом `x'`

    ψ_X(x') ≥ F_LO(S) − δ − (C·‖ρ(x) − ρ(x₀)‖ + Δ)²,   F_LO(S) = ψ_S(x₀).

С `C = |S|K` (максимальный объём), `‖Δρ‖ ≤ √(εF̂)/C`, `Δ = kη√K ≤ √(εF̂)` и `δ ≤ εF̂`
потеря не больше `5εF̂` (`sf_step_eps`). -/
theorem sf_step (hdet : (rowMat a T).det ≠ 0) {S X : Finset ι} {C δ Δ : ℝ} {x₀ x : κ → ℝ}
    (hTS : rowsT T ⊆ S) (hTX : rowsT T ⊆ X)
    (hclamp : ∀ v, gram a S v ≤ C * gramK a T v) (hC : 0 < C)
    (hnormal : IsNormal a y S x₀) (hself : ∀ j ∈ S, cl j → 0 ≤ y j - dotp (a j) x₀)
    (hscore : psiC a y (clOff cl T) S x ≤ psiC a y (clOff cl T) X x + δ)
    (hΔ : 0 ≤ Δ) (hkey : ∑ l, (omegaT a y cl T X x l - omegaT a y cl T S x l) ^ 2 ≤ Δ ^ 2)
    (hsign : ∀ l, cl (T l) → 0 ≤ omegaT a y cl T X x l) (x' : κ → ℝ) :
    psiC a y cl S x₀ - δ
        - (C * Real.sqrt (∑ l, (rhoT a y T x l - rhoT a y T x₀ l) ^ 2) + Δ) ^ 2
      ≤ psiC a y cl X x' := by
  set F := psiC a y cl S x₀ with hF
  have hselfOff : ∀ j ∈ S, clOff cl T j → 0 ≤ y j - dotp (a j) x₀ := by
    intro j hj hc
    simp only [clOff, Bool.and_eq_true] at hc
    exact hself j hj hc.1
  have hmin : ∀ x'', F ≤ psiC a y (clOff cl T) S x'' := fun x'' =>
    le_trans (psiC_min_of_normal_of_nonneg hnormal hself x'') (psiC_le_psiC_clOff S x'')
  have hF0 : psiC a y (clOff cl T) S x₀ = F := by
    rw [hF, psiC_eq_phi_of_nonneg hselfOff, psiC_eq_phi_of_nonneg hself]
  have hgrad := sf_grad (cl := clOff cl T) hdet hclamp hC hmin x
  have hnode := sf_node (cl := clOff cl T) hclamp hnormal hselfOff x
  rw [hF0] at hnode
  set D2 := ∑ l, (rhoT a y T x l - rhoT a y T x₀ l) ^ 2 with hD2
  have hD0 : 0 ≤ D2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hk2 : ∑ l, ((1 / 2) * gradRho a y (clOff cl T) T S x l) ^ 2
      = ∑ l, kapC a y (clOff cl T) T S x l ^ 2 :=
    Finset.sum_congr rfl fun l _ => by rw [gradRho]; ring
  have hkap : ∑ l, kapC a y (clOff cl T) T S x l ^ 2 ≤ (C * Real.sqrt D2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hD0]
    have := mul_le_mul_of_nonneg_left hnode hC.le
    nlinarith [hgrad, this]
  have hsq : Real.sqrt (∑ l, ((1 / 2) * gradRho a y (clOff cl T) T S x l) ^ 2)
      ≤ C * Real.sqrt D2 := by
    rw [hk2]
    calc Real.sqrt (∑ l, kapC a y (clOff cl T) T S x l ^ 2)
        ≤ Real.sqrt ((C * Real.sqrt D2) ^ 2) := Real.sqrt_le_sqrt hkap
      _ = C * Real.sqrt D2 := Real.sqrt_sq (by positivity)
  have hstep := sf_step_grad hdet hTS hTX hscore hΔ hkey hsign x'
  have hψ : F ≤ psiC a y (clOff cl T) S x := hmin x
  have hmono : (Real.sqrt (∑ l, ((1 / 2) * gradRho a y (clOff cl T) T S x l) ^ 2) + Δ) ^ 2
      ≤ (C * Real.sqrt D2 + Δ) ^ 2 := by
    have h0 := Real.sqrt_nonneg (∑ l, ((1 / 2) * gradRho a y (clOff cl T) T S x l) ^ 2)
    nlinarith [hsq, h0, hΔ]
  linarith

/-- **Лемма 5 с параметрами схемы.** При `C·‖Δρ‖ ≤ √(εF̂)` (шаг решётки `√(εF̂)/(C√K)`),
`Δ ≤ √(εF̂)` (`Δ = kη√K`, `η = √(εF̂)/(k√K)`), `δ ≤ εF̂` (округление счёта) и `F̂ ≤ F_LO(S)`:
`ψ_X(x') ≥ (1 − 5ε)·F_LO(S)` при любом `x'`. -/
theorem sf_step_eps (hdet : (rowMat a T).det ≠ 0) {S X : Finset ι} {C δ Δ ε Fh : ℝ}
    {x₀ x : κ → ℝ} (hTS : rowsT T ⊆ S) (hTX : rowsT T ⊆ X)
    (hclamp : ∀ v, gram a S v ≤ C * gramK a T v) (hC : 0 < C)
    (hnormal : IsNormal a y S x₀) (hself : ∀ j ∈ S, cl j → 0 ≤ y j - dotp (a j) x₀)
    (hscore : psiC a y (clOff cl T) S x ≤ psiC a y (clOff cl T) X x + δ)
    (hΔ : 0 ≤ Δ) (hkey : ∑ l, (omegaT a y cl T X x l - omegaT a y cl T S x l) ^ 2 ≤ Δ ^ 2)
    (hsign : ∀ l, cl (T l) → 0 ≤ omegaT a y cl T X x l)
    (hε : 0 ≤ ε) (hFh : 0 ≤ Fh) (hFhF : Fh ≤ psiC a y cl S x₀)
    (hnode : C * Real.sqrt (∑ l, (rhoT a y T x l - rhoT a y T x₀ l) ^ 2)
      ≤ Real.sqrt (ε * Fh))
    (hΔε : Δ ≤ Real.sqrt (ε * Fh)) (hδ : δ ≤ ε * Fh) (x' : κ → ℝ) :
    (1 - 5 * ε) * psiC a y cl S x₀ ≤ psiC a y cl X x' := by
  have h := sf_step hdet hTS hTX hclamp hC hnormal hself hscore hΔ hkey hsign x'
  have hr := Real.sq_sqrt (mul_nonneg hε hFh)
  have h0 : 0 ≤ C * Real.sqrt (∑ l, (rhoT a y T x l - rhoT a y T x₀ l) ^ 2) := by positivity
  have hsq : (C * Real.sqrt (∑ l, (rhoT a y T x l - rhoT a y T x₀ l) ^ 2) + Δ) ^ 2
      ≤ 4 * (ε * Fh) := by
    have hs0 := Real.sqrt_nonneg (ε * Fh)
    nlinarith [hnode, hΔε, h0, hΔ]
  have hεF : ε * Fh ≤ ε * psiC a y cl S x₀ := mul_le_mul_of_nonneg_left hFhF hε
  nlinarith [h, hsq, hδ, hεF]

/-- `κ̃ = κ`, если строки `T` активны в `x`. -/
lemma kapC_clOff_eq_of_active {S : Finset ι} {x : κ → ℝ}
    (hact : ∀ l, cl (T l) → 0 ≤ rhoT a y T x l) (l : κ) :
    kapC a y (clOff cl T) T S x l = kapC a y cl T S x l := by
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  by_cases hj : j ∈ rowsT T
  · obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hj
    rw [resC_clOff_T]
    by_cases hc : cl (T m)
    · have h0 : 0 ≤ y (T m) - dotp (a (T m)) x := hact m hc
      simp only [resC, hc, ite_true, rhoT]; rw [max_eq_left h0]
    · simp only [resC, hc, ite_false, Bool.false_eq_true, rhoT]
  · rw [resC_clOff_of_not_mem hj]

/-- **Лемма 5 в форме спецификации** (строки `T` активны в узле): при
`ψ_X(x) ≥ ψ_S(x) − δ`, `‖ω_T(X) − ω_T(S)‖ ≤ Δ`, `ω_T(X) ≥ 0`

    F_LO(X) ≥ ψ_S(x) − δ − (½‖∇_ρψ_S(x)‖ + Δ)². -/
theorem sf_step_grad_active (hdet : (rowMat a T).det ≠ 0) {S X : Finset ι} {δ Δ : ℝ}
    {x : κ → ℝ} (hTS : rowsT T ⊆ S) (hTX : rowsT T ⊆ X)
    (hact : ∀ l, cl (T l) → 0 ≤ rhoT a y T x l)
    (hscore : psiC a y cl S x ≤ psiC a y cl X x + δ)
    (hΔ : 0 ≤ Δ) (hkey : ∑ l, (omegaT a y cl T X x l - omegaT a y cl T S x l) ^ 2 ≤ Δ ^ 2)
    (hsign : ∀ l, cl (T l) → 0 ≤ omegaT a y cl T X x l) (x' : κ → ℝ) :
    psiC a y cl S x - δ
        - (Real.sqrt (∑ l, ((1 / 2) * gradRho a y cl T S x l) ^ 2) + Δ) ^ 2
      ≤ psiC a y cl X x' := by
  have h := sf_step_grad hdet hTS hTX
    (by rw [psiC_clOff_eq_of_active hact, psiC_clOff_eq_of_active hact]; exact hscore)
    hΔ hkey hsign x'
  rw [psiC_clOff_eq_of_active hact] at h
  have e : ∀ l, gradRho a y (clOff cl T) T S x l = gradRho a y cl T S x l := fun l => by
    rw [gradRho, gradRho, kapC_clOff_eq_of_active hact]
  simp only [e] at h
  exact h

/-- **Лемма 5 с константой спецификации `|S|·K`:**
`F_LO(X) ≥ F_LO(S) − δ − (|S|K·‖ρ(x) − ρ(x₀)‖ + Δ)²` при максимальном объёме `T`. -/
theorem sf_step_maxvol (hdet : (rowMat a T).det ≠ 0) {S X : Finset ι} {δ Δ : ℝ}
    {x₀ x : κ → ℝ} (hmax : MaxVol a S T) (hTX : rowsT T ⊆ X)
    (hnormal : IsNormal a y S x₀) (hself : ∀ j ∈ S, cl j → 0 ≤ y j - dotp (a j) x₀)
    (hscore : psiC a y (clOff cl T) S x ≤ psiC a y (clOff cl T) X x + δ)
    (hΔ : 0 ≤ Δ) (hkey : ∑ l, (omegaT a y cl T X x l - omegaT a y cl T S x l) ^ 2 ≤ Δ ^ 2)
    (hsign : ∀ l, cl (T l) → 0 ≤ omegaT a y cl T X x l) (hSK : 0 < S.card * Fintype.card κ)
    (x' : κ → ℝ) :
    psiC a y cl S x₀ - δ
        - ((S.card * Fintype.card κ : ℝ)
            * Real.sqrt (∑ l, (rhoT a y T x l - rhoT a y T x₀ l) ^ 2) + Δ) ^ 2
      ≤ psiC a y cl X x' := by
  have hTS : rowsT T ⊆ S := by
    intro r hr; obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hr; exact hmax.1 l
  exact sf_step hdet hTS hTX (fun v => gram_le_card_mul_gramK hmax hdet v)
    (by exact_mod_cast hSK) hnormal hself hscore hΔ hkey hsign x'

/-! ### Лемма 7: одна тугая строка -/

/-- `H = Σ_{j∈S∖T} c_j c_jᵀ` — матрица, через которую смещение узла входит в свидетель
(`omegaT_sub_eq_Hmat`). -/
noncomputable def Hmat (a : ι → κ → ℝ) (T : κ → ι) (S : Finset ι) (l m : κ) : ℝ :=
  ∑ j ∈ S \ rowsT T, cf a T j l * cf a T j m

/-- В точке нормальных уравнений с активными строками `κ_S(x₀) = 0` (`∇_ρψ_S(x₀) = 0`). -/
lemma kapC_eq_zero_of_normal (hdet : (rowMat a T).det ≠ 0) {S : Finset ι} {x₀ : κ → ℝ}
    (hnormal : IsNormal a y S x₀) (hself : ∀ j ∈ S, cl j → 0 ≤ y j - dotp (a j) x₀)
    (l : κ) : kapC a y cl T S x₀ l = 0 := by
  obtain ⟨v, hv⟩ := exists_point_with_residuals hdet (fun l' => if l' = l then (1:ℝ) else 0)
  have hres : ∀ j ∈ S, resC a y cl j x₀ = y j - dotp (a j) x₀ := by
    intro j hj
    by_cases hc : cl j
    · simp only [resC, hc, ite_true]; exact max_eq_left (hself j hj hc)
    · simp only [resC, hc, ite_false, Bool.false_eq_true]
  have e : mom a y S x₀ v = kapC a y cl T S x₀ l := by
    simp only [mom, kapC]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hres j hj, dotp_eq_sum_cf hdet j v]
    simp [hv]
  rw [← e]; exact hnormal v

/-- **Свидетель оптимума в его двойственной точке — его невязки:** `ω_T(S)(x₀) = ρ(x₀) = w*_T`
(`≥ 0` на обрезаемых строках). -/
lemma omegaT_opt (hdet : (rowMat a T).det ≠ 0) {S : Finset ι} {x₀ : κ → ℝ}
    (hTS : rowsT T ⊆ S) (hnormal : IsNormal a y S x₀)
    (hself : ∀ j ∈ S, cl j → 0 ≤ y j - dotp (a j) x₀) (l : κ) :
    omegaT a y cl T S x₀ l = rhoT a y T x₀ l := by
  have h0 := kapC_eq_zero_of_normal hdet hnormal hself l
  rw [kapC_split hdet hTS cl x₀ l] at h0
  have hT : resC a y cl (T l) x₀ = rhoT a y T x₀ l := by
    by_cases hc : cl (T l)
    · simp only [resC, hc, ite_true, rhoT]
      exact max_eq_left (hself (T l) (hTS (mem_rowsT T l)) hc)
    · simp only [resC, hc, ite_false, Bool.false_eq_true, rhoT]
  rw [omegaT]; linarith

/-- Сдвиг свидетеля набора `S` между точками `x₀` и `x`. -/
lemma omegaT_sub_eq (S : Finset ι) (x x₀ : κ → ℝ) (m : κ) :
    omegaT a y cl T S x m - omegaT a y cl T S x₀ m
      = -∑ j ∈ S \ rowsT T, (resC a y cl j x - resC a y cl j x₀) * cf a T j m := by
  simp only [omegaT, kapC, sub_mul, Finset.sum_sub_distrib]; ring

/-- `resC` — 1-липшицева функция невязки. -/
lemma abs_resC_sub_le (j : ι) (x x₀ : κ → ℝ) :
    |resC a y cl j x - resC a y cl j x₀|
      ≤ |(y j - dotp (a j) x) - (y j - dotp (a j) x₀)| := by
  by_cases hc : cl j
  · simp only [resC, hc, ite_true]; exact abs_max_sub_max_le_abs _ _ _
  · simp only [resC, hc, ite_false, Bool.false_eq_true]; exact le_refl _

/-- При `|c_j|_∞ ≤ 1` и `|Δρ|_∞ ≤ D`: `|r_j(x) − r_j(x₀)| ≤ K·D`. -/
lemma abs_res_sub_le (hdet : (rowMat a T).det ≠ 0) {j : ι} {x x₀ : κ → ℝ} {D : ℝ}
    (hcf : ∀ m, |cf a T j m| ≤ 1) (hD : ∀ m, |rhoT a y T x m - rhoT a y T x₀ m| ≤ D) :
    |(y j - dotp (a j) x) - (y j - dotp (a j) x₀)| ≤ Fintype.card κ * D := by
  rw [res_sub_eq_sum_cf hdet j x x₀]
  calc |∑ m, cf a T j m * (rhoT a y T x m - rhoT a y T x₀ m)|
      ≤ ∑ m, |cf a T j m * (rhoT a y T x m - rhoT a y T x₀ m)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m : κ, D := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [abs_mul]
        calc |cf a T j m| * |rhoT a y T x m - rhoT a y T x₀ m|
            ≤ 1 * |rhoT a y T x m - rhoT a y T x₀ m| :=
              mul_le_mul_of_nonneg_right (hcf m) (abs_nonneg _)
          _ ≤ D := by rw [one_mul]; exact hD m
    _ = Fintype.card κ * D := by simp

/-- **Запас активности.** Строка с `|c_j|_∞ ≤ 1` и `r_j(x₀) ≥ K·D` активна в узле `x` с
`|Δρ|_∞ ≤ D`. -/
lemma active_of_margin (hdet : (rowMat a T).det ≠ 0) {j : ι} {x x₀ : κ → ℝ} {D : ℝ}
    (hcf : ∀ m, |cf a T j m| ≤ 1) (hD : ∀ m, |rhoT a y T x m - rhoT a y T x₀ m| ≤ D)
    (hm : Fintype.card κ * D ≤ y j - dotp (a j) x₀) : 0 ≤ y j - dotp (a j) x := by
  have h := abs_res_sub_le hdet hcf hD
  rw [abs_le] at h
  linarith [h.1]

/-- **Отклонение свидетеля оптимума в узле:** `|ω_T(S)(x) − ω_T(S)(x₀)| ≤ |S∖T|·K·D` — с
учётом обрезания (строки, ставшие неактивными, тоже учтены). -/
lemma abs_omegaT_sub_le (hdet : (rowMat a T).det ≠ 0) {S : Finset ι} {x x₀ : κ → ℝ} {D : ℝ}
    (hcf : ∀ j ∈ S, ∀ m, |cf a T j m| ≤ 1)
    (hD : ∀ m, |rhoT a y T x m - rhoT a y T x₀ m| ≤ D) (m : κ) :
    |omegaT a y cl T S x m - omegaT a y cl T S x₀ m|
      ≤ (S \ rowsT T).card * (Fintype.card κ * D) := by
  rw [omegaT_sub_eq, abs_neg]
  calc |∑ j ∈ S \ rowsT T, (resC a y cl j x - resC a y cl j x₀) * cf a T j m|
      ≤ ∑ j ∈ S \ rowsT T, |(resC a y cl j x - resC a y cl j x₀) * cf a T j m| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ S \ rowsT T, (Fintype.card κ * D) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjS := (Finset.mem_sdiff.mp hj).1
        rw [abs_mul]
        calc |resC a y cl j x - resC a y cl j x₀| * |cf a T j m|
            ≤ |resC a y cl j x - resC a y cl j x₀| * 1 :=
              mul_le_mul_of_nonneg_left (hcf j hjS m) (abs_nonneg _)
          _ ≤ Fintype.card κ * D := by
              rw [mul_one]
              exact le_trans (abs_resC_sub_le j x x₀) (abs_res_sub_le hdet (hcf j hjS) hD)
    _ = (S \ rowsT T).card * (Fintype.card κ * D) := by simp

/-- **Линейная формула свидетеля:** если все строки `S∖T` активны в `x₀` и в `x`, то
`ω_T(S)(x) = ω_T(S)(x₀) − H·Δρ`, `H = Σ_{j∈S∖T} c_jc_jᵀ`. -/
lemma omegaT_sub_eq_Hmat (hdet : (rowMat a T).det ≠ 0) {S : Finset ι} {x x₀ : κ → ℝ}
    (hself : ∀ j ∈ S, cl j → 0 ≤ y j - dotp (a j) x₀)
    (hact : ∀ j ∈ S \ rowsT T, cl j → 0 ≤ y j - dotp (a j) x) (l : κ) :
    omegaT a y cl T S x l - omegaT a y cl T S x₀ l
      = -∑ m, Hmat a T S l m * (rhoT a y T x m - rhoT a y T x₀ m) := by
  rw [omegaT_sub_eq]
  congr 1
  have hres : ∀ j ∈ S \ rowsT T, resC a y cl j x - resC a y cl j x₀
      = ∑ m, cf a T j m * (rhoT a y T x m - rhoT a y T x₀ m) := by
    intro j hj
    rw [← res_sub_eq_sum_cf hdet j x x₀]
    have hjS := (Finset.mem_sdiff.mp hj).1
    by_cases hc : cl j
    · simp only [resC, hc, ite_true]
      rw [max_eq_left (hact j hj hc), max_eq_left (hself j hjS hc)]
    · simp only [resC, hc, ite_false, Bool.false_eq_true]
  rw [Finset.sum_congr rfl fun j hj => by rw [hres j hj]]
  simp only [Hmat, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Лемма 7, нетугие строки.** Если все обрезаемые строки `T` имеют запас
`w*_m = ρ_m(x₀) ≥ E + k·K·D` (`E` — допуск ключа, `D ≥ |Δρ|_∞`, `|S∖T| ≤ k`), то у любого
представителя `X = base ∪ U_X` с `|κ_{U_X} − κ_{U_S}|_∞ ≤ E` веса строк `T` неотрицательны —
независимо от активности строк в узле. -/
theorem sf_signs_no_tight (hdet : (rowMat a T).det ≠ 0) {base US UX : Finset ι}
    {x₀ x : κ → ℝ} {D E : ℝ} {k : ℕ}
    (hTb : rowsT T ⊆ base) (hdS : Disjoint base US) (hdX : Disjoint base UX)
    (hcf : ∀ j ∈ base ∪ US, ∀ m, |cf a T j m| ≤ 1)
    (hcard : ((base ∪ US) \ rowsT T).card ≤ k)
    (hnormal : IsNormal a y (base ∪ US) x₀)
    (hself : ∀ j ∈ base ∪ US, cl j → 0 ≤ y j - dotp (a j) x₀)
    (hD : ∀ m, |rhoT a y T x m - rhoT a y T x₀ m| ≤ D)
    (hkey : ∀ m, |kapC a y cl T UX x m - kapC a y cl T US x m| ≤ E)
    (hnt : ∀ m, cl (T m) → E + k * (Fintype.card κ * D) ≤ rhoT a y T x₀ m) :
    ∀ m, cl (T m) → 0 ≤ omegaT a y cl T (base ∪ UX) x m := by
  intro m hm
  have hTS : rowsT T ⊆ base ∪ US := le_trans hTb Finset.subset_union_left
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD m)
  have hω0 := omegaT_opt hdet hTS hnormal hself m
  have hdev := abs_omegaT_sub_le (cl := cl) hdet hcf hD (x := x) m
  rw [hω0] at hdev
  have hck : ((base ∪ US) \ rowsT T).card * (Fintype.card κ * D)
      ≤ (k : ℝ) * (Fintype.card κ * D) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  have hX := omegaT_union (a := a) (y := y) (cl := cl) hdX hTb x m
  have hS := omegaT_union (a := a) (y := y) (cl := cl) hdS hTb x m
  have hk := hkey m
  rw [abs_le] at hdev hk
  have := hnt m hm
  linarith [hdev.1, hk.2]

/-- **Лемма 7 (одна тугая строка `l`).** Строка `T l` тугая (её вес `w*_l = ρ_l(x₀)` может быть
сколь угодно мал), остальные обрезаемые строки `T` — с запасом `E + kKD`. Если

* узел — угол ячейки решётки со знаками `H_{lm}·Δρ_m ≤ 0` (`exists_corner`);
* **строки `S∖T` активны в узле** (`hact`; достаточно запаса `r_j(x₀) ≥ K·D`, `active_of_margin`);
* в корзине хранится набор с наименьшим точным `κ_l` (`hmin`),

то все веса строк `T` у представителя неотрицательны. Без `hact` вывод неверен:
`spec7_counterexample`. -/
theorem sf_signs_one_tight (hdet : (rowMat a T).det ≠ 0) {base US UX : Finset ι}
    {x₀ x : κ → ℝ} {D E : ℝ} {k : ℕ} {l : κ}
    (hTb : rowsT T ⊆ base) (hdS : Disjoint base US) (hdX : Disjoint base UX)
    (hcf : ∀ j ∈ base ∪ US, ∀ m, |cf a T j m| ≤ 1)
    (hcard : ((base ∪ US) \ rowsT T).card ≤ k)
    (hnormal : IsNormal a y (base ∪ US) x₀)
    (hself : ∀ j ∈ base ∪ US, cl j → 0 ≤ y j - dotp (a j) x₀)
    (hD : ∀ m, |rhoT a y T x m - rhoT a y T x₀ m| ≤ D)
    (hkey : ∀ m, |kapC a y cl T UX x m - kapC a y cl T US x m| ≤ E)
    (hnt : ∀ m, m ≠ l → cl (T m) → E + k * (Fintype.card κ * D) ≤ rhoT a y T x₀ m)
    (hcorner : ∀ m, Hmat a T (base ∪ US) l m * (rhoT a y T x m - rhoT a y T x₀ m) ≤ 0)
    (hact : ∀ j ∈ (base ∪ US) \ rowsT T, cl j → 0 ≤ y j - dotp (a j) x)
    (hmin : kapC a y cl T UX x l ≤ kapC a y cl T US x l) :
    ∀ m, cl (T m) → 0 ≤ omegaT a y cl T (base ∪ UX) x m := by
  intro m hm
  have hTS : rowsT T ⊆ base ∪ US := le_trans hTb Finset.subset_union_left
  have hω0 := omegaT_opt hdet hTS hnormal hself m
  have hX := omegaT_union (a := a) (y := y) (cl := cl) hdX hTb x m
  have hS := omegaT_union (a := a) (y := y) (cl := cl) hdS hTb x m
  by_cases hml : m = l
  · subst hml
    have hlin := omegaT_sub_eq_Hmat (cl := cl) hdet hself hact m
    rw [hω0] at hlin
    have hH : ∑ m', Hmat a T (base ∪ US) m m' * (rhoT a y T x m' - rhoT a y T x₀ m') ≤ 0 :=
      Finset.sum_nonpos fun m' _ => hcorner m'
    have hw : 0 ≤ rhoT a y T x₀ m := hself (T m) (hTS (mem_rowsT T m)) hm
    linarith
  · have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD m)
    have hdev := abs_omegaT_sub_le (cl := cl) hdet hcf hD (x := x) m
    rw [hω0] at hdev
    have hck : ((base ∪ US) \ rowsT T).card * (Fintype.card κ * D)
        ≤ (k : ℝ) * (Fintype.card κ * D) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    have hk := hkey m
    rw [abs_le] at hdev hk
    have := hnt m hml hm
    linarith [hdev.1, hk.2]

/-- **Угол ячейки решётки** с заданными знаками: для любых `ρ₀` и `h` есть узел `s·z` с
`h_m·(s z_m − ρ₀_m) ≤ 0`, `|s z_m − ρ₀_m| ≤ s` и `|z_m| ≤ |ρ₀_m|/s + 1`. -/
lemma exists_corner {s : ℝ} (hs : 0 < s) (ρ₀ h : κ → ℝ) :
    ∃ z : κ → ℤ, (∀ m, h m * (s * z m - ρ₀ m) ≤ 0) ∧ (∀ m, |s * z m - ρ₀ m| ≤ s)
      ∧ ∀ m, |(z m : ℝ)| ≤ |ρ₀ m| / s + 1 := by
  classical
  refine ⟨fun m => if 0 ≤ h m then ⌊ρ₀ m / s⌋ else ⌈ρ₀ m / s⌉, fun m => ?_, fun m => ?_,
    fun m => ?_⟩
  all_goals
    have hq1 := Int.floor_le (ρ₀ m / s)
    have hq2 := Int.lt_floor_add_one (ρ₀ m / s)
    have hc1 := Int.le_ceil (ρ₀ m / s)
    have hc2 := Int.ceil_lt_add_one (ρ₀ m / s)
    have hsq : s * (ρ₀ m / s) = ρ₀ m := by field_simp
  · by_cases hh : 0 ≤ h m
    · simp only [hh, ite_true]
      have : s * (⌊ρ₀ m / s⌋ : ℝ) ≤ s * (ρ₀ m / s) := mul_le_mul_of_nonneg_left hq1 hs.le
      nlinarith
    · simp only [hh, ite_false]
      have : s * (ρ₀ m / s) ≤ s * (⌈ρ₀ m / s⌉ : ℝ) := mul_le_mul_of_nonneg_left hc1 hs.le
      rw [not_le] at hh
      nlinarith
  · by_cases hh : 0 ≤ h m
    · simp only [hh, ite_true]
      have h1 : s * (⌊ρ₀ m / s⌋ : ℝ) ≤ s * (ρ₀ m / s) := mul_le_mul_of_nonneg_left hq1 hs.le
      have h2 : s * (ρ₀ m / s) < s * ((⌊ρ₀ m / s⌋ : ℝ) + 1) := mul_lt_mul_of_pos_left hq2 hs
      rw [abs_le]; constructor <;> nlinarith
    · simp only [hh, ite_false]
      have h1 : s * (ρ₀ m / s) ≤ s * (⌈ρ₀ m / s⌉ : ℝ) := mul_le_mul_of_nonneg_left hc1 hs.le
      have h2 : s * (⌈ρ₀ m / s⌉ : ℝ) < s * (ρ₀ m / s + 1) := mul_lt_mul_of_pos_left hc2 hs
      rw [abs_le]; constructor <;> nlinarith
  · have hdiv : |ρ₀ m / s| = |ρ₀ m| / s := by rw [abs_div, abs_of_pos hs]
    by_cases hh : 0 ≤ h m
    · simp only [hh, ite_true]
      rw [abs_le]; rw [← hdiv]
      constructor
      · have := neg_abs_le (ρ₀ m / s); linarith
      · have := le_abs_self (ρ₀ m / s); linarith
    · simp only [hh, ite_false]
      rw [abs_le]; rw [← hdiv]
      constructor
      · have := neg_abs_le (ρ₀ m / s); linarith
      · have := le_abs_self (ρ₀ m / s); linarith

/-- Если строки `T` — единичные векторы, то координаты Крамера — сами координаты строки. -/
lemma rowMat_eq_one_of_unit (hunit : ∀ l j', a (T l) j' = if l = j' then 1 else 0) :
    rowMat a T = 1 := by
  ext l j'; simp [rowMat, hunit, Matrix.one_apply]

lemma cf_eq_of_unit (hunit : ∀ l j', a (T l) j' = if l = j' then 1 else 0) (j : ι) (l : κ) :
    cf a T j l = a j l := by
  have hdet : (rowMat a T).det ≠ 0 := by
    rw [rowMat_eq_one_of_unit hunit, Matrix.det_one]; exact one_ne_zero
  rw [row_eq_sum_cf hdet j l]
  simp [hunit]

end RowForm

/-! ### Лемма 2 в портфельных координатах

Строки `rowsK d B G`, цели `targetsK m d`, обрезаются строки активов. Для стационарных весов
строк `ω` на `barK X` вес актива `w_i = ω_i/√d_i` — настоящий портфель, а веса якорей
определяются стационарностью: **вес якоря `l` равен невязке якоря в точке ККТ
`t̂ = Σ_fB'w`** (`anchor_weight_eq`). Цель `objLO` этого портфеля — строчная цель
(`objLO_eq_rowObj`), поэтому для свидетеля Крамера
`objLO(X, w) = ψ̃_X(x) − ‖ω_T − ρ(x)‖²` (`objLO_cramer`). -/

section Portfolio

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- `G Σ_f Gᵀ = 1` при `GᵀG = Σ_f⁻¹`. -/
lemma G_Sf_Gt (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (l l' : κ) :
    ∑ j, ∑ j', G l j * Sf j j' * G l' j' = if l = l' then 1 else 0 := by
  have hGm : (Matrix.of G).transpose * Matrix.of G = Matrix.of P := by
    ext j j'; simpa [Matrix.mul_apply] using hG j j'
  have hPm : Matrix.of P * Matrix.of Sf = 1 := by
    ext j j'; simpa [Matrix.mul_apply, Matrix.one_apply] using hPS j j'
  have h1 : (Matrix.of G).transpose * (Matrix.of G * Matrix.of Sf) = 1 := by
    rw [← Matrix.mul_assoc, hGm, hPm]
  have h2 : (Matrix.of G * Matrix.of Sf) * (Matrix.of G).transpose = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl κ)).mp h1
  have h3 := congrFun (congrFun h2 l) l'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.one_apply] at h3
  rw [← h3, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [Finset.sum_mul]

/-- Стационарность весов строк `barK X` в координате `j₀`: `Σ_l ω_l G_{l j₀} = −(B'w)_{j₀}`. -/
lemma anchor_stat {X : Finset ι} {ω : ι ⊕ κ → ℝ}
    (hst : RowStat (rowsK d B G) (barK X) ω) (j₀ : κ) :
    ∑ l, ω (Sum.inr l) * G l j₀ = -Bw B X (fun i => ω (Sum.inl i) / Real.sqrt (d i)) j₀ := by
  have h := hst (basisVec j₀)
  rw [barK, Finset.sum_disjSum] at h
  have hA : ∑ i ∈ X, ω (Sum.inl i) * dotp (rowsK d B G (Sum.inl i)) (basisVec j₀)
      = Bw B X (fun i => ω (Sum.inl i) / Real.sqrt (d i)) j₀ := by
    simp only [Bw]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [rowsK, dotp, basisVec]
    ring
  have hK : ∑ l, ω (Sum.inr l) * dotp (rowsK d B G (Sum.inr l)) (basisVec j₀)
      = ∑ l, ω (Sum.inr l) * G l j₀ := by
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [rowsK, dotp, basisVec]
  rw [hA, hK] at h
  linarith

/-- **Веса якорей у стационарных весов — невязки якорей в точке ККТ `t̂ = Σ_fB'w`:**
`ω_l = 0 − ⟨G_l, t̂⟩` (в том числе у якорей, вошедших в `T`). -/
theorem anchor_weight_eq (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {X : Finset ι}
    {ω : ι ⊕ κ → ℝ} (hst : RowStat (rowsK d B G) (barK X) ω) (l : κ) :
    ω (Sum.inr l) = targetsK m d (Sum.inr l)
      - dotp (rowsK d B G (Sum.inr l)) (tw Sf B X (fun i => ω (Sum.inl i) / Real.sqrt (d i))) := by
  have hst' := anchor_stat hst
  simp only [targetsK, rowsK, Sum.elim_inr, zero_sub]
  -- `⟨G_l, Σ_f u⟩ = −Σ_{l'} ω_{l'} (GΣ_fGᵀ)_{l l'} = −ω_l`
  have e : dotp (fun j => G l j) (tw Sf B X (fun i => ω (Sum.inl i) / Real.sqrt (d i)))
      = -∑ l', ω (Sum.inr l') * ∑ j, ∑ j', G l j * Sf j j' * G l' j' := by
    have hu : ∀ j', Bw B X (fun i => ω (Sum.inl i) / Real.sqrt (d i)) j'
        = -∑ l', ω (Sum.inr l') * G l' j' := by
      intro j'; rw [hst' j']; ring
    have h1 : dotp (fun j => G l j) (tw Sf B X (fun i => ω (Sum.inl i) / Real.sqrt (d i)))
        = -∑ j, ∑ j', ∑ l', ω (Sum.inr l') * (G l j * Sf j j' * G l' j') := by
      simp only [dotp, tw, hu, Finset.mul_sum, Finset.sum_neg_distrib, mul_neg]
      congr 1
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ =>
        Finset.sum_congr rfl fun l' _ => by ring
    have h2 : ∑ j, ∑ j', ∑ l', ω (Sum.inr l') * (G l j * Sf j j' * G l' j')
        = ∑ l', ω (Sum.inr l') * ∑ j, ∑ j', G l j * Sf j j' * G l' j' := by
      calc ∑ j, ∑ j', ∑ l', ω (Sum.inr l') * (G l j * Sf j j' * G l' j')
          = ∑ j, ∑ l', ∑ j', ω (Sum.inr l') * (G l j * Sf j j' * G l' j') :=
            Finset.sum_congr rfl fun j _ => Finset.sum_comm
        _ = ∑ l', ∑ j, ∑ j', ω (Sum.inr l') * (G l j * Sf j j' * G l' j') := Finset.sum_comm
        _ = ∑ l', ω (Sum.inr l') * ∑ j, ∑ j', G l j * Sf j j' * G l' j' := by
            refine Finset.sum_congr rfl fun l' _ => ?_
            simp only [Finset.mul_sum]
    rw [h1, h2]
  rw [e]
  simp only [G_Sf_Gt hG hPS, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, neg_neg]

/-- **Строчная цель — это `objLO`.** Для стационарных весов строк `barK X` портфель
`w_i = ω_i/√d_i` даёт `objLO(X, w) = Σ_{j∈barK X}(2y_jω_j − ω_j²)`. -/
theorem objLO_eq_rowObj (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {X : Finset ι}
    {ω : ι ⊕ κ → ℝ} (hst : RowStat (rowsK d B G) (barK X) ω) :
    objLO m d B Sf X (fun i => ω (Sum.inl i) / Real.sqrt (d i))
      = rowObj (targetsK m d) (barK X) ω := by
  have hanch := anchor_weight_eq (m := m) hG hPS hst
  -- `Σ_l ω_l² = quadf P t̂ = quadf Σ_f (B'w)`
  have hq : ∑ l, ω (Sum.inr l) ^ 2
      = quadf Sf (Bw B X (fun i => ω (Sum.inl i) / Real.sqrt (d i))) := by
    rw [← quadf_P_tw (Sf := Sf) (B := B) hG hPS X, quadf_eq_sum_sq hG]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hanch l]
    simp only [targetsK, rowsK, Sum.elim_inr, zero_sub, neg_sq]
  set w : ι → ℝ := fun i => ω (Sum.inl i) / Real.sqrt (d i) with hw
  rw [objLO_eq, rowObj, barK, Finset.sum_disjSum]
  have hA : ∑ i ∈ X, (2 * targetsK m d (Sum.inl i : ι ⊕ κ) * ω (Sum.inl i) - ω (Sum.inl i) ^ 2)
      = 2 * (∑ i ∈ X, m i * w i) - ∑ i ∈ X, d i * w i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdi := hd i
    have hs : 0 < Real.sqrt (d i) := Real.sqrt_pos.mpr hdi
    have hsq : Real.sqrt (d i) ^ 2 = d i := Real.sq_sqrt hdi.le
    simp only [targetsK, Sum.elim_inl, hw]
    field_simp
    linear_combination (-(ω (Sum.inl i)) ^ 2) * hsq
  have hK : ∑ l, (2 * targetsK m d (Sum.inr l : ι ⊕ κ) * ω (Sum.inr l) - ω (Sum.inr l) ^ 2)
      = -∑ l, ω (Sum.inr l) ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [targetsK]
  rw [hA, hK, hq]; ring

/-- **Лемма 2 в портфельных координатах.** Свидетель Крамера `ω^Cr` (строки `rowsK`, точка
`x`, `T ⊆ barK X`) задаёт портфель `w_i = ω^Cr_i/√d_i` с

    objLO(X, w) = ψ̃_X(x) − ‖ω_T − ρ(x)‖²,

`w_i = resC_i(x)/√d_i ≥ 0` у активов вне `T`, `w ≥ 0` у активов `T` при `ω_T ≥ 0`; веса якорей
равны их невязкам в точке ККТ портфеля (`anchor_weight_eq`). -/
theorem objLO_cramer (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {X : Finset ι}
    {T : κ → ι ⊕ κ} (hdet : (rowMat (rowsK d B G) T).det ≠ 0) (hTX : rowsT T ⊆ barK X)
    (x : κ → ℝ) :
    objLO m d B Sf X (fun i => wCr (rowsK d B G) (targetsK m d) (fun r => r.isLeft) T (barK X) x
        (Sum.inl i) / Real.sqrt (d i))
      = psiC (rowsK d B G) (targetsK m d) (clOff (fun r => r.isLeft) T) (barK X) x
        - ∑ l, (omegaT (rowsK d B G) (targetsK m d) (fun r => r.isLeft) T (barK X) x l
            - rhoT (rowsK d B G) (targetsK m d) T x l) ^ 2
    ∧ ((∀ l, (T l).isLeft → 0 ≤ omegaT (rowsK d B G) (targetsK m d) (fun r => r.isLeft) T
          (barK X) x l) →
        ∀ i ∈ X, 0 ≤ wCr (rowsK d B G) (targetsK m d) (fun r => r.isLeft) T (barK X) x
          (Sum.inl i) / Real.sqrt (d i)) := by
  refine ⟨?_, fun hsign i hi => ?_⟩
  · rw [objLO_eq_rowObj (m := m) hd hG hPS (isStat_wCr hdet hTX x), rowObj_wCr hdet hTX x]
  · have hmem : (Sum.inl i : ι ⊕ κ) ∈ barK X := inl_mem_barK hi
    have := wCr_nonneg (injective_of_det_ne_zero hdet) hsign (Sum.inl i) hmem (by simp)
    exact div_nonneg this (Real.sqrt_nonneg _)

end Portfolio

/-! ### Точка остановки: п. 7 `SPEC_C1.md` без гипотезы активности неверен

Строки в `ℝ²`: актив `T₁ = e₁`, якорь `T₂ = e₂` (`y = 0`), активы `j₁ = (1, ½)`, `j₂ = (1, −⅖)`,
якорь `(1/10, 0)`. `K`-ка `T = (T₁, T₂)` максимального объёма (`|det| ≤ 1` у всех пар),
`|c_j|_∞ ≤ 1`. Оптимум `x₀ = (1051/10, −799/2000)`: все строки активны, невязки
`(1/20, 799/2000, 1/1000, 1, −1051/100)`, нормальные уравнения выполнены. Строка `T₁` тугая
(`w*₁ = ρ₁(x₀) = 1/20`), `T₂` — якорь (знак не нужен), так что у `T` ровно одна тугая строка.
`H = Σ_{j∉T} c_jc_jᵀ = [[201/100, 1/10], [1/10, 41/100]]`, правило угла ячейки
`sign(Δρ_m) = −sign(H_{1m})` для решётки шага `1` даёт узел `ρ = (0, 0)`,
`Δρ = (−1/20, −799/2000)`, `(HΔρ)₁ ≤ 0`. Но строка `j₁` (`r_{j₁}(x₀) = 1/1000`) в узле
неактивна (`r_{j₁}(x) = −199/800`), и свидетель самого оптимума в узле
`ω₁(S)(x) = −583/10000 < 0 ≤ w*₁`. Представитель `X = S` (ключ и минимум `κ₁` — тривиально)
имеет отрицательный вес строки `T₁`: вывод п. 7 неверен, нужна гипотеза `hact` леммы
`sf_signs_one_tight`. -/

/-- Строки контрпримера. -/
noncomputable def ceA : Fin 5 → Fin 2 → ℝ :=
  ![![1, 0], ![0, 1], ![1, 1 / 2], ![1, -2 / 5], ![1 / 10, 0]]

/-- Цели контрпримера (у якорей `0`). -/
noncomputable def ceY : Fin 5 → ℝ := ![2103 / 20, 0, 83921 / 800, 531299 / 5000, 0]

/-- Обрезаются строки активов `0, 2, 3`. -/
def ceCl : Fin 5 → Bool := ![true, false, true, true, false]

/-- `K`-ка: актив `0` и якорь `1`. -/
def ceT : Fin 2 → Fin 5 := ![0, 1]

/-- Двойственная точка оптимума. -/
noncomputable def ceX0 : Fin 2 → ℝ := ![1051 / 10, -799 / 2000]

/-- Узел — угол ячейки решётки по правилу знаков `H`. -/
noncomputable def ceX : Fin 2 → ℝ := ![2103 / 20, 0]

lemma ceT_unit : ∀ l j', ceA (ceT l) j' = if l = j' then 1 else 0 := by
  intro l j'; fin_cases l <;> fin_cases j' <;> simp [ceA, ceT]

lemma ce_rowsT : rowsT ceT = {0, 1} := by decide

lemma ce_compl : (Finset.univ : Finset (Fin 5)) \ rowsT ceT = {2, 3, 4} := by
  rw [ce_rowsT]; decide

lemma ce_det : (rowMat ceA ceT).det ≠ 0 := by
  rw [rowMat_eq_one_of_unit ceT_unit, Matrix.det_one]; exact one_ne_zero

lemma ce_cf : ∀ j m, cf ceA ceT j m = ceA j m := cf_eq_of_unit ceT_unit

lemma ce_cf_le : ∀ j m, |cf ceA ceT j m| ≤ 1 := by
  intro j m; rw [ce_cf]; fin_cases j <;> fin_cases m <;> norm_num [ceA, abs_le]

/-- `K`-ка `T = (0, 1)` максимального объёма среди всех пяти строк. -/
lemma ce_maxvol : MaxVol ceA Finset.univ ceT := by
  refine ⟨fun l => Finset.mem_univ _, fun T' _ => ?_⟩
  rw [rowMat_eq_one_of_unit ceT_unit, Matrix.det_one, abs_one, Matrix.det_fin_two]
  simp only [rowMat, Matrix.of_apply]
  generalize T' 0 = i; generalize T' 1 = j
  fin_cases i <;> fin_cases j <;> norm_num [ceA, abs_le]

lemma ce_Hmat (m : Fin 2) : Hmat ceA ceT Finset.univ 0 m = if m = 0 then 201 / 100 else 1 / 10 := by
  simp only [Hmat, ce_compl, ce_cf]
  fin_cases m <;> norm_num [Finset.sum_insert, ceA]

/-- **Контрпример к п. 7 `SPEC_C1.md`.** Все гипотезы `sf_signs_one_tight` с `base = {0,1,4}`,
`U_S = U_X = {2,3}` (так что `X = S`, ключ и минимум `κ₁` выполнены тривиально, `E = 0`),
`k = 3`, `D = 2/5`, `l = 0` выполнены, кроме `hact` (строка `2` неактивна в узле), а вывод
неверен: вес тугой строки `T 0` у представителя `−583/10000 < 0`. При этом `T` —
максимального объёма, у `T` одна тугая строка (вторая — якорь), и узел — угол ячейки
решётки шага `1` по правилу знаков `H`. -/
theorem spec7_counterexample :
    (rowMat ceA ceT).det ≠ 0
    ∧ MaxVol ceA Finset.univ ceT
    ∧ (∀ j m, |cf ceA ceT j m| ≤ 1)
    ∧ IsNormal ceA ceY Finset.univ ceX0
    ∧ (∀ j ∈ (Finset.univ : Finset (Fin 5)), ceCl j → 0 ≤ ceY j - dotp (ceA j) ceX0)
    ∧ ((Finset.univ : Finset (Fin 5)) \ rowsT ceT).card ≤ 3
    ∧ (∀ m, |rhoT ceA ceY ceT ceX m - rhoT ceA ceY ceT ceX0 m| ≤ 2 / 5)
    ∧ (∀ m, m ≠ 0 → ceCl (ceT m) → False)
    ∧ (∀ m, Hmat ceA ceT Finset.univ 0 m
        * (rhoT ceA ceY ceT ceX m - rhoT ceA ceY ceT ceX0 m) ≤ 0)
    ∧ rhoT ceA ceY ceT ceX0 0 = 1 / 20
    ∧ ceY 2 - dotp (ceA 2) ceX0 = 1 / 1000
    ∧ ceY 2 - dotp (ceA 2) ceX < 0
    ∧ omegaT ceA ceY ceCl ceT Finset.univ ceX 0 = -583 / 10000 := by
  refine ⟨ce_det, ce_maxvol, ce_cf_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    simp only [mom, dotp, Fin.sum_univ_succ, Fin.sum_univ_zero, ceA, ceY, ceX0]
    simp
    ring
  · intro j _ hj
    fin_cases j <;> simp_all [ceCl, ceA, ceY, ceX0, dotp, Fin.sum_univ_two] <;> norm_num
  · rw [ce_compl]; decide
  · intro m
    fin_cases m <;> norm_num [rhoT, ceT, ceA, ceY, ceX, ceX0, dotp, Fin.sum_univ_two, abs_le]
  · intro m hm hc; fin_cases m
    · exact hm rfl
    · simp [ceCl, ceT] at hc
  · intro m
    rw [ce_Hmat]
    fin_cases m <;> norm_num [rhoT, ceT, ceA, ceY, ceX, ceX0, dotp, Fin.sum_univ_two]
  · norm_num [rhoT, ceT, ceA, ceY, ceX0, dotp, Fin.sum_univ_two]
  · norm_num [ceA, ceY, ceX0, dotp, Fin.sum_univ_two]
  · norm_num [ceA, ceY, ceX, dotp, Fin.sum_univ_two]
  · simp only [omegaT, kapC, ce_compl, ce_cf]
    norm_num [Finset.sum_insert, resC, ceCl, ceA, ceY, ceX, dotp, Fin.sum_univ_two, max_def]

/-- **Лемма 7 спецификации без гипотезы активности ложна:** утверждение `sf_signs_one_tight`,
из которого убрана гипотеза `hact` (строки `S̄∖T` активны в узле), неверно уже при `K = 2`,
пяти строках, `X = S` (`E = 0`, минимум `κ_l` — тривиально) и угловом узле по правилу знаков `H`. -/
theorem spec7_fails :
    ¬ ∀ (a : Fin 5 → Fin 2 → ℝ) (y : Fin 5 → ℝ) (cl : Fin 5 → Bool) (T : Fin 2 → Fin 5)
        (base US UX : Finset (Fin 5)) (x₀ x : Fin 2 → ℝ) (D E : ℝ) (k : ℕ) (l : Fin 2),
        (rowMat a T).det ≠ 0 → rowsT T ⊆ base → Disjoint base US → Disjoint base UX →
        (∀ j ∈ base ∪ US, ∀ m, |cf a T j m| ≤ 1) → ((base ∪ US) \ rowsT T).card ≤ k →
        IsNormal a y (base ∪ US) x₀ → (∀ j ∈ base ∪ US, cl j → 0 ≤ y j - dotp (a j) x₀) →
        (∀ m, |rhoT a y T x m - rhoT a y T x₀ m| ≤ D) →
        (∀ m, |kapC a y cl T UX x m - kapC a y cl T US x m| ≤ E) →
        (∀ m, m ≠ l → cl (T m) → E + k * (Fintype.card (Fin 2) * D) ≤ rhoT a y T x₀ m) →
        (∀ m, Hmat a T (base ∪ US) l m * (rhoT a y T x m - rhoT a y T x₀ m) ≤ 0) →
        kapC a y cl T UX x l ≤ kapC a y cl T US x l →
        ∀ m, cl (T m) → 0 ≤ omegaT a y cl T (base ∪ UX) x m := by
  intro h
  have hU : ({0, 1, 4} : Finset (Fin 5)) ∪ {2, 3} = Finset.univ := by decide
  obtain ⟨hdet, -, hcf, hnorm, hself, hcard, hD, hnt, hcorner, -, -, -, hω⟩ :=
    spec7_counterexample
  have h0 := h ceA ceY ceCl ceT {0, 1, 4} {2, 3} {2, 3} ceX0 ceX (2 / 5) 0 3 0 hdet
    (by rw [ce_rowsT]; decide) (by decide) (by decide)
    (by rw [hU]; exact fun j _ m => hcf j m) (by rw [hU]; exact hcard)
    (by rw [hU]; exact hnorm) (by rw [hU]; exact hself) hD (by intro m; simp)
    (fun m hm hc => (hnt m hm hc).elim) (by rw [hU]; exact hcorner) le_rfl 0 rfl
  rw [hU, hω] at h0
  norm_num at h0

/-! ### Непустота гипотез лемм шага

Те же строки, другой оптимум: `x₀ = (205, 1/10)`, невязки `(1/20, −1/10, 1, 1, −41/2)`
(строка `T₁` по-прежнему тугая, а у активов `j₁, j₂` запас `1`). Узел — угол ячейки решётки шага
`1` по правилу знаков `H`: `ρ = (0, −1)`, `Δρ = (−1/20, −9/10)`; строки `j₁, j₂` в нём активны
(`1/2` и `131/100`). Здесь выполнены все гипотезы Лемм 1–3, 5, 7. -/

/-- Цели положительного примера. -/
noncomputable def exY : Fin 5 → ℝ := ![4101 / 20, 0, 4121 / 20, 5149 / 25, 0]

/-- Двойственная точка положительного примера. -/
noncomputable def exX0 : Fin 2 → ℝ := ![205, 1 / 10]

/-- Узел положительного примера (угол ячейки). -/
noncomputable def exX : Fin 2 → ℝ := ![4101 / 20, 1]

lemma ex_normal : IsNormal ceA exY Finset.univ exX0 := by
  intro v
  simp only [mom, dotp, Fin.sum_univ_succ, Fin.sum_univ_zero, ceA, exY, exX0]
  simp
  ring

lemma ex_self : ∀ j ∈ (Finset.univ : Finset (Fin 5)), ceCl j → 0 ≤ exY j - dotp (ceA j) exX0 := by
  intro j _ hj
  fin_cases j <;> simp_all [ceCl, ceA, exY, exX0, dotp, Fin.sum_univ_two] <;> norm_num

lemma ex_drho : ∀ m, rhoT ceA exY ceT exX m - rhoT ceA exY ceT exX0 m
    = if m = 0 then -1 / 20 else -9 / 10 := by
  intro m; fin_cases m <;> norm_num [rhoT, ceT, ceA, exY, exX, exX0, dotp, Fin.sum_univ_two]

lemma ex_univ : ({0, 1, 4} : Finset (Fin 5)) ∪ {2, 3} = Finset.univ := by decide

/-- Лемма 1 выполнима: `ψ_S(x) − F_LO(S) ≤ |S|K·‖Δρ‖²` с `|S| = 5`, `K = 2`. -/
example : psiC ceA exY ceCl Finset.univ exX - psiC ceA exY ceCl Finset.univ exX0
    ≤ ((Finset.univ : Finset (Fin 5)).card * Fintype.card (Fin 2) : ℝ)
      * ∑ l, (rhoT ceA exY ceT exX l - rhoT ceA exY ceT exX0 l) ^ 2 :=
  sf_node_maxvol ce_maxvol ce_det ex_normal ex_self exX

/-- Лемма 3 выполнима: `F = F_LO(S) = ψ_S(x₀)`, `C = |S|K = 10`. -/
example : ∑ l, kapC ceA exY ceCl ceT Finset.univ exX l ^ 2
    ≤ ((Finset.univ : Finset (Fin 5)).card * Fintype.card (Fin 2) : ℝ)
      * (psiC ceA exY ceCl Finset.univ exX - psiC ceA exY ceCl Finset.univ exX0) :=
  sf_grad ce_det (fun v => gram_le_card_mul_gramK ce_maxvol ce_det v) (by norm_num)
    (psiC_min_of_normal_of_nonneg ex_normal ex_self) exX

/-- Лемма 2 выполнима (`X = S`, узел `x`). -/
example : rowObj exY Finset.univ (wCr ceA exY ceCl ceT Finset.univ exX)
    = psiC ceA exY (clOff ceCl ceT) Finset.univ exX
      - ∑ l, (omegaT ceA exY ceCl ceT Finset.univ exX l - rhoT ceA exY ceT exX l) ^ 2 :=
  (cramer_witness ce_det (Finset.subset_univ _) exX).2.2.2.1

/-- Лемма 4, округление: разные наборы `{0}` и `{1}` с равными ключами `⌊f/η⌋`. -/
example : |∑ i ∈ ({0} : Finset (Fin 2)), (![1 / 3, 1 / 2] : Fin 2 → ℝ) i
    - ∑ i ∈ ({1} : Finset (Fin 2)), (![1 / 3, 1 / 2] : Fin 2 → ℝ) i| < (1 : ℕ) * 1 := by
  refine abs_sum_sub_lt_of_floor_eq one_pos one_pos (by simp) (by simp) ?_
  norm_num [Int.floor_eq_iff]

/-- Лемма 7 выполнима (одна тугая строка `T 0`, все гипотезы, включая `hact`): веса строк `T`
у представителя неотрицательны. -/
theorem ex_signs : ∀ m, ceCl (ceT m) →
    0 ≤ omegaT ceA exY ceCl ceT (({0, 1, 4} : Finset (Fin 5)) ∪ {2, 3}) exX m := by
  have hU := ex_univ
  refine sf_signs_one_tight (k := 3) (D := 9 / 10) (E := 0) (l := 0) (x₀ := exX0) ce_det
    ?_ (by decide) (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (le_refl _)
  · rw [ce_rowsT]; decide
  · intro j _ m; exact ce_cf_le j m
  · rw [hU, ce_compl]; decide
  · rw [hU]; exact ex_normal
  · rw [hU]; exact ex_self
  · intro m; rw [ex_drho]; split_ifs <;> norm_num [abs_le]
  · intro m; simp
  · intro m hm hc; fin_cases m
    · exact absurd rfl hm
    · simp [ceCl, ceT] at hc
  · intro m; rw [hU, ce_Hmat, ex_drho]; split_ifs <;> norm_num
  · rw [hU, ce_compl]
    intro j hj hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · norm_num [ceA, exY, exX, dotp, Fin.sum_univ_two]
    · norm_num [ceA, exY, exX, dotp, Fin.sum_univ_two]
    · simp [ceCl] at hc

/-- Лемма 5 выполнима: представитель `X = S` в угловом узле (`δ = Δ = 0`, знак — `ex_signs`). -/
example (x' : Fin 2 → ℝ) :
    psiC ceA exY ceCl Finset.univ exX0 - 0
        - (((Finset.univ : Finset (Fin 5)).card * Fintype.card (Fin 2) : ℝ)
            * Real.sqrt (∑ l, (rhoT ceA exY ceT exX l - rhoT ceA exY ceT exX0 l) ^ 2) + 0) ^ 2
      ≤ psiC ceA exY ceCl Finset.univ x' := by
  have hsign : ∀ l, ceCl (ceT l) → 0 ≤ omegaT ceA exY ceCl ceT Finset.univ exX l := by
    have := ex_signs; rwa [ex_univ] at this
  exact sf_step ce_det (Finset.subset_univ _) (Finset.subset_univ _)
    (fun v => gram_le_card_mul_gramK ce_maxvol ce_det v) (by norm_num) ex_normal ex_self
    (by simp) (le_refl _) (by simp) hsign x'

end SparseSharpe.Factor
