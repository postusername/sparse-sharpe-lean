import SparseSharpe.Basic

set_option linter.style.header false

/-!
# Форма инерции и ядро FPTAS

Главное наблюдение: при любом `t` значение `F(S)` записывается **без сокращения**
как разность `φ_S(t) − M_t(S)²/κ(S)`, где

* `κ(S) = 1/σ² + Σ_{i∈S} β_i²/d_i`  — суммарный вес (всегда `> 0`);
* `M_t(S) = −t/σ² + Σ_{i∈S} β_i(m_i − tβ_i)/d_i` — взвешенный первый момент;
* `φ_S(t) = t²/σ² + Σ_{i∈S} (m_i − tβ_i)²/d_i` — взвешенный второй момент.

Это в точности «взвешенная инерция» набора точек `r_i = m_i/β_i` с весами
`u_i = β_i²/d_i` и обязательной точкой-якорем `r_0 = 0`, `u_0 = 1/σ²`
(запись через `m, β, d` корректна и при `β_i = 0`, когда `r_i` не определено).

Отсюда три факта, на которых стоит FPTAS:

* `Mt_sq_le_kappa_mul_phi` — `M_t² ≤ κ·φ` (Коши–Буняковский);
* `Mt_prefix_bound` — та же оценка **для любого подмножества** `S' ⊆ S`, но
  с `κ(S)` и `φ_S(t)` от объемлющего `S`: диапазон промежуточных значений `M`
  в динамике измеряется в единицах `√(κ·φ)`;
* `phi_le_of_small_dev` — если `t` близко к `t̂(S)`, то `φ_S(t) ≤ (1+ε)F(S)`,
  и тогда `√(κφ)` и требуемая точность `√(ε·F·κ)` отличаются в `O(1/√ε)` раз
  **независимо от величин входа**. Это и делает округление полиномиальным.
-/

namespace SparseSharpe

open Finset

variable {ι : Type*}

namespace OneFactor

/-- Взвешенный первый момент в координатах, сдвинутых на `t`
(с учётом точки-якоря `r₀ = 0`, `u₀ = 1/σ²`). -/
noncomputable def Mt (P : OneFactor ι) (S : Finset ι) (t : ℝ) : ℝ :=
  -(t / P.σ2) + ∑ i ∈ S, P.β i * (P.m i - t * P.β i) / P.d i

variable {P : OneFactor ι} {S S' : Finset ι} {t : ℝ}

/-- `M_t(S) = κ(S)·(t̂(S) − t)`. -/
lemma Mt_eq : P.Mt S t = P.kappa S * (P.that S - t) := by
  have hσ := P.hσ2.ne'
  have e1 : ∑ i ∈ S, P.β i * (P.m i - t * P.β i) / P.d i
      = P.Acoef S - t * ∑ i ∈ S, (P.β i) ^ 2 / P.d i := by
    rw [OneFactor.Acoef, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := (P.hd i).ne'
    field_simp
  have hB : ∑ i ∈ S, (P.β i) ^ 2 / P.d i = P.kappa S - 1 / P.σ2 := by
    simp [OneFactor.kappa]
  rw [OneFactor.Mt, e1, hB, Acoef_eq]
  field_simp
  ring

/-- **Форма инерции.** Для любого `t`:  `F(S) = φ_S(t) − M_t(S)²/κ(S)`.
Сокращения нет: оба члена справа неотрицательны, см. `Mt_sq_le_kappa_mul_phi`. -/
theorem Fval_eq_phi_sub (t : ℝ) :
    P.Fval S = P.phi S t - (P.Mt S t) ^ 2 / P.kappa S := by
  have hκ : P.kappa S ≠ 0 := kappa_ne_zero
  rw [Mt_eq, phi_eq_completed_square]
  field_simp
  ring

lemma phi_nonneg : 0 ≤ P.phi S t := by
  have h1 : (0:ℝ) ≤ t ^ 2 / P.σ2 := by have := P.hσ2; positivity
  have h2 : (0:ℝ) ≤ ∑ i ∈ S, (P.m i - t * P.β i) ^ 2 / P.d i :=
    Finset.sum_nonneg fun i _ => by have := (P.hd i).le; positivity
  simpa [OneFactor.phi] using add_nonneg h1 h2

lemma Fval_nonneg : 0 ≤ P.Fval S := phi_that ▸ phi_nonneg

/-- Коши–Буняковский в форме `M_t(S)² ≤ κ(S)·φ_S(t)`. -/
theorem Mt_sq_le_kappa_mul_phi : (P.Mt S t) ^ 2 ≤ P.kappa S * P.phi S t := by
  have h := Fval_eq_phi_sub (P := P) (S := S) t
  have h0 : (0:ℝ) ≤ P.Fval S := Fval_nonneg
  have hκ : 0 < P.kappa S := kappa_pos
  have : (P.Mt S t) ^ 2 / P.kappa S ≤ P.phi S t := by linarith
  calc (P.Mt S t) ^ 2 = P.kappa S * ((P.Mt S t) ^ 2 / P.kappa S) := by field_simp
    _ ≤ P.kappa S * P.phi S t := by exact mul_le_mul_of_nonneg_left this hκ.le

/-! ### Монотонность по носителю -/

lemma kappa_mono (h : S ⊆ S') : P.kappa S ≤ P.kappa S' := by
  have hs : ∑ i ∈ S, (P.β i) ^ 2 / P.d i ≤ ∑ i ∈ S', (P.β i) ^ 2 / P.d i :=
    Finset.sum_le_sum_of_subset_of_nonneg h
      (fun i _ _ => by have := (P.hd i).le; positivity)
  simp only [OneFactor.kappa]
  linarith

lemma phi_mono (h : S ⊆ S') : P.phi S t ≤ P.phi S' t := by
  have hs : ∑ i ∈ S, (P.m i - t * P.β i) ^ 2 / P.d i
      ≤ ∑ i ∈ S', (P.m i - t * P.β i) ^ 2 / P.d i :=
    Finset.sum_le_sum_of_subset_of_nonneg h
      (fun i _ _ => by have := (P.hd i).le; positivity)
  simp only [OneFactor.phi]
  linarith

/-- Монотонность `F` по включению носителей. -/
theorem Fval_mono (h : S ⊆ S') : P.Fval S ≤ P.Fval S' :=
  le_trans (Fval_le_phi (P := P) (S := S) (P.that S'))
    (le_trans (phi_mono h) (le_of_eq phi_that))

/-- **Оценка диапазона первого момента по подмножествам (факт (F3)).**
Для любого `S' ⊆ S` величина `M_t(S')` лежит в `[−√(κ(S)φ_S(t)), √(κ(S)φ_S(t))]`.
Именно поэтому в динамике достаточно `O(k/√ε)` корзин по `M`. -/
theorem Mt_prefix_bound (h : S' ⊆ S) :
    (P.Mt S' t) ^ 2 ≤ P.kappa S * P.phi S t := by
  refine le_trans Mt_sq_le_kappa_mul_phi ?_
  exact mul_le_mul (kappa_mono h) (phi_mono h) phi_nonneg
    (le_trans kappa_pos.le (kappa_mono h))


/-! ### Теорема E: форма без вычитания (тождество Лагранжа) -/

/-- `B(S) = Σ_{i∈S} β_i²/d_i = κ(S) − 1/σ²`. -/
lemma Bcoef_eq : ∑ i ∈ S, (P.β i) ^ 2 / P.d i = P.kappa S - 1 / P.σ2 := by
  simp [OneFactor.kappa]

/-- **Тождество Лагранжа** во взвешенной форме:
`C·B − A² = ½ Σ_i Σ_j (m_iβ_j − m_jβ_i)²/(d_i d_j)`. -/
theorem lagrange_identity :
    P.Ccoef S * (∑ i ∈ S, (P.β i) ^ 2 / P.d i) - (P.Acoef S) ^ 2
      = (1 / 2) * ∑ i ∈ S, ∑ j ∈ S,
          (P.m i * P.β j - P.m j * P.β i) ^ 2 / (P.d i * P.d j) := by
  have hexp : ∀ i ∈ S, ∀ j ∈ S,
      (P.m i * P.β j - P.m j * P.β i) ^ 2 / (P.d i * P.d j)
        = (P.m i) ^ 2 / P.d i * ((P.β j) ^ 2 / P.d j)
          - 2 * ((P.m i * P.β i / P.d i) * (P.m j * P.β j / P.d j))
          + (P.m j) ^ 2 / P.d j * ((P.β i) ^ 2 / P.d i) := by
    intro i _ j _
    have hi := (P.hd i).ne'
    have hj := (P.hd j).ne'
    field_simp
    ring
  have hdouble : ∑ i ∈ S, ∑ j ∈ S,
      (P.m i * P.β j - P.m j * P.β i) ^ 2 / (P.d i * P.d j)
      = 2 * (P.Ccoef S * (∑ i ∈ S, (P.β i) ^ 2 / P.d i)) - 2 * (P.Acoef S) ^ 2 := by
    rw [Finset.sum_congr rfl fun i hi =>
      Finset.sum_congr rfl fun j hj => hexp i hi j hj]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul]
    simp only [OneFactor.Ccoef, OneFactor.Acoef]
    ring
  rw [hdouble]
  ring

/-- **Теорема E (форма без вычитания).**

    F(S) = [ (1/σ²)·Σ_{i∈S} m_i²/d_i + ½ Σ_{i,j∈S} (m_iβ_j − m_jβ_i)²/(d_i d_j) ] / κ(S).

Числитель и знаменатель — суммы неотрицательных слагаемых: сокращения нет.
(Двойная сумма с множителем ½ — это сумма по неупорядоченным парам `{i,j}`,
диагональ даёт нули.) -/
theorem Fval_pairwise :
    P.Fval S = ((1 / P.σ2) * P.Ccoef S
        + (1 / 2) * ∑ i ∈ S, ∑ j ∈ S,
            (P.m i * P.β j - P.m j * P.β i) ^ 2 / (P.d i * P.d j)) / P.kappa S := by
  have hκ : P.kappa S ≠ 0 := kappa_ne_zero
  have hlag := lagrange_identity (P := P) (S := S)
  have hB := Bcoef_eq (P := P) (S := S)
  rw [OneFactor.Fval]
  rw [← hlag, hB]
  field_simp
  ring

/-! ### Лемма G: когда точка сетки хороша -/

/-- Отдельное слагаемое `φ_S(t̂)` не превосходит `F(S)`. -/
lemma term_le_Fval {j : ι} (hj : j ∈ S) :
    (P.m j - P.that S * P.β j) ^ 2 / P.d j ≤ P.Fval S := by
  rw [← phi_that, OneFactor.phi]
  have h1 : (0:ℝ) ≤ (P.that S) ^ 2 / P.σ2 := by have := P.hσ2; positivity
  have h2 : (P.m j - P.that S * P.β j) ^ 2 / P.d j
      ≤ ∑ i ∈ S, (P.m i - P.that S * P.β i) ^ 2 / P.d i :=
    Finset.single_le_sum (f := fun i => (P.m i - P.that S * P.β i) ^ 2 / P.d i)
      (fun i _ => by have := (P.hd i).le; positivity) hj
  linarith

/-- Вклад якоря тоже не превосходит `F(S)`. -/
lemma anchor_le_Fval : (P.that S) ^ 2 / P.σ2 ≤ P.Fval S := by
  rw [← phi_that, OneFactor.phi]
  have h2 : (0:ℝ) ≤ ∑ i ∈ S, (P.m i - P.that S * P.β i) ^ 2 / P.d i :=
    Finset.sum_nonneg fun i _ => by have := (P.hd i).le; positivity
  linarith

/-- **Лемма G (общая форма).** Если отклонение `t` от `t̂(S)`, взвешенное кривизной,
не превосходит `ε·c` для какого-нибудь `c ≤ F(S)`, то `φ_S(t) ≤ (1+ε)·F(S)`. -/
theorem phi_le_of_small_dev {ε c : ℝ} (hε : 0 ≤ ε)
    (hdev : P.kappa S * (t - P.that S) ^ 2 ≤ ε * c) (hc : c ≤ P.Fval S) :
    P.phi S t ≤ (1 + ε) * P.Fval S := by
  have h := phi_eq_completed_square (P := P) (S := S) t
  nlinarith [hdev, hc, hε]

/-- **Лемма G, вариант «тяжёлый актив».** Пусть `j ∈ S`, вес актива `j` составляет
не менее `1/(k+1)` от всей кривизны, и `t` отстоит от `t̂(S)` так, что
`(k+1)·(β_j²/d_j)·(t − t̂)² ≤ ε·(m_j − t̂β_j)²/d_j`
(то есть `|t − t̂| ≤ √(ε/(k+1))·|m_j/β_j − t̂|`). Тогда `φ_S(t) ≤ (1+ε)·F(S)`. -/
theorem phi_le_of_near_that {j : ι} {ε : ℝ} {N : ℝ} (hj : j ∈ S) (hε : 0 ≤ ε)
    (hcurv : P.kappa S ≤ N * ((P.β j) ^ 2 / P.d j))
    (hdev : N * ((P.β j) ^ 2 / P.d j) * (t - P.that S) ^ 2
      ≤ ε * ((P.m j - P.that S * P.β j) ^ 2 / P.d j)) :
    P.phi S t ≤ (1 + ε) * P.Fval S := by
  refine phi_le_of_small_dev hε ?_ (term_le_Fval hj)
  refine le_trans (mul_le_mul_of_nonneg_right hcurv (sq_nonneg _)) hdev

/-! ### Лемма об округлении

Чисто алгебраическая оценка: если в состоянии динамики вместо `(M, W, Q)`
хранится `(M', W', Q')` с `|M' − M| ≤ δ`, `1/W' ≤ c/W`, `Q ≤ Q'`,
то инерция не падает ниже явной величины. -/

theorem rounding_bound {W W' Q Q' M M' δ c : ℝ}
    (hW : 0 < W) (hW' : 0 < W') (hc : 1 / W' ≤ c / W)
    (hQ : Q ≤ Q') (hM : |M' - M| ≤ δ) (hcpos : 0 ≤ c) :
    Q - c * (M ^ 2 + 2 * δ * |M| + δ ^ 2) / W ≤ Q' - M' ^ 2 / W' := by
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) hM
  have hb : 0 ≤ M ^ 2 + 2 * δ * |M| + δ ^ 2 := by positivity
  have key : M * (M' - M) ≤ |M| * δ := by
    calc M * (M' - M) ≤ |M * (M' - M)| := le_abs_self _
      _ = |M| * |M' - M| := abs_mul _ _
      _ ≤ |M| * δ := by
          exact mul_le_mul_of_nonneg_left hM (abs_nonneg M)
  have key2 : (M' - M) ^ 2 ≤ δ ^ 2 := by
    have h0 := abs_nonneg (M' - M)
    nlinarith [sq_abs (M' - M)]
  have hMsq : M' ^ 2 ≤ M ^ 2 + 2 * δ * |M| + δ ^ 2 := by nlinarith [key, key2]
  have h5 : M' ^ 2 / W' ≤ (M ^ 2 + 2 * δ * |M| + δ ^ 2) / W' := by gcongr
  have hfrac : (M ^ 2 + 2 * δ * |M| + δ ^ 2) / W'
      ≤ c * (M ^ 2 + 2 * δ * |M| + δ ^ 2) / W := by
    have e1 : (M ^ 2 + 2 * δ * |M| + δ ^ 2) / W'
        = (M ^ 2 + 2 * δ * |M| + δ ^ 2) * (1 / W') := by field_simp
    have e2 : c * (M ^ 2 + 2 * δ * |M| + δ ^ 2) / W
        = (M ^ 2 + 2 * δ * |M| + δ ^ 2) * (c / W) := by field_simp
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hc hb
  linarith

end OneFactor

end SparseSharpe
