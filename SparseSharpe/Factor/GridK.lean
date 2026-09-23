import SparseSharpe.Factor.MaxVolume

set_option linter.style.header false

/-!
# Теорема H и сетка: `K`-мерная замена Леммы G

`theoremH` — K-мерный аналог Леммы G: если узел `t` отстоит от `t̂(S)` не больше чем на
`√(εF/C)` **в координатах невязок максимально-объёмной `K`-ки** (`C ≥ |S|·K`), то
`φ_S(t) ≤ (1+ε)F(S)`.

`exists_grid_node` — что такой узел есть в решётке `s·ℤ^K` с шагом `s = 2√(εV/(K·C))`,
когда `V ≤ F(S) ≤ 2V`. Главное в нём — **оценка на номера узлов**:

    |z_l| ≤ √(K·C/(2ε)) + ½

не содержит ни `V`, ни каких-либо величин входа. Это и есть `K`-мерный аналог
`Mt_range_over_precision`: число узлов сетки по каждой оси равно `O(√(KC/ε))`,
то есть `O((k+K)K/√ε)`, и от масштаба задачи не зависит.
-/

namespace SparseSharpe.Factor

open Finset Matrix

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {S : Finset ι} {T : κ → ι} {th t : κ → ℝ}

/-- **Теорема H (K-мерная Лемма G).** Отклонение узла измеряется в координатах
невязок максимально-объёмной `K`-ки; множитель `C` — любая мажоранта `|S|·K`. -/
theorem theoremH (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0)
    (hnormal : IsNormal a y S th) {ε C : ℝ}
    (hC : (S.card * Fintype.card κ : ℝ) ≤ C) (hCpos : 0 < C)
    (hh : gramK a T (t - th) ≤ ε * phi a y S th / C) :
    phi a y S t ≤ (1 + ε) * phi a y S th := by
  have hg := gram_le_card_mul_gramK hmax hdet (t - th)
  have hK0 := gramK_nonneg a T (t - th)
  have h2 : (S.card * Fintype.card κ : ℝ) * gramK a T (t - th) ≤ C * gramK a T (t - th) :=
    mul_le_mul_of_nonneg_right hC hK0
  have h3 : C * gramK a T (t - th) ≤ C * (ε * phi a y S th / C) :=
    mul_le_mul_of_nonneg_left hh hCpos.le
  have h4 : C * (ε * phi a y S th / C) = ε * phi a y S th := by field_simp
  rw [phi_eq_add hnormal t]
  linarith

/-- Узел решётки `s·ℤ` не дальше `s/2` от любой точки, покоординатно. -/
theorem exists_grid_point (s : ℝ) (hs : 0 < s) (x : κ → ℝ) :
    ∃ z : κ → ℤ, (∀ l, |s * (z l : ℝ) - x l| ≤ s / 2) ∧
      (∀ l, |(z l : ℝ)| ≤ |x l| / s + 1 / 2) := by
  refine ⟨fun l => round (x l / s), fun l => ?_, fun l => ?_⟩
  · have h := abs_sub_round (x l / s)
    have : s * (round (x l / s) : ℝ) - x l = -(s * (x l / s - (round (x l / s) : ℝ))) := by
      field_simp; ring
    rw [this, abs_neg, abs_mul, abs_of_pos hs]
    calc s * |x l / s - (round (x l / s) : ℝ)| ≤ s * (1 / 2) :=
          mul_le_mul_of_nonneg_left h hs.le
      _ = s / 2 := by ring
  · have h := abs_sub_round (x l / s)
    have h2 : |(round (x l / s) : ℝ)| ≤ |x l / s| + 1 / 2 := by
      have := abs_sub_abs_le_abs_sub (x l / s) ((round (x l / s) : ℝ))
      cases' abs_cases (x l / s - (round (x l / s) : ℝ)) with hc hc <;>
        cases' abs_cases (x l / s) with hd hd <;>
        cases' abs_cases ((round (x l / s) : ℝ)) with he he <;> linarith [h]
    rwa [abs_div, abs_of_pos hs] at h2

/-- Узел сетки по заданным невязкам существует: при `det A_T ≠ 0` система
`⟨a_{T_l}, t⟩ = g_l` разрешима. -/
theorem exists_point_with_residuals (hdet : (rowMat a T).det ≠ 0) (g : κ → ℝ) :
    ∃ t : κ → ℝ, ∀ l, dotp (a (T l)) t = g l := by
  refine ⟨(rowMat a T)⁻¹ *ᵥ g, fun l => ?_⟩
  have hinv : (rowMat a T) *ᵥ ((rowMat a T)⁻¹ *ᵥ g) = g := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have h2 := congrFun hinv l
  simpa [Matrix.mulVec, dotProduct, rowMat, dotp] using h2

/-- Отношение «радиус сетки / шаг» не зависит ни от `V`, ни от величин входа. -/
lemma grid_ratio {V ε C Kc : ℝ} (hV : 0 < V) (hε : 0 < ε) (hC : 0 < C) (hKc : 0 < Kc) :
    Real.sqrt (2 * V) / (2 * Real.sqrt (ε * V / (Kc * C))) = Real.sqrt (Kc * C / (2 * ε)) := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hw : (0:ℝ) ≤ 4 * (ε * V / (Kc * C)) := by positivity
  have h1 : 2 * Real.sqrt (ε * V / (Kc * C)) = Real.sqrt (4 * (ε * V / (Kc * C))) := by
    rw [Real.sqrt_mul (by norm_num) _, h4]
  rw [h1, ← Real.sqrt_div (by positivity)]
  congr 1
  field_simp
  ring

/-- **Существование годного узла сетки.** При `V ≤ F` и `F ≤ 2V` в решётке с шагом
`s = 2√(εV/(K·C))` есть узел `z`, задающий точку `t` с `φ_S(t) ≤ (1+ε)F`, причём
номера узлов ограничены величиной `√(KC/(2ε)) + ½`, свободной от данных входа. -/
theorem exists_grid_node (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0)
    (hnormal : IsNormal a y S th) {ε C V s : ℝ}
    (hC : (S.card * Fintype.card κ : ℝ) ≤ C) (hCpos : 0 < C)
    (hε : 0 < ε) (hV : 0 < V) (hVF : V ≤ phi a y S th) (hFV : phi a y S th ≤ 2 * V)
    (hKc : 0 < (Fintype.card κ : ℝ))
    (hs : s = 2 * Real.sqrt (ε * V / ((Fintype.card κ : ℝ) * C))) :
    ∃ z : κ → ℤ,
      (∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C / (2 * ε)) + 1 / 2) ∧
      (∀ t : κ → ℝ, (∀ l, dotp (a (T l)) t = y (T l) + s * (z l : ℝ)) →
        phi a y S t ≤ (1 + ε) * phi a y S th) := by
  set Kc := (Fintype.card κ : ℝ) with hKcdef
  set F := phi a y S th with hFdef
  have hspos : 0 < s := by
    rw [hs]; have : 0 < ε * V / (Kc * C) := by positivity
    simpa using (Real.sqrt_pos.mpr this)
  -- невязки оптимальной точки
  set r : ι → ℝ := fun i => y i - dotp (a i) th with hr
  have hFr : F = ∑ i ∈ S, (r i) ^ 2 := by
    rw [hFdef, phi]; exact Finset.sum_congr rfl fun i _ => by rw [hr]; ring
  -- каждая невязка `K`-ки не больше `√F ≤ √(2V)` по модулю
  have hrT : ∀ l, (r (T l)) ^ 2 ≤ F := by
    intro l
    have hsum := sum_comp_le hmax.1 (injective_of_det_ne_zero hdet)
      (fun i => (r i) ^ 2) (fun _ => sq_nonneg _)
    have hterm : (r (T l)) ^ 2 ≤ ∑ l', (r (T l')) ^ 2 :=
      Finset.single_le_sum (f := fun l' => (r (T l')) ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ l)
    rw [hFr]; linarith
  obtain ⟨z, hz1, hz2⟩ := exists_grid_point s hspos (fun l => -(r (T l)))
  refine ⟨z, fun l => ?_, fun t ht => ?_⟩
  · -- оценка номера узла: `|z_l| ≤ √(2V)/s + ½ = √(KC/(2ε)) + ½`
    have habs : |(-(r (T l)))| ≤ Real.sqrt (2 * V) := by
      have h1 : (r (T l)) ^ 2 ≤ 2 * V := le_trans (hrT l) hFV
      rw [abs_neg, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt h1
    have h2 := hz2 l
    have h3 : |(-(r (T l)))| / s ≤ Real.sqrt (2 * V) / s := by gcongr
    have h4 : Real.sqrt (2 * V) / s = Real.sqrt (Kc * C / (2 * ε)) := by
      rw [hs]; exact grid_ratio hV hε hCpos hKc
    linarith [h2, h3, h4 ▸ h3]
  · -- отклонение узла в координатах `K`-ки
    have hdev : ∀ l, dotp (a (T l)) (t - th) = s * (z l : ℝ) - (-(r (T l))) := by
      intro l
      rw [dotp_sub, ht l, hr]
      ring
    have hgK : gramK a T (t - th) ≤ Kc * s ^ 2 / 4 := by
      rw [gramK]
      calc ∑ l, (dotp (a (T l)) (t - th)) ^ 2
          = ∑ l, (s * (z l : ℝ) - (-(r (T l)))) ^ 2 :=
            Finset.sum_congr rfl fun l _ => by rw [hdev l]
        _ ≤ ∑ _l : κ, (s / 2) ^ 2 := by
            refine Finset.sum_le_sum fun l _ => ?_
            have := hz1 l
            nlinarith [abs_nonneg (s * (z l : ℝ) - (-(r (T l)))),
              sq_abs (s * (z l : ℝ) - (-(r (T l)))), hspos]
        _ = Kc * s ^ 2 / 4 := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hKcdef]; ring
    have hs2 : s ^ 2 = 4 * (ε * V / (Kc * C)) := by
      rw [hs, mul_pow, Real.sq_sqrt (by positivity)]
      ring
    have hfin : gramK a T (t - th) ≤ ε * F / C := by
      have h1 : Kc * s ^ 2 / 4 = ε * V / C := by
        rw [hs2]; field_simp
      have h2 : ε * V / C ≤ ε * F / C := by gcongr
      linarith [hgK, h1 ▸ hgK]
    exact theoremH hmax hdet hnormal hC hCpos hfin

end SparseSharpe.Factor
