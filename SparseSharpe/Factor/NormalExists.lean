import SparseSharpe.Factor.MaxVolume

set_option linter.style.header false

/-!
# Существование неподвижной точки

`IsNormal a y V t̂` — это нормальные уравнения `Κ(V)·t̂ = M(V)`. До сих пор их
разрешимость бралась гипотезой (`hex` в `Factor/DPRun.lean`). Здесь она
доказана: при невырожденной `K`-ке строк внутри набора форма Грама
положительно определена, матрица `Κ(V)` обратима (`Matrix.PosDef.isUnit`), и
`t̂ = Κ(V)⁻¹M(V)` подходит.

В приложении невырожденная `K`-ка — это якорные строки `Σ_f^{-1/2}`
(`det_anchor_ne_zero` из `Factor/KBridge.lean`), которые входят в каждый набор
динамики. Поэтому гипотеза становится свойством **входа**, а не предположением
о промежуточных объектах алгоритма.
-/

namespace SparseSharpe.Factor

open Finset Matrix

variable {ι κ : Type*} [Fintype κ]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {V : Finset ι}

/-- Матрица Грама набора: `Κ(V)_{jj'} = Σ_{i∈V} a_{ij}a_{ij'}`. -/
def KMat (a : ι → κ → ℝ) (V : Finset ι) : Matrix κ κ ℝ :=
  fun j j' => ∑ i ∈ V, a i j * a i j'

/-- Вектор первых моментов: `M(V)_j = Σ_{i∈V} y_i a_{ij}`. -/
def momVec (a : ι → κ → ℝ) (y : ι → ℝ) (V : Finset ι) : κ → ℝ :=
  fun j => ∑ i ∈ V, y i * a i j

lemma KMat_mulVec (a : ι → κ → ℝ) (V : Finset ι) (t : κ → ℝ) (j : κ) :
    (KMat a V *ᵥ t) j = ∑ i ∈ V, a i j * dotp (a i) t := by
  simp only [Matrix.mulVec, dotProduct, KMat, dotp, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j' _ => by ring

/-- Форма Грама — это квадратичная форма матрицы `Κ(V)`. -/
lemma dotProduct_KMat_mulVec (a : ι → κ → ℝ) (V : Finset ι) (v : κ → ℝ) :
    v ⬝ᵥ (KMat a V *ᵥ v) = gram a V v := by
  have h1 : v ⬝ᵥ (KMat a V *ᵥ v) = ∑ j, ∑ i ∈ V, v j * (a i j * dotp (a i) v) := by
    simp only [dotProduct, KMat_mulVec, Finset.mul_sum]
  rw [h1, Finset.sum_comm, gram]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ∑ j, v j * (a i j * dotp (a i) v) = (∑ j, a i j * v j) * dotp (a i) v := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h2, show (∑ j, a i j * v j) = dotp (a i) v from rfl, sq]

/-- Момент как скалярное произведение невязки нормальных уравнений. -/
lemma mom_eq_dotProduct (a : ι → κ → ℝ) (y : ι → ℝ) (V : Finset ι) (t v : κ → ℝ) :
    mom a y V t v = (momVec a y V - KMat a V *ᵥ t) ⬝ᵥ v := by
  have h1 : ∀ j : κ, (momVec a y V - KMat a V *ᵥ t) j * v j
      = ∑ i ∈ V, ((y i - dotp (a i) t) * a i j) * v j := by
    intro j
    simp only [Pi.sub_apply, momVec, KMat_mulVec, ← Finset.sum_sub_distrib, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [dotProduct]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => h1 j), Finset.sum_comm, mom]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [dotp]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **`Κ(V)` положительно определена**, если форма Грама положительна вне нуля. -/
theorem KMat_posDef (hpos : ∀ v : κ → ℝ, v ≠ 0 → 0 < gram a V v) : (KMat a V).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · ext j j'
    simp only [Matrix.conjTranspose_apply, KMat, star_trivial]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · have hstar : star x = x := by funext j; simp
    rw [hstar, dotProduct_KMat_mulVec]
    exact hpos x hx

/-- **Нормальные уравнения разрешимы.** -/
theorem exists_isNormal [DecidableEq κ] (a : ι → κ → ℝ) (y : ι → ℝ) (V : Finset ι)
    (hpos : ∀ v : κ → ℝ, v ≠ 0 → 0 < gram a V v) :
    ∃ th : κ → ℝ, IsNormal a y V th := by
  have hpd : (KMat a V).PosDef := KMat_posDef hpos
  have hunit : IsUnit (KMat a V) := hpd.isUnit
  refine ⟨(KMat a V)⁻¹ *ᵥ momVec a y V, fun v => ?_⟩
  rw [mom_eq_dotProduct]
  have hsolve : KMat a V *ᵥ ((KMat a V)⁻¹ *ᵥ momVec a y V) = momVec a y V := by
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det (KMat a V) |>.mp hunit),
      Matrix.one_mulVec]
  rw [hsolve, sub_self]
  simp

/-- **Невырожденная `K`-ка внутри набора даёт положительную определённость.** -/
theorem gram_pos_of_det [DecidableEq κ] {Ta : κ → ι} (hTV : ∀ l, Ta l ∈ V)
    (hdet : (rowMat a Ta).det ≠ 0) {v : κ → ℝ} (hv : v ≠ 0) : 0 < gram a V v := by
  rcases lt_or_eq_of_le (gram_nonneg a V v) with h | h
  · exact h
  · exfalso
    have hz : ∀ i ∈ V, (dotp (a i) v) ^ 2 = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (dotp (a j) v)).mp ?_
      exact h.symm
    have hmv : (rowMat a Ta) *ᵥ v = 0 := by
      funext l
      have := hz (Ta l) (hTV l)
      have hd : dotp (a (Ta l)) v = 0 := by nlinarith [this, sq_nonneg (dotp (a (Ta l)) v)]
      simpa [rowMat, Matrix.mulVec, dotProduct, dotp] using hd
    have hv0 : v = 0 := by
      have hinv := congrArg (fun w => (rowMat a Ta)⁻¹ *ᵥ w) hmv
      simp only [Matrix.mulVec_mulVec] at hinv
      rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec] at hinv
      simpa using hinv
    exact hv hv0

/-- **Итог для динамики.** Если в наборе есть невырожденная `K`-ка (в приложении —
якорные строки), то у него есть неподвижная точка. -/
theorem exists_isNormal_of_det [DecidableEq κ] {Ta : κ → ι} (hTV : ∀ l, Ta l ∈ V)
    (hdet : (rowMat a Ta).det ≠ 0) (y : ι → ℝ) :
    ∃ th : κ → ℝ, IsNormal a y V th :=
  exists_isNormal a y V (fun _ hv => gram_pos_of_det hTV hdet hv)

end SparseSharpe.Factor
