import Mathlib

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Existence of the root `G` with `GᵀG = Σ_f⁻¹`

The end-to-end statements of the development take a matrix `G` with `GᵀG = P` and `P Σ_f = I` as data. This
file shows that such `P` and `G` exist for every positive definite `Σ_f`: `P = Σ_f⁻¹`, and `G = D Uᵀ` from the
spectral decomposition `P = U diag(μ) Uᵀ`, `D = diag(√μ)`.
-/

namespace SparseSharpe.Factor

open Matrix

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A positive semidefinite real matrix is `GᵀG` for a square `G`. -/
theorem exists_root_of_posSemidef (P : Matrix κ κ ℝ) (hP : P.PosSemidef) :
    ∃ G : Matrix κ κ ℝ, Gᵀ * G = P := by
  have hH := hP.isHermitian
  set U : Matrix κ κ ℝ := (hH.eigenvectorUnitary : Matrix κ κ ℝ) with hU
  set D : Matrix κ κ ℝ := diagonal (fun i => Real.sqrt (hH.eigenvalues i)) with hD
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hDD : D * D = diagonal (hH.eigenvalues) := by
    rw [hD, diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hP.eigenvalues_nonneg i)
  refine ⟨D * star U, ?_⟩
  have hstar : star U = Uᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have : (D * star U)ᵀ * (D * star U) = U * (D * D) * star U := by
    rw [hstar, transpose_mul, transpose_transpose, hD, diagonal_transpose]
    simp only [mul_assoc]
  rw [this, hDD]
  conv_rhs => rw [hspec]
  simp [hU]

/-- **For every positive definite `Σ_f` the data `P`, `G` of the statements exist:**
`P Σ_f = I` and `GᵀG = P`. -/
theorem exists_root_of_posDef (Sf : κ → κ → ℝ) (hSf : (Matrix.of Sf).PosDef) :
    ∃ P G : κ → κ → ℝ, (∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) ∧
      (∀ j j', ∑ l, G l j * G l j' = P j j') := by
  have hunit : IsUnit (Matrix.of Sf) := hSf.isUnit
  have hdet : IsUnit (Matrix.of Sf).det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  set Pm : Matrix κ κ ℝ := (Matrix.of Sf)⁻¹ with hPm
  obtain ⟨G, hG⟩ := exists_root_of_posSemidef Pm hSf.inv.posSemidef
  refine ⟨fun j j' => Pm j j', fun j j' => G j j', fun j j' => ?_, fun j j' => ?_⟩
  · have h := Matrix.nonsing_inv_mul (Matrix.of Sf) hdet
    have := congrFun (congrFun h j) j'
    simpa [Matrix.mul_apply, Matrix.one_apply, hPm] using this
  · have := congrFun (congrFun hG j) j'
    simpa [Matrix.mul_apply, Matrix.transpose_apply] using this

end SparseSharpe.Factor
