import Mathlib

set_option linter.style.header false

/-!
# Padding: SUBSET SUM with a prescribed number of summands

`subsetSum_reduction` (`Factor/Landscape.lean`) reduces the problem with *exactly* `r`
summands (K-SUBSET SUM) to the sparse tangency portfolio. This file supplies the missing
link to the classical SUBSET SUM, in which the number of summands is free: add `n` dummy
numbers and shift every number by `X`. Then a subset of the `n` original numbers sums to
`L` if and only if some `n` of the `2n` padded numbers sum to `L + n·X`
(`subsetSum_padding`). With `X ≥ 1` and nonnegative original numbers all padded numbers
are positive (`padded_pos`), which is the class of Proposition 4 (`β > 0`, `m > 0`).
-/

namespace SparseSharpe.Factor

open Finset

/-- Padded numbers: original number plus `X`, and `n` dummies equal to `X`. -/
def padded {n : ℕ} (ℓ : Fin n → ℤ) (X : ℤ) : Fin n ⊕ Fin n → ℤ :=
  Sum.elim (fun i => ℓ i + X) (fun _ => X)

/-- **Padding.** A subset of `ℓ` sums to `L` iff exactly `n` padded numbers sum to
`L + n·X`. -/
theorem subsetSum_padding {n : ℕ} (ℓ : Fin n → ℤ) (L X : ℤ) :
    (∃ S : Finset (Fin n), ∑ i ∈ S, ℓ i = L) ↔
    (∃ S' : Finset (Fin n ⊕ Fin n), S'.card = n ∧ ∑ x ∈ S', padded ℓ X x = L + n * X) := by
  constructor
  · rintro ⟨S, hS⟩
    have hSn : S.card ≤ n := by
      simpa using Finset.card_le_univ S
    obtain ⟨D, -, hD⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin n))) (n := n - S.card) (by simp)
    refine ⟨S.disjSum D, ?_, ?_⟩
    · rw [Finset.card_disjSum, hD]; omega
    · rw [Finset.sum_disjSum]
      simp only [padded, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib, hS,
        Finset.sum_const, hD, nsmul_eq_mul]
      rw [Nat.cast_sub hSn]
      ring
  · rintro ⟨S', hcard, hsum⟩
    refine ⟨S'.toLeft, ?_⟩
    have hsplit : ∑ x ∈ S', padded ℓ X x
        = ∑ i ∈ S'.toLeft, (ℓ i + X) + ∑ _j ∈ S'.toRight, X := by
      conv_lhs => rw [← Finset.toLeft_disjSum_toRight (u := S')]
      rw [Finset.sum_disjSum]
      simp [padded]
    have hc : (S'.toLeft.card : ℤ) + S'.toRight.card = n := by
      have := Finset.card_toLeft_add_card_toRight (u := S')
      rw [hcard] at this
      exact_mod_cast this
    rw [hsplit, Finset.sum_add_distrib] at hsum
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    have : ∑ i ∈ S'.toLeft, ℓ i = L + n * X - (S'.toLeft.card * X + S'.toRight.card * X) := by
      linarith
    rw [this]
    have hX : (S'.toLeft.card : ℤ) * X + S'.toRight.card * X = n * X := by
      rw [← add_mul, hc]
    rw [hX]; ring

/-- With nonnegative originals and `X ≥ 1` every padded number is positive. -/
lemma padded_pos {n : ℕ} {ℓ : Fin n → ℤ} {X : ℤ} (hℓ : ∀ i, 0 ≤ ℓ i) (hX : 1 ≤ X)
    (x : Fin n ⊕ Fin n) : 0 < padded ℓ X x := by
  rcases x with i | j
  · simp only [padded, Sum.elim_inl]; linarith [hℓ i]
  · simp only [padded, Sum.elim_inr]; linarith

/-- The padding is nontrivial: `ℓ = (2, 3)`, `L = 5`, `X = 1`: the subset `{0, 1}` sums to
`5`, and exactly two padded numbers (`3` and `4`) sum to `5 + 2·1 = 7`. -/
example : ∃ S' : Finset (Fin 2 ⊕ Fin 2), S'.card = 2 ∧
    ∑ x ∈ S', padded ![(2:ℤ), 3] 1 x = 5 + 2 * 1 :=
  (subsetSum_padding ![(2:ℤ), 3] 5 1).mp ⟨Finset.univ, by simp [Fin.sum_univ_two]⟩

end SparseSharpe.Factor
