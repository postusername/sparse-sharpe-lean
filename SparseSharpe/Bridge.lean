import SparseSharpe.Basic
import SparseSharpe.TheoremA

set_option linter.style.header false

/-!
# Мост: однофакторная модель — частный случай общей квадратичной задачи

`OneFactor` задаёт `V = D + σ²ββ'`. Здесь строится соответствующая `QuadData`
и проверяется, что целевые функции совпадают:

    (P.toQuad).ell w = P.obj univ w   для всех `w`.

Отсюда Теорема A (`submodularity_ratio_ge_of_pd`) применима к разрежённой
максимизации Шарпа буквально, а не «по аналогии».
-/

namespace SparseSharpe

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace OneFactor

/-- Однофакторная модель как общая квадратичная задача: `V = D + σ²ββ'`. -/
noncomputable def toQuad (P : OneFactor ι) : QuadData ι where
  m := P.m
  V := fun i j => (if i = j then P.d i else 0) + P.σ2 * (P.β i * P.β j)
  hsymm := by
    intro i j
    by_cases h : i = j
    · subst h; ring
    · have h' : ¬ (j = i) := fun e => h e.symm
      simp only [if_neg h, if_neg h']
      ring
  hdiag := by
    intro i
    have h1 := P.hd i
    have h2 := P.hσ2
    show 0 < (if i = i then P.d i else 0) + P.σ2 * (P.β i * P.β i)
    rw [if_pos rfl]
    nlinarith [mul_self_nonneg (P.β i)]

/-- Квадратичная форма `V = D + σ²ββ'` раскладывается как надо. -/
lemma toQuad_quadForm (P : OneFactor ι) (w : ι → ℝ) :
    ∑ i, ∑ j, (P.toQuad).V i j * w i * w j
      = (∑ i, P.d i * (w i) ^ 2) + P.σ2 * (∑ i, P.β i * w i) ^ 2 := by
  have hsplit : ∀ i, ∑ j, (P.toQuad).V i j * w i * w j
      = P.d i * (w i) ^ 2 + (P.σ2 * (P.β i * w i)) * ∑ j, P.β j * w j := by
    intro i
    simp only [OneFactor.toQuad, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_eq_single i]
      · simp; ring
      · intro j _ hj
        have : ¬ (i = j) := fun e => hj e.symm
        simp [if_neg this]
      · intro h; exact absurd (Finset.mem_univ i) h
    · exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, ← Finset.sum_mul]
  congr 1
  rw [← Finset.mul_sum]
  ring

/-- **Мост.** Целевые функции совпадают. -/
theorem toQuad_ell (P : OneFactor ι) (w : ι → ℝ) :
    (P.toQuad).ell w = P.obj Finset.univ w := by
  simp only [QuadData.ell, OneFactor.obj, OneFactor.toQuad]
  rw [show (∑ i, ∑ j, ((if i = j then P.d i else 0) + P.σ2 * (P.β i * P.β j)) * w i * w j)
      = ∑ i, ∑ j, (P.toQuad).V i j * w i * w j from rfl, toQuad_quadForm]

end OneFactor

end SparseSharpe
