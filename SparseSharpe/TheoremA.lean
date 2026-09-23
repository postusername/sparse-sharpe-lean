import SparseSharpe.Greedy
import SparseSharpe.GreedyRecursion
import SparseSharpe.Existence

set_option linter.style.header false

/-!
# Теорема A: отношение субмодулярности `F_LO` не меньше `λ_min`

Соединяем две оценки прироста из `Greedy.lean` в неравенство, которое в
`GreedyRecursion.lean` называется `hratio`, — то есть в определение отношения
субмодулярности (Das–Kempe, Def. 2).

`FLO T` — значение `max_{w ≥ 0, supp w ⊆ T} [2m'w − w'Vw]`; оно задаётся гипотезой
`hopt : ∀ T, IsGreatest (ell '' Feas T) (FLO T)` (существование максимума —
отдельный факт про строго вогнутую коэрцитивную форму на конусе, здесь не доказывается).

Знаковое ограничение `w ≥ 0` **не портит константу**: `(·)₊` появляется одинаково
в обеих оценках и сокращается.
-/

namespace SparseSharpe

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace QuadData

variable (Q : QuadData ι)

/-- **Ядро Теоремы A.** При единичной диагонали `V_ii = 1` и ограниченном снизу
наименьшем собственном числе `lam` на носителе `L ∪ S`:

    lam · (FLO(L ∪ S) − FLO(L))  ≤  Σ_{i∈S} [FLO(L ∪ {i}) − FLO(L)].

Это в точности гипотеза `hratio` теоремы `greedy_theorem` с `γ = lam`. -/
theorem submodularity_ratio_ge {FLO : Finset ι → ℝ}
    (hopt : ∀ T, IsGreatest (Q.ell '' Feas T) (FLO T))
    (hdiag1 : ∀ i, Q.V i i = 1) {L S : Finset ι} (hdis : Disjoint L S)
    {lam : ℝ} (hlampos : 0 < lam)
    (hlam : ∀ d : ι → ℝ, (∀ i ∉ L ∪ S, d i = 0) →
      lam * (∑ i, d i ^ 2) ≤ ∑ i, ∑ j, Q.V i j * d i * d j) :
    lam * (FLO (L ∪ S) - FLO L) ≤ ∑ i ∈ S, (FLO (insert i L) - FLO L) := by
  obtain ⟨⟨w, hwF, hwv⟩, hwub⟩ := hopt L
  have hmax : ∀ v ∈ Feas L, Q.ell v ≤ Q.ell w := by
    intro v hv
    rw [hwv]
    exact hwub ⟨v, hv, rfl⟩
  -- совместный прирост сверху
  have hjoint : FLO (L ∪ S) - FLO L
      ≤ (∑ i ∈ S, (max (Q.grad w i) 0) ^ 2) / (4 * lam) := by
    obtain ⟨⟨v, hvF, hvv⟩, _⟩ := hopt (L ∪ S)
    have := Q.joint_gain hmax hwF hvF hdis hlampos hlam
    rw [hvv, hwv] at this
    exact this
  -- индивидуальный прирост снизу
  have hind : ∀ i ∈ S, (max (Q.grad w i) 0) ^ 2 / 4 ≤ FLO (insert i L) - FLO L := by
    intro i _
    obtain ⟨v, hvF, hv⟩ := Q.individual_gain hwF i
    have hub : Q.ell v ≤ FLO (insert i L) := (hopt (insert i L)).2 ⟨v, hvF, rfl⟩
    rw [hdiag1 i, mul_one] at hv
    rw [hwv] at hv
    linarith
  have hsum : ∑ i ∈ S, (max (Q.grad w i) 0) ^ 2 / 4
      ≤ ∑ i ∈ S, (FLO (insert i L) - FLO L) := Finset.sum_le_sum hind
  have hsum' : (∑ i ∈ S, (max (Q.grad w i) 0) ^ 2) / 4
      ≤ ∑ i ∈ S, (FLO (insert i L) - FLO L) := by
    rw [Finset.sum_div] at *
    exact hsum
  have h4 : lam * (FLO (L ∪ S) - FLO L)
      ≤ (∑ i ∈ S, (max (Q.grad w i) 0) ^ 2) / 4 := by
    have := mul_le_mul_of_nonneg_left hjoint hlampos.le
    calc lam * (FLO (L ∪ S) - FLO L)
        ≤ lam * ((∑ i ∈ S, (max (Q.grad w i) 0) ^ 2) / (4 * lam)) := this
      _ = (∑ i ∈ S, (max (Q.grad w i) 0) ^ 2) / 4 := by
          field_simp
  linarith


/-- Значение long-only задачи на носителе `T`: `F_LO(T) = max_{w ≥ 0, supp w ⊆ T} ℓ(w)`. -/
noncomputable def FLO (Q : QuadData ι) (T : Finset ι) : ℝ := sSup (Q.ell '' Feas T)

/-- При положительно определённой `V` максимум достигается, и `FLO` — действительно он. -/
theorem isGreatest_FLO (Q : QuadData ι) {c : ℝ} (hc : 0 < c)
    (hpd : ∀ w : ι → ℝ, c * (∑ i, w i ^ 2) ≤ ∑ i, ∑ j, Q.V i j * w i * w j)
    (T : Finset ι) : IsGreatest (Q.ell '' Feas T) (Q.FLO T) := by
  obtain ⟨w, _, hg⟩ := Q.exists_isGreatest_ell T hc hpd
  have : Q.FLO T = Q.ell w := IsGreatest.csSup_eq hg
  exact this ▸ hg

/-- **Теорема A, безусловная форма.** При `V ≻ 0` и единичной диагонали
отношение субмодулярности `F_LO` не меньше ограниченного снизу наименьшего
собственного числа `lam` на носителе `L ∪ S`. Гипотеза существования максимума
снята: она следует из положительной определённости (`exists_isGreatest_ell`). -/
theorem submodularity_ratio_ge_of_pd (Q : QuadData ι) {c : ℝ} (hc : 0 < c)
    (hpd : ∀ w : ι → ℝ, c * (∑ i, w i ^ 2) ≤ ∑ i, ∑ j, Q.V i j * w i * w j)
    (hdiag1 : ∀ i, Q.V i i = 1) {L S : Finset ι} (hdis : Disjoint L S)
    {lam : ℝ} (hlampos : 0 < lam)
    (hlam : ∀ d : ι → ℝ, (∀ i ∉ L ∪ S, d i = 0) →
      lam * (∑ i, d i ^ 2) ≤ ∑ i, ∑ j, Q.V i j * d i * d j) :
    lam * (Q.FLO (L ∪ S) - Q.FLO L) ≤ ∑ i ∈ S, (Q.FLO (insert i L) - Q.FLO L) :=
  Q.submodularity_ratio_ge (Q.isGreatest_FLO hc hpd) hdiag1 hdis hlampos hlam

end QuadData

end SparseSharpe
