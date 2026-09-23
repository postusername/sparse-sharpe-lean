import SparseSharpe.Basic

set_option linter.style.header false

/-!
# Жадный long-only шаг для общей квадратичной задачи
-/

namespace SparseSharpe

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure QuadData (ι : Type*) [Fintype ι] where
  m : ι → ℝ
  V : ι → ι → ℝ
  hsymm : ∀ i j, V i j = V j i
  hdiag : ∀ i, 0 < V i i

namespace QuadData

variable (Q : QuadData ι)

/-- `ℓ(w) = 2 m'w − w'Vw`. -/
noncomputable def ell (w : ι → ℝ) : ℝ :=
  2 * ∑ i, Q.m i * w i - ∑ i, ∑ j, Q.V i j * w i * w j

/-- Половина градиента (с нормировкой, удобной для квадратичной формы). -/
noncomputable def grad (w : ι → ℝ) (i : ι) : ℝ :=
  2 * (Q.m i - ∑ j, Q.V i j * w j)

/-- Допустимые веса на носителе `S`: неотрицательные, нулевые вне `S`. -/
def Feas (S : Finset ι) : Set (ι → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∀ i ∉ S, w i = 0}

private lemma cross_symm (w d : ι → ℝ) :
    (∑ i, ∑ j, Q.V i j * w i * d j) = ∑ i, ∑ j, Q.V i j * d i * w j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Q.hsymm]
  ring

/-- Точное разложение квадратичной цели при произвольном сдвиге. -/
theorem ell_add (w d : ι → ℝ) :
    Q.ell (w + d) = Q.ell w + (∑ i, Q.grad w i * d i)
      - ∑ i, ∑ j, Q.V i j * d i * d j := by
  have hc := Q.cross_symm w d
  have hg : (∑ i, Q.grad w i * d i) =
      2 * ∑ i, Q.m i * d i - 2 * ∑ i, ∑ j, Q.V i j * d i * w j := by
    simp only [grad]
    have hi : ∀ x : ι, (∑ y, Q.V x y * w y) * d x =
        ∑ y, Q.V x y * d x * w y := by
      intro x
      rw [Finset.sum_mul Finset.univ (fun y => Q.V x y * w y) (d x)]
      apply Finset.sum_congr rfl
      intro y _
      ring
    calc
      (∑ i, (2 * (Q.m i - ∑ j, Q.V i j * w j)) * d i)
          = ∑ i, 2 * (Q.m i * d i - (∑ j, Q.V i j * w j) * d i) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = 2 * ∑ i, (Q.m i * d i - (∑ j, Q.V i j * w j) * d i) := by
              rw [Finset.mul_sum Finset.univ]
      _ = 2 * (∑ i, Q.m i * d i - ∑ i, (∑ j, Q.V i j * w j) * d i) := by
              rw [Finset.sum_sub_distrib]
      _ = 2 * ∑ i, Q.m i * d i - 2 * ∑ i, ∑ j, Q.V i j * d i * w j := by
              simp_rw [hi]
              ring
  simp only [ell, Pi.add_apply]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  rw [hc]
  rw [hg]
  ring

/-- Точное изменение цели при движении по одной координате. -/
theorem ell_add_single (w : ι → ℝ) (a : ℝ) (i : ι) :
    Q.ell (w + a • (Pi.single i 1)) = Q.ell w + a * Q.grad w i - a ^ 2 * Q.V i i := by
  rw [Q.ell_add]
  classical
  simp [Pi.single_apply]
  ring

private lemma feas_add_single {L : Finset ι} {w : ι → ℝ} (hw : w ∈ Feas L)
    {i : ι} (hi : i ∈ L) {a : ℝ} (ha : 0 ≤ a) :
    w + a • (Pi.single i 1) ∈ Feas L := by
  constructor
  · intro j
    by_cases h : j = i
    · subst j
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      exact add_nonneg (hw.1 i) ha
    · simp [Pi.single_apply, h, hw.1 j]
  · intro j hj
    have hji : j ≠ i := fun e => hj (e ▸ hi)
    simp [Pi.single_apply, hji, hw.2 j hj]

/-- ККТ: на допустимой координате градиент не положителен. -/
theorem kkt_nonpos {L : Finset ι} {w : ι → ℝ}
    (hmax : ∀ v ∈ Feas L, Q.ell v ≤ Q.ell w) (hw : w ∈ Feas L) :
    ∀ i ∈ L, Q.grad w i ≤ 0 := by
  intro i hi
  by_contra hn
  have hg : 0 < Q.grad w i := lt_of_not_ge hn
  let a : ℝ := Q.grad w i / (2 * Q.V i i)
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos hg (mul_pos (by norm_num) (Q.hdiag i))
  have hf := hmax (w + a • Pi.single i 1) (feas_add_single hw hi ha.le)
  rw [Q.ell_add_single] at hf
  have hv : 0 < a * Q.grad w i - a ^ 2 * Q.V i i := by
    dsimp [a]
    have hd := Q.hdiag i
    field_simp
    nlinarith
  linarith

private lemma feas_add_single_neg {L : Finset ι} {w : ι → ℝ} (hw : w ∈ Feas L)
    {i : ι} (hi : i ∈ L) {a : ℝ} (ha : -w i ≤ a) :
    w + a • (Pi.single i 1) ∈ Feas L := by
  constructor
  · intro j
    by_cases h : j = i
    · subst j
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      linarith
    · simp [Pi.single_apply, h, hw.1 j]
  · intro j hj
    have hji : j ≠ i := fun e => hj (e ▸ hi)
    simp [Pi.single_apply, hji, hw.2 j hj]

/-- ККТ: на положительной допустимой координате градиент равен нулю. -/
theorem kkt_eq {L : Finset ι} {w : ι → ℝ}
    (hmax : ∀ v ∈ Feas L, Q.ell v ≤ Q.ell w) (hw : w ∈ Feas L) :
    ∀ i ∈ L, 0 < w i → Q.grad w i = 0 := by
  intro i hi hwi
  have hle := Q.kkt_nonpos hmax hw i hi
  by_contra hn
  have hg : Q.grad w i < 0 := lt_of_le_of_ne hle hn
  let a : ℝ := max (-w i) (Q.grad w i / (2 * Q.V i i))
  have ha_bound : -w i ≤ a := le_max_left _ _
  have ha_neg : a < 0 := by
    apply max_lt
    · linarith
    · exact div_neg_of_neg_of_pos hg (mul_pos (by norm_num) (Q.hdiag i))
  have hf := hmax (w + a • Pi.single i 1) (feas_add_single_neg hw hi ha_bound)
  rw [Q.ell_add_single] at hf
  have hv : 0 < a * Q.grad w i - a ^ 2 * Q.V i i := by
    dsimp [a]
    rcases le_total (-w i) (Q.grad w i / (2 * Q.V i i)) with hcase | hcase
    · rw [max_eq_right hcase]
      have hd := Q.hdiag i
      field_simp
      nlinarith
    · rw [max_eq_left hcase]
      have hd := Q.hdiag i
      have hh : Q.grad w i ≤ -2 * w i * Q.V i i := by
        have hq := (div_le_iff₀ (mul_pos (by norm_num) hd)).mp hcase
        linarith
      have hp : 0 < w i * Q.V i i := mul_pos hwi hd
      nlinarith
  linarith

/-- Явный прирост от добавления одной координаты. -/
theorem individual_gain {L : Finset ι} {w : ι → ℝ} (hw : w ∈ Feas L)
    (i : ι) : ∃ v ∈ Feas (insert i L),
      Q.ell w + (max (Q.grad w i) 0) ^ 2 / (4 * Q.V i i) ≤ Q.ell v := by
  let a : ℝ := max (Q.grad w i) 0 / (2 * Q.V i i)
  have ha : 0 ≤ a := div_nonneg (le_max_right _ _) (mul_nonneg (by norm_num) (Q.hdiag i).le)
  refine ⟨w + a • Pi.single i 1, ?_, ?_⟩
  · constructor
    · intro j
      by_cases h : j = i
      · subst j
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
        exact add_nonneg (hw.1 i) ha
      · simp [Pi.single_apply, h, hw.1 j]
    · intro j hj
      have hjL : j ∉ L := fun hL => hj (mem_insert_of_mem hL)
      have hji : j ≠ i := fun e => hj (e ▸ mem_insert_self i L)
      simp [Pi.single_apply, hji, hw.2 j hjL]
  · rw [Q.ell_add_single]
    have hd := Q.hdiag i
    dsimp [a]
    have hden : 0 < 2 * Q.V i i := mul_pos (by norm_num) hd
    have hM : 0 ≤ max (Q.grad w i) 0 := le_max_right _ _
    have hcalc : (max (Q.grad w i) 0) ^ 2 / (4 * Q.V i i)
        ≤ (max (Q.grad w i) 0 / (2 * Q.V i i)) * Q.grad w i
          - (max (Q.grad w i) 0 / (2 * Q.V i i)) ^ 2 * Q.V i i := by
      rcases le_total (Q.grad w i) 0 with hg | hg
      · rw [max_eq_right hg]
        field_simp
        norm_num
      · rw [max_eq_left hg]
        field_simp
        nlinarith
    linarith

/-- Совместный прирост не превосходит суммы одноточечных градиентных оценок. -/
theorem joint_gain {L S : Finset ι} {w v : ι → ℝ}
    (hmax : ∀ u ∈ Feas L, Q.ell u ≤ Q.ell w) (hw : w ∈ Feas L)
    (hv : v ∈ Feas (L ∪ S)) (hdis : Disjoint L S) {lam : ℝ} (hlampos : 0 < lam)
    (hlam : ∀ d : ι → ℝ, (∀ i ∉ L ∪ S, d i = 0) →
      lam * (∑ i, d i ^ 2) ≤ ∑ i, ∑ j, Q.V i j * d i * d j) :
    Q.ell v - Q.ell w ≤ (∑ i ∈ S, (max (Q.grad w i) 0) ^ 2) / (4 * lam) := by
  classical
  let d : ι → ℝ := v - w
  have hdout : ∀ i ∉ L ∪ S, d i = 0 := by
    intro i hi
    dsimp [d]
    rw [hv.2 i hi, hw.2 i (fun h => hi (mem_union_left S h))]
    ring
  have hvwd : v = w + d := by
    funext i
    dsimp [d]
    ring
  have hL : ∀ i ∈ L, Q.grad w i * d i ≤ 0 := by
    intro i hi
    rcases eq_or_lt_of_le (hw.1 i) with hz | hp
    · have hg := Q.kkt_nonpos hmax hw i hi
      have hd : 0 ≤ d i := by
        dsimp [d]
        rw [hz]
        linarith [hv.1 i]
      exact mul_nonpos_of_nonpos_of_nonneg hg hd
    · rw [Q.kkt_eq hmax hw i hi hp]
      norm_num
  have hS : ∀ i ∈ S, Q.grad w i * d i ≤ max (Q.grad w i) 0 * d i := by
    intro i hi
    have hiL : i ∉ L := fun h => (Finset.disjoint_left.1 hdis h hi)
    have hw0 : w i = 0 := hw.2 i hiL
    have hd : 0 ≤ d i := by
      dsimp [d]
      rw [hw0]
      simpa using hv.1 i
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hd
  have hterm : ∀ i, Q.grad w i * d i ≤ if i ∈ S then max (Q.grad w i) 0 * d i else 0 := by
    intro i
    by_cases hiL : i ∈ L
    · have := hL i hiL
      by_cases hiS : i ∈ S
      · exact False.elim (Finset.disjoint_left.1 hdis hiL hiS)
      · simpa [hiS] using this
    · by_cases hiS : i ∈ S
      · simpa [hiS] using hS i hiS
      · have hout : i ∉ L ∪ S := by simpa [Finset.mem_union, hiL, hiS]
        rw [hdout i hout]
        simp [hiS]
  have hgrad : (∑ i, Q.grad w i * d i) ≤ ∑ i ∈ S, max (Q.grad w i) 0 * d i := by
    calc
      (∑ i, Q.grad w i * d i) ≤ ∑ i, if i ∈ S then max (Q.grad w i) 0 * d i else 0 :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = ∑ i ∈ S, max (Q.grad w i) 0 * d i := by simp
  let A : ℝ := ∑ i ∈ S, (max (Q.grad w i) 0) ^ 2
  let B : ℝ := ∑ i ∈ S, max (Q.grad w i) 0 * d i
  let C : ℝ := ∑ i, d i ^ 2
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg fun i hi =>
    mul_nonneg (le_max_right _ _) (by
      have hiL : i ∉ L := fun h => Finset.disjoint_left.1 hdis h hi
      have hw0 := hw.2 i hiL
      dsimp [d]
      rw [hw0]
      linarith [hv.1 i])
  have hCS0 := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => max (Q.grad w i) 0) d
  have hSC : (∑ i ∈ S, d i ^ 2) ≤ C := by
    dsimp [C]
    exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ S)
      (fun i _ _ => sq_nonneg _)
  have hBC : B ^ 2 ≤ A * C := by
    dsimp [A, B]
    exact le_trans hCS0 (mul_le_mul_of_nonneg_left hSC
      (Finset.sum_nonneg fun i _ => sq_nonneg _))
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hquad : B - lam * C ≤ A / (4 * lam) := by
    have h4 : 0 < 4 * lam := mul_pos (by norm_num) hlampos
    rcases eq_or_lt_of_le hC with hc | hc
    · have hc0 : C = 0 := hc.symm
      rw [hc0] at hBC
      have hb0 : B = 0 := by nlinarith [hBC, sq_nonneg B]
      rw [hc0, hb0]
      simpa using div_nonneg hA h4.le
    · apply (le_div_iff₀ h4).2
      have hp : 0 ≤ (A - 4 * lam * B + 4 * lam ^ 2 * C) * C := by
        nlinarith [hBC, sq_nonneg (B - 2 * lam * C)]
      have hh : 0 ≤ A - 4 * lam * B + 4 * lam ^ 2 * C :=
        nonneg_of_mul_nonneg_right (by simpa [mul_comm] using hp) hc
      nlinarith
  have hq := hlam d hdout
  have he := Q.ell_add w d
  rw [← hvwd] at he
  have hmain : Q.ell v - Q.ell w ≤ B - lam * C := by
    dsimp [B, C]
    linarith
  exact le_trans hmain hquad

end QuadData

end SparseSharpe
