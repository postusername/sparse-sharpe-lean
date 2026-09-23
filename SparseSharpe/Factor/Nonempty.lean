import SparseSharpe.Factor.DPRun

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Непустота сквозных теорем: все гипотезы сразу на одном инстансе

`lake build` не отличает верное утверждение от бессодержательного: если гипотезы
несовместны, теорема верна даром. В проекте такое уже было (калибровка
выводилась из `F(base) = 0` и вынуждала `θ₀ = 0`). Поэтому здесь обе сквозные
теоремы — `lo_fptas_block` (`δ`-цепочка) и `lo_fptas` (`γ`-цепочка) —
применены к **одному конкретному инстансу**, на котором **все** их гипотезы
доказаны одновременно, а вывод содержателен (`1 − 2ε > 0`).

Инстанс: `K = 1`, две строки с нагрузкой `1` — якорь (`y = 0`, не зажат) и актив
(`y = 2`, зажат). `A = S` — обе строки, `base` — якорь, список `L = [актив]`.
Неподвижная точка `t̂ = 1`, `F = 2`, `V = 1`, актив самосогласован (`r = 1 ≥ 0`).

* `δ`-цепочка: `ε = 1/4`, покрытие с `k = 1`, `c = 2` (из плеч строк, `ω = 1`),
  `θ₀ = √(εV/(8c)) = 1/8`, `η = 1/64`, `ξ = 1/8`.
* `γ`-цепочка: `ε = 1/4`, `γ = 1/2` (`gram_S = 2v²`, `gram_anch = v²`), `n = 4`,
  `η = 1/2000`, `ξ = 1/8`.

Вывод обеих теорем здесь: `F_LO(R) ≥ (1 − 2ε)·F = 1`. И он правдив: `R` — обе
строки, `ψ(t) = t² + ((2 − t)_+)² ≥ 2`.
-/

namespace SparseSharpe.Factor

open Finset

/-- Строки: обе с нагрузкой `1`. -/
def aN : Fin 2 → Fin 1 → ℝ := fun _ _ => 1

/-- Правые части: якорь `0`, актив `2`. -/
def yN : Fin 2 → ℝ := fun i => if i = 0 then 0 else 2

/-- Зажат только актив. -/
def clN : Fin 2 → Bool := fun i => decide (i = 1)

def baseN : Finset (Fin 2) := {0}

def TN : Fin 1 → Fin 2 := fun _ => 0

def thN : Fin 1 → ℝ := fun _ => 1

lemma dotp_aN (i : Fin 2) (v : Fin 1 → ℝ) : dotp (aN i) v = v 0 := by
  simp [dotp, aN]

lemma normalN : IsNormal aN yN Finset.univ thN := by
  intro v
  simp only [mom, Fin.sum_univ_two, dotp_aN, yN, thN]
  norm_num

lemma phiN : phi aN yN Finset.univ thN = 2 := by
  simp only [phi, Fin.sum_univ_two, dotp_aN, yN, thN]
  norm_num

lemma rowMatN (T' : Fin 1 → Fin 2) : (rowMat aN T').det = 1 := by
  simp [rowMat, aN, Matrix.det_unique]

lemma maxVolN : MaxVol aN Finset.univ TN :=
  ⟨fun _ => Finset.mem_univ _, fun T' _ => by rw [rowMatN, rowMatN]⟩

lemma detN : (rowMat aN TN).det ≠ 0 := by rw [rowMatN]; norm_num

lemma selfN : ∀ i ∈ (Finset.univ : Finset (Fin 2)), clN i → 0 ≤ yN i - dotp (aN i) thN := by
  intro i _ hc
  fin_cases i
  · simp [clN] at hc
  · simp [yN, dotp_aN, thN]

lemma anchorSetN : anchorSet clN Finset.univ ⊆ baseN := by
  intro i hi
  fin_cases i
  · simp [baseN]
  · simp [anchorSet, clN] at hi

lemma baseAnchN : ∀ i ∈ baseN, ¬ clN i := by
  intro i hi
  simp [baseN] at hi
  subst hi
  simp [clN]

lemma LN_prop : [(1 : Fin 2)].Nodup ∧ (∀ i ∈ [(1 : Fin 2)], i ∉ baseN)
    ∧ (Finset.univ : Finset (Fin 2)) ⊆ baseN ∪ [(1 : Fin 2)].toFinset := by
  refine ⟨by simp, by simp [baseN], ?_⟩
  intro i _
  fin_cases i <;> simp [baseN]

/-- Покрытие нарушителей с `k = 1`, `c = 2`: плечо актива относительно якоря — `1`. -/
lemma coverN : AnchorCover aN yN clN Finset.univ baseN 1 2 := by
  have h := anchorCover_of_rowLev_uniform (a := aN) (y := yN) (cl := clN)
    (S := Finset.univ) (base := baseN) (k := 1) (ω := 1) (by norm_num)
    (fun i _ _ v => by simp [gram, baseN, dotp_aN])
  norm_num at h
  exact h

/-! ### `δ`-цепочка -/

/-- Шаг сетки `δ`-цепочки на инстансе. -/
noncomputable def sB : ℝ :=
  2 * Real.sqrt (((1/4 : ℝ) / (32 * 2)) * 1 / ((Fintype.card (Fin 1) : ℝ) * 2))

lemma theta0B_N : theta0B (1/4) 1 2 = 1 / 8 := by
  rw [theta0B, show (1/4 : ℝ) * 1 / (8 * 2) = (1/8) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- **Все гипотезы `lo_fptas_block` выполнены одновременно**, и вывод
содержателен: `F_LO(R) ≥ (1 − 2·(1/4))·F = 1`. -/
theorem lo_fptas_block_instance :
    ∃ z : Fin 1 → ℤ,
      (∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card (Fin 1) : ℝ) * 2
        / (2 * ((1/4 : ℝ) / (32 * 2)))) + 1 / 2) ∧
      ∀ t : Fin 1 → ℝ, (∀ l, dotp (aN (TN l)) t = yN (TN l) + sB * (z l : ℝ)) →
        ∃ adm : Fin 2 → Bool,
          (∀ i, adm i → -theta0B (1/4) 1 2 ≤ yN i - dotp (aN i) t) ∧
          (∀ i ∈ (Finset.univ : Finset (Fin 2)), i ∉ baseN → adm i) ∧
          ∃ R ∈ survivors (fun W => phi aN yN W t) (keyOf aN yN TN t (1/64) (1/8)) adm
              baseN [1],
            R.card = (Finset.univ : Finset (Fin 2)).card ∧
            ∀ t' : Fin 1 → ℝ,
              (1 - 2 * (1/4 : ℝ)) * phi aN yN Finset.univ thN ≤ psiC aN yN clN R t' := by
  obtain ⟨hnd, hdisj, hAL⟩ := LN_prop
  exact lo_fptas_block (S := Finset.univ) (A := Finset.univ) (base := baseN) (cl := clN)
    (thA := thN) (η := 1/64) (ξ := 1/8) (ε := 1/4) (V := 1) (C := 2) (c := 2) (s := sB)
    (k := 1) (L := [1]) (T := TN) (Tb := TN)
    maxVolN detN normalN (by simp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [phiN]; norm_num) (by rw [phiN]; norm_num) (by simp) rfl selfN
    (by norm_num) (by norm_num) hnd hdisj (by simp) hAL (Finset.Subset.refl _)
    (Finset.subset_univ _) (fun _ _ => Finset.mem_univ _) anchorSetN baseAnchN coverN
    (by simp [baseN]) (fun _ => by simp [baseN, TN]) detN
    (by rw [theta0B_N]; norm_num) (by norm_num)

/-! ### `γ`-цепочка -/

/-- Шаг сетки `γ`-цепочки на инстансе. -/
noncomputable def sG : ℝ :=
  2 * Real.sqrt (((1/4 : ℝ) ^ 2 * (1/2) / (1024 * (4 : ℕ))) * 1
    / ((Fintype.card (Fin 1) : ℝ) * 2))

lemma gram_anchN (v : Fin 1 → ℝ) : gram aN (anchorSet clN Finset.univ) v = (v 0) ^ 2 := by
  have : anchorSet clN Finset.univ = ({0} : Finset (Fin 2)) := by
    ext i; fin_cases i <;> simp [anchorSet, clN]
  rw [this]; simp [gram, dotp_aN]

lemma theta0_N : (1 : ℝ) / 250 ≤ theta0 (1/4) (1/2) 1 4 := by
  rw [theta0]
  have h4 : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [h4]
  have hs : (16 / 25 : ℝ) ≤ Real.sqrt (1/2 * 1) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  rw [le_div_iff₀ (by norm_num)]
  nlinarith [hs]

/-- **Все гипотезы `lo_fptas` (`γ`-цепочка) выполнены одновременно**, и вывод
содержателен: `F_LO(R) ≥ (1 − 2·(1/4))·F = 1`. -/
theorem lo_fptas_instance :
    ∃ z : Fin 1 → ℤ,
      (∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card (Fin 1) : ℝ) * 2
        / (2 * ((1/4 : ℝ) ^ 2 * (1/2) / (1024 * ((4 : ℕ) : ℝ))))) + 1 / 2) ∧
      ∀ t : Fin 1 → ℝ, (∀ l, dotp (aN (TN l)) t = yN (TN l) + sG * (z l : ℝ)) →
        ∃ adm : Fin 2 → Bool,
          (∀ i, adm i → -theta0 (1/4) (1/2) 1 4 ≤ yN i - dotp (aN i) t) ∧
          (∀ i ∈ (Finset.univ : Finset (Fin 2)), i ∉ baseN → adm i) ∧
          ∃ R ∈ survivors (fun W => phi aN yN W t) (keyOf aN yN TN t (1/2000) (1/8)) adm
              baseN [1],
            R.card = (Finset.univ : Finset (Fin 2)).card ∧
            ∀ t' : Fin 1 → ℝ,
              (1 - 2 * (1/4 : ℝ)) * phi aN yN Finset.univ thN ≤ psiC aN yN clN R t' := by
  obtain ⟨hnd, hdisj, hAL⟩ := LN_prop
  exact lo_fptas (S := Finset.univ) (A := Finset.univ) (base := baseN) (cl := clN)
    (thA := thN) (η := 1/2000) (ξ := 1/8) (γ := 1/2) (ε := 1/4) (V := 1) (C := 2) (s := sG)
    (n := 4) (L := [1]) (T := TN) (Tb := TN)
    maxVolN detN normalN (by simp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by rw [phiN]; norm_num) (by rw [phiN]; norm_num) (by simp)
    (by norm_num) (by norm_num [Finset.card_univ, Fintype.card_fin]) rfl selfN (by norm_num)
    (by norm_num) hnd hdisj (by simp) hAL
    (Finset.Subset.refl _) (Finset.subset_univ _) (fun _ _ => Finset.mem_univ _)
    (fun i hi => by
      fin_cases i
      · simp [yN]
      · simp [clN] at hi)
    anchorSetN baseAnchN
    (fun v => by
      rw [gram_anchN]
      simp [gram, dotp_aN])
    (fun _ => by simp [baseN, TN]) detN
    (by
      refine le_trans ?_ theta0_N
      norm_num)
    (by norm_num)

/-- И вывод здесь правдив: `R` — обе строки, и `ψ(t) = t² + ((2 − t)_+)² ≥ 1`. -/
example (t' : Fin 1 → ℝ) : (1 : ℝ) ≤ psiC aN yN clN Finset.univ t' := by
  simp only [psiC, Fin.sum_univ_two, resC, clN, dotp_aN, yN]
  simp
  rcases le_total (t' 0) 2 with h | h
  · rw [max_eq_left (by linarith)]; nlinarith [sq_nonneg (t' 0 - 1)]
  · rw [max_eq_right (by linarith)]; nlinarith

end SparseSharpe.Factor
