import SparseSharpe.Factor.ClippedNode

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Sharper loss at a node (Remark 4.3 of the paper)

`F − obj(S, w(τ)) ≤ (ν_S − 1)·(Q_S(τ) − F) ≤ ν_S(ν_S − 1)·q`, where `ν_S − 1 = Σ_{i∈S} ω_i` (`levSum`).
It improves `objLO_wclip_ge_of_node` (which has `ν_S²`) by the factor `(ν_S − 1)/ν_S`; the loss vanishes with
`Σ_{i∈S} ω_i`.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- **The sharper loss at a node.** If `t₀` minimizes `Q_S` and `F = Q_S(t₀)`, then for every `τ`
`F − obj(S, w(τ)) ≤ levSum(S)·(Q_S(τ) − F) ≤ levSum(S)·(1 + levSum(S))·(τ−t₀)'Σ_f⁻¹(τ−t₀)`. -/
theorem objLO_wclip_ge_of_node_sharp (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {S : Finset ι} {t₀ : κ → ℝ} (hmin : ∀ t, QLO m d B P S t₀ ≤ QLO m d B P S t) (τ : κ → ℝ) :
    QLO m d B P S t₀ - levSum d B Sf S * (QLO m d B P S τ - QLO m d B P S t₀)
        ≤ objLO m d B Sf S (wclip m d B τ) ∧
      levSum d B Sf S * (QLO m d B P S τ - QLO m d B P S t₀)
        ≤ levSum d B Sf S * (1 + levSum d B Sf S) * quadf P (τ - t₀) := by
  have hl : 0 ≤ levSum d B Sf S := levSum_nonneg (B := B) hd hG hPS S
  have hdef := defect_le (m := m) (B := B) (Sf := Sf) hd hG hPS S hmin τ
  have hgap := QLO_sub_le_of_min (m := m) (B := B) (Sf := Sf) hd hG hPS hmin τ
  refine ⟨?_, ?_⟩
  · rw [objLO_wclip_deficit hd hG hPS S τ]
    nlinarith [hdef]
  · have := mul_le_mul_of_nonneg_left hgap hl
    nlinarith [this]

end SparseSharpe.Factor
