import SparseSharpe.Factor.SaddleExistence

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The dual bound is the dual of the perspective relaxation (session 25, task 2.7 of TZ v0.25)

The perspective (Boolean) relaxation of the cardinality-constrained long-only problem is

    max { 2m'w − (B'w)'Σ_f(B'w) − Σ_i d_i w_i²/z_i :  z ∈ Λ_k,  w ≥ 0,  w_i = 0 where z_i = 0 },

`Λ_k = {z ∈ [0,1]^M : Σ z_i = k}`; for `z` the indicator of a support `S` it is the long-only problem on `S`.

* `perspObj_le_dualBound` — every feasible `(z, w)` has value at most `g_k(t)` for every `t` (weak duality:
  `−u'Σ_f u ≤ t'Pt − 2t'u` and `2rw − dw²/z ≤ z r_+²/d`, then `L(t, z) ≤ g_k(t)`).
* `perspective_relaxation` — at a saddle point `(t*, λ*)` the pair `z = λ*`, `w_i = λ*_i w_i(t*)` is feasible
  and has value `g_k(t*) = G*_k`: the maximum of the perspective relaxation equals `G*_k = min_t g_k(t)`, and
  both are attained.

In the notation of Lean, `d_i w_i²/z_i` with `z_i = 0` is `0` (division by zero), and feasibility requires
`w_i = 0` there, which is the usual convention of the perspective function.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- The objective of the perspective relaxation, `2m'w − (B'w)'Σ_f(B'w) − Σ_i d_i w_i²/z_i`. -/
noncomputable def perspObj (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf : κ → κ → ℝ) (z w : ι → ℝ) : ℝ :=
  2 * ∑ i, m i * w i - quadf Sf (Bw B univ w) - ∑ i, d i * w i ^ 2 / z i

/-- Feasibility for the perspective relaxation: `z ∈ Λ_k`, `w ≥ 0`, and `w_i = 0` where `z_i = 0`. -/
def PerspFeasible (k : ℕ) (z w : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ ∑ i, z i = k ∧ (∀ i, 0 ≤ w i) ∧ ∀ i, z i = 0 → w i = 0

/-- Pointwise: `2rw − dw²/z ≤ z·(r)_+²/d` for `d > 0`, `z ≥ 0`, `w ≥ 0` and `w = 0` if `z = 0`. -/
lemma persp_item_le {r dd zz ww : ℝ} (hd : 0 < dd) (hz : 0 ≤ zz) (hw : 0 ≤ ww)
    (hzw : zz = 0 → ww = 0) :
    2 * r * ww - dd * ww ^ 2 / zz ≤ zz * ((max r 0) ^ 2 / dd) := by
  rcases hz.lt_or_eq with hzpos | hz0
  · have key : 0 ≤ dd / zz * (ww - zz * max r 0 / dd) ^ 2 := by positivity
    have hexp : dd / zz * (ww - zz * max r 0 / dd) ^ 2
        = dd * ww ^ 2 / zz - 2 * max r 0 * ww + zz * ((max r 0) ^ 2 / dd) := by
      field_simp; ring
    have hr : r * ww ≤ max r 0 * ww := mul_le_mul_of_nonneg_right (le_max_left _ _) hw
    linarith
  · have hw0 : ww = 0 := hzw hz0.symm
    rw [hw0, ← hz0]; simp

/-- **Weak duality for the perspective relaxation.** -/
theorem perspObj_le_dualBound (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {k : ℕ} {z w : ι → ℝ}
    (hf : PerspFeasible k z w) (t : κ → ℝ) :
    perspObj m d B Sf z w ≤ dualBound m d B P k t := by
  obtain ⟨hz, hzk, hw, hzw⟩ := hf
  have hyoung := young_Sf (B := B) (P := P) (G := G) hG hPS univ w t
  have hdot := Bw_dot (B := B) univ w t
  have hitems : ∑ i, (2 * (m i - dotp (B i) t) * w i - d i * w i ^ 2 / z i)
      ≤ ∑ i, z i * clipScore m d B t i :=
    Finset.sum_le_sum fun i _ => persp_item_le (hd i) (hz i).1 (hw i) (hzw i)
  have hsplit : ∑ i, (2 * (m i - dotp (B i) t) * w i - d i * w i ^ 2 / z i)
      = 2 * (∑ i, m i * w i) - 2 * (∑ j, Bw B univ w j * t j) - ∑ i, d i * w i ^ 2 / z i := by
    rw [hdot]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hlag := lagrangian_le_dualBound (m := m) (d := d) (B := B) (P := P) (t := t) hz hzk
  unfold perspObj
  linarith

/-- The value of a clipped weight: `2m_iw_i − d_iw_i² = s_i(t) + 2w_i⟨B_i,t⟩`. -/
lemma wclip_item (hd : ∀ i, 0 < d i) (t : κ → ℝ) (i : ι) :
    2 * (m i * wclip m d B t i) - d i * wclip m d B t i ^ 2
      = clipScore m d B t i + 2 * (wclip m d B t i * dotp (B i) t) := by
  have hne : d i ≠ 0 := ne_of_gt (hd i)
  have hz := max_mul_sub_max (m i - dotp (B i) t)
  simp only [wclip, clipScore]
  field_simp
  nlinarith [hz]

/-- **The perspective relaxation (Proposition of §5.4).** There are a minimizer `t*` of `g_k` and a feasible
pair `(z, w)` of the perspective relaxation with value `g_k(t*) = G*_k`, and every feasible pair has value at
most `G*_k`. So `G*_k = max{perspective relaxation} = min_t g_k(t)`. The pair is `z = λ*`, `w_i = λ*_i w_i(t*)`
for a saddle point `(t*, λ*)`. -/
theorem perspective_relaxation [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ Fintype.card ι) :
    ∃ (t : κ → ℝ) (z w : ι → ℝ), (∀ t', dualBound m d B P k t ≤ dualBound m d B P k t') ∧
      PerspFeasible k z w ∧ perspObj m d B Sf z w = dualBound m d B P k t ∧
      ∀ z' w' : ι → ℝ, PerspFeasible k z' w' → perspObj m d B Sf z' w' ≤ dualBound m d B P k t := by
  obtain ⟨t, lam, σ, hmin, hS, -, -⟩ :=
    exists_saddle_vertex (m := m) (B := B) (Sf := Sf) (G := G) hd hG hPS hk1 hk
  set w : ι → ℝ := fun i => lam i * wclip m d B t i with hw
  have hfeas : PerspFeasible k lam w :=
    ⟨hS.range, hS.sum, fun i => mul_nonneg (hS.range i).1 (wclip_nonneg hd t i),
      fun i hi => by simp [hw, hi]⟩
  refine ⟨t, lam, w, hmin, hfeas, ?_, fun z' w' hf => perspObj_le_dualBound hd hG hPS hf t⟩
  -- `B'w = Pt` by stationarity, hence `Σ_f B'w = t`
  have hBw : ∀ j, Bw B univ w j = ∑ j', P j j' * t j' := by
    intro j
    rw [hS.stat j, Bw]
    exact Finset.sum_congr rfl fun i _ => by simp only [hw]; ring
  have hSP := SP_of_PS (P := P) (Sf := Sf) hPS
  have htw : tw Sf B univ w = t := by
    funext j
    simp only [tw]
    rw [Finset.sum_congr rfl fun j' _ => by rw [hBw j']]
    have hswap : ∑ j' : κ, Sf j j' * ∑ l, P j' l * t l = ∑ l, (∑ j', Sf j j' * P j' l) * t l := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j' _ => by ring
    rw [hswap, Finset.sum_congr rfl fun l _ => by rw [hSP j l]]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hq : quadf Sf (Bw B univ w) = quadf P t := by
    rw [← quadf_P_tw hG hPS univ w, htw]
  have hlin : ∑ j, Bw B univ w j * t j = quadf P t := by
    simp only [hBw, quadf, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
  -- the terms of the assets
  have hitem : ∀ i, 2 * (m i * w i) - d i * w i ^ 2 / lam i
      = lam i * clipScore m d B t i + 2 * (w i * dotp (B i) t) := by
    intro i
    by_cases h0 : lam i = 0
    · simp [hw, h0]
    · have h1 := wclip_item (m := m) (B := B) hd t i
      have h2 : d i * w i ^ 2 / lam i = lam i * (d i * wclip m d B t i ^ 2) := by
        simp only [hw]; field_simp
      rw [h2]
      have h3 : 2 * (m i * w i) = lam i * (2 * (m i * wclip m d B t i)) := by simp only [hw]; ring
      have h4 : 2 * (w i * dotp (B i) t) = lam i * (2 * (wclip m d B t i * dotp (B i) t)) := by
        simp only [hw]; ring
      rw [h3, h4]
      linear_combination lam i * h1
  have hsum : 2 * (∑ i, m i * w i) - ∑ i, d i * w i ^ 2 / lam i
      = ∑ i, lam i * clipScore m d B t i + 2 * ∑ i, w i * dotp (B i) t := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [← hitem i]
  have hdot := Bw_dot (B := B) univ w t
  rw [hS.dualBound_eq_lagrangian hd, perspObj, hq]
  rw [← hdot, hlin] at hsum
  linarith

end SparseSharpe.Factor
