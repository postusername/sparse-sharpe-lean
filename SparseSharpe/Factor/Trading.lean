import SparseSharpe.Factor.Main

set_option linter.style.header false

/-!
# Trading form of the main theorem

Everything a portfolio manager needs to turn `main_theorem` into a statement about a
**tradable** portfolio, proved from the data of the problem only.

* **Sharpe ratio.** `pRet`, `pVar`, `sharpe` — expected excess return `m_S'w`, variance
  `w'V_Sw` and the Sharpe ratio `m_S'w/√(w'V_Sw)`. The objective of the paper is
  `objLO = 2·pRet − pVar`; it never exceeds the squared Sharpe ratio
  (`objLO_le_ret_sq_div`) and equals it after the optimal rescaling
  (`objLO_opt_scale`). Hence a `(1 − 2ε)` guarantee for the objective is a `√(1 − 2ε)`
  guarantee for the Sharpe ratio (`sharpe_ge_of_obj_ge`).
* **Scale invariance and budget.** `sharpe_smul`: the Sharpe ratio does not change under a
  positive rescaling; `normalize_budget`: a nonzero long-only portfolio can be rescaled to
  a fully invested one (`Σ x_i = 1`) with the same Sharpe ratio; `pVar_smul` gives the
  variance after rescaling (volatility targeting).
* **Guesses of the optimal value.** With `L = max_i (m_i)_+²/V_ii` the optimal value lies in
  `[L, k(1 + ω)L]` (`opt_ge_single_of_opt`, `objLO_le_sum_posPart`, `sum_posPart_le`), so a
  doubling grid `L·2^j`, `j ≤ J`, `k(1 + ω) ≤ 2^J`, contains a guess `V` with
  `V ≤ OPT ≤ 2V` (`exists_doubling_guess`). The number of guesses does not depend on the
  magnitudes of the data.
* **The scheme as a finite search** (`candidates`, `card_candidates_le`,
  `exists_good_candidate`, `best_candidate_sharpe`): the union over guesses, `K`-tuples and
  grid nodes of the tables of the dynamic program is an explicit finite family of supports
  of explicitly bounded size; it contains a support carrying a long-only portfolio within
  `1 − 2ε` of the optimum, and every best candidate (evaluated exactly, Theorem D) has
  Sharpe ratio at least `√(1 − 2ε)` times that of **any** long-only portfolio with at most
  `k` names.
-/

namespace SparseSharpe.Factor

open Finset

set_option linter.unusedSectionVars false

section Trading

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-! ### Return, variance, Sharpe ratio -/

/-- Expected excess return `m_S'w` of a portfolio supported on `S`. -/
noncomputable def pRet (m : ι → ℝ) (S : Finset ι) (w : ι → ℝ) : ℝ := ∑ i ∈ S, m i * w i

/-- Variance `w'V_Sw` of a portfolio supported on `S`, `V = D + BΣ_fB'`. -/
noncomputable def pVar (d : ι → ℝ) (B : ι → κ → ℝ) (Sf : κ → κ → ℝ) (S : Finset ι)
    (w : ι → ℝ) : ℝ :=
  ∑ i ∈ S, ∑ i' ∈ S, Vmat d B Sf i i' * (w i * w i')

/-- Sharpe ratio `m_S'w / √(w'V_Sw)`. -/
noncomputable def sharpe (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf : κ → κ → ℝ) (S : Finset ι)
    (w : ι → ℝ) : ℝ :=
  pRet m S w / Real.sqrt (pVar d B Sf S w)

/-- The objective of the paper is `2·return − variance`. -/
lemma objLO_eq_ret_var (S : Finset ι) (w : ι → ℝ) :
    objLO m d B Sf S w = 2 * pRet m S w - pVar d B Sf S w := rfl

/-- `u'Σ_f u ≥ 0` (the factor covariance is positive semidefinite). -/
lemma quadf_Sf_Bw_nonneg (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (S : Finset ι) (w : ι → ℝ) : 0 ≤ quadf Sf (Bw B S w) := by
  have h := young_Sf (B := B) (P := P) (G := G) hG hPS S w (fun _ => 0)
  have h0 : quadf P (fun _ : κ => (0:ℝ)) = 0 := by simp [quadf]
  simp only [mul_zero, Finset.sum_const_zero, h0, sub_zero] at h
  linarith

/-- The variance dominates its idiosyncratic part: `w'V_Sw ≥ Σ_{i∈S} d_i w_i²`. -/
lemma pVar_ge_diag (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (S : Finset ι) (w : ι → ℝ) :
    ∑ i ∈ S, d i * w i ^ 2 ≤ pVar d B Sf S w := by
  rw [pVar, quad_Vmat]
  have := quadf_Sf_Bw_nonneg (B := B) hG hPS S w
  linarith

lemma pVar_nonneg (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (S : Finset ι) (w : ι → ℝ) : 0 ≤ pVar d B Sf S w := by
  refine le_trans (Finset.sum_nonneg fun i _ => ?_) (pVar_ge_diag (B := B) hG hPS S w)
  have := hd i
  positivity

/-- A portfolio with a nonzero weight has positive variance. -/
lemma pVar_pos (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {S : Finset ι} {w : ι → ℝ} {i : ι} (hi : i ∈ S) (hwi : w i ≠ 0) :
    0 < pVar d B Sf S w := by
  have h1 : 0 < d i * w i ^ 2 := mul_pos (hd i) (sq_pos_of_ne_zero hwi)
  have h2 : d i * w i ^ 2 ≤ ∑ j ∈ S, d j * w j ^ 2 :=
    Finset.single_le_sum (f := fun j => d j * w j ^ 2)
      (fun j _ => mul_nonneg (hd j).le (sq_nonneg _)) hi
  linarith [pVar_ge_diag (B := B) (Sf := Sf) (d := d) hG hPS S w]

/-- A portfolio with positive expected return has a nonzero weight. -/
lemma exists_ne_zero_of_pRet_pos {S : Finset ι} {w : ι → ℝ} (h : 0 < pRet m S w) :
    ∃ i ∈ S, w i ≠ 0 := by
  by_contra hcon
  have hz : ∀ i ∈ S, w i = 0 := by
    intro i hi
    by_contra hne
    exact hcon ⟨i, hi, hne⟩
  have : pRet m S w = 0 := by
    unfold pRet
    exact Finset.sum_eq_zero fun i hi => by rw [hz i hi, mul_zero]
  linarith

/-- **The objective never exceeds the squared Sharpe ratio**:
`2m'w − w'Vw ≤ (m'w)²/(w'Vw)` whenever `w'Vw > 0`. -/
lemma objLO_le_ret_sq_div (S : Finset ι) (w : ι → ℝ) (hv : 0 < pVar d B Sf S w) :
    objLO m d B Sf S w ≤ pRet m S w ^ 2 / pVar d B Sf S w := by
  rw [objLO_eq_ret_var, le_div_iff₀ hv]
  nlinarith [sq_nonneg (pRet m S w - pVar d B Sf S w)]

lemma pRet_smul (S : Finset ι) (w : ι → ℝ) (c : ℝ) :
    pRet m S (fun i => c * w i) = c * pRet m S w := by
  simp only [pRet, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Variance after rescaling: `(cw)'V(cw) = c²·w'Vw` (volatility targeting). -/
lemma pVar_smul (S : Finset ι) (w : ι → ℝ) (c : ℝ) :
    pVar d B Sf S (fun i => c * w i) = c ^ 2 * pVar d B Sf S w := by
  simp only [pVar, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring

lemma objLO_smul (S : Finset ι) (w : ι → ℝ) (c : ℝ) :
    objLO m d B Sf S (fun i => c * w i)
      = 2 * c * pRet m S w - c ^ 2 * pVar d B Sf S w := by
  rw [objLO_eq_ret_var, pRet_smul, pVar_smul]; ring

/-- **The optimal rescaling attains the squared Sharpe ratio**:
with `c = m'w/(w'Vw)`, `2m'(cw) − (cw)'V(cw) = (m'w)²/(w'Vw)`. -/
lemma objLO_opt_scale (S : Finset ι) (w : ι → ℝ) (hv : 0 < pVar d B Sf S w) :
    objLO m d B Sf S (fun i => (pRet m S w / pVar d B Sf S w) * w i)
      = pRet m S w ^ 2 / pVar d B Sf S w := by
  rw [objLO_smul]
  field_simp
  ring

/-- **Scale invariance of the Sharpe ratio.** -/
lemma sharpe_smul (S : Finset ι) (w : ι → ℝ) {c : ℝ} (hc : 0 < c) :
    sharpe m d B Sf S (fun i => c * w i) = sharpe m d B Sf S w := by
  unfold sharpe
  rw [pRet_smul, pVar_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  by_cases hv : Real.sqrt (pVar d B Sf S w) = 0
  · simp [hv]
  · field_simp

/-- The squared Sharpe ratio. -/
lemma sharpe_sq (S : Finset ι) (w : ι → ℝ) (hv : 0 < pVar d B Sf S w) :
    sharpe m d B Sf S w ^ 2 = pRet m S w ^ 2 / pVar d B Sf S w := by
  unfold sharpe
  rw [div_pow, Real.sq_sqrt hv.le]

/-- **From the objective to the Sharpe ratio.** If a portfolio `w` on `R` has objective at
least `(1 − 2ε)` times the squared Sharpe ratio of a long-only portfolio `u` with positive
expected return, then `w` has positive return and variance, and
`sharpe(w) ≥ √(1 − 2ε)·sharpe(u)`. -/
theorem sharpe_ge_of_obj_ge (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {S R : Finset ι} {u w : ι → ℝ} {ε : ℝ} (hε : 2 * ε < 1)
    (hru : 0 < pRet m S u)
    (hobj : (1 - 2 * ε) * (pRet m S u ^ 2 / pVar d B Sf S u) ≤ objLO m d B Sf R w) :
    0 < pRet m R w ∧ 0 < pVar d B Sf R w ∧
      Real.sqrt (1 - 2 * ε) * sharpe m d B Sf S u ≤ sharpe m d B Sf R w := by
  obtain ⟨i, hi, hui⟩ := exists_ne_zero_of_pRet_pos hru
  have hvu : 0 < pVar d B Sf S u := pVar_pos (B := B) hd hG hPS hi hui
  have hq : 0 < pRet m S u ^ 2 / pVar d B Sf S u := by positivity
  have hc : 0 < 1 - 2 * ε := by linarith
  have hobjpos : 0 < objLO m d B Sf R w := lt_of_lt_of_le (mul_pos hc hq) hobj
  have hvw0 : 0 ≤ pVar d B Sf R w := pVar_nonneg (B := B) hd hG hPS R w
  have hrw : 0 < pRet m R w := by
    rw [objLO_eq_ret_var] at hobjpos
    linarith
  obtain ⟨i', hi', hwi'⟩ := exists_ne_zero_of_pRet_pos hrw
  have hvw : 0 < pVar d B Sf R w := pVar_pos (B := B) hd hG hPS hi' hwi'
  refine ⟨hrw, hvw, ?_⟩
  have hsq : (1 - 2 * ε) * (pRet m S u ^ 2 / pVar d B Sf S u)
      ≤ pRet m R w ^ 2 / pVar d B Sf R w :=
    le_trans hobj (objLO_le_ret_sq_div R w hvw)
  -- take square roots of both sides
  have hL : Real.sqrt (1 - 2 * ε) * sharpe m d B Sf S u
      = Real.sqrt ((1 - 2 * ε) * (pRet m S u ^ 2 / pVar d B Sf S u)) := by
    rw [Real.sqrt_mul hc.le, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hru.le]
    rfl
  have hR : sharpe m d B Sf R w = Real.sqrt (pRet m R w ^ 2 / pVar d B Sf R w) := by
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hrw.le]
    rfl
  rw [hL, hR]
  exact Real.sqrt_le_sqrt hsq

/-- **Budget normalization.** A long-only portfolio with positive expected return can be
rescaled to a fully invested one (`Σ x_i = 1`, `x ≥ 0`) with the same Sharpe ratio. -/
theorem normalize_budget {R : Finset ι} {w : ι → ℝ} (hw : ∀ i ∈ R, 0 ≤ w i)
    (hr : 0 < pRet m R w) :
    ∃ x : ι → ℝ, (∀ i ∈ R, 0 ≤ x i) ∧ ∑ i ∈ R, x i = 1 ∧
      sharpe m d B Sf R x = sharpe m d B Sf R w := by
  obtain ⟨i, hi, hwi⟩ := exists_ne_zero_of_pRet_pos hr
  have hwi' : 0 < w i := lt_of_le_of_ne (hw i hi) (Ne.symm hwi)
  have hsum : 0 < ∑ j ∈ R, w j :=
    lt_of_lt_of_le hwi' (Finset.single_le_sum (f := w) (fun j hj => hw j hj) hi)
  refine ⟨fun j => (∑ j' ∈ R, w j')⁻¹ * w j, fun j hj => ?_, ?_, ?_⟩
  · exact mul_nonneg (inv_nonneg.mpr hsum.le) (hw j hj)
  · rw [← Finset.mul_sum]; exact inv_mul_cancel₀ hsum.ne'
  · exact sharpe_smul R w (inv_pos.mpr hsum)

/-! ### Bracketing the optimal value: a doubling grid of guesses -/

/-- Diagonal of the covariance: `V_ii = d_i + B_i'Σ_fB_i`. -/
lemma Vmat_diag (i : ι) : Vmat d B Sf i i = d i + sysVar B Sf i := by
  simp [Vmat, sysVar, mul_assoc]

lemma Vmat_diag_pos (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (i : ι) :
    0 < Vmat d B Sf i i := by
  rw [Vmat_diag]
  have := sysVar_nonneg (B := B) hG hPS i
  linarith [hd i]

lemma pRet_single {S : Finset ι} {i : ι} (hi : i ∈ S) (c : ℝ) :
    pRet m S (fun j => if j = i then c else 0) = m i * c := by
  unfold pRet
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd hi h

lemma pVar_single {S : Finset ι} {i : ι} (hi : i ∈ S) (c : ℝ) :
    pVar d B Sf S (fun j => if j = i then c else 0) = c ^ 2 * Vmat d B Sf i i := by
  unfold pVar
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · simp; ring
    · intro b _ hb; simp [hb]
    · intro h; exact absurd hi h
  · intro b _ hb; simp [hb]
  · intro h; exact absurd hi h

/-- A single asset: the best long-only position in asset `i` has objective
`(m_i)_+²/V_ii` (its squared Sharpe ratio when `m_i > 0`). -/
lemma objLO_single_value (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {S : Finset ι} {i : ι} (hi : i ∈ S) :
    objLO m d B Sf S (fun j => if j = i then max (m i) 0 / Vmat d B Sf i i else 0)
      = max (m i) 0 ^ 2 / Vmat d B Sf i i := by
  have hV := Vmat_diag_pos (B := B) (Sf := Sf) hd hG hPS i
  rw [objLO_eq_ret_var, pRet_single hi, pVar_single hi]
  have hmm : m i * max (m i) 0 = max (m i) 0 ^ 2 := by
    rcases le_or_gt (m i) 0 with h | h
    · rw [max_eq_right h]; ring
    · rw [max_eq_left h.le]; ring
  have hmm' : max (m i) 0 * m i = max (m i) 0 ^ 2 := by rw [mul_comm]; exact hmm
  field_simp
  linear_combination 2 * hmm'

/-- **Lower bracket.** If `S` is optimal among supports with at most `k ≥ 1` names, its value
is at least `(m_i)_+²/V_ii` for every asset `i`. -/
lemma opt_ge_single_of_opt (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {Fopt : ℝ}
    (hSopt : ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        objLO m d B Sf S' u ≤ Fopt) (i : ι) :
    max (m i) 0 ^ 2 / Vmat d B Sf i i ≤ Fopt := by
  have hV := Vmat_diag_pos (B := B) (Sf := Sf) hd hG hPS i
  have h := hSopt {i} (by simpa using hk1)
    (fun j => if j = i then max (m i) 0 / Vmat d B Sf i i else 0) (by
      intro j hj
      have : j = i := Finset.mem_singleton.mp hj
      subst this
      simp only [ite_true]
      exact div_nonneg (le_max_right _ _) hV.le)
  rwa [objLO_single_value (B := B) hd hG hPS (Finset.mem_singleton_self i)] at h

/-- **Upper bracket (weak duality at `t = 0`).** Every long-only portfolio on `S` has
objective at most `Σ_{i∈S} (m_i)_+²/d_i`. -/
lemma objLO_le_sum_posPart (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {S : Finset ι} {w : ι → ℝ} (hw : ∀ i ∈ S, 0 ≤ w i) :
    objLO m d B Sf S w ≤ ∑ i ∈ S, max (m i) 0 ^ 2 / d i := by
  have h := objLO_le_QLO (m := m) (B := B) (Sf := Sf) (P := P) (G := G) hd hG hPS hw
    (fun _ => 0)
  have h0 : QLO m d B P S (fun _ => 0) = ∑ i ∈ S, max (m i) 0 ^ 2 / d i := by
    simp [QLO, quadf, dotp]
  linarith

/-- Each term of the upper bracket is at most `(1 + ω)` times the single-asset value. -/
lemma posPart_div_d_le (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {ω : ℝ} {i : ι} (hsys : sysVar B Sf i / d i ≤ ω) :
    max (m i) 0 ^ 2 / d i ≤ (1 + ω) * (max (m i) 0 ^ 2 / Vmat d B Sf i i) := by
  have hV := Vmat_diag_pos (B := B) (Sf := Sf) hd hG hPS i
  have hdi := hd i
  have hratio : Vmat d B Sf i i / d i ≤ 1 + ω := by
    rw [Vmat_diag, add_div, div_self hdi.ne']
    linarith
  have heq : max (m i) 0 ^ 2 / d i
      = (Vmat d B Sf i i / d i) * (max (m i) 0 ^ 2 / Vmat d B Sf i i) := by
    field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_right hratio (by positivity)

/-- **The bracket `[L, k(1 + ω)L]`.** -/
lemma sum_posPart_le (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {ω L : ℝ} (hω : 0 ≤ ω) (hsys : ∀ i, sysVar B Sf i / d i ≤ ω) (hL0 : 0 ≤ L)
    (hL : ∀ i, max (m i) 0 ^ 2 / Vmat d B Sf i i ≤ L) {k : ℕ} {S : Finset ι}
    (hkS : S.card ≤ k) :
    ∑ i ∈ S, max (m i) 0 ^ 2 / d i ≤ (k : ℝ) * (1 + ω) * L := by
  calc ∑ i ∈ S, max (m i) 0 ^ 2 / d i ≤ ∑ _i ∈ S, (1 + ω) * L :=
        Finset.sum_le_sum fun i _ =>
          le_trans (posPart_div_d_le (B := B) hd hG hPS (hsys i))
            (mul_le_mul_of_nonneg_left (hL i) (by linarith))
    _ = (S.card : ℝ) * ((1 + ω) * L) := by simp
    _ ≤ (k : ℝ) * ((1 + ω) * L) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hkS) (by positivity)
    _ = (k : ℝ) * (1 + ω) * L := by ring

/-- **Doubling grid of guesses.** If `0 < L ≤ F ≤ 2^J·L`, some `j ≤ J` has
`L·2^j ≤ F ≤ 2·L·2^j`. -/
theorem exists_doubling_guess : ∀ (J : ℕ) {L F : ℝ}, 0 < L → L ≤ F → F ≤ 2 ^ J * L →
    ∃ j ≤ J, L * 2 ^ j ≤ F ∧ F ≤ 2 * (L * 2 ^ j)
  | 0, L, F, _, hLF, hFJ => ⟨0, le_rfl, by simpa using hLF, by simp at hFJ; linarith⟩
  | J + 1, L, F, hL, hLF, hFJ => by
    by_cases h : F ≤ 2 * L
    · exact ⟨0, Nat.zero_le _, by simpa using hLF, by simpa using h⟩
    · have h' : 2 * L < F := lt_of_not_ge h
      have hFJ' : F ≤ 2 ^ J * (2 * L) := by
        have : (2:ℝ) ^ (J + 1) * L = 2 ^ J * (2 * L) := by rw [pow_succ]; ring
        linarith
      obtain ⟨j, hj, h1, h2⟩ := exists_doubling_guess J (L := 2 * L) (by linarith) h'.le hFJ'
      refine ⟨j + 1, by omega, ?_, ?_⟩
      · have : L * 2 ^ (j + 1) = 2 * L * 2 ^ j := by rw [pow_succ]; ring
        linarith
      · have : L * 2 ^ (j + 1) = 2 * L * 2 ^ j := by rw [pow_succ]; ring
        linarith

/-- **Everything together:** for an optimal support `S` the doubling grid `L·2^j`,
`j ≤ J`, `k(1 + ω) ≤ 2^J`, contains a guess `V` with `V ≤ OPT ≤ 2V`. -/
theorem exists_guess_of_opt (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ω L : ℝ} (hω : 0 ≤ ω) (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    (hL0 : 0 < L) (hL : ∀ i, max (m i) 0 ^ 2 / Vmat d B Sf i i ≤ L)
    (hLatt : ∃ i, max (m i) 0 ^ 2 / Vmat d B Sf i i = L)
    {J : ℕ} (hJ : (k : ℝ) * (1 + ω) ≤ 2 ^ J)
    {S : Finset ι} (hkS : S.card ≤ k) {Fopt : ℝ}
    (hFopt : IsGreatest {v : ℝ | ∃ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i)
        ∧ v = objLO m d B Sf S u} Fopt)
    (hSopt : ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        objLO m d B Sf S' u ≤ Fopt) :
    ∃ j ≤ J, L * 2 ^ j ≤ Fopt ∧ Fopt ≤ 2 * (L * 2 ^ j) := by
  obtain ⟨i₀, hi₀⟩ := hLatt
  have hLF : L ≤ Fopt := hi₀ ▸ opt_ge_single_of_opt (B := B) hd hG hPS hk1 hSopt i₀
  obtain ⟨u, hu, hFu⟩ := hFopt.1
  have hFU : Fopt ≤ (k : ℝ) * (1 + ω) * L := by
    rw [hFu]
    exact le_trans (objLO_le_sum_posPart (B := B) hd hG hPS hu)
      (sum_posPart_le (B := B) hd hG hPS hω hsys hL0.le hL hkS)
  have hFJ : Fopt ≤ 2 ^ J * L := le_trans hFU (mul_le_mul_of_nonneg_right hJ hL0.le)
  exact exists_doubling_guess J hL0 hLF hFJ

/-! ### The scheme as a finite search -/

/-- Grid step of the scheme at guess `V` (the step of `main_theorem`, `c = k(1+kω)`,
`C = (k+K)K`). -/
noncomputable def schemeStep (Kc k : ℕ) (ε ω V : ℝ) : ℝ :=
  2 * Real.sqrt ((ε / (32 * ((k : ℝ) * (1 + (k : ℝ) * ω)))) * V
    / ((Kc : ℝ) * (((k + Kc : ℕ) : ℝ) * (Kc : ℝ))))

/-- Radius of the box of node indices of `main_theorem`. -/
noncomputable def schemeZ (Kc k : ℕ) (ε ω : ℝ) : ℕ :=
  ⌈4 * (Kc : ℝ) * Real.sqrt (((k + Kc : ℕ) : ℝ) * ((k : ℝ) * (1 + (k : ℝ) * ω)) / ε)
    + 1 / 2⌉₊

/-- Node point: the point whose residuals on the `K`-tuple `T` are `y_{T_l} + s·z_l`
(an arbitrary point if `T` is degenerate). -/
noncomputable def nodePoint {ι' : Type*} (a : ι' → κ → ℝ) (y : ι' → ℝ) (T : κ → ι') (s : ℝ)
    (z : κ → ℤ) : κ → ℝ :=
  if h : (rowMat a T).det ≠ 0 then
    Classical.choose (exists_point_with_residuals h (fun l => y (T l) + s * (z l : ℝ)))
  else fun _ => 0

lemma nodePoint_spec {ι' : Type*} {a : ι' → κ → ℝ} {y : ι' → ℝ} {T : κ → ι'} {s : ℝ}
    {z : κ → ℤ} (h : (rowMat a T).det ≠ 0) (l : κ) :
    dotp (a (T l)) (nodePoint a y T s z) = y (T l) + s * (z l : ℝ) := by
  unfold nodePoint
  rw [dif_pos h]
  exact Classical.choose_spec (exists_point_with_residuals h
    (fun l => y (T l) + s * (z l : ℝ))) l

/-- The table of the dynamic program with key-box pruning at guess `V`, `K`-tuple `T` and
point `t` — literally the object of `main_theorem`. -/
noncomputable def schemeTable (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ)
    (ε ω V : ℝ) (T : κ → (ι ⊕ κ)) (t : κ → ℝ) : Finset (Finset (ι ⊕ κ)) :=
  survivorsBox (fun W => phi (rowsK d B G) (targetsK m d) W t)
    (keyOf (rowsK d B G) (targetsK m d) T t
      (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
        / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
      (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ))))
    (fun x => decide (-theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
      ≤ targetsK m d x - dotp (rowsK d B G x) t))
    (boxOf κ 1 V (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
        / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
      (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ)))
      (k + Fintype.card κ) (Fintype.card ι))
    (anchorRows ι κ) ((Finset.univ : Finset ι).toList.map Sum.inl)

/-- **The candidate family of the scheme**: union over the guesses `V = L·2^j`, `j ≤ J`, all
`K`-tuples of rows and all grid nodes of the tables of the dynamic program. -/
noncomputable def candidates (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ)
    (ε ω L : ℝ) (J : ℕ) : Finset (Finset (ι ⊕ κ)) :=
  (Finset.range (J + 1)).biUnion fun j =>
    (Finset.univ : Finset (κ → (ι ⊕ κ))).biUnion fun T =>
      (nodeBox (κ := κ) (schemeZ (Fintype.card κ) k ε ω)).biUnion fun z =>
        schemeTable m d B G k ε ω (L * 2 ^ j) T
          (nodePoint (rowsK d B G) (targetsK m d) T
            (schemeStep (Fintype.card κ) k ε ω (L * 2 ^ j)) z)

/-- Size bound of one table (does not depend on the guess). -/
noncomputable def tableBound (Mc Kc k : ℕ) (ε ω : ℝ) : ℕ :=
  (2 * ⌈1 * (48 * (Mc : ℝ) * Real.sqrt (Kc : ℝ)
      * Real.sqrt (((k + Kc : ℕ) : ℝ) * ((k : ℝ) * (1 + (k : ℝ) * ω)) / ε))
      + (Mc : ℝ)⌉ + 1).toNat ^ Kc
    * ((2 * ⌈8 * ((k + Kc : ℕ) : ℝ) * (Mc : ℝ) * (Kc : ℝ) * 1 ^ 2 + (Mc : ℝ)⌉ + 1).toNat
        ^ (Kc * Kc) * (k + Kc + 1))

/-- Every table of the scheme has at most `tableBound + 1` entries. -/
lemma card_schemeTable_le [Nonempty κ] [Nonempty ι] {k : ℕ} (hk1 : 1 ≤ k) {ε ω V : ℝ}
    (hε : 0 < ε) (hω : 0 ≤ ω) (hV : 0 < V) (T : κ → (ι ⊕ κ)) (t : κ → ℝ) :
    (schemeTable m d B G k ε ω V T t).card
      ≤ tableBound (Fintype.card ι) (Fintype.card κ) k ε ω + 1 := by
  have hK0 : 0 < Fintype.card κ := Fintype.card_pos
  have hM0 : 0 < Fintype.card ι := Fintype.card_pos
  have hc : (0:ℝ) < (k : ℝ) * (1 + (k : ℝ) * ω) := by
    have hk : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have : (0:ℝ) ≤ (k : ℝ) * ω := mul_nonneg (by linarith) hω
    nlinarith
  have hN : 0 < k + Fintype.card κ := by omega
  have hbox := card_boxOf_le (κ := κ) (ε := ε) (c := (k : ℝ) * (1 + (k : ℝ) * ω)) (V := V)
    (ρ := 1) (N := k + Fintype.card κ) (Mn := Fintype.card ι) hε hc hV hN hM0 hK0
    zero_le_one rfl rfl
  unfold schemeTable
  refine le_trans (survivorsBox_card_le _ _ _ _ _ _) ?_
  unfold tableBound
  push_cast at hbox ⊢
  omega

/-- **Size of the candidate family**: at most `(J+1)·(M+K)^K·(2Z+1)^K·(tableBound+1)`. -/
theorem card_candidates_le [Nonempty κ] [Nonempty ι] {k : ℕ} (hk1 : 1 ≤ k) {ε ω L : ℝ}
    (hε : 0 < ε) (hω : 0 ≤ ω) (hL0 : 0 < L) (J : ℕ) :
    (candidates m d B G k ε ω L J).card
      ≤ (J + 1) * ((Fintype.card ι + Fintype.card κ) ^ Fintype.card κ
        * ((2 * schemeZ (Fintype.card κ) k ε ω + 1) ^ Fintype.card κ
          * (tableBound (Fintype.card ι) (Fintype.card κ) k ε ω + 1))) := by
  unfold candidates
  refine le_trans Finset.card_biUnion_le ?_
  have h1 : ∀ j ∈ Finset.range (J + 1),
      ((Finset.univ : Finset (κ → (ι ⊕ κ))).biUnion fun T =>
        (nodeBox (κ := κ) (schemeZ (Fintype.card κ) k ε ω)).biUnion fun z =>
          schemeTable m d B G k ε ω (L * 2 ^ j) T
            (nodePoint (rowsK d B G) (targetsK m d) T
              (schemeStep (Fintype.card κ) k ε ω (L * 2 ^ j)) z)).card
      ≤ (Fintype.card ι + Fintype.card κ) ^ Fintype.card κ
        * ((2 * schemeZ (Fintype.card κ) k ε ω + 1) ^ Fintype.card κ
          * (tableBound (Fintype.card ι) (Fintype.card κ) k ε ω + 1)) := by
    intro j _
    have hV : (0:ℝ) < L * 2 ^ j := by positivity
    refine le_trans Finset.card_biUnion_le ?_
    have h2 : ∀ T ∈ (Finset.univ : Finset (κ → (ι ⊕ κ))),
        ((nodeBox (κ := κ) (schemeZ (Fintype.card κ) k ε ω)).biUnion fun z =>
          schemeTable m d B G k ε ω (L * 2 ^ j) T
            (nodePoint (rowsK d B G) (targetsK m d) T
              (schemeStep (Fintype.card κ) k ε ω (L * 2 ^ j)) z)).card
        ≤ (2 * schemeZ (Fintype.card κ) k ε ω + 1) ^ Fintype.card κ
          * (tableBound (Fintype.card ι) (Fintype.card κ) k ε ω + 1) := by
      intro T _
      refine le_trans Finset.card_biUnion_le ?_
      refine le_trans (Finset.sum_le_card_nsmul _ _
        (tableBound (Fintype.card ι) (Fintype.card κ) k ε ω + 1)
        (fun z _ => card_schemeTable_le (m := m) (d := d) (B := B) (G := G) hk1 hε hω hV T _))
        ?_
      rw [card_nodeBox, smul_eq_mul]
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ h2) ?_
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_sum, smul_eq_mul]
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ h1) ?_
  rw [Finset.card_range, smul_eq_mul]

/-- Every candidate has at most `k` assets. -/
lemma card_assetsOf_le_of_mem_candidates [Nonempty κ] [Nonempty ι] {k : ℕ} {ε ω L : ℝ}
    {J : ℕ} {R : Finset (ι ⊕ κ)} (hR : R ∈ candidates m d B G k ε ω L J) :
    (assetsOf (κ := κ) R).card ≤ k := by
  unfold candidates at hR
  simp only [Finset.mem_biUnion] at hR
  obtain ⟨j, _, T, _, z, _, hRt⟩ := hR
  unfold schemeTable at hRt
  have hmem := survivorsBox_mem _ _ _ _ _ _ R hRt
  have hbR : anchorRows ι κ ⊆ R := hmem.1
  have hRbar : R = barK (κ := κ) (assetsOf (κ := κ) R) := barK_assetsOf hbR
  rcases survivorsBox_key_mem _ _ _ _ _ _ R hRt with hbase | hkey
  · -- only the anchors
    have : assetsOf (κ := κ) R = ∅ := by
      rw [hbase]
      ext i
      simp [mem_assetsOf, anchorRows]
    rw [this]; simp
  · simp only [boxOf, keyBox, keyOf, Finset.mem_product, Finset.mem_range] at hkey
    have hcard : R.card ≤ k + Fintype.card κ := by omega
    have h2 := card_barK (κ := κ) (assetsOf (κ := κ) R)
    rw [← hRbar] at h2
    omega

/-- **The candidate family contains a near-optimal support.** For an optimal support `S`
(value `OPT`), some candidate carries a long-only portfolio `w` with
`2m'w − w'Vw ≥ (1 − 2ε)·OPT`. -/
theorem exists_good_candidate [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    (hL0 : 0 < L) (hL : ∀ i, max (m i) 0 ^ 2 / Vmat d B Sf i i ≤ L)
    (hLatt : ∃ i, max (m i) 0 ^ 2 / Vmat d B Sf i i = L)
    {J : ℕ} (hJ : (k : ℝ) * (1 + ω) ≤ 2 ^ J)
    {S : Finset ι} (hkS : S.card ≤ k) {Fopt : ℝ}
    (hFopt : IsGreatest {v : ℝ | ∃ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i)
        ∧ v = objLO m d B Sf S u} Fopt)
    (hSopt : ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        objLO m d B Sf S' u ≤ Fopt) :
    ∃ R ∈ candidates m d B G k ε ω L J, ∃ w : ι → ℝ, (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i)
      ∧ (1 - 2 * ε) * Fopt ≤ objLO m d B Sf (assetsOf (κ := κ) R) w := by
  obtain ⟨j, hjJ, hVF, hFV⟩ := exists_guess_of_opt (B := B) hd hG hPS hk1 hω hsys hL0 hL
    hLatt hJ hkS hFopt hSopt
  have hV : (0:ℝ) < L * 2 ^ j := by positivity
  obtain ⟨⟨T, hdet, z, hz, hmain⟩, _⟩ := main_theorem (m := m) (d := d) (B := B) (Sf := Sf)
    (P := P) (G := G) hd hG hPS hk1 hε hε1 hω hsys hkS hFopt hV hVF hFV
  set t := nodePoint (rowsK d B G) (targetsK m d) T
    (schemeStep (Fintype.card κ) k ε ω (L * 2 ^ j)) z with ht
  have hnode := fun l => nodePoint_spec (y := targetsK m d)
    (s := schemeStep (Fintype.card κ) k ε ω (L * 2 ^ j)) (z := z) hdet l
  obtain ⟨adm, hadm, R, hR, _, w, hw, hval⟩ := hmain t hnode
  subst hadm
  refine ⟨R, ?_, w, hw, ?_⟩
  · unfold candidates
    simp only [Finset.mem_biUnion]
    exact ⟨j, Finset.mem_range.mpr (by omega), T, Finset.mem_univ _, z, hz, hR⟩
  · obtain ⟨u, hu, hFu⟩ := hFopt.1
    have := hval u hu
    rw [hFu]
    exact this

/-- **A best candidate exists**: a pair `(R*, w*)`, `R*` a candidate, `w* ≥ 0` on it, whose
objective is at least that of every candidate with every long-only portfolio on it. It is
what the scheme returns after evaluating every candidate exactly (Theorem D). -/
theorem exists_best_pair [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} {ε ω L : ℝ} {J : ℕ} (hne : (candidates m d B G k ε ω L J).Nonempty) :
    ∃ R₀ ∈ candidates m d B G k ε ω L J, ∃ w₀ : ι → ℝ,
      (∀ i ∈ assetsOf (κ := κ) R₀, 0 ≤ w₀ i) ∧
      ∀ R ∈ candidates m d B G k ε ω L J, ∀ w : ι → ℝ, (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i) →
        objLO m d B Sf (assetsOf (κ := κ) R) w
          ≤ objLO m d B Sf (assetsOf (κ := κ) R₀) w₀ := by
  classical
  have hval : ∀ R : Finset (ι ⊕ κ), ∃ z : ℝ,
      IsGreatest {v : ℝ | ∃ w : ι → ℝ, (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i)
        ∧ v = objLO m d B Sf (assetsOf (κ := κ) R) w} z := by
    intro R
    obtain ⟨z, _, hz⟩ := isGreatest_objLO_isLeast_QLO (m := m) (B := B) (Sf := Sf) (P := P)
      (G := G) hd hG hPS (assetsOf (κ := κ) R)
    exact ⟨z, hz⟩
  choose val hvalG using hval
  obtain ⟨R₀, hR₀, hmax⟩ := Finset.exists_max_image _ val hne
  obtain ⟨w₀, hw₀, hw₀v⟩ := (hvalG R₀).1
  refine ⟨R₀, hR₀, w₀, hw₀, fun R hR w hw => ?_⟩
  rw [← hw₀v]
  exact le_trans ((hvalG R).2 ⟨w, hw, rfl⟩) (hmax R hR)

/-- **Trading form of the main theorem.** Let `S` be an optimal support with at most `k`
names. Every best pair `(R*, w*)` of the candidate family (`exists_best_pair`) is a
long-only portfolio with at most `k` names; it can be normalized to a fully invested
portfolio `x*` (`Σ x* = 1`, `x* ≥ 0`), and its Sharpe ratio is at least `√(1 − 2ε)` times
the Sharpe ratio of **every** long-only portfolio with at most `k` names and positive
expected excess return. -/
theorem best_pair_sharpe [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω L : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    (hL0 : 0 < L) (hL : ∀ i, max (m i) 0 ^ 2 / Vmat d B Sf i i ≤ L)
    (hLatt : ∃ i, max (m i) 0 ^ 2 / Vmat d B Sf i i = L)
    {J : ℕ} (hJ : (k : ℝ) * (1 + ω) ≤ 2 ^ J)
    {S : Finset ι} (hkS : S.card ≤ k) {Fopt : ℝ}
    (hFopt : IsGreatest {v : ℝ | ∃ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i)
        ∧ v = objLO m d B Sf S u} Fopt)
    (hSopt : ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        objLO m d B Sf S' u ≤ Fopt)
    {R₀ : Finset (ι ⊕ κ)} (hR₀ : R₀ ∈ candidates m d B G k ε ω L J) {w₀ : ι → ℝ}
    (hw₀ : ∀ i ∈ assetsOf (κ := κ) R₀, 0 ≤ w₀ i)
    (hbest : ∀ R ∈ candidates m d B G k ε ω L J, ∀ w : ι → ℝ,
      (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i) →
        objLO m d B Sf (assetsOf (κ := κ) R) w ≤ objLO m d B Sf (assetsOf (κ := κ) R₀) w₀) :
    (assetsOf (κ := κ) R₀).card ≤ k
    ∧ (1 - 2 * ε) * Fopt ≤ objLO m d B Sf (assetsOf (κ := κ) R₀) w₀
    ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        0 < pRet m S' u →
        ∃ x : ι → ℝ, (∀ i ∈ assetsOf (κ := κ) R₀, 0 ≤ x i)
          ∧ ∑ i ∈ assetsOf (κ := κ) R₀, x i = 1
          ∧ Real.sqrt (1 - 2 * ε) * sharpe m d B Sf S' u
              ≤ sharpe m d B Sf (assetsOf (κ := κ) R₀) x := by
  obtain ⟨R, hR, w, hw, hgood⟩ := exists_good_candidate (Sf := Sf) (P := P) hd hG hPS hk1 hε
    hε1.le hω hsys hL0 hL hLatt hJ hkS hFopt hSopt
  have hval : (1 - 2 * ε) * Fopt ≤ objLO m d B Sf (assetsOf (κ := κ) R₀) w₀ :=
    le_trans hgood (hbest R hR w hw)
  refine ⟨card_assetsOf_le_of_mem_candidates hR₀, hval, fun S' hS' u hu hru => ?_⟩
  -- the optimal rescaling of `u` is a `k`-sparse long-only portfolio
  obtain ⟨i, hi, hui⟩ := exists_ne_zero_of_pRet_pos hru
  have hvu : 0 < pVar d B Sf S' u := pVar_pos (B := B) hd hG hPS hi hui
  have hc : 0 ≤ pRet m S' u / pVar d B Sf S' u := div_nonneg hru.le hvu.le
  have hopt := hSopt S' hS' (fun i => (pRet m S' u / pVar d B Sf S' u) * u i)
    (fun i hi => mul_nonneg hc (hu i hi))
  rw [objLO_opt_scale S' u hvu] at hopt
  have hcoef : (0:ℝ) ≤ 1 - 2 * ε := by linarith
  have hobj : (1 - 2 * ε) * (pRet m S' u ^ 2 / pVar d B Sf S' u)
      ≤ objLO m d B Sf (assetsOf (κ := κ) R₀) w₀ :=
    le_trans (mul_le_mul_of_nonneg_left hopt hcoef) hval
  obtain ⟨hrw, _, hsh⟩ := sharpe_ge_of_obj_ge (B := B) hd hG hPS (by linarith) hru hobj
  obtain ⟨x, hx, hxs, hxsh⟩ := normalize_budget (d := d) (B := B) (Sf := Sf) hw₀ hrw
  exact ⟨x, hx, hxs, hxsh ▸ hsh⟩

end Trading

/-! ### Nonvacuity: the whole trading chain on a concrete instance

One asset (`m = 1`, `d = 1`, `B = 0`), one factor (`Σ_f = 1`), `k = 1`, `ε = 1/4`, `ω = 0`,
`L = 1`, `J = 0`. All hypotheses of `exists_good_candidate`, `exists_best_pair` and
`best_pair_sharpe` are proved; the conclusion is the nontrivial bound
`sharpe(x*) ≥ √(1/2) > 0` for a fully invested best candidate. -/

section Instance

/-- The objective of any portfolio of the one-asset instance is at most `1`. -/
lemma inst_obj_le (S : Finset (Fin 1)) (u : Fin 1 → ℝ) (hu : ∀ i ∈ S, 0 ≤ u i) :
    objLO (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1) (fun _ (_ : Unit) => 0) (fun _ _ => 1) S u
      ≤ 1 := by
  have h := objLO_le_sum_posPart (m := fun _ : Fin 1 => (1:ℝ)) (d := fun _ => 1)
    (B := fun _ (_ : Unit) => 0) (Sf := fun _ _ => 1) (P := fun _ _ => 1) (G := fun _ _ => 1)
    (fun _ => one_pos) (by intro j j'; simp) (by intro j j'; simp) hu
  refine le_trans h ?_
  have hS : S.card ≤ 1 := by
    calc S.card ≤ (Finset.univ : Finset (Fin 1)).card := Finset.card_le_univ S
      _ = 1 := by simp
  have : ∑ i ∈ S, max ((fun _ : Fin 1 => (1:ℝ)) i) 0 ^ 2 / (fun _ : Fin 1 => (1:ℝ)) i
      = (S.card : ℝ) := by simp
  rw [this]
  exact_mod_cast hS

theorem trading_instance :
    ∃ R₀ ∈ candidates (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1) (fun _ (_ : Unit) => 0)
        (fun _ _ => 1) 1 (1/4) 0 1 0,
      ∃ x : Fin 1 → ℝ, (∀ i ∈ assetsOf (κ := Unit) R₀, 0 ≤ x i)
        ∧ ∑ i ∈ assetsOf (κ := Unit) R₀, x i = 1
        ∧ Real.sqrt (1 - 2 * (1/4)) ≤ sharpe (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1)
            (fun _ (_ : Unit) => 0) (fun _ _ => 1) (assetsOf (κ := Unit) R₀) x := by
  set m : Fin 1 → ℝ := fun _ => 1
  set d : Fin 1 → ℝ := fun _ => 1
  set B : Fin 1 → Unit → ℝ := fun _ _ => 0
  set Sf : Unit → Unit → ℝ := fun _ _ => 1
  set G : Unit → Unit → ℝ := fun _ _ => 1
  set P : Unit → Unit → ℝ := fun _ _ => 1
  have hd : ∀ i, 0 < d i := fun _ => one_pos
  have hG : ∀ j j' : Unit, ∑ l : Unit, G l j * G l j' = P j j' := by intro j j'; simp [G, P]
  have hPS : ∀ j j' : Unit, ∑ l : Unit, P j l * Sf l j' = if j = j' then 1 else 0 := by
    intro j j'; simp [P, Sf]
  have hsys : ∀ i, sysVar B Sf i / d i ≤ 0 := by intro i; simp [sysVar, B]
  have hVd : ∀ i, Vmat d B Sf i i = 1 := by intro i; simp [Vmat, d, B]
  have hL : ∀ i, max (m i) 0 ^ 2 / Vmat d B Sf i i ≤ 1 := by intro i; simp [hVd, m]
  have hLatt : ∃ i, max (m i) 0 ^ 2 / Vmat d B Sf i i = 1 := ⟨0, by simp [hVd, m]⟩
  have hJ : ((1:ℕ) : ℝ) * (1 + 0) ≤ 2 ^ (0:ℕ) := by norm_num
  have hSopt : ∀ S' : Finset (Fin 1), S'.card ≤ 1 → ∀ u : Fin 1 → ℝ, (∀ i ∈ S', 0 ≤ u i) →
      objLO m d B Sf S' u ≤ 1 := fun S' _ u hu => inst_obj_le S' u hu
  have hFopt : IsGreatest {v : ℝ | ∃ u : Fin 1 → ℝ, (∀ i ∈ (Finset.univ : Finset (Fin 1)),
      0 ≤ u i) ∧ v = objLO m d B Sf Finset.univ u} 1 := by
    refine ⟨⟨fun _ => 1, fun _ _ => zero_le_one, ?_⟩, ?_⟩
    · simp [objLO, Vmat, m, d, B]; norm_num
    · rintro v ⟨u, hu, rfl⟩
      exact inst_obj_le _ u hu
  obtain ⟨R, hR, _⟩ := exists_good_candidate (G := G) (P := P)
    hd hG hPS le_rfl (by norm_num : (0:ℝ) < 1/4) (by norm_num) le_rfl hsys one_pos hL hLatt
    hJ (by simp : (Finset.univ : Finset (Fin 1)).card ≤ 1) hFopt hSopt
  obtain ⟨R₀, hR₀, w₀, hw₀, hbest⟩ := exists_best_pair (Sf := Sf) (P := P) hd hG hPS
    ⟨R, hR⟩
  obtain ⟨_, _, hsh⟩ := best_pair_sharpe (G := G) (P := P) hd hG hPS
    le_rfl (by norm_num : (0:ℝ) < 1/4) (by norm_num) le_rfl hsys one_pos hL hLatt hJ
    (by simp : (Finset.univ : Finset (Fin 1)).card ≤ 1) hFopt hSopt hR₀ hw₀ hbest
  obtain ⟨x, hx, hxs, hxsh⟩ := hsh Finset.univ (by simp) (fun _ => 1) (fun _ _ => zero_le_one)
    (by simp [pRet, m])
  refine ⟨R₀, hR₀, x, hx, hxs, ?_⟩
  have hsu : sharpe m d B Sf Finset.univ (fun _ => 1) = 1 := by
    simp [sharpe, pRet, pVar, Vmat, m, d, B]
  rw [hsu, mul_one] at hxsh
  exact hxsh

end Instance

end SparseSharpe.Factor
