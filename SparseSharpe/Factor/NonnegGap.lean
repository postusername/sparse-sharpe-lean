import SparseSharpe.Factor.SaddleExistence

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The gap of the relaxation for nonnegative loadings, `K` factors (session 25, task 2.4 of TZ v0.25)

* `dualBound_le_opt_nonneg_K` (Theorem 5.9 for `K` factors) — if `B_il ≥ 0` for all `i, l` and `Fopt` bounds the
  objective of every long-only portfolio with at most `k` names, then at the single point `t⋆ = √Fopt·σ`,
  `σ_l = √((Σ_f)_ll)`, `g_k(t⋆) ≤ (1 + c)·Fopt` with `c = σ'Σ_f⁻¹σ`. The sign of the dual points is not needed:
  `t_S ≤ t⋆` coordinatewise by Cauchy–Schwarz, and `B ≥ 0` makes every score nonincreasing in every coordinate.
* `quadf_sigma_diag` — for a diagonal `Σ_f`, `c = K`; `dualBound_le_opt_nonneg_diag`: the factor is `K + 1`.
* `nonneg_gap_example`, `nonneg_gap_example_value`, `nonneg_gap_example_attained` — the factor `K + 1` is attained in the limit: `k = 1`, `M = K + 1`, `Σ_f = I`, `d = 1`,
  `B_l = b·e_l`, `m_l = a` for the first `K` assets and `B = 0`, `m = 1` for the last one, with
  `a = (n² + 1)/(2n)`, `b = (n² − 1)/(2n)` (so `a² = 1 + b²`); then `OPT_LO(1) ≤ 1` and
  `g_1(t) ≥ 1 + K((n − 1)/(n + 1))²` for every `t` if `2nK ≤ (n + 1)²`; the ratio tends to `K + 1`.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- `t_l² ≤ (Σ_f)_ll · t'Σ_f⁻¹t` (Cauchy–Schwarz in the metric of `Σ_f⁻¹`) and `(Σ_f)_ll ≥ 0`. -/
lemma coord_sq_le_Sf (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (t : κ → ℝ) (l : κ) :
    0 ≤ Sf l l ∧ t l ^ 2 ≤ Sf l l * quadf P t := by
  have hsys : sysVar (fun l' : κ => basisVec l') Sf l = Sf l l := by
    simp [sysVar, basisVec]
  have h0 := sysVar_nonneg (B := fun l' : κ => basisVec l') hG hPS l
  have h1 := sq_dotp_le_sysVar (B := fun l' : κ => basisVec l') hG hPS l t
  have hdot : dotp (basisVec l) t = t l := by
    simp [dotp, basisVec]
  rw [hsys] at h0 h1
  rw [hdot] at h1
  exact ⟨h0, h1⟩

/-- **Theorem 5.9 for `K` factors.** If all loadings are nonnegative and `Fopt` bounds the objective of every
long-only portfolio with at most `k` names, then `g_k(√Fopt·σ) ≤ (1 + σ'Σ_f⁻¹σ)·Fopt`, `σ_l = √((Σ_f)_ll)`. -/
theorem dualBound_le_opt_nonneg_K [Nonempty κ] (hd : ∀ i, 0 < d i) (hB : ∀ i l, 0 ≤ B i l)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {k : ℕ} {Fopt : ℝ}
    (hopt : ∀ S : Finset ι, S.card ≤ k → ∀ w : ι → ℝ, (∀ i ∈ S, 0 ≤ w i) →
        objLO m d B Sf S w ≤ Fopt) :
    dualBound m d B P k (fun l => Real.sqrt Fopt * Real.sqrt (Sf l l))
      ≤ (1 + quadf P (fun l => Real.sqrt (Sf l l))) * Fopt := by
  classical
  have hF0 : 0 ≤ Fopt := by
    have := hopt ∅ (by simp) (fun _ => 0) (by simp)
    simpa [objLO] using this
  set σ : κ → ℝ := fun l => Real.sqrt (Sf l l) with hσ
  set ts : κ → ℝ := fun l => Real.sqrt Fopt * Real.sqrt (Sf l l) with hts
  have htsσ : ts = Real.sqrt Fopt • σ := by funext l; simp [hts, hσ]
  have hq : quadf P ts = Fopt * quadf P σ := by
    rw [htsσ, quadf_smul, Real.sq_sqrt hF0]
  unfold dualBound
  rw [hq]
  have hsup : ((Finset.univ : Finset (Finset ι)).filter fun S => S.card ≤ k).sup'
      (supportsLe_nonempty k)
      (fun S => ∑ i ∈ S, (max (m i - dotp (B i) ts) 0) ^ 2 / d i) ≤ Fopt := by
    refine Finset.sup'_le _ _ fun S hS => ?_
    have hSk : S.card ≤ k := (Finset.mem_filter.mp hS).2
    obtain ⟨z, ⟨⟨t₀, hz⟩, hleast⟩, ⟨⟨wS, hwS, hwz⟩, -⟩⟩ :=
      isGreatest_objLO_isLeast_QLO (m := m) (B := B) (Sf := Sf) (G := G) hd hG hPS S
    have hFS : QLO m d B P S t₀ ≤ Fopt := by
      rw [← hz, hwz]; exact hopt S hSk wS hwS
    have hscore0 : 0 ≤ ∑ i ∈ S, (max (m i - dotp (B i) t₀) 0) ^ 2 / d i :=
      Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hd i).le
    have hqt : quadf P t₀ ≤ Fopt := by
      have : QLO m d B P S t₀ = quadf P t₀ + ∑ i ∈ S, (max (m i - dotp (B i) t₀) 0) ^ 2 / d i := rfl
      linarith
    -- `t₀ ≤ t⋆` coordinatewise
    have hle : ∀ l, t₀ l ≤ ts l := by
      intro l
      obtain ⟨hS0, hcs⟩ := coord_sq_le_Sf hG hPS t₀ l
      have h1 : t₀ l ^ 2 ≤ Sf l l * Fopt := le_trans hcs (mul_le_mul_of_nonneg_left hqt hS0)
      have h2 : |t₀ l| ≤ Real.sqrt (Sf l l * Fopt) := Real.abs_le_sqrt h1
      have h3 : Real.sqrt (Sf l l * Fopt) = ts l := by
        simp only [hts]; rw [Real.sqrt_mul hS0, mul_comm]
      linarith [le_abs_self (t₀ l)]
    -- the scores at `t⋆` are at most those at `t₀`
    have hterm : ∀ i ∈ S, (max (m i - dotp (B i) ts) 0) ^ 2 / d i
        ≤ (max (m i - dotp (B i) t₀) 0) ^ 2 / d i := by
      intro i _
      have hdot : dotp (B i) t₀ ≤ dotp (B i) ts :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hle l) (hB i l)
      have hmx : max (m i - dotp (B i) ts) 0 ≤ max (m i - dotp (B i) t₀) 0 :=
        max_le_max (by linarith) le_rfl
      have hnn : 0 ≤ max (m i - dotp (B i) ts) 0 := le_max_right _ _
      gcongr
      exact (hd i).le
    have hsum := Finset.sum_le_sum hterm
    have hq0 : 0 ≤ quadf P t₀ := quadf_nonneg_of_root hG t₀
    have : QLO m d B P S t₀ = quadf P t₀ + ∑ i ∈ S, (max (m i - dotp (B i) t₀) 0) ^ 2 / d i := rfl
    linarith
  nlinarith [hsup]

/-- For a diagonal `Σ_f` (with `P Σ_f = I`) the constant `c = σ'Σ_f⁻¹σ` equals `K`. -/
lemma quadf_sigma_diag (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hdiag : ∀ j j', j ≠ j' → Sf j j' = 0) :
    quadf P (fun l => Real.sqrt (Sf l l)) = Fintype.card κ := by
  -- `P_jj' · Σ_f,j'j' = δ_jj'`
  have hP : ∀ j j', P j j' * Sf j' j' = if j = j' then 1 else 0 := by
    intro j j'
    rw [← hPS j j', Finset.sum_eq_single j']
    · intro b _ hb; rw [hdiag b j' hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j') h
  have hpos : ∀ j, 0 < Sf j j := by
    intro j
    have h1 := hP j j
    simp only [ite_true] at h1
    have h0 := (coord_sq_le_Sf hG hPS (fun _ => 0) j).1
    rcases h0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at h1; exact absurd h1 zero_ne_one
  simp only [quadf]
  have hrow : ∀ j, ∑ j', P j j' * (Real.sqrt (Sf j j) * Real.sqrt (Sf j' j')) = 1 := by
    intro j
    rw [Finset.sum_eq_single j]
    · rw [← sq, Real.sq_sqrt (hpos j).le]
      have := hP j j; simp only [ite_true] at this; exact this
    · intro b _ hb
      have h1 := hP j b
      rw [ite_eq_right (Ne.symm hb)] at h1
      have hPjb : P j b = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact h
        · exact absurd h (hpos b).ne'
      rw [hPjb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [Finset.sum_congr rfl fun j _ => hrow j]
  simp

/-- **Corollary: a diagonal `Σ_f` and nonnegative loadings give the factor `K + 1`.** -/
theorem dualBound_le_opt_nonneg_diag [Nonempty κ] (hd : ∀ i, 0 < d i) (hB : ∀ i l, 0 ≤ B i l)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hdiag : ∀ j j', j ≠ j' → Sf j j' = 0) {k : ℕ} {Fopt : ℝ}
    (hopt : ∀ S : Finset ι, S.card ≤ k → ∀ w : ι → ℝ, (∀ i ∈ S, 0 ≤ w i) →
        objLO m d B Sf S w ≤ Fopt) :
    dualBound m d B P k (fun l => Real.sqrt Fopt * Real.sqrt (Sf l l))
      ≤ (1 + Fintype.card κ) * Fopt := by
  have h := dualBound_le_opt_nonneg_K (m := m) hd hB hG hPS hopt
  rwa [quadf_sigma_diag hG hPS hdiag] at h

/-! ### The factor `K + 1` is attained in the limit -/

section Example

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The returns of the example: `a = (n²+1)/(2n)` for the assets `some l`, `1` for the asset `none`. -/
noncomputable def exM (n : ℝ) : Option κ → ℝ
  | some _ => (n ^ 2 + 1) / (2 * n)
  | none => 1

/-- The loadings of the example: `b = (n²−1)/(2n)` on the own factor of `some l`, none for `none`. -/
noncomputable def exB (n : ℝ) : Option κ → κ → ℝ
  | some l => fun j => if j = l then (n ^ 2 - 1) / (2 * n) else 0
  | none => fun _ => 0

/-- The one-dimensional bound: if `a − b x₁ = 1`, `0 ≤ x₁`, `K x₁ ≤ b`, then
`K x² + max(1, (a − b x)_+²) ≥ 1 + K x₁²` for every `x`. -/
lemma one_dim_bound {K a b x₁ x : ℝ} (hK : 0 ≤ K) (hx₁ : 0 ≤ x₁) (h1 : a - b * x₁ = 1)
    (hcond : K * x₁ ≤ b) :
    1 + K * x₁ ^ 2 ≤ K * x ^ 2 + max 1 (max (a - b * x) 0 ^ 2) := by
  rcases le_or_gt x₁ x with hx | hx
  · have : K * x₁ ^ 2 ≤ K * x ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx₁ hx 2) hK
    linarith [le_max_left (1 : ℝ) (max (a - b * x) 0 ^ 2)]
  · set h := x₁ - x with hh
    have hh0 : 0 < h := by rw [hh]; linarith
    have hb0 : 0 ≤ b := le_trans (mul_nonneg hK hx₁) hcond
    have hax : a - b * x = 1 + b * h := by rw [hh]; linarith
    have hpos : 0 ≤ a - b * x := by rw [hax]; nlinarith
    rw [max_eq_left hpos]
    have hm : (a - b * x) ^ 2 ≤ max 1 ((a - b * x) ^ 2) := le_max_right _ _
    have hxx : x = x₁ - h := by rw [hh]; ring
    have key : 1 + K * x₁ ^ 2 ≤ K * x ^ 2 + (a - b * x) ^ 2 := by
      rw [hax, hxx]
      nlinarith [mul_nonneg hh0.le (sub_nonneg.mpr hcond), sq_nonneg h, mul_nonneg hK (sq_nonneg h),
        sq_nonneg (b * h)]
    linarith

/-- **The example.** With `n > 1` and `2nK ≤ (n+1)²` (`K = |κ|`): every long-only portfolio with at most one
name has objective at most `1`, while `g_1(t) ≥ 1 + K((n−1)/(n+1))²` at every point. All loadings are
nonnegative and `Σ_f = I`, so Theorem 5.9 for `K` factors gives `g_1 ≤ K + 1` at its point; the ratio
`1 + K((n−1)/(n+1))²` tends to `K + 1` as `n → ∞`. -/
theorem nonneg_gap_example [Nonempty κ] {n : ℝ} (hn : 1 < n)
    (hK : 2 * n * Fintype.card κ ≤ (n + 1) ^ 2) :
    (∀ i l, 0 ≤ exB (κ := κ) n i l) ∧
    (∀ S : Finset (Option κ), S.card ≤ 1 → ∀ w : Option κ → ℝ, (∀ i ∈ S, 0 ≤ w i) →
        objLO (exM n) (fun _ => 1) (exB n) (idMat κ) S w ≤ 1) ∧
    ∀ t : κ → ℝ, 1 + Fintype.card κ * ((n - 1) / (n + 1)) ^ 2
        ≤ dualBound (exM n) (fun _ => 1) (exB n) (idMat κ) 1 t := by
  classical
  have hn0 : 0 < n := by linarith
  set a : ℝ := (n ^ 2 + 1) / (2 * n) with ha
  set b : ℝ := (n ^ 2 - 1) / (2 * n) with hb
  have hb0 : 0 ≤ b := by rw [hb]; apply div_nonneg <;> nlinarith
  have hab : a ^ 2 = 1 + b ^ 2 := by rw [ha, hb]; field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · intro i l
    cases i with
    | none => simp [exB]
    | some l' =>
        simp only [exB]
        split_ifs
        · exact hb0
        · exact le_rfl
  · intro S hS w hw
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hS with h0 | h1
    · rw [Finset.card_eq_zero.mp h0]; simp [objLO]
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
      have hV : Vmat (fun _ => (1 : ℝ)) (exB (κ := κ) n) (idMat κ) i i = exM n i ^ 2 := by
        cases i with
        | none => simp [Vmat, exB, exM, idMat]
        | some l =>
            simp only [Vmat, exB, exM, idMat, ite_true]
            have : ∑ j : κ, ∑ j' : κ, (if j = l then b else 0) * ((if j = j' then (1 : ℝ) else 0)
                * (if j' = l then b else 0)) = b ^ 2 := by
              simp [Finset.sum_ite_eq', sq]
            rw [← hb, this, ← ha, hab]
      simp only [objLO, Finset.sum_singleton]
      rw [hV]
      nlinarith [sq_nonneg (exM n i * w i - 1)]
  · intro t
    set K : ℝ := (Fintype.card κ : ℝ) with hKdef
    have hKpos : 0 < K := by rw [hKdef]; exact_mod_cast Fintype.card_pos
    set x₁ : ℝ := (n - 1) / (n + 1) with hx₁
    have hx₁0 : 0 ≤ x₁ := by rw [hx₁]; apply div_nonneg <;> linarith
    have h1 : a - b * x₁ = 1 := by
      rw [ha, hb, hx₁]; field_simp; ring
    have hcond : K * x₁ ≤ b := by
      rw [hx₁, hb]
      have hn1 : 0 < n + 1 := by linarith
      have h2n : 0 < 2 * n := by linarith
      rw [mul_div_assoc', div_le_div_iff₀ hn1 h2n]
      nlinarith [hK, mul_le_mul_of_nonneg_left hK (by linarith : (0 : ℝ) ≤ n - 1)]
    -- the mean of the coordinates and a coordinate below it
    set xbar : ℝ := (∑ l, t l) / K with hxbar
    obtain ⟨l₀, -, hl₀⟩ := Finset.exists_min_image Finset.univ t Finset.univ_nonempty
    have hl₀x : t l₀ ≤ xbar := by
      rw [hxbar, le_div_iff₀ hKpos]
      have : ∑ _l : κ, t l₀ ≤ ∑ l, t l := Finset.sum_le_sum fun l _ => hl₀ l (Finset.mem_univ l)
      simpa [hKdef, mul_comm] using this
    have hsq : K * xbar ^ 2 ≤ ∑ l, t l ^ 2 := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) t
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
      rw [hxbar, div_pow]
      try rw [← hKdef] at hcs
      have : K * ((∑ l, t l) ^ 2 / K ^ 2) = (∑ l, t l) ^ 2 / K := by field_simp
      rw [this, div_le_iff₀ hKpos]
      linarith
    have hq : quadf (idMat κ) t = ∑ l, t l ^ 2 := quadf_idMat t
    -- two lower bounds of the maximum over supports with one name
    have hnone : (1 : ℝ) ≤ ((Finset.univ : Finset (Finset (Option κ))).filter fun S => S.card ≤ 1).sup'
        (supportsLe_nonempty 1)
        (fun S => ∑ i ∈ S, (max (exM n i - dotp (exB n i) t) 0) ^ 2 / 1) := by
      have hmem : ({none} : Finset (Option κ))
          ∈ ((Finset.univ : Finset (Finset (Option κ))).filter fun S => S.card ≤ 1) := by simp
      have := Finset.le_sup' (fun S : Finset (Option κ) =>
          ∑ i ∈ S, (max (exM n i - dotp (exB n i) t) 0) ^ 2 / 1) hmem
      simp only [Finset.sum_singleton] at this
      have hval : (max (exM (κ := κ) n none - dotp (exB n none) t) 0) ^ 2 / 1 = 1 := by
        simp [exM, exB, dotp]
      linarith
    have hsome : (max (a - b * xbar) 0) ^ 2
        ≤ ((Finset.univ : Finset (Finset (Option κ))).filter fun S => S.card ≤ 1).sup'
        (supportsLe_nonempty 1)
        (fun S => ∑ i ∈ S, (max (exM n i - dotp (exB n i) t) 0) ^ 2 / 1) := by
      have hmem : ({some l₀} : Finset (Option κ))
          ∈ ((Finset.univ : Finset (Finset (Option κ))).filter fun S => S.card ≤ 1) := by simp
      have := Finset.le_sup' (fun S : Finset (Option κ) =>
          ∑ i ∈ S, (max (exM n i - dotp (exB n i) t) 0) ^ 2 / 1) hmem
      simp only [Finset.sum_singleton] at this
      rw [div_one] at this
      have hdot : dotp (exB n (some l₀)) t = b * t l₀ := by
        simp only [dotp, exB]
        rw [Finset.sum_eq_single l₀]
        · simp [hb]
        · intro j _ hj; simp [hj]
        · intro h; exact absurd (Finset.mem_univ l₀) h
      have hm : exM (κ := κ) n (some l₀) = a := by simp [exM, ha]
      rw [hdot, hm] at this
      have hmono : max (a - b * xbar) 0 ≤ max (a - b * t l₀) 0 :=
        max_le_max (by nlinarith [mul_le_mul_of_nonneg_left hl₀x hb0]) le_rfl
      have hnn : 0 ≤ max (a - b * xbar) 0 := le_max_right _ _
      have : (max (a - b * xbar) 0) ^ 2 ≤ (max (a - b * t l₀) 0) ^ 2 :=
        pow_le_pow_left₀ hnn hmono 2
      linarith
    have hone := one_dim_bound (x := xbar) hKpos.le hx₁0 h1 hcond
    unfold dualBound
    rw [hq]
    have hmax : max 1 (max (a - b * xbar) 0 ^ 2)
        ≤ ((Finset.univ : Finset (Finset (Option κ))).filter fun S => S.card ≤ 1).sup'
        (supportsLe_nonempty 1)
        (fun S => ∑ i ∈ S, (max (exM n i - dotp (exB n i) t) 0) ^ 2 / 1) := max_le hnone hsome
    linarith

/-- **The value of the example is exact:** at the point `t = x₁·𝟙`, `x₁ = (n−1)/(n+1)`, all scores are at most
`1`, so `g_1(t) ≤ 1 + K x₁²`; with `nonneg_gap_example`, `G*_1 = 1 + K((n−1)/(n+1))²`. -/
theorem nonneg_gap_example_value [Nonempty κ] {n : ℝ} (hn : 1 < n) :
    dualBound (exM n) (fun _ => 1) (exB n) (idMat κ) 1 (fun _ => (n - 1) / (n + 1))
      ≤ 1 + Fintype.card κ * ((n - 1) / (n + 1)) ^ 2 := by
  classical
  have hn0 : 0 < n := by linarith
  set x₁ : ℝ := (n - 1) / (n + 1) with hx₁
  have h1 : (n ^ 2 + 1) / (2 * n) - (n ^ 2 - 1) / (2 * n) * x₁ = 1 := by
    rw [hx₁]; field_simp; ring
  unfold dualBound
  rw [quadf_idMat]
  have hq : ∑ _l : κ, x₁ ^ 2 = Fintype.card κ * x₁ ^ 2 := by simp
  rw [hq]
  have hsup : ((Finset.univ : Finset (Finset (Option κ))).filter fun S => S.card ≤ 1).sup'
      (supportsLe_nonempty 1)
      (fun S => ∑ i ∈ S, (max (exM n i - dotp (exB n i) (fun _ => x₁)) 0) ^ 2 / 1) ≤ 1 := by
    refine Finset.sup'_le _ _ fun S hS => ?_
    have hSk : S.card ≤ 1 := (Finset.mem_filter.mp hS).2
    have hterm : ∀ i : Option κ, (max (exM n i - dotp (exB n i) (fun _ => x₁)) 0) ^ 2 / 1 ≤ 1 := by
      intro i
      cases i with
      | none => simp [exM, exB, dotp]
      | some l =>
          have hdot : dotp (exB (κ := κ) n (some l)) (fun _ => x₁) = (n ^ 2 - 1) / (2 * n) * x₁ := by
            simp only [dotp, exB]
            rw [Finset.sum_eq_single l]
            · simp
            · intro j _ hj; simp [hj]
            · intro h; exact absurd (Finset.mem_univ l) h
          simp only [exM]
          rw [hdot, h1]
          norm_num
    have h0 : ∀ i : Option κ, 0 ≤ (max (exM n i - dotp (exB n i) (fun _ => x₁)) 0) ^ 2 / 1 :=
      fun i => div_nonneg (sq_nonneg _) zero_le_one
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hSk with hc | hc
    · rw [Finset.card_eq_zero.mp hc]; simp
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
      rw [Finset.sum_singleton]
      exact hterm i
  linarith

/-- **The optimum of the example is attained:** the last asset alone, with weight `1`, has objective `2·1 − 1 = 1`; with
`nonneg_gap_example`, `OPT_LO(1) = 1`. -/
theorem nonneg_gap_example_attained (n : ℝ) :
    objLO (exM (κ := κ) n) (fun _ => 1) (exB n) (idMat κ) {none} (fun _ => 1) = 1 := by
  simp [objLO, Vmat, exM, exB]
  norm_num

end Example

end SparseSharpe.Factor
