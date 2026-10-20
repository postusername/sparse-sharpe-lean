import SparseSharpe.Factor.SaddleExistence
import SparseSharpe.Factor.ClippedTrading
import SparseSharpe.Factor.CapDuality
import SparseSharpe.Factor.NodeSharp

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Localization of the grid by the gap of the certificate (session 25, tasks 2.1–2.2 of TZ v0.25)

* `QLO_sub_ge_of_min` (L1) — `(τ − t₀)'Σ_f⁻¹(τ − t₀) ≤ Q_S(τ) − F_LO(S)`: the general defect identity
  `objLO_eq_defect_general` for the optimal weights `w(t₀)` at the point `τ` (no derivatives). With
  `QLO_sub_le_of_min` this is the two-sided bound `q ≤ Q_S(τ) − F ≤ ν_S q` (`node_estimates`, Theorem 4.2 of
  the paper).
* `quadf_sub_le_dualBound_sub` (L2) — for `|S| ≤ k` and every `t`: `‖G(t − t₀(S))‖² ≤ g_k(t) − F_LO(S)`.
* `localize` (L3) — if `F_LO(S) ≥ θ`, then `Gt₀(S)` lies in the ball of radius `√(g_k(t) − θ)` around `Gt`
  for every `t`; `certificate_of_lt` — if `g_k(t) < θ` and `(1 − 2ε)θ ≤ F_h`, the heuristic value `F_h` is
  already within the factor `1 − 2ε` of every long-only portfolio with at most `k` names.
* `locNodes` (Theorem L4, corrected by addendum 1 of the TZ) — no nodes if `g_k(t̂) ≤ θ`; otherwise, with
  `r = √(g_k(t̂) − θ)`, the nodes `z` of the grid of Definition 4.7 (`|z_l| ≤ Z`) with
  `|s z_l − (Gt̂)_l| ≤ r + s/2` for every `l` and `‖s z − Gt̂‖ ≤ r + s√K/2`. `card_locNodes_le`: at most
  `2Z+1` and at most `2r/s + 2` nodes per axis.
* `one_guess_of_rep` — Theorem 4.8 (one guess) for any table with the representative property of
  Lemma 4.5(b); `clip_one_guess_loc` — the node that Theorem 4.8 uses is a localized node.
* `trading_theorem_localized` — the end-to-end form from the data: the heuristic support and the tables at
  the localized nodes for the adaptive guesses; every best pair has the guarantee of Theorem 4.11.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-! ### Strong convexity of the dual function -/

/-- `(x − y)'P(x − y) = Σ_l (⟨G_l, x⟩ − ⟨G_l, y⟩)²`: the distance in the metric of `Σ_f⁻¹` is the Euclidean
distance of `Gx` and `Gy`. -/
lemma quadf_sub_eq_sum_sq (hG : ∀ j j', ∑ l, G l j * G l j' = P j j') (x y : κ → ℝ) :
    quadf P (x - y) = ∑ l, (dotp (G l) x - dotp (G l) y) ^ 2 := by
  rw [quadf_eq_sum_sq hG]
  exact Finset.sum_congr rfl fun l _ => by rw [dotp_sub']

lemma quadf_sub_comm (hG : ∀ j j', ∑ l, G l j * G l j' = P j j') (x y : κ → ℝ) :
    quadf P (x - y) = quadf P (y - x) := by
  rw [quadf_sub_eq_sum_sq hG, quadf_sub_eq_sum_sq hG]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- **Strong convexity of the dual function (L1).** If `t₀` minimizes `Q_S`, then for every `τ`
`(τ − t₀)'Σ_f⁻¹(τ − t₀) ≤ Q_S(τ) − Q_S(t₀)`. Proof: the general defect identity for the optimal weights
`w(t₀)` at the point `τ`, with `Σ_f B_S'w(t₀) = t₀` and `2(m_i − B_i'τ)w_i − d_iw_i² ≤ s_i(τ)`. -/
theorem QLO_sub_ge_of_min (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {S : Finset ι} {t₀ : κ → ℝ} (hmin : ∀ t, QLO m d B P S t₀ ≤ QLO m d B P S t) (τ : κ → ℝ) :
    quadf P (τ - t₀) ≤ QLO m d B P S τ - QLO m d B P S t₀ := by
  have htw : tw Sf B S (wclip m d B t₀) = t₀ := tw_wclip_eq (P := P) hd hG hPS hmin
  have hval : objLO m d B Sf S (wclip m d B t₀) = QLO m d B P S t₀ := by
    rw [objLO_wclip_deficit hd hG hPS S t₀, htw, sub_self]
    simp [quadf]
  have hgen := objLO_eq_defect_general (m := m) (d := d) (B := B) hG hPS S (wclip m d B t₀) τ
  rw [htw, hval] at hgen
  have hitems : ∑ i ∈ S, (2 * (m i - dotp (B i) τ) * wclip m d B t₀ i - d i * wclip m d B t₀ i ^ 2)
      ≤ ∑ i ∈ S, (max (m i - dotp (B i) τ) 0) ^ 2 / d i :=
    Finset.sum_le_sum fun i _ => quad_item_le (hd i) (wclip_nonneg hd t₀ i)
  have hsym := quadf_sub_comm hG t₀ τ
  have hQτ : QLO m d B P S τ = quadf P τ + ∑ i ∈ S, (max (m i - dotp (B i) τ) 0) ^ 2 / d i := rfl
  linarith

/-- **The estimates at a node, two-sided (Theorem 4.2 (a′), (a), (b), (c), (d) of the paper).** If `t₀`
minimizes `Q_S`, `F = Q_S(t₀)`, `q = (τ − t₀)'Σ_f⁻¹(τ − t₀)` and `ν_S = 1 + levSum(S)`, then
`q ≤ Q_S(τ) − F ≤ ν_S q`, the defect of `S` at `τ` is at most `ν_S (Q_S(τ) − F) ≤ ν_S² q`,
`obj(S, w(τ)) ≥ F − ν_S² q`, and the sharper `F − obj(S, w(τ)) ≤ (ν_S − 1)(Q_S(τ) − F) ≤ (ν_S − 1)ν_S q`. -/
theorem node_estimates (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {S : Finset ι} {t₀ : κ → ℝ} (hmin : ∀ t, QLO m d B P S t₀ ≤ QLO m d B P S t) (τ : κ → ℝ) :
    quadf P (τ - t₀) ≤ QLO m d B P S τ - QLO m d B P S t₀ ∧
    QLO m d B P S τ - QLO m d B P S t₀ ≤ (1 + levSum d B Sf S) * quadf P (τ - t₀) ∧
    quadf P (tw Sf B S (wclip m d B τ) - τ)
      ≤ (1 + levSum d B Sf S) * (QLO m d B P S τ - QLO m d B P S t₀) ∧
    (1 + levSum d B Sf S) * (QLO m d B P S τ - QLO m d B P S t₀)
      ≤ (1 + levSum d B Sf S) ^ 2 * quadf P (τ - t₀) ∧
    QLO m d B P S t₀ - (1 + levSum d B Sf S) ^ 2 * quadf P (τ - t₀)
      ≤ objLO m d B Sf S (wclip m d B τ) ∧
    QLO m d B P S t₀ - levSum d B Sf S * (QLO m d B P S τ - QLO m d B P S t₀)
      ≤ objLO m d B Sf S (wclip m d B τ) ∧
    levSum d B Sf S * (QLO m d B P S τ - QLO m d B P S t₀)
      ≤ levSum d B Sf S * (1 + levSum d B Sf S) * quadf P (τ - t₀) := by
  have hν : 0 ≤ 1 + levSum d B Sf S := by
    have := levSum_nonneg (B := B) hd hG hPS S
    linarith
  have hgap := QLO_sub_le_of_min (m := m) (B := B) (Sf := Sf) hd hG hPS hmin τ
  have hsharp := objLO_wclip_ge_of_node_sharp (m := m) (B := B) (Sf := Sf) hd hG hPS hmin τ
  refine ⟨QLO_sub_ge_of_min hd hG hPS hmin τ, hgap,
    defect_le (m := m) (B := B) (Sf := Sf) hd hG hPS S hmin τ, ?_,
    objLO_wclip_ge_of_node hd hG hPS hmin τ, hsharp.1, hsharp.2⟩
  have := mul_le_mul_of_nonneg_left hgap hν
  nlinarith [this]

/-! ### Localization by the gap of the certificate -/

/-- **L2.** For `|S| ≤ k`, a minimizer `t₀` of `Q_S` and every `t`:
`(t − t₀)'Σ_f⁻¹(t − t₀) ≤ g_k(t) − F_LO(S)`, `F_LO(S) = Q_S(t₀)`. -/
theorem quadf_sub_le_dualBound_sub (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} {S : Finset ι} (hS : S.card ≤ k) {t₀ : κ → ℝ}
    (hmin : ∀ t, QLO m d B P S t₀ ≤ QLO m d B P S t) (t : κ → ℝ) :
    quadf P (t - t₀) ≤ dualBound m d B P k t - QLO m d B P S t₀ := by
  have h1 := QLO_sub_ge_of_min (m := m) (d := d) (B := B) hd hG hPS hmin t
  have h2 := QLO_le_dualBound (m := m) (d := d) (B := B) (P := P) hS t
  linarith

/-- **L3 (localization).** If `|S| ≤ k` and `F_LO(S) = Q_S(t₀) ≥ θ`, then for every point `t`
`‖Gt₀ − Gt‖² ≤ g_k(t) − θ`: the point `Gt₀(S)` lies in the ball of radius `√(g_k(t) − θ)` around `Gt`. -/
theorem localize (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} {S : Finset ι} (hS : S.card ≤ k) {t₀ : κ → ℝ}
    (hmin : ∀ t, QLO m d B P S t₀ ≤ QLO m d B P S t) {θ : ℝ} (hθ : θ ≤ QLO m d B P S t₀)
    (t : κ → ℝ) :
    ∑ l, (dotp (G l) t₀ - dotp (G l) t) ^ 2 ≤ dualBound m d B P k t - θ := by
  have h := quadf_sub_le_dualBound_sub (m := m) (d := d) (B := B) hd hG hPS hS hmin t
  rw [quadf_sub_comm hG, quadf_sub_eq_sum_sq hG] at h
  linarith

/-- **The other branch of L3: the certificate.** If `g_k(t) < θ` and `(1 − 2ε)θ ≤ F_h` with `ε ≤ 1/2`, then
`(1 − 2ε)·obj(S, w) ≤ F_h` for every long-only portfolio with at most `k` names. -/
theorem certificate_of_lt (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} {ε θ Fh : ℝ} (hε : ε ≤ 1 / 2) {t : κ → ℝ} (hlt : dualBound m d B P k t ≤ θ)
    (hθ : (1 - 2 * ε) * θ ≤ Fh) {S : Finset ι} (hS : S.card ≤ k) {w : ι → ℝ}
    (hw : ∀ i ∈ S, 0 ≤ w i) :
    (1 - 2 * ε) * objLO m d B Sf S w ≤ Fh := by
  have h1 := objLO_le_dualBound (m := m) (B := B) (Sf := Sf) (P := P) (G := G) hd hG hPS hS hw t
  have hc : 0 ≤ 1 - 2 * ε := by linarith
  have h2 : (1 - 2 * ε) * objLO m d B Sf S w ≤ (1 - 2 * ε) * θ :=
    mul_le_mul_of_nonneg_left (by linarith) hc
  linarith

/-! ### The localized nodes -/

/-- **The localized nodes (Theorem L4).** None if `g_k(t̂) ≤ θ`. Otherwise, with `r = √(g_k(t̂) − θ)`, the
nodes `z` of the grid of Definition 4.7 (`|z_l| ≤ Z`) with `|s z_l − (Gt̂)_l| ≤ r + s/2` for every `l` and
`‖s z − Gt̂‖² ≤ (r + s√K/2)²`. -/
noncomputable def locNodes (m d : ι → ℝ) (B : ι → κ → ℝ) (P G : κ → κ → ℝ) (k : ℕ) (s : ℝ) (Z : ℕ)
    (that : κ → ℝ) (θ : ℝ) : Finset (κ → ℤ) :=
  if dualBound m d B P k that ≤ θ then ∅ else
    (Fintype.piFinset fun _ : κ => Finset.Icc (-(Z : ℤ)) Z).filter fun z =>
      (∀ l, |s * z l - dotp (G l) that| ≤ Real.sqrt (dualBound m d B P k that - θ) + s / 2) ∧
      ∑ l, (s * z l - dotp (G l) that) ^ 2
        ≤ (Real.sqrt (dualBound m d B P k that - θ) + s * Real.sqrt (Fintype.card κ) / 2) ^ 2

/-- **No nodes when the certificate passes.** -/
theorem locNodes_eq_empty {k : ℕ} {s : ℝ} {Z : ℕ} {that : κ → ℝ} {θ : ℝ}
    (h : dualBound m d B P k that ≤ θ) : locNodes m d B P G k s Z that θ = ∅ := by
  rw [locNodes, ite_eq_left h]

lemma mem_locNodes {k : ℕ} {s : ℝ} {Z : ℕ} {that : κ → ℝ} {θ : ℝ} {z : κ → ℤ} :
    z ∈ locNodes m d B P G k s Z that θ ↔
      θ < dualBound m d B P k that ∧ (∀ l, z l ∈ Finset.Icc (-(Z : ℤ)) Z) ∧
      (∀ l, |s * z l - dotp (G l) that| ≤ Real.sqrt (dualBound m d B P k that - θ) + s / 2) ∧
      ∑ l, (s * z l - dotp (G l) that) ^ 2
        ≤ (Real.sqrt (dualBound m d B P k that - θ) + s * Real.sqrt (Fintype.card κ) / 2) ^ 2 := by
  unfold locNodes
  by_cases h : dualBound m d B P k that ≤ θ
  · rw [ite_eq_left h]
    simp only [Finset.notMem_empty, false_iff, not_and]
    intro hlt; exact absurd h (not_le.mpr hlt)
  · rw [ite_eq_right h, Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hz, h1, h2⟩; exact ⟨not_le.mp h, hz, h1, h2⟩
    · rintro ⟨-, hz, h1, h2⟩; exact ⟨hz, h1, h2⟩

/-- The number of integers in `[⌈x⌉, ⌊y⌋]` is at most `y − x + 1` when `x ≤ y + 1`. -/
lemma card_Icc_ceil_floor_le {x y : ℝ} (h : x ≤ y + 1) :
    ((Finset.Icc ⌈x⌉ ⌊y⌋).card : ℝ) ≤ y - x + 1 := by
  rw [Int.card_Icc]
  rcases le_or_gt (⌊y⌋ + 1 - ⌈x⌉) 0 with h0 | h0
  · rw [Int.toNat_of_nonpos h0]; simp; linarith
  · have hc : (((⌊y⌋ + 1 - ⌈x⌉).toNat : ℕ) : ℝ) = (⌊y⌋ : ℝ) + 1 - ⌈x⌉ := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0.le]; push_cast; ring
    rw [hc]
    linarith [Int.floor_le y, Int.le_ceil x]

/-- **The number of localized nodes.** At most `(2Z+1)^K`, and at most `2r/s + 2` per axis,
`r = √(g_k(t̂) − θ)`. -/
theorem card_locNodes_le {k : ℕ} {s : ℝ} (hs : 0 < s) {Z : ℕ} {that : κ → ℝ} {θ : ℝ} :
    (locNodes m d B P G k s Z that θ).card ≤ (2 * Z + 1) ^ Fintype.card κ ∧
    ((locNodes m d B P G k s Z that θ).card : ℝ)
      ≤ (2 * Real.sqrt (dualBound m d B P k that - θ) / s + 2) ^ Fintype.card κ := by
  classical
  set r := Real.sqrt (dualBound m d B P k that - θ) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hbox : locNodes m d B P G k s Z that θ
      ⊆ Fintype.piFinset fun _ : κ => Finset.Icc (-(Z : ℤ)) Z := by
    intro z hz
    exact Fintype.mem_piFinset.mpr (mem_locNodes.mp hz).2.1
  set c : κ → ℝ := fun l => dotp (G l) that with hc
  have hcube : locNodes m d B P G k s Z that θ
      ⊆ Fintype.piFinset fun l : κ => Finset.Icc ⌈(c l - (r + s / 2)) / s⌉ ⌊(c l + (r + s / 2)) / s⌋ := by
    intro z hz
    have h1 := (mem_locNodes.mp hz).2.2.1
    refine Fintype.mem_piFinset.mpr fun l => ?_
    have hl := abs_le.mp (h1 l)
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.ceil_le, div_le_iff₀ hs]; simp only [hc]; linarith [hl.1]
    · rw [Int.le_floor, le_div_iff₀ hs]; simp only [hc]; linarith [hl.2]
  refine ⟨?_, ?_⟩
  · refine le_trans (Finset.card_le_card hbox) (le_of_eq ?_)
    rw [Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ]
    congr 1
    omega
  · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card hcube)) ?_
    rw [Fintype.card_piFinset, Nat.cast_prod]
    have hterm : ∀ l : κ, ((Finset.Icc ⌈(c l - (r + s / 2)) / s⌉ ⌊(c l + (r + s / 2)) / s⌋).card : ℝ)
        ≤ 2 * r / s + 2 := by
      intro l
      have hle : (c l - (r + s / 2)) / s ≤ (c l + (r + s / 2)) / s + 1 := by
        have : (c l - (r + s / 2)) / s ≤ (c l + (r + s / 2)) / s :=
          div_le_div_of_nonneg_right (by linarith) hs.le
        linarith
      refine le_trans (card_Icc_ceil_floor_le hle) (le_of_eq ?_)
      field_simp
      ring
    calc ∏ l : κ, ((Finset.Icc ⌈(c l - (r + s / 2)) / s⌉ ⌊(c l + (r + s / 2)) / s⌋).card : ℝ)
        ≤ ∏ _l : κ, (2 * r / s + 2) :=
          Finset.prod_le_prod₀ (fun l _ => Nat.cast_nonneg _) fun l _ => hterm l
      _ = (2 * r / s + 2) ^ Fintype.card κ := by simp

/-! ### One guess for any table with the representative property -/

/-- **The rounding step for a given representative** (the second half of `clip_node_step`): if `R` has the
key of `S` and at least its sum of scores, then `|R| = |S|` and
`obj(R, w(τ)) ≥ obj(S, w(τ)) − 2e√D_S − e²`, `e = √K·|S|·η`. -/
theorem clip_node_step_of_rep (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {η : ℝ} (hη : 0 < η) {S R : Finset ι} {τ : κ → ℝ}
    (hkey : ∑ i ∈ R, clipKeyItem m d B Sf G η τ i = ∑ i ∈ S, clipKeyItem m d B Sf G η τ i)
    (hval : ∑ i ∈ S, clipScore m d B τ i ≤ ∑ i ∈ R, clipScore m d B τ i) :
    R.card = S.card ∧
      objLO m d B Sf S (wclip m d B τ)
        - (2 * (Real.sqrt (Fintype.card κ) * (S.card * η))
              * Real.sqrt (quadf P (tw Sf B S (wclip m d B τ) - τ))
            + (Real.sqrt (Fintype.card κ) * (S.card * η)) ^ 2)
        ≤ objLO m d B Sf R (wclip m d B τ) := by
  have hcard := clip_key_card (m := m) (d := d) (B := B) (Sf := Sf) (G := G) hkey
  refine ⟨hcard, ?_⟩
  set w := wclip m d B τ with hw
  set Kc : ℝ := (Fintype.card κ : ℝ) with hKc
  set e : ℝ := Real.sqrt Kc * (S.card * η) with he
  have hKc0 : 0 ≤ Kc := Nat.cast_nonneg _
  have he0 : 0 ≤ e := mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hη.le)
  have hDR := defect_eq_sum_sq (B := B) (Sf := Sf) hG R w τ
  have hDS := defect_eq_sum_sq (B := B) (Sf := Sf) hG S w τ
  set vR : κ → ℝ := fun l => ∑ i ∈ R, vcoord G Sf B w i l with hvR
  set vS : κ → ℝ := fun l => ∑ i ∈ S, vcoord G Sf B w i l with hvS
  set gt : κ → ℝ := fun l => dotp (G l) τ with hgt
  have hsplit : ∀ l, vR l - gt l = (vS l - gt l) + (vR l - vS l) := fun l => by ring
  have hsum_b : ∑ l, (vR l - vS l) ^ 2 ≤ Kc * (S.card * η) ^ 2 := by
    calc ∑ l, (vR l - vS l) ^ 2 ≤ ∑ _l : κ, (S.card * η) ^ 2 := by
          refine Finset.sum_le_sum fun l _ => ?_
          have := clip_key_close (m := m) (d := d) (B := B) (Sf := Sf) (G := G) hη hkey l
          exact sq_le_sq' (by linarith [(abs_le.mp this).1]) (by linarith [(abs_le.mp this).2])
      _ = Kc * (S.card * η) ^ 2 := by simp [hKc]
  have hsqrt_b : Real.sqrt (∑ l, (vR l - vS l) ^ 2) ≤ e := by
    calc Real.sqrt (∑ l, (vR l - vS l) ^ 2) ≤ Real.sqrt (Kc * (S.card * η) ^ 2) :=
          Real.sqrt_le_sqrt hsum_b
      _ = e := by
          rw [Real.sqrt_mul hKc0, Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg _) hη.le)]
  have hDS0 : 0 ≤ quadf P (tw Sf B S w - τ) := defect_nonneg hG S w τ
  set DS := quadf P (tw Sf B S w - τ) with hDSdef
  have hDSsq : ∑ l, (vS l - gt l) ^ 2 = DS := hDS.symm
  have hDR_le : quadf P (tw Sf B R w - τ) ≤ (Real.sqrt DS + e) ^ 2 := by
    rw [hDR]
    have h1 := sum_sq_add_le Finset.univ (fun l => vS l - gt l) (fun l => vR l - vS l)
    have h2 : ∑ l, (vR l - gt l) ^ 2 = ∑ l, ((vS l - gt l) + (vR l - vS l)) ^ 2 :=
      Finset.sum_congr rfl fun l _ => by rw [hsplit l]
    rw [h2]
    refine le_trans h1 ?_
    rw [hDSsq]
    have : Real.sqrt DS + Real.sqrt (∑ l, (vR l - vS l) ^ 2) ≤ Real.sqrt DS + e := by linarith
    exact pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) this 2
  have hQR : objLO m d B Sf R w = quadf P τ + ∑ i ∈ R, clipScore m d B τ i
      - quadf P (tw Sf B R w - τ) := by
    rw [hw, objLO_wclip_deficit hd hG hPS R τ, QLO]; rfl
  have hQS : objLO m d B Sf S w = quadf P τ + ∑ i ∈ S, clipScore m d B τ i - DS := by
    rw [hw, objLO_wclip_deficit hd hG hPS S τ, QLO]; rfl
  have hDSeq : DS = Real.sqrt DS ^ 2 := (Real.sq_sqrt hDS0).symm
  rw [hQR, hQS]
  nlinarith [hval, hDR_le, hDSeq, Real.sqrt_nonneg DS]

/-- The representative property of the plain table (`knap_spec`): if the keys of all subsets of `S` lie in the
box, the table at `τ` contains `R` with the key of `S` and at least its sum of scores. -/
theorem clipTable_rep {η : ℝ} {Q k : ℕ} {S : Finset ι} (hSk : S.card ≤ k) {τ : κ → ℝ}
    (hbox : ∀ U ⊆ S, ∀ l, |∑ i ∈ U, ⌊vcoord G Sf B (wclip m d B τ) i l / η⌋| ≤ (Q : ℤ))
    {L : List ι} (hnd : L.Nodup) (hL : ∀ i, i ∈ L) :
    ∃ R ∈ clipTable m d B Sf G η Q k L τ,
      ∑ i ∈ R, clipKeyItem m d B Sf G η τ i = ∑ i ∈ S, clipKeyItem m d B Sf G η τ i ∧
      ∑ i ∈ S, clipScore m d B τ i ≤ ∑ i ∈ R, clipScore m d B τ i := by
  classical
  have hbox' : ∀ U' ⊆ S, ∑ j ∈ U', clipKeyItem m d B Sf G η τ j ∈ clipBox κ Q k := by
    intro U' hU'
    rw [clipBox, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun l => ?_, ?_⟩
    · rw [Finset.mem_Icc, ← abs_le, sum_clipKeyItem_fst]
      exact hbox U' hU' l
    · rw [sum_clipKeyItem_snd]
      have := Finset.card_le_card hU'
      omega
  have hSL : S ⊆ L.toFinset := fun i _ => List.mem_toFinset.mpr (hL i)
  exact knap_spec (fun i => clipScore m d B τ i) (clipKeyItem m d B Sf G η τ) (clipBox κ Q k) L hnd
    S hSL hbox'

/-- **One guess for any table with the representative property (Theorem 4.8 of the paper, abstract form).**
Let `S`, `t₀`, `V` be as in `clip_one_guess`, and let `tab τ` be a family of sets such that, whenever the keys
of all subsets of `S` at `τ` lie in the box, `tab τ` contains a set with the key of `S` and at least its sum
of scores. Then the node `z` obtained by rounding `Gt₀/s` coordinatewise lies in the grid `|z_l| ≤ Z`, is at
most `s/2` from `Gt₀` in every coordinate, and `tab` at this node contains `R`, `|R| ≤ k`, with a portfolio
`w ≥ 0` of objective at least `(1 − 2ε)·F_LO(S)`. -/
theorem one_guess_of_rep [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {ω : ℝ} (hω : 0 ≤ ω) (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    {S : Finset ι} (hSk : S.card ≤ k) {t₀ : κ → ℝ}
    (hmin : ∀ t, QLO m d B P S t₀ ≤ QLO m d B P S t)
    {V : ℝ} (hV : 0 < V) (hVF : V ≤ QLO m d B P S t₀) (hFV : QLO m d B P S t₀ ≤ 2 * V)
    (tab : (κ → ℝ) → Finset (Finset ι))
    (hrep : ∀ τ : κ → ℝ, (∀ U ⊆ S, ∀ l,
        |∑ i ∈ U, ⌊vcoord G Sf B (wclip m d B τ) i l / clipEta ε V k (Fintype.card κ)⌋|
          ≤ (clipQ ε ω k (Fintype.card κ) : ℤ)) →
      ∃ R ∈ tab τ, ∑ i ∈ R, clipKeyItem m d B Sf G (clipEta ε V k (Fintype.card κ)) τ i
          = ∑ i ∈ S, clipKeyItem m d B Sf G (clipEta ε V k (Fintype.card κ)) τ i ∧
        ∑ i ∈ S, clipScore m d B τ i ≤ ∑ i ∈ R, clipScore m d B τ i) :
    ∃ z : κ → ℤ,
      (∀ l, z l ∈ Finset.Icc (-(clipZ ε ω k (Fintype.card κ) : ℤ)) (clipZ ε ω k (Fintype.card κ))) ∧
      (∀ l, |clipStep ε V ω k (Fintype.card κ) * z l - dotp (G l) t₀|
          ≤ clipStep ε V ω k (Fintype.card κ) / 2) ∧
      ∃ R ∈ tab (nodeOf G (clipStep ε V ω k (Fintype.card κ)) z), R.card ≤ k ∧
        ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (1 - 2 * ε) * QLO m d B P S t₀ ≤ objLO m d B Sf R w := by
  classical
  set Kn := Fintype.card κ with hKn
  have hKpos : 0 < (Kn : ℝ) := by exact_mod_cast Fintype.card_pos
  set sK := Real.sqrt (Kn : ℝ) with hsK
  have hsKpos : 0 < sK := Real.sqrt_pos.mpr hKpos
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set ν : ℝ := 1 + k * ω with hν
  have hν1 : 1 ≤ ν := by nlinarith [mul_nonneg hkpos.le hω]
  have hνpos : 0 < ν := by linarith
  set F := QLO m d B P S t₀ with hF
  set s := clipStep ε V ω k Kn with hs
  have hspos : 0 < s :=
    div_pos (Real.sqrt_pos.mpr (by positivity)) (mul_pos hνpos hsKpos)
  set η := clipEta ε V k Kn with hηdef
  have hηpos : 0 < η :=
    div_pos (Real.sqrt_pos.mpr (by positivity)) (mul_pos hkpos hsKpos)
  have hs2 : s ^ 2 = 2 * ε * V / (ν ^ 2 * Kn) := by
    rw [hs, clipStep, div_pow, Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt hKpos.le]
  have hη2 : η ^ 2 = (ε * V / 2) / ((k : ℝ) ^ 2 * Kn) := by
    rw [hηdef, clipEta, div_pow, Real.sq_sqrt (by positivity), mul_pow,
      Real.sq_sqrt hKpos.le]
  -- the node: coordinatewise rounding of `Gt₀/s`
  have hdet := det_G_ne_zero hG hPS
  obtain ⟨z, hz1, hz2⟩ := exists_grid_point s hspos (fun l => dotp (G l) t₀)
  set τ := nodeOf G s z with hτ
  have hq : quadf P (τ - t₀) ≤ (Kn : ℝ) * (s / 2) ^ 2 := by
    rw [quadf_eq_sum_sq hG]
    calc ∑ l, dotp (G l) (τ - t₀) ^ 2
        ≤ ∑ _l : κ, (s / 2) ^ 2 := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [dotp_sub', hτ, dotp_G_nodeOf hdet]
          exact sq_le_sq' (by linarith [(abs_le.mp (hz1 l)).1]) (by linarith [(abs_le.mp (hz1 l)).2])
      _ = (Kn : ℝ) * (s / 2) ^ 2 := by simp [hKn]
  set q := quadf P (τ - t₀) with hqdef
  have hq0 : 0 ≤ q := quadf_nonneg_of_root hG _
  have hq' : ν ^ 2 * q ≤ ε * V / 2 := by
    have h1 : ν ^ 2 * ((Kn : ℝ) * (s / 2) ^ 2) = ε * V / 2 := by
      rw [div_pow, hs2]; field_simp
    have h2 : ν ^ 2 * q ≤ ν ^ 2 * ((Kn : ℝ) * (s / 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hq (sq_nonneg ν)
    linarith
  -- the leverage of the support
  have hlev : levSum d B Sf S ≤ k * ω := by
    calc levSum d B Sf S = ∑ i ∈ S, sysVar B Sf i / d i := rfl
      _ ≤ ∑ i ∈ S, ω := Finset.sum_le_sum fun i _ => hsys i
      _ = S.card * ω := by simp
      _ ≤ k * ω := mul_le_mul_of_nonneg_right (by exact_mod_cast hSk) hω
  have hlev0 := levSum_nonneg (B := B) hd hG hPS S
  set νS := 1 + levSum d B Sf S with hνS
  have hνSle : νS ≤ ν := by linarith
  -- estimates at the node
  have hgap := QLO_sub_le_of_min (m := m) (B := B) (Sf := Sf) hd hG hPS hmin τ
  have hdef := defect_le (m := m) (B := B) (Sf := Sf) hd hG hPS S hmin τ
  have hQτ : F ≤ QLO m d B P S τ := hmin τ
  have ha : QLO m d B P S τ - F ≤ ν * q :=
    le_trans hgap (mul_le_mul_of_nonneg_right hνSle hq0)
  have hD : quadf P (tw Sf B S (wclip m d B τ) - τ) ≤ ε * V / 2 :=
    arith_defect hν1 hνSle (by linarith) hq0 (sub_nonneg.mpr hQτ) hdef ha hq'
  set DS := quadf P (tw Sf B S (wclip m d B τ) - τ) with hDSdef
  have hDS0 : 0 ≤ DS := defect_nonneg hG S _ τ
  -- the box
  have hscore : ∑ i ∈ S, clipScore m d B τ i ≤ 9 * V / 4 := by
    have h0 : 0 ≤ quadf P τ := quadf_nonneg_of_root hG _
    have hQLO : QLO m d B P S τ = quadf P τ + ∑ i ∈ S, clipScore m d B τ i := rfl
    exact arith_score hν1 hq0 ha hq' hε2 hV hFV (by linarith) (by linarith)
  set Q := clipQ ε ω k Kn with hQdef
  have hXle : Real.sqrt (5 * ω * (k : ℝ) ^ 3 * Kn / ε) ≤ (Q : ℝ) - k := by
    rw [hQdef, clipQ]; push_cast; simp only [add_sub_cancel_left]
    exact Nat.le_ceil _
  have hQk : (k : ℝ) ≤ Q := by
    have := Real.sqrt_nonneg (5 * ω * (k : ℝ) ^ 3 * Kn / ε); linarith
  have hQ2 : ω * k * (9 * V / 4) ≤ (((Q : ℝ) - k) * η) ^ 2 := by
    have hX0 := Real.sqrt_nonneg (5 * ω * (k : ℝ) ^ 3 * Kn / ε)
    have hXsq : Real.sqrt (5 * ω * (k : ℝ) ^ 3 * Kn / ε) ^ 2 = 5 * ω * (k : ℝ) ^ 3 * Kn / ε :=
      Real.sq_sqrt (by positivity)
    have h1 : (5 / 2) * ω * k * V
        = Real.sqrt (5 * ω * (k : ℝ) ^ 3 * Kn / ε) ^ 2 * η ^ 2 := by
      rw [hXsq, hη2]; field_simp
    have h2 : Real.sqrt (5 * ω * (k : ℝ) ^ 3 * Kn / ε) * η ≤ ((Q : ℝ) - k) * η :=
      mul_le_mul_of_nonneg_right hXle hηpos.le
    have h3 : (Real.sqrt (5 * ω * (k : ℝ) ^ 3 * Kn / ε) * η) ^ 2 ≤ (((Q : ℝ) - k) * η) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hX0 hηpos.le) h2 2
    have h4 : ω * k * V ≥ 0 := by positivity
    have h5 : (Real.sqrt (5 * ω * (k : ℝ) ^ 3 * Kn / ε) * η) ^ 2 = (5 / 2) * ω * k * V := by
      rw [mul_pow]; exact h1.symm
    linarith [h3, h5, h4]
  have hbox := clip_box_bound (m := m) hd hG hPS hηpos hSk hω (fun i _ => hsys i) hscore hQk hQ2
  obtain ⟨R, hR, hkey, hval⟩ := hrep τ hbox
  obtain ⟨hRcard, hRobj⟩ := clip_node_step_of_rep (P := P) hd hG hPS hηpos hkey hval
  -- the sum
  have he : Real.sqrt (Kn : ℝ) * (S.card * η) ≤ Real.sqrt (ε * V / 2) := by
    have h1 : Real.sqrt (Kn : ℝ) * (k * η) = Real.sqrt (ε * V / 2) := by
      rw [hηdef, clipEta, ← hsK]; field_simp
    calc Real.sqrt (Kn : ℝ) * (S.card * η) ≤ Real.sqrt (Kn : ℝ) * (k * η) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by exact_mod_cast hSk)
            hηpos.le) (Real.sqrt_nonneg _)
      _ = _ := h1
  set e := Real.sqrt (Kn : ℝ) * (S.card * η) with hedef
  have he0 : 0 ≤ e := mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hηpos.le)
  have hobjS : F - DS ≤ objLO m d B Sf S (wclip m d B τ) := by
    rw [objLO_wclip_deficit hd hG hPS S τ]; linarith
  have hfinal : (1 - 2 * ε) * F ≤ objLO m d B Sf R (wclip m d B τ) :=
    arith_final hε hV hVF he0 hDS0 hD he hobjS hRobj
  -- the node lies in the grid
  have hzbox : ∀ l, z l ∈ Finset.Icc (-(clipZ ε ω k Kn : ℤ)) (clipZ ε ω k Kn) := by
    intro l
    rw [Finset.mem_Icc, ← abs_le]
    have hG0 : dotp (G l) t₀ ^ 2 ≤ 2 * V := by
      have h1 : dotp (G l) t₀ ^ 2 ≤ quadf P t₀ := by
        rw [quadf_eq_sum_sq hG]
        exact Finset.single_le_sum (f := fun l => dotp (G l) t₀ ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ l)
      have h2 : quadf P t₀ ≤ F := by
        have : F = quadf P t₀ + ∑ i ∈ S, max (m i - dotp (B i) t₀) 0 ^ 2 / d i := rfl
        have : 0 ≤ ∑ i ∈ S, max (m i - dotp (B i) t₀) 0 ^ 2 / d i :=
          Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hd i).le
        linarith
      linarith
    have hGabs : |dotp (G l) t₀| ≤ Real.sqrt (2 * V) := Real.abs_le_sqrt hG0
    have hzl := hz2 l
    have hdivle : |dotp (G l) t₀| / s ≤ Real.sqrt (2 * V) / s :=
      div_le_div_of_nonneg_right hGabs hspos.le
    have hkey : Real.sqrt (2 * V) / s = ν * Real.sqrt ((Kn : ℝ) / ε) := by
      rw [hs, clipStep, Real.sqrt_div hKpos.le, ← hsK]
      have h2 : Real.sqrt (2 * ε * V) = Real.sqrt (2 * V) * Real.sqrt ε := by
        rw [show 2 * ε * V = 2 * V * ε by ring, Real.sqrt_mul (by positivity)]
      rw [h2]
      have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
      have hs2V : 0 < Real.sqrt (2 * V) := Real.sqrt_pos.mpr (by positivity)
      field_simp
      rfl
    have hceil : ν * Real.sqrt ((Kn : ℝ) / ε) + 1 / 2 ≤ (clipZ ε ω k Kn : ℝ) := by
      rw [clipZ]; exact Nat.le_ceil _
    have hreal : |(z l : ℝ)| ≤ (clipZ ε ω k Kn : ℝ) := by
      rw [hkey] at hdivle; linarith
    exact_mod_cast hreal
  refine ⟨z, hzbox, hz1, R, hR, by omega, wclip m d B τ, fun i => wclip_nonneg hd τ i, hfinal⟩

/-! ### The localized family -/

/-- The localized family at one guess `V`: the tables of Algorithm 4.1 at the localized nodes. -/
noncomputable def locFamily (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf P G : κ → κ → ℝ) (ε ω V : ℝ) (k : ℕ)
    (L : List ι) (that : κ → ℝ) (θ : ℝ) : Finset (Finset ι) :=
  (locNodes m d B P G k (clipStep ε V ω k (Fintype.card κ)) (clipZ ε ω k (Fintype.card κ)) that θ).biUnion
    fun z => clipTable m d B Sf G (clipEta ε V k (Fintype.card κ)) (clipQ ε ω k (Fintype.card κ)) k L
      (nodeOf G (clipStep ε V ω k (Fintype.card κ)) z)

/-- **The node of Theorem 4.8 is a localized node.** If `|S| ≤ k`, `t₀` minimizes `Q_S` and
`θ < F_LO(S) = Q_S(t₀)`, then the rounding `z` of `Gt₀/s` satisfies the conditions of `locNodes` at every
point `t̂`. -/
theorem node_mem_locNodes (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} {S : Finset ι} (hSk : S.card ≤ k) {t₀ : κ → ℝ}
    (hmin : ∀ t, QLO m d B P S t₀ ≤ QLO m d B P S t) {θ : ℝ} (hθ : θ < QLO m d B P S t₀)
    (that : κ → ℝ) {s : ℝ} (hs : 0 < s) {Z : ℕ} {z : κ → ℤ}
    (hzZ : ∀ l, z l ∈ Finset.Icc (-(Z : ℤ)) Z) (hz : ∀ l, |s * z l - dotp (G l) t₀| ≤ s / 2) :
    z ∈ locNodes m d B P G k s Z that θ := by
  have hloc := localize (m := m) (d := d) (B := B) (Sf := Sf) hd hG hPS hSk hmin hθ.le that
  have hgθ : θ < dualBound m d B P k that :=
    lt_of_lt_of_le hθ (le_trans (hmin that) (QLO_le_dualBound hSk that))
  set r := Real.sqrt (dualBound m d B P k that - θ) with hr
  have hr2 : r ^ 2 = dualBound m d B P k that - θ := Real.sq_sqrt (by linarith)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  -- every coordinate of `Gt₀ − Gt̂` is at most `r`
  have hcoord : ∀ l, |dotp (G l) t₀ - dotp (G l) that| ≤ r := by
    intro l
    apply Real.abs_le_sqrt
    exact le_trans (Finset.single_le_sum (f := fun l => (dotp (G l) t₀ - dotp (G l) that) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ l)) hloc
  refine mem_locNodes.mpr ⟨hgθ, hzZ, fun l => ?_, ?_⟩
  · have h1 := hz l
    have h2 := hcoord l
    calc |s * z l - dotp (G l) that|
        = |(s * z l - dotp (G l) t₀) + (dotp (G l) t₀ - dotp (G l) that)| := by ring_nf
      _ ≤ |s * z l - dotp (G l) t₀| + |dotp (G l) t₀ - dotp (G l) that| := abs_add_le _ _
      _ ≤ s / 2 + r := add_le_add h1 h2
      _ = r + s / 2 := by ring
  · -- the ball: triangle inequality in `ℝ^K`
    have hA : ∑ l, (s * z l - dotp (G l) t₀) ^ 2 ≤ (s * Real.sqrt (Fintype.card κ) / 2) ^ 2 := by
      calc ∑ l, (s * z l - dotp (G l) t₀) ^ 2 ≤ ∑ _l : κ, (s / 2) ^ 2 :=
            Finset.sum_le_sum fun l _ =>
              sq_le_sq' (by linarith [(abs_le.mp (hz l)).1]) (by linarith [(abs_le.mp (hz l)).2])
        _ = (Fintype.card κ : ℝ) * (s / 2) ^ 2 := by simp
        _ = (s * Real.sqrt (Fintype.card κ) / 2) ^ 2 := by
            rw [show (s * Real.sqrt (Fintype.card κ) / 2) ^ 2
                = s ^ 2 * Real.sqrt (Fintype.card κ) ^ 2 / 4 by ring,
              Real.sq_sqrt (Nat.cast_nonneg _)]; ring
    have h1 := sum_sq_add_le Finset.univ (fun l => s * z l - dotp (G l) t₀)
      (fun l => dotp (G l) t₀ - dotp (G l) that)
    have hsK0 : 0 ≤ s * Real.sqrt (Fintype.card κ) / 2 := by positivity
    have hsA : Real.sqrt (∑ l, (s * z l - dotp (G l) t₀) ^ 2) ≤ s * Real.sqrt (Fintype.card κ) / 2 :=
      calc Real.sqrt (∑ l, (s * z l - dotp (G l) t₀) ^ 2)
          ≤ Real.sqrt ((s * Real.sqrt (Fintype.card κ) / 2) ^ 2) := Real.sqrt_le_sqrt hA
        _ = s * Real.sqrt (Fintype.card κ) / 2 := Real.sqrt_sq hsK0
    have hsB : Real.sqrt (∑ l, (dotp (G l) t₀ - dotp (G l) that) ^ 2) ≤ r := Real.sqrt_le_sqrt hloc
    have h2 : ∑ l, (s * z l - dotp (G l) that) ^ 2
        = ∑ l, ((s * z l - dotp (G l) t₀) + (dotp (G l) t₀ - dotp (G l) that)) ^ 2 :=
      Finset.sum_congr rfl fun l _ => by ring_nf
    rw [h2]
    refine le_trans h1 ?_
    have h3 : Real.sqrt (∑ l, (s * z l - dotp (G l) t₀) ^ 2)
        + Real.sqrt (∑ l, (dotp (G l) t₀ - dotp (G l) that) ^ 2)
        ≤ r + s * Real.sqrt (Fintype.card κ) / 2 := by linarith
    exact pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) h3 2

/-- **L4 for one guess.** Under the hypotheses of Theorem 4.8 (`clip_one_guess`) and `θ < F_LO(S)`, the
localized family at the guess `V` and the point `t̂` contains `R`, `|R| ≤ k`, with a portfolio `w ≥ 0` of
objective at least `(1 − 2ε)·F_LO(S)`. -/
theorem clip_one_guess_loc [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {ω : ℝ} (hω : 0 ≤ ω) (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    {S : Finset ι} (hSk : S.card ≤ k) {t₀ : κ → ℝ}
    (hmin : ∀ t, QLO m d B P S t₀ ≤ QLO m d B P S t)
    {V : ℝ} (hV : 0 < V) (hVF : V ≤ QLO m d B P S t₀) (hFV : QLO m d B P S t₀ ≤ 2 * V)
    {θ : ℝ} (hθ : θ < QLO m d B P S t₀) (that : κ → ℝ)
    {L : List ι} (hnd : L.Nodup) (hL : ∀ i, i ∈ L) :
    ∃ R ∈ locFamily m d B Sf P G ε ω V k L that θ, R.card ≤ k ∧
      ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (1 - 2 * ε) * QLO m d B P S t₀ ≤ objLO m d B Sf R w := by
  obtain ⟨z, hzZ, hz, R, hR, hRk, w, hw, hobj⟩ := one_guess_of_rep (m := m) (B := B) (Sf := Sf)
    (P := P) (G := G) hd hG hPS hk hε hε2 hω hsys hSk hmin hV hVF hFV
    (fun τ => clipTable m d B Sf G (clipEta ε V k (Fintype.card κ)) (clipQ ε ω k (Fintype.card κ)) k L τ)
    (fun τ hbox => clipTable_rep hSk hbox hnd hL)
  have hspos : 0 < clipStep ε V ω k (Fintype.card κ) := by
    have hKpos : 0 < (Fintype.card κ : ℝ) := by exact_mod_cast Fintype.card_pos
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    exact div_pos (Real.sqrt_pos.mpr (by positivity))
      (mul_pos (by nlinarith [mul_nonneg hkpos.le hω]) (Real.sqrt_pos.mpr hKpos))
  have hzloc := node_mem_locNodes (m := m) (d := d) (B := B) (Sf := Sf) hd hG hPS hSk hmin hθ that
    hspos hzZ hz
  refine ⟨R, ?_, hRk, w, hw, hobj⟩
  rw [locFamily, Finset.mem_biUnion]
  exact ⟨z, hzloc, hR⟩

end SparseSharpe.Factor

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-! ### The localized family over the adaptive guesses, from the data -/

/-- The localized candidates for the guesses `L·2^j`, `j ≤ J`. -/
noncomputable def locCandidates (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf P G : κ → κ → ℝ) (ε ω L : ℝ)
    (J k : ℕ) (La : List ι) (that : κ → ℝ) (θ : ℝ) : Finset (Finset ι) :=
  (Finset.range (J + 1)).biUnion fun j => locFamily m d B Sf P G ε ω (L * 2 ^ j) k La that θ

/-- The localized family is a part of the family of Definition 4.7. -/
theorem locFamily_subset (ε ω V : ℝ) (k : ℕ) (La : List ι) (that : κ → ℝ) (θ : ℝ) :
    locFamily m d B Sf P G ε ω V k La that θ ⊆ clipFamily m d B Sf G ε ω V k La := by
  intro R hR
  rw [locFamily, Finset.mem_biUnion] at hR
  obtain ⟨z, hz, hRz⟩ := hR
  rw [clipFamily, Finset.mem_biUnion]
  exact ⟨z, Fintype.mem_piFinset.mpr (mem_locNodes.mp hz).2.1, hRz⟩

theorem locCandidates_subset (ε ω L : ℝ) (J k : ℕ) (La : List ι) (that : κ → ℝ) (θ : ℝ) :
    locCandidates m d B Sf P G ε ω L J k La that θ ⊆ clipCandidates m d B Sf G ε ω L J k La := by
  intro R hR
  rw [locCandidates, Finset.mem_biUnion] at hR
  obtain ⟨j, hj, hRj⟩ := hR
  rw [clipCandidates, Finset.mem_biUnion]
  exact ⟨j, hj, locFamily_subset ε ω _ k La that θ hRj⟩

/-- **No candidates when the certificate passes:** if `g_k(t̂) ≤ θ`, the localized family is empty. -/
theorem locCandidates_eq_empty {ε ω L : ℝ} {J k : ℕ} {La : List ι} {that : κ → ℝ} {θ : ℝ}
    (h : dualBound m d B P k that ≤ θ) : locCandidates m d B Sf P G ε ω L J k La that θ = ∅ := by
  rw [locCandidates]
  ext R
  simp only [Finset.mem_biUnion, Finset.notMem_empty, iff_false, not_exists, not_and]
  intro j _ hR
  rw [locFamily, locNodes_eq_empty h, Finset.biUnion_empty] at hR
  exact Finset.notMem_empty _ hR

/-- The size of the localized family at one guess: the number of localized nodes times the bound
`(2Q+1)^K(k+1)+1` of one table. -/
theorem card_locFamily_le (ε ω V : ℝ) (k : ℕ) (La : List ι) (that : κ → ℝ) (θ : ℝ) :
    (locFamily m d B Sf P G ε ω V k La that θ).card
      ≤ (locNodes m d B P G k (clipStep ε V ω k (Fintype.card κ)) (clipZ ε ω k (Fintype.card κ))
          that θ).card
        * ((2 * clipQ ε ω k (Fintype.card κ) + 1) ^ Fintype.card κ * (k + 1) + 1) := by
  refine le_trans Finset.card_biUnion_le ?_
  rw [← smul_eq_mul]
  exact Finset.sum_le_card_nsmul _ _ _ fun z _ => card_clipTable_le _ _ _ _ _ _ _ _ _ _

/-- **The localized scheme, from the data (Theorem L4).** Let `(S_h, w_h)` be any long-only portfolio with at
most `k` names (the heuristic), `0 < L ≤ obj(S_h, w_h)`, `θ` a threshold with `(1 − 2ε)θ ≤ obj(S_h, w_h)`
(for instance `θ = F_h/(1 − 2ε)`), `t̂` any point with `g_k(t̂) ≤ 2^{J+1}L`. The family consists of `S_h`
and the tables at the localized nodes of the guesses `L·2^j`, `j ≤ J`; it is a part of the family of
Theorem 4.11 together with `S_h`, and it is `{S_h}` if `g_k(t̂) ≤ θ`. For every order of the assets, every
best pair `(R*, w*)` of this family has at most `k` names, objective at least `1 − 2ε` times that of every
long-only portfolio with at most `k` names, and the fully invested `x* = w*/Σw*` has a Sharpe ratio at least
`√(1 − 2ε)` times that of every such portfolio with positive expected excess return. -/
theorem trading_theorem_localized [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    {Sh : Finset ι} (hSh : Sh.card ≤ k) {wh : ι → ℝ} (hwh : ∀ i ∈ Sh, 0 ≤ wh i)
    {L : ℝ} (hL0 : 0 < L) (hLh : L ≤ objLO m d B Sf Sh wh)
    {θ : ℝ} (hθ : (1 - 2 * ε) * θ ≤ objLO m d B Sf Sh wh)
    {that : κ → ℝ} {J : ℕ} (hJ : dualBound m d B P k that ≤ 2 ^ (J + 1) * L)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    {R₀ : Finset ι} (hR₀ : R₀ ∈ insert Sh (locCandidates m d B Sf P G ε ω L J k La that θ))
    {w₀ : ι → ℝ} (hw₀ : ∀ i ∈ R₀, 0 ≤ w₀ i)
    (hbest : ∀ R ∈ insert Sh (locCandidates m d B Sf P G ε ω L J k La that θ), ∀ w : ι → ℝ,
      (∀ i ∈ R, 0 ≤ w i) → objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀) :
    R₀.card ≤ k
    ∧ (∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        (1 - 2 * ε) * objLO m d B Sf S' u ≤ objLO m d B Sf R₀ w₀)
    ∧ (∀ i ∈ R₀, 0 ≤ (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i)
    ∧ ∑ i ∈ R₀, (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i = 1
    ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        0 < pRet m S' u →
        Real.sqrt (1 - 2 * ε) * sharpe m d B Sf S' u
          ≤ sharpe m d B Sf R₀ (fun i => (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i) := by
  obtain ⟨S, hkS, Fopt, hFopt, hSopt⟩ := exists_optimal_support (m := m) (d := d) (B := B)
    (Sf := Sf) (P := P) (G := G) hd hG hPS k
  have hc : (0 : ℝ) ≤ 1 - 2 * ε := by linarith
  have hhbest := hbest Sh (Finset.mem_insert_self _ _) wh hwh
  have hgood : (1 - 2 * ε) * Fopt ≤ objLO m d B Sf R₀ w₀ := by
    by_cases hcase : Fopt ≤ θ
    · calc (1 - 2 * ε) * Fopt ≤ (1 - 2 * ε) * θ := mul_le_mul_of_nonneg_left hcase hc
        _ ≤ objLO m d B Sf Sh wh := hθ
        _ ≤ objLO m d B Sf R₀ w₀ := hhbest
    · have hθF : θ < Fopt := lt_of_not_ge hcase
      obtain ⟨hLF, hFJ⟩ := opt_mem_bracket hd hG hPS hkS hFopt hSopt hSh hwh hLh hJ
      obtain ⟨j, hjJ, hVF, hFV⟩ := exists_doubling_guess_succ J hL0 hLF hFJ
      obtain ⟨z, hzmin, hzmax⟩ := isGreatest_objLO_isLeast_QLO (m := m) (B := B) (Sf := Sf)
        (P := P) (G := G) hd hG hPS S
      have hz : z = Fopt := hzmax.unique hFopt
      obtain ⟨t₀, ht₀⟩ := hzmin.1
      have hmin : ∀ t, QLO m d B P S t₀ ≤ QLO m d B P S t := by
        intro t; rw [← ht₀]; exact hzmin.2 ⟨t, rfl⟩
      have hF : QLO m d B P S t₀ = Fopt := by rw [← ht₀, hz]
      have hV : 0 < L * 2 ^ j := by positivity
      obtain ⟨R, hR, -, w, hw, hobj⟩ := clip_one_guess_loc (m := m) (B := B) (Sf := Sf) (P := P)
        (G := G) hd hG hPS hk1 hε hε1.le hω hsys hkS hmin hV (by rw [hF]; exact hVF)
        (by rw [hF]; exact hFV) (by rw [hF]; exact hθF) that hnd hall
      have hRmem : R ∈ insert Sh (locCandidates m d B Sf P G ε ω L J k La that θ) := by
        refine Finset.mem_insert_of_mem ?_
        rw [locCandidates, Finset.mem_biUnion]
        exact ⟨j, Finset.mem_range.mpr (by omega), hR⟩
      rw [← hF]
      exact le_trans hobj (hbest R hRmem w (fun i _ => hw i))
  have hLF : L ≤ Fopt := le_trans hLh (hSopt Sh hSh wh hwh)
  obtain ⟨hx0, hx1, hxs⟩ := best_pair_sharpe_uniform (B := B) hd hG hPS hε1
    (lt_of_lt_of_le hL0 hLF) hSopt hw₀ hgood
  have hcard : R₀.card ≤ k := by
    rcases Finset.mem_insert.mp hR₀ with h | h
    · rw [h]; exact hSh
    · exact card_le_of_mem_clipCandidates (locCandidates_subset ε ω L J k La that θ h)
  refine ⟨hcard, fun S' hS' u hu => ?_, hx0, hx1, hxs⟩
  have hub := hSopt S' hS' u hu
  linarith [mul_le_mul_of_nonneg_left hub hc]

end SparseSharpe.Factor
