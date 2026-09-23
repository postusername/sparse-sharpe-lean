import SparseSharpe.Factor.Trading

set_option linter.style.header false

/-!
# Every processing order, and the trading form of the anchor-basis variant

`main_theorem` and `main_theorem_anchor` (`Factor/Main.lean`) run the dynamic program on
the list `Finset.univ.toList` of all assets, whose order is not specified. An
implementation processes the assets in an order of its own, and the table of a dynamic
program with pruning depends on the order. This file removes the discrepancy.

* `main_theorem_list`, `main_theorem_anchor_list`: the two main theorems for **every**
  duplicate-free list `La` that contains all assets (the proofs are those of
  `Factor/Main.lean`; only the facts `La.Nodup`, `A₀ ⊆ La` and `La.length = M` are used).
* `candidatesAnchor`: the candidate family of the anchor-basis variant for a given
  processing order — the union over the guesses `L·2^j`, `j ≤ J`, and the grid nodes of
  the tables of the dynamic program in the coordinates of the anchor rows; its size is
  bounded by `(J+1)·(2Z+1)^K·(tableBoundAnchor+1)` (`card_candidatesAnchor_le`).
* `best_pair_sharpe_of_family`: the trading argument for an **arbitrary** finite family
  of supports with at most `k` assets that contains a support carrying a portfolio within
  `1 − 2ε` of the optimum: every best pair of the family, normalized to a fully invested
  portfolio, has Sharpe ratio at least `√(1 − 2ε)` times that of every long-only portfolio
  with at most `k` names.
* `best_pair_sharpe_anchor`: the trading form of the anchor-basis variant, for every
  processing order; `trading_instance_anchor`: all hypotheses on a concrete instance.
-/

namespace SparseSharpe.Factor

open Finset

set_option linter.unusedSectionVars false

section Orders

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

omit [DecidableEq ι] in
/-- A duplicate-free list that contains every asset has length `M`. -/
lemma length_of_nodup_complete {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La) :
    La.length = Fintype.card ι := by
  classical
  have h1 : La.toFinset = Finset.univ := by
    ext i; simp [hall i]
  rw [← List.toFinset_card_of_nodup hnd, h1, Finset.card_univ]

/-- **Main Theorem for every processing order** (enumeration of `K`-tuples). As
`main_theorem`, with the assets processed in the order of any duplicate-free list `La`
of all assets. -/
theorem main_theorem_list [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    {S : Finset ι} (hkS : S.card ≤ k) {Fopt V : ℝ}
    (hFopt : IsGreatest {v : ℝ | ∃ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i)
        ∧ v = objLO m d B Sf S u} Fopt)
    (hV : 0 < V) (hVF : V ≤ Fopt) (hFV : Fopt ≤ 2 * V) :
    (∃ T : κ → (ι ⊕ κ), (rowMat (rowsK d B G) T).det ≠ 0 ∧ ∃ z : κ → ℤ,
      z ∈ nodeBox (κ := κ) ⌈4 * (Fintype.card κ : ℝ)
        * Real.sqrt (((k + Fintype.card κ : ℕ) : ℝ) * ((k : ℝ) * (1 + (k : ℝ) * ω)) / ε)
          + 1 / 2⌉₊ ∧
      ∀ t : κ → ℝ, (∀ l, dotp (rowsK d B G (T l)) t = targetsK m d (T l)
          + 2 * Real.sqrt ((ε / (32 * ((k : ℝ) * (1 + (k : ℝ) * ω)))) * V
            / ((Fintype.card κ : ℝ) * (((k + Fintype.card κ : ℕ) : ℝ)
              * (Fintype.card κ : ℝ)))) * (z l : ℝ)) →
        ∃ adm : (ι ⊕ κ) → Bool,
          adm = (fun x => decide (-theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
            ≤ targetsK m d x - dotp (rowsK d B G x) t)) ∧
          ∃ R ∈ survivorsBox (fun W => phi (rowsK d B G) (targetsK m d) W t)
              (keyOf (rowsK d B G) (targetsK m d) T t
                (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
                  / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
                (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ))))
              adm
              (boxOf κ 1 V (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
                  / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
                (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ)))
                (k + Fintype.card κ) (Fintype.card ι))
              (anchorRows ι κ) (La.map Sum.inl),
            (assetsOf (κ := κ) R).card ≤ S.card
            ∧ ∃ w : ι → ℝ, (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i)
              ∧ ∀ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i) →
                  (1 - 2 * ε) * objLO m d B Sf S u
                    ≤ objLO m d B Sf (assetsOf (κ := κ) R) w)
    ∧ ∀ (T : κ → (ι ⊕ κ)) (t : κ → ℝ) (adm : (ι ⊕ κ) → Bool),
      (survivorsBox (fun W => phi (rowsK d B G) (targetsK m d) W t)
          (keyOf (rowsK d B G) (targetsK m d) T t
            (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
              / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
            (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ))))
          adm
          (boxOf κ 1 V (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
              / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
            (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ)))
            (k + Fintype.card κ) (Fintype.card ι))
          (anchorRows ι κ) (La.map Sum.inl)).card
      ≤ (2 * ⌈1 * (48 * (Fintype.card ι : ℝ) * Real.sqrt (Fintype.card κ : ℝ)
            * Real.sqrt (((k + Fintype.card κ : ℕ) : ℝ) * ((k : ℝ) * (1 + (k : ℝ) * ω)) / ε))
            + (Fintype.card ι : ℝ)⌉ + 1).toNat ^ Fintype.card κ
        * ((2 * ⌈8 * ((k + Fintype.card κ : ℕ) : ℝ) * (Fintype.card ι : ℝ)
            * (Fintype.card κ : ℝ) * 1 ^ 2 + (Fintype.card ι : ℝ)⌉ + 1).toNat
            ^ (Fintype.card κ * Fintype.card κ) * (k + Fintype.card κ + 1)) + 1 := by
  classical
  set c : ℝ := (k : ℝ) * (1 + (k : ℝ) * ω) with hcdef
  set N : ℕ := k + Fintype.card κ with hNdef
  set Mn : ℕ := Fintype.card ι with hMdef
  have hK0 : 0 < Fintype.card κ := Fintype.card_pos
  have hKc : (0:ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast hK0
  have hM0 : 0 < Mn := Fintype.card_pos
  have hN0 : 0 < N := by omega
  have hc1 : (1:ℝ) ≤ c := by
    have hk : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    rw [hcdef]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (k:ℝ)) hω]
  have hcpos : (0:ℝ) < c := by linarith
  refine ⟨?_, ?_⟩
  swap
  · intro T t adm
    have := card_boxOf_le (κ := κ) (ε := ε) (c := c) (V := V) (ρ := 1) (N := N) (Mn := Mn)
      hε hcpos hV hN0 hM0 hK0 zero_le_one rfl rfl
    exact le_trans (survivorsBox_card_le _ _ _ _ _ _) (by omega)
  -- носитель оптимума, нормальная точка, `K`-ка
  obtain ⟨A₀, hA₀S, th, hcardA, hnormA, hselfA, hoptA⟩ :=
    exists_optimal_selfconsistent (m := m) (B := B) (Sf := Sf) hd hG hPS S
  have hFeq : Fopt = phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) th :=
    hFopt.unique hoptA
  obtain ⟨T, hmax⟩ := exists_maxvol_barK (d := d) (B := B) (G := G) (S := A₀)
  have hdet := maxvol_det_ne_zero (P := P) (Sf := Sf) hmax hG hPS
  have hAN : (barK (κ := κ) A₀).card ≤ N := by
    rw [card_barK, hNdef]; have := le_trans hcardA hkS; omega
  have hC : ((barK (κ := κ) A₀).card * Fintype.card κ : ℝ) ≤ (N : ℝ) * (Fintype.card κ : ℝ) := by
    have : ((barK (κ := κ) A₀).card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hAN
    exact mul_le_mul_of_nonneg_right this hKc.le
  have hCpos : (0:ℝ) < (N : ℝ) * (Fintype.card κ : ℝ) := by
    have : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN0
    positivity
  have hLalen : La.length = Mn := length_of_nodup_complete hnd hall
  have hM0r : (0:ℝ) < (Mn : ℝ) := by exact_mod_cast hM0
  have hsK : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr hKc
  have hθpos : 0 < theta0B ε V c := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨z, hz1, hz2⟩ := lo_fptas_portfolio_box (m := m) (P := P) hd hG hPS
    (cand := Finset.univ) (A₀ := A₀) (La := La) (T := T) (thA := th)
    (η := theta0B ε V c / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Mn : ℝ)))
    (ξ := 1 / (8 * (Mn : ℝ) * (Fintype.card κ : ℝ))) (ε := ε) (V := V)
    (C := (N : ℝ) * (Fintype.card κ : ℝ)) (c := c) (ρ := 1) (k := k)
    (s := 2 * Real.sqrt ((ε / (32 * c)) * V / ((Fintype.card κ : ℝ)
      * ((N : ℝ) * (Fintype.card κ : ℝ)))))
    hmax.1 hdet (clamp_of_maxvol hmax hdet hC) zero_le_one
    (fun x hx l => abs_cf_le_one hmax hdet hx l) hnormA hCpos hε hε1 hc1 hV
    (by rw [← hFeq]; exact hVF) (by rw [← hFeq]; exact hFV) hKc rfl hselfA
    (by positivity) (by positivity) hnd
    (fun i _ => List.mem_toFinset.mpr (hall i)) (fun i _ => Finset.mem_univ i)
    (anchorCover_of_sysVar (m := m) hd hG hPS hω (fun i _ => hsys i))
    (le_trans hcardA hkS) (Finset.subset_univ _)
    (by rw [hLalen]; field_simp; linarith)
    (by rw [hLalen]; field_simp; norm_num)
  refine ⟨T, hdet, z, mem_nodeBox_of_grid_block hε hcpos hN0 hK0 hCpos le_rfl hz1, fun t ht => ?_⟩
  obtain ⟨adm, hadmEq, _hadm1, _hadm2, R, hR, hcard, w, hw, hval⟩ := hz2 t ht
  rw [hLalen] at hR
  refine ⟨adm, hadmEq, R, hR, ?_, w, hw, fun u hu => ?_⟩
  · rw [hcard]; exact Finset.card_le_card hA₀S
  · have hub : objLO m d B Sf S u ≤ Fopt := hFopt.2 ⟨u, hu, rfl⟩
    have hcoef : (0:ℝ) ≤ 1 - 2 * ε := by linarith
    have := mul_le_mul_of_nonneg_left hub hcoef
    rw [hFeq] at this
    linarith

/-- **Anchor-basis Main Theorem for every processing order.** As `main_theorem_anchor`,
with the assets processed in the order of any duplicate-free list `La` of all assets. -/
theorem main_theorem_anchor_list [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    {S : Finset ι} (hkS : S.card ≤ k) {Fopt V : ℝ}
    (hFopt : IsGreatest {v : ℝ | ∃ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i)
        ∧ v = objLO m d B Sf S u} Fopt)
    (hV : 0 < V) (hVF : V ≤ Fopt) (hFV : Fopt ≤ 2 * V) :
    (∃ z : κ → ℤ,
      z ∈ nodeBox (κ := κ) ⌈Real.sqrt ((Fintype.card κ : ℝ)
          * ((Fintype.card κ : ℝ) + (k : ℝ) * ω)
          / (2 * (ε / (32 * ((k : ℝ) * (1 + (k : ℝ) * ω)))))) + 1 / 2⌉₊ ∧
      ∀ t : κ → ℝ, (∀ l, dotp (rowsK d B G (Sum.inr l)) t = targetsK m d (Sum.inr l)
          + 2 * Real.sqrt ((ε / (32 * ((k : ℝ) * (1 + (k : ℝ) * ω)))) * V
            / ((Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) + (k : ℝ) * ω))) * (z l : ℝ)) →
        ∃ adm : (ι ⊕ κ) → Bool,
          adm = (fun x => decide (-theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
            ≤ targetsK m d x - dotp (rowsK d B G x) t)) ∧
          ∃ R ∈ survivorsBox (fun W => phi (rowsK d B G) (targetsK m d) W t)
              (keyOf (rowsK d B G) (targetsK m d) (fun l => Sum.inr l) t
                (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
                  / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
                (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ))))
              adm
              (boxOf κ (Real.sqrt (max 1 ω)) V (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
                  / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
                (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ)))
                (k + Fintype.card κ) (Fintype.card ι))
              (anchorRows ι κ) (La.map Sum.inl),
            (assetsOf (κ := κ) R).card ≤ S.card
            ∧ ∃ w : ι → ℝ, (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i)
              ∧ ∀ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i) →
                  (1 - 2 * ε) * objLO m d B Sf S u
                    ≤ objLO m d B Sf (assetsOf (κ := κ) R) w)
    ∧ ∀ (t : κ → ℝ) (adm : (ι ⊕ κ) → Bool),
      (survivorsBox (fun W => phi (rowsK d B G) (targetsK m d) W t)
          (keyOf (rowsK d B G) (targetsK m d) (fun l => Sum.inr l) t
            (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
              / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
            (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ))))
          adm
          (boxOf κ (Real.sqrt (max 1 ω)) V (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
              / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
            (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ)))
            (k + Fintype.card κ) (Fintype.card ι))
          (anchorRows ι κ) (La.map Sum.inl)).card
      ≤ (2 * ⌈Real.sqrt (max 1 ω) * (48 * (Fintype.card ι : ℝ) * Real.sqrt (Fintype.card κ : ℝ)
            * Real.sqrt (((k + Fintype.card κ : ℕ) : ℝ) * ((k : ℝ) * (1 + (k : ℝ) * ω)) / ε))
            + (Fintype.card ι : ℝ)⌉ + 1).toNat ^ Fintype.card κ
        * ((2 * ⌈8 * ((k + Fintype.card κ : ℕ) : ℝ) * (Fintype.card ι : ℝ)
            * (Fintype.card κ : ℝ) * Real.sqrt (max 1 ω) ^ 2 + (Fintype.card ι : ℝ)⌉ + 1).toNat
            ^ (Fintype.card κ * Fintype.card κ) * (k + Fintype.card κ + 1)) + 1 := by
  classical
  set c : ℝ := (k : ℝ) * (1 + (k : ℝ) * ω) with hcdef
  set N : ℕ := k + Fintype.card κ with hNdef
  set Mn : ℕ := Fintype.card ι with hMdef
  set Cn : ℝ := (Fintype.card κ : ℝ) + (k : ℝ) * ω with hCndef
  have hK0 : 0 < Fintype.card κ := Fintype.card_pos
  have hKc : (0:ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast hK0
  have hM0 : 0 < Mn := Fintype.card_pos
  have hN0 : 0 < N := by omega
  have hc1 : (1:ℝ) ≤ c := by
    have hk : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    rw [hcdef]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (k:ℝ)) hω]
  have hcpos : (0:ℝ) < c := by linarith
  have hρ : (0:ℝ) ≤ Real.sqrt (max 1 ω) := Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  swap
  · intro t adm
    have := card_boxOf_le (κ := κ) (ε := ε) (c := c) (V := V) (ρ := Real.sqrt (max 1 ω))
      (N := N) (Mn := Mn) hε hcpos hV hN0 hM0 hK0 hρ rfl rfl
    exact le_trans (survivorsBox_card_le _ _ _ _ _ _) (by omega)
  obtain ⟨A₀, hA₀S, th, hcardA, hnormA, hselfA, hoptA⟩ :=
    exists_optimal_selfconsistent (m := m) (B := B) (Sf := Sf) hd hG hPS S
  have hFeq : Fopt = phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) th :=
    hFopt.unique hoptA
  have hkA : A₀.card ≤ k := le_trans hcardA hkS
  have hCpos : (0:ℝ) < Cn := by
    have : (0:ℝ) ≤ (k : ℝ) * ω := mul_nonneg (by positivity) hω
    rw [hCndef]; linarith
  have hLalen : La.length = Mn := length_of_nodup_complete hnd hall
  have hM0r : (0:ℝ) < (Mn : ℝ) := by exact_mod_cast hM0
  have hsK : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr hKc
  have hθpos : 0 < theta0B ε V c := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨z, hz1, hz2⟩ := lo_fptas_portfolio_box (m := m) (P := P) hd hG hPS
    (cand := Finset.univ) (A₀ := A₀) (La := La) (T := fun l => (Sum.inr l : ι ⊕ κ))
    (thA := th)
    (η := theta0B ε V c / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Mn : ℝ)))
    (ξ := 1 / (8 * (Mn : ℝ) * (Fintype.card κ : ℝ))) (ε := ε) (V := V)
    (C := Cn) (c := c) (ρ := Real.sqrt (max 1 ω)) (k := k)
    (s := 2 * Real.sqrt ((ε / (32 * c)) * V / ((Fintype.card κ : ℝ) * Cn)))
    (fun l => inr_mem_barK A₀ l)
    (det_anchor_ne_zero (d := d) (B := B) (P := P) (Sf := Sf) hG hPS)
    (clamp_anchor hd hG hPS (fun i _ => hsys i) hω hkA le_rfl) hρ
    (fun x hx l => abs_cf_anchor_le hd hG hPS (fun i _ => hsys i) x hx l)
    hnormA hCpos hε hε1 hc1 hV
    (by rw [← hFeq]; exact hVF) (by rw [← hFeq]; exact hFV) hKc rfl hselfA
    (by positivity) (by positivity) hnd
    (fun i _ => List.mem_toFinset.mpr (hall i)) (fun i _ => Finset.mem_univ i)
    (anchorCover_of_sysVar (m := m) hd hG hPS hω (fun i _ => hsys i))
    hkA (Finset.subset_univ _)
    (by rw [hLalen]; field_simp; linarith)
    (by rw [hLalen]; field_simp; norm_num)
  refine ⟨z, mem_nodeBox_of_abs_le fun l => le_trans (hz1 l) (Nat.le_ceil _), fun t ht => ?_⟩
  obtain ⟨adm, hadmEq, _hadm1, _hadm2, R, hR, hcard, w, hw, hval⟩ := hz2 t ht
  rw [hLalen] at hR
  refine ⟨adm, hadmEq, R, hR, ?_, w, hw, fun u hu => ?_⟩
  · rw [hcard]; exact Finset.card_le_card hA₀S
  · have hub : objLO m d B Sf S u ≤ Fopt := hFopt.2 ⟨u, hu, rfl⟩
    have hcoef : (0:ℝ) ≤ 1 - 2 * ε := by linarith
    have := mul_le_mul_of_nonneg_left hub hcoef
    rw [hFeq] at this
    linarith


/-! ### The anchor-basis variant as a finite search -/

/-- Grid step of the anchor variant at guess `V` (`c = k(1+kω)`, `C = K + kω`). -/
noncomputable def anchorStep (Kc k : ℕ) (ε ω V : ℝ) : ℝ :=
  2 * Real.sqrt ((ε / (32 * ((k : ℝ) * (1 + (k : ℝ) * ω)))) * V
    / ((Kc : ℝ) * ((Kc : ℝ) + (k : ℝ) * ω)))

/-- Radius of the box of node indices of the anchor variant. -/
noncomputable def anchorZ (Kc k : ℕ) (ε ω : ℝ) : ℕ :=
  ⌈Real.sqrt ((Kc : ℝ) * ((Kc : ℝ) + (k : ℝ) * ω)
    / (2 * (ε / (32 * ((k : ℝ) * (1 + (k : ℝ) * ω)))))) + 1 / 2⌉₊

/-- The table of the dynamic program of the anchor variant at guess `V` and point `t`,
the assets processed in the order of `La` — literally the object of
`main_theorem_anchor_list`. -/
noncomputable def anchorTable (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ)
    (ε ω V : ℝ) (La : List ι) (t : κ → ℝ) : Finset (Finset (ι ⊕ κ)) :=
  survivorsBox (fun W => phi (rowsK d B G) (targetsK m d) W t)
    (keyOf (rowsK d B G) (targetsK m d) (fun l => Sum.inr l) t
      (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
        / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
      (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ))))
    (fun x => decide (-theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
      ≤ targetsK m d x - dotp (rowsK d B G x) t))
    (boxOf κ (Real.sqrt (max 1 ω)) V (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
        / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
      (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ)))
      (k + Fintype.card κ) (Fintype.card ι))
    (anchorRows ι κ) (La.map Sum.inl)

/-- **The candidate family of the anchor variant**: union over the guesses `V = L·2^j`,
`j ≤ J`, and the grid nodes of the tables of the dynamic program. -/
noncomputable def candidatesAnchor (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ)
    (ε ω L : ℝ) (J : ℕ) (La : List ι) : Finset (Finset (ι ⊕ κ)) :=
  (Finset.range (J + 1)).biUnion fun j =>
    (nodeBox (κ := κ) (anchorZ (Fintype.card κ) k ε ω)).biUnion fun z =>
      anchorTable m d B G k ε ω (L * 2 ^ j) La
        (nodePoint (rowsK d B G) (targetsK m d) (fun l => (Sum.inr l : ι ⊕ κ))
          (anchorStep (Fintype.card κ) k ε ω (L * 2 ^ j)) z)

/-- Size bound of one table of the anchor variant (does not depend on the guess). -/
noncomputable def tableBoundAnchor (Mc Kc k : ℕ) (ε ω : ℝ) : ℕ :=
  (2 * ⌈Real.sqrt (max 1 ω) * (48 * (Mc : ℝ) * Real.sqrt (Kc : ℝ)
      * Real.sqrt (((k + Kc : ℕ) : ℝ) * ((k : ℝ) * (1 + (k : ℝ) * ω)) / ε))
      + (Mc : ℝ)⌉ + 1).toNat ^ Kc
    * ((2 * ⌈8 * ((k + Kc : ℕ) : ℝ) * (Mc : ℝ) * (Kc : ℝ) * Real.sqrt (max 1 ω) ^ 2
        + (Mc : ℝ)⌉ + 1).toNat ^ (Kc * Kc) * (k + Kc + 1))

/-- Every table of the anchor variant has at most `tableBoundAnchor + 1` entries. -/
lemma card_anchorTable_le [Nonempty κ] [Nonempty ι] {k : ℕ} (hk1 : 1 ≤ k) {ε ω V : ℝ}
    (hε : 0 < ε) (hω : 0 ≤ ω) (hV : 0 < V) (La : List ι) (t : κ → ℝ) :
    (anchorTable m d B G k ε ω V La t).card
      ≤ tableBoundAnchor (Fintype.card ι) (Fintype.card κ) k ε ω + 1 := by
  have hK0 : 0 < Fintype.card κ := Fintype.card_pos
  have hM0 : 0 < Fintype.card ι := Fintype.card_pos
  have hc : (0:ℝ) < (k : ℝ) * (1 + (k : ℝ) * ω) := by
    have hk : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have : (0:ℝ) ≤ (k : ℝ) * ω := mul_nonneg (by linarith) hω
    nlinarith
  have hN : 0 < k + Fintype.card κ := by omega
  have hbox := card_boxOf_le (κ := κ) (ε := ε) (c := (k : ℝ) * (1 + (k : ℝ) * ω)) (V := V)
    (ρ := Real.sqrt (max 1 ω)) (N := k + Fintype.card κ) (Mn := Fintype.card ι)
    hε hc hV hN hM0 hK0 (Real.sqrt_nonneg _) rfl rfl
  unfold anchorTable
  refine le_trans (survivorsBox_card_le _ _ _ _ _ _) ?_
  unfold tableBoundAnchor
  push_cast at hbox ⊢
  omega

/-- **Size of the candidate family of the anchor variant**: at most
`(J+1)·(2Z+1)^K·(tableBoundAnchor+1)`; no enumeration of `K`-tuples. -/
theorem card_candidatesAnchor_le [Nonempty κ] [Nonempty ι] {k : ℕ} (hk1 : 1 ≤ k)
    {ε ω L : ℝ} (hε : 0 < ε) (hω : 0 ≤ ω) (hL0 : 0 < L) (J : ℕ) (La : List ι) :
    (candidatesAnchor m d B G k ε ω L J La).card
      ≤ (J + 1) * ((2 * anchorZ (Fintype.card κ) k ε ω + 1) ^ Fintype.card κ
          * (tableBoundAnchor (Fintype.card ι) (Fintype.card κ) k ε ω + 1)) := by
  unfold candidatesAnchor
  refine le_trans Finset.card_biUnion_le ?_
  have h1 : ∀ j ∈ Finset.range (J + 1),
      ((nodeBox (κ := κ) (anchorZ (Fintype.card κ) k ε ω)).biUnion fun z =>
          anchorTable m d B G k ε ω (L * 2 ^ j) La
            (nodePoint (rowsK d B G) (targetsK m d) (fun l => (Sum.inr l : ι ⊕ κ))
              (anchorStep (Fintype.card κ) k ε ω (L * 2 ^ j)) z)).card
      ≤ (2 * anchorZ (Fintype.card κ) k ε ω + 1) ^ Fintype.card κ
          * (tableBoundAnchor (Fintype.card ι) (Fintype.card κ) k ε ω + 1) := by
    intro j _
    have hV : (0:ℝ) < L * 2 ^ j := by positivity
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _
      (tableBoundAnchor (Fintype.card ι) (Fintype.card κ) k ε ω + 1)
      (fun z _ => card_anchorTable_le (m := m) (d := d) (B := B) (G := G) hk1 hε hω hV La _))
      ?_
    rw [card_nodeBox, smul_eq_mul]
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ h1) ?_
  rw [Finset.card_range, smul_eq_mul]

/-- Every candidate of the anchor variant has at most `k` assets. -/
lemma card_assetsOf_le_of_mem_candidatesAnchor [Nonempty κ] [Nonempty ι] {k : ℕ}
    {ε ω L : ℝ} {J : ℕ} {La : List ι} {R : Finset (ι ⊕ κ)}
    (hR : R ∈ candidatesAnchor m d B G k ε ω L J La) :
    (assetsOf (κ := κ) R).card ≤ k := by
  unfold candidatesAnchor at hR
  simp only [Finset.mem_biUnion] at hR
  obtain ⟨j, _, z, _, hRt⟩ := hR
  unfold anchorTable at hRt
  have hmem := survivorsBox_mem _ _ _ _ _ _ R hRt
  have hbR : anchorRows ι κ ⊆ R := hmem.1
  have hRbar : R = barK (κ := κ) (assetsOf (κ := κ) R) := barK_assetsOf hbR
  rcases survivorsBox_key_mem _ _ _ _ _ _ R hRt with hbase | hkey
  · have : assetsOf (κ := κ) R = ∅ := by
      rw [hbase]
      ext i
      simp [mem_assetsOf, anchorRows]
    rw [this]; simp
  · simp only [boxOf, keyBox, keyOf, Finset.mem_product, Finset.mem_range] at hkey
    have hcard : R.card ≤ k + Fintype.card κ := by omega
    have h2 := card_barK (κ := κ) (assetsOf (κ := κ) R)
    rw [← hRbar] at h2
    omega

/-- **The candidate family of the anchor variant contains a near-optimal support**, for
every processing order. -/
theorem exists_good_candidate_anchor [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    (hL0 : 0 < L) (hL : ∀ i, max (m i) 0 ^ 2 / Vmat d B Sf i i ≤ L)
    (hLatt : ∃ i, max (m i) 0 ^ 2 / Vmat d B Sf i i = L)
    {J : ℕ} (hJ : (k : ℝ) * (1 + ω) ≤ 2 ^ J)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    {S : Finset ι} (hkS : S.card ≤ k) {Fopt : ℝ}
    (hFopt : IsGreatest {v : ℝ | ∃ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i)
        ∧ v = objLO m d B Sf S u} Fopt)
    (hSopt : ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        objLO m d B Sf S' u ≤ Fopt) :
    ∃ R ∈ candidatesAnchor m d B G k ε ω L J La, ∃ w : ι → ℝ,
      (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i)
      ∧ (1 - 2 * ε) * Fopt ≤ objLO m d B Sf (assetsOf (κ := κ) R) w := by
  obtain ⟨j, hjJ, hVF, hFV⟩ := exists_guess_of_opt (B := B) hd hG hPS hk1 hω hsys hL0 hL
    hLatt hJ hkS hFopt hSopt
  have hV : (0:ℝ) < L * 2 ^ j := by positivity
  obtain ⟨⟨z, hz, hmain⟩, _⟩ := main_theorem_anchor_list (m := m) (d := d) (B := B)
    (Sf := Sf) (P := P) (G := G) hd hG hPS hk1 hε hε1 hω hsys hnd hall hkS hFopt hV hVF hFV
  have hdet := det_anchor_ne_zero (d := d) (B := B) (G := G) (P := P) (Sf := Sf) hG hPS
  have hnode := fun l => nodePoint_spec (y := targetsK m d)
    (s := anchorStep (Fintype.card κ) k ε ω (L * 2 ^ j)) (z := z) hdet l
  obtain ⟨adm, hadm, R, hR, _, w, hw, hval⟩ := hmain _ hnode
  subst hadm
  refine ⟨R, ?_, w, hw, ?_⟩
  · unfold candidatesAnchor
    simp only [Finset.mem_biUnion]
    exact ⟨j, Finset.mem_range.mpr (by omega), z, hz, hR⟩
  · obtain ⟨u, hu, hFu⟩ := hFopt.1
    rw [hFu]
    exact hval u hu

/-! ### The enumeration variant as a finite search, for every processing order -/

/-- The table of the dynamic program of the Main Theorem at guess `V`, `K`-tuple `T` and
point `t`, the assets processed in the order of `La` (`schemeTable` with an arbitrary
order) — literally the object of `main_theorem_list`. -/
noncomputable def schemeTableList (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ)
    (ε ω V : ℝ) (La : List ι) (T : κ → (ι ⊕ κ)) (t : κ → ℝ) : Finset (Finset (ι ⊕ κ)) :=
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
    (anchorRows ι κ) (La.map Sum.inl)

/-- **The candidate family of the Main Theorem for the processing order `La`**: union over
the guesses `V = L·2^j`, `j ≤ J`, all `K`-tuples of rows and all grid nodes of the tables
of the dynamic program. -/
noncomputable def candidatesList (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ)
    (ε ω L : ℝ) (J : ℕ) (La : List ι) : Finset (Finset (ι ⊕ κ)) :=
  (Finset.range (J + 1)).biUnion fun j =>
    (Finset.univ : Finset (κ → (ι ⊕ κ))).biUnion fun T =>
      (nodeBox (κ := κ) (schemeZ (Fintype.card κ) k ε ω)).biUnion fun z =>
        schemeTableList m d B G k ε ω (L * 2 ^ j) La T
          (nodePoint (rowsK d B G) (targetsK m d) T
            (schemeStep (Fintype.card κ) k ε ω (L * 2 ^ j)) z)

/-- Every table has at most `tableBound + 1` entries, for every order. -/
lemma card_schemeTableList_le [Nonempty κ] [Nonempty ι] {k : ℕ} (hk1 : 1 ≤ k) {ε ω V : ℝ}
    (hε : 0 < ε) (hω : 0 ≤ ω) (hV : 0 < V) (La : List ι) (T : κ → (ι ⊕ κ)) (t : κ → ℝ) :
    (schemeTableList m d B G k ε ω V La T t).card
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
  unfold schemeTableList
  refine le_trans (survivorsBox_card_le _ _ _ _ _ _) ?_
  unfold tableBound
  push_cast at hbox ⊢
  omega

/-- **Size of the candidate family**, for every order:
at most `(J+1)·(M+K)^K·(2Z+1)^K·(tableBound+1)`. -/
theorem card_candidatesList_le [Nonempty κ] [Nonempty ι] {k : ℕ} (hk1 : 1 ≤ k)
    {ε ω L : ℝ} (hε : 0 < ε) (hω : 0 ≤ ω) (hL0 : 0 < L) (J : ℕ) (La : List ι) :
    (candidatesList m d B G k ε ω L J La).card
      ≤ (J + 1) * ((Fintype.card ι + Fintype.card κ) ^ Fintype.card κ
        * ((2 * schemeZ (Fintype.card κ) k ε ω + 1) ^ Fintype.card κ
          * (tableBound (Fintype.card ι) (Fintype.card κ) k ε ω + 1))) := by
  unfold candidatesList
  refine le_trans Finset.card_biUnion_le ?_
  have h1 : ∀ j ∈ Finset.range (J + 1),
      ((Finset.univ : Finset (κ → (ι ⊕ κ))).biUnion fun T =>
        (nodeBox (κ := κ) (schemeZ (Fintype.card κ) k ε ω)).biUnion fun z =>
          schemeTableList m d B G k ε ω (L * 2 ^ j) La T
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
          schemeTableList m d B G k ε ω (L * 2 ^ j) La T
            (nodePoint (rowsK d B G) (targetsK m d) T
              (schemeStep (Fintype.card κ) k ε ω (L * 2 ^ j)) z)).card
        ≤ (2 * schemeZ (Fintype.card κ) k ε ω + 1) ^ Fintype.card κ
          * (tableBound (Fintype.card ι) (Fintype.card κ) k ε ω + 1) := by
      intro T _
      refine le_trans Finset.card_biUnion_le ?_
      refine le_trans (Finset.sum_le_card_nsmul _ _
        (tableBound (Fintype.card ι) (Fintype.card κ) k ε ω + 1)
        (fun z _ => card_schemeTableList_le (m := m) (d := d) (B := B) (G := G) hk1 hε hω hV
          La T _)) ?_
      rw [card_nodeBox, smul_eq_mul]
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ h2) ?_
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_sum, smul_eq_mul]
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ h1) ?_
  rw [Finset.card_range, smul_eq_mul]

/-- Every candidate has at most `k` assets, for every order. -/
lemma card_assetsOf_le_of_mem_candidatesList [Nonempty κ] [Nonempty ι] {k : ℕ} {ε ω L : ℝ}
    {J : ℕ} {La : List ι} {R : Finset (ι ⊕ κ)}
    (hR : R ∈ candidatesList m d B G k ε ω L J La) :
    (assetsOf (κ := κ) R).card ≤ k := by
  unfold candidatesList at hR
  simp only [Finset.mem_biUnion] at hR
  obtain ⟨j, _, T, _, z, _, hRt⟩ := hR
  unfold schemeTableList at hRt
  have hmem := survivorsBox_mem _ _ _ _ _ _ R hRt
  have hbR : anchorRows ι κ ⊆ R := hmem.1
  have hRbar : R = barK (κ := κ) (assetsOf (κ := κ) R) := barK_assetsOf hbR
  rcases survivorsBox_key_mem _ _ _ _ _ _ R hRt with hbase | hkey
  · have : assetsOf (κ := κ) R = ∅ := by
      rw [hbase]
      ext i
      simp [mem_assetsOf, anchorRows]
    rw [this]; simp
  · simp only [boxOf, keyBox, keyOf, Finset.mem_product, Finset.mem_range] at hkey
    have hcard : R.card ≤ k + Fintype.card κ := by omega
    have h2 := card_barK (κ := κ) (assetsOf (κ := κ) R)
    rw [← hRbar] at h2
    omega

/-- **The candidate family contains a near-optimal support**, for every order. -/
theorem exists_good_candidate_list [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    (hL0 : 0 < L) (hL : ∀ i, max (m i) 0 ^ 2 / Vmat d B Sf i i ≤ L)
    (hLatt : ∃ i, max (m i) 0 ^ 2 / Vmat d B Sf i i = L)
    {J : ℕ} (hJ : (k : ℝ) * (1 + ω) ≤ 2 ^ J)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    {S : Finset ι} (hkS : S.card ≤ k) {Fopt : ℝ}
    (hFopt : IsGreatest {v : ℝ | ∃ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i)
        ∧ v = objLO m d B Sf S u} Fopt)
    (hSopt : ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        objLO m d B Sf S' u ≤ Fopt) :
    ∃ R ∈ candidatesList m d B G k ε ω L J La, ∃ w : ι → ℝ,
      (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i)
      ∧ (1 - 2 * ε) * Fopt ≤ objLO m d B Sf (assetsOf (κ := κ) R) w := by
  obtain ⟨j, hjJ, hVF, hFV⟩ := exists_guess_of_opt (B := B) hd hG hPS hk1 hω hsys hL0 hL
    hLatt hJ hkS hFopt hSopt
  have hV : (0:ℝ) < L * 2 ^ j := by positivity
  obtain ⟨⟨T, hdet, z, hz, hmain⟩, _⟩ := main_theorem_list (m := m) (d := d) (B := B)
    (Sf := Sf) (P := P) (G := G) hd hG hPS hk1 hε hε1 hω hsys hnd hall hkS hFopt hV hVF hFV
  have hnode := fun l => nodePoint_spec (y := targetsK m d)
    (s := schemeStep (Fintype.card κ) k ε ω (L * 2 ^ j)) (z := z) hdet l
  obtain ⟨adm, hadm, R, hR, _, w, hw, hval⟩ := hmain _ hnode
  subst hadm
  refine ⟨R, ?_, w, hw, ?_⟩
  · unfold candidatesList
    simp only [Finset.mem_biUnion]
    exact ⟨j, Finset.mem_range.mpr (by omega), T, Finset.mem_univ _, z, hz, hR⟩
  · obtain ⟨u, hu, hFu⟩ := hFopt.1
    rw [hFu]
    exact hval u hu

/-! ### The trading argument for an arbitrary family of supports -/

/-- **A best pair exists in every nonempty family**: `(R*, w*)`, `R*` in the family,
`w* ≥ 0` on it, whose objective is at least that of every member with every long-only
portfolio on it (each member is evaluated exactly, Theorem D). -/
theorem exists_best_pair_of_family [Nonempty κ]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {Fam : Finset (Finset (ι ⊕ κ))} (hne : Fam.Nonempty) :
    ∃ R₀ ∈ Fam, ∃ w₀ : ι → ℝ,
      (∀ i ∈ assetsOf (κ := κ) R₀, 0 ≤ w₀ i) ∧
      ∀ R ∈ Fam, ∀ w : ι → ℝ, (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i) →
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

/-- **Trading form for an arbitrary family.** Let `Fopt` bound the objective of every
long-only portfolio with at most `k` names, let every member of the family `Fam` have at
most `k` assets, and let some member carry a long-only portfolio with objective at least
`(1 − 2ε)·Fopt`. Then every best pair `(R*, w*)` of `Fam` has at most `k` assets,
objective at least `(1 − 2ε)·Fopt`, and can be normalized to a fully invested long-only
portfolio whose Sharpe ratio is at least `√(1 − 2ε)` times that of every long-only
portfolio with at most `k` names and positive expected excess return. -/
theorem best_pair_sharpe_of_family
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} {ε : ℝ} (hε1 : ε < 1 / 2) {Fopt : ℝ}
    (hSopt : ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        objLO m d B Sf S' u ≤ Fopt)
    {Fam : Finset (Finset (ι ⊕ κ))} (hFamk : ∀ R ∈ Fam, (assetsOf (κ := κ) R).card ≤ k)
    (hgood : ∃ R ∈ Fam, ∃ w : ι → ℝ, (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i)
      ∧ (1 - 2 * ε) * Fopt ≤ objLO m d B Sf (assetsOf (κ := κ) R) w)
    {R₀ : Finset (ι ⊕ κ)} (hR₀ : R₀ ∈ Fam) {w₀ : ι → ℝ}
    (hw₀ : ∀ i ∈ assetsOf (κ := κ) R₀, 0 ≤ w₀ i)
    (hbest : ∀ R ∈ Fam, ∀ w : ι → ℝ, (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i) →
        objLO m d B Sf (assetsOf (κ := κ) R) w ≤ objLO m d B Sf (assetsOf (κ := κ) R₀) w₀) :
    (assetsOf (κ := κ) R₀).card ≤ k
    ∧ (1 - 2 * ε) * Fopt ≤ objLO m d B Sf (assetsOf (κ := κ) R₀) w₀
    ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        0 < pRet m S' u →
        ∃ x : ι → ℝ, (∀ i ∈ assetsOf (κ := κ) R₀, 0 ≤ x i)
          ∧ ∑ i ∈ assetsOf (κ := κ) R₀, x i = 1
          ∧ Real.sqrt (1 - 2 * ε) * sharpe m d B Sf S' u
              ≤ sharpe m d B Sf (assetsOf (κ := κ) R₀) x := by
  obtain ⟨R, hR, w, hw, hgood⟩ := hgood
  have hval : (1 - 2 * ε) * Fopt ≤ objLO m d B Sf (assetsOf (κ := κ) R₀) w₀ :=
    le_trans hgood (hbest R hR w hw)
  refine ⟨hFamk R₀ hR₀, hval, fun S' hS' u hu hru => ?_⟩
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

/-- **Trading form of the anchor-basis variant, for every processing order.** Let `S` be
an optimal support with at most `k` names and `La` any duplicate-free list of all assets.
Every best pair `(R*, w*)` of `candidatesAnchor … La` is a long-only portfolio with at
most `k` names within `1 − 2ε` of the optimum; normalized to a fully invested portfolio,
its Sharpe ratio is at least `√(1 − 2ε)` times that of every long-only portfolio with at
most `k` names and positive expected excess return. -/
theorem best_pair_sharpe_anchor [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω L : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    (hL0 : 0 < L) (hL : ∀ i, max (m i) 0 ^ 2 / Vmat d B Sf i i ≤ L)
    (hLatt : ∃ i, max (m i) 0 ^ 2 / Vmat d B Sf i i = L)
    {J : ℕ} (hJ : (k : ℝ) * (1 + ω) ≤ 2 ^ J)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    {S : Finset ι} (hkS : S.card ≤ k) {Fopt : ℝ}
    (hFopt : IsGreatest {v : ℝ | ∃ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i)
        ∧ v = objLO m d B Sf S u} Fopt)
    (hSopt : ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        objLO m d B Sf S' u ≤ Fopt)
    {R₀ : Finset (ι ⊕ κ)} (hR₀ : R₀ ∈ candidatesAnchor m d B G k ε ω L J La) {w₀ : ι → ℝ}
    (hw₀ : ∀ i ∈ assetsOf (κ := κ) R₀, 0 ≤ w₀ i)
    (hbest : ∀ R ∈ candidatesAnchor m d B G k ε ω L J La, ∀ w : ι → ℝ,
      (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i) →
        objLO m d B Sf (assetsOf (κ := κ) R) w ≤ objLO m d B Sf (assetsOf (κ := κ) R₀) w₀) :
    (assetsOf (κ := κ) R₀).card ≤ k
    ∧ (1 - 2 * ε) * Fopt ≤ objLO m d B Sf (assetsOf (κ := κ) R₀) w₀
    ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        0 < pRet m S' u →
        ∃ x : ι → ℝ, (∀ i ∈ assetsOf (κ := κ) R₀, 0 ≤ x i)
          ∧ ∑ i ∈ assetsOf (κ := κ) R₀, x i = 1
          ∧ Real.sqrt (1 - 2 * ε) * sharpe m d B Sf S' u
              ≤ sharpe m d B Sf (assetsOf (κ := κ) R₀) x :=
  best_pair_sharpe_of_family (B := B) hd hG hPS hε1 hSopt
    (fun _ hR => card_assetsOf_le_of_mem_candidatesAnchor hR)
    (exists_good_candidate_anchor (Sf := Sf) (P := P) hd hG hPS hk1 hε hε1.le hω hsys hL0
      hL hLatt hJ hnd hall hkS hFopt hSopt)
    hR₀ hw₀ hbest

/-! ### The optimum and the squared maximal Sharpe ratio -/

/-- **An optimal support exists**: some `S` with `|S| ≤ k` and a value `Fopt`, attained on
`S`, that bounds the objective of every long-only portfolio with at most `k` names. -/
theorem exists_optimal_support [Nonempty κ]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (k : ℕ) :
    ∃ S : Finset ι, S.card ≤ k ∧ ∃ Fopt : ℝ,
      IsGreatest {v : ℝ | ∃ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i) ∧ v = objLO m d B Sf S u} Fopt
      ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
          objLO m d B Sf S' u ≤ Fopt := by
  classical
  have hval : ∀ S : Finset ι, ∃ z : ℝ,
      IsGreatest {v : ℝ | ∃ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i) ∧ v = objLO m d B Sf S u} z := by
    intro S
    obtain ⟨z, _, hz⟩ := isGreatest_objLO_isLeast_QLO (m := m) (B := B) (Sf := Sf) (P := P)
      (G := G) hd hG hPS S
    exact ⟨z, hz⟩
  choose val hvalG using hval
  have hne : ((Finset.univ : Finset (Finset ι)).filter (fun S => S.card ≤ k)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image _ val hne
  have hSk : S.card ≤ k := (Finset.mem_filter.mp hS).2
  refine ⟨S, hSk, val S, hvalG S, fun S' hS' u hu => ?_⟩
  have h1 : objLO m d B Sf S' u ≤ val S' := (hvalG S').2 ⟨u, hu, rfl⟩
  have h2 : val S' ≤ val S := hmax S' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS'⟩)
  linarith

/-- **The squared Sharpe ratio never exceeds the optimum**: if `Fopt` bounds the objective
of every long-only portfolio with at most `k` names, every such portfolio with positive
expected excess return has `sharpe² ≤ Fopt`. -/
theorem sharpe_sq_le_opt (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {k : ℕ} {Fopt : ℝ}
    (hSopt : ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        objLO m d B Sf S' u ≤ Fopt)
    {S' : Finset ι} (hS' : S'.card ≤ k) {u : ι → ℝ} (hu : ∀ i ∈ S', 0 ≤ u i)
    (hru : 0 < pRet m S' u) :
    sharpe m d B Sf S' u ^ 2 ≤ Fopt := by
  obtain ⟨i, hi, hui⟩ := exists_ne_zero_of_pRet_pos hru
  have hvu : 0 < pVar d B Sf S' u := pVar_pos (B := B) hd hG hPS hi hui
  have hc : 0 ≤ pRet m S' u / pVar d B Sf S' u := div_nonneg hru.le hvu.le
  have hopt := hSopt S' hS' (fun i => (pRet m S' u / pVar d B Sf S' u) * u i)
    (fun i hi => mul_nonneg hc (hu i hi))
  rw [objLO_opt_scale S' u hvu] at hopt
  rw [sharpe_sq S' u hvu]
  exact hopt

/-- **A portfolio with positive objective has positive expected excess return and squared
Sharpe ratio at least its objective.** With `sharpe_sq_le_opt`: the optimum is the square
of the largest Sharpe ratio of a long-only portfolio with at most `k` names. -/
theorem obj_le_sharpe_sq (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {S : Finset ι} {w : ι → ℝ} (hpos : 0 < objLO m d B Sf S w) :
    0 < pRet m S w ∧ objLO m d B Sf S w ≤ sharpe m d B Sf S w ^ 2 := by
  have hvw0 : 0 ≤ pVar d B Sf S w := pVar_nonneg (B := B) hd hG hPS S w
  have hrw : 0 < pRet m S w := by
    rw [objLO_eq_ret_var] at hpos
    linarith
  obtain ⟨i, hi, hwi⟩ := exists_ne_zero_of_pRet_pos hrw
  have hvw : 0 < pVar d B Sf S w := pVar_pos (B := B) hd hG hPS hi hwi
  refine ⟨hrw, ?_⟩
  rw [sharpe_sq S w hvw]
  exact objLO_le_ret_sq_div S w hvw

/-! ### One portfolio for all comparisons -/

/-- **Budget normalization, explicitly**: `x = w/Σ_{i∈R} w_i` is long-only, fully invested
and has the Sharpe ratio of `w` (the portfolio of `normalize_budget`). -/
theorem normalize_budget_explicit {R : Finset ι} {w : ι → ℝ} (hw : ∀ i ∈ R, 0 ≤ w i)
    (hr : 0 < pRet m R w) :
    (∀ i ∈ R, 0 ≤ (∑ j ∈ R, w j)⁻¹ * w i) ∧ ∑ i ∈ R, (∑ j ∈ R, w j)⁻¹ * w i = 1 ∧
      sharpe m d B Sf R (fun i => (∑ j ∈ R, w j)⁻¹ * w i) = sharpe m d B Sf R w := by
  obtain ⟨i, hi, hwi⟩ := exists_ne_zero_of_pRet_pos hr
  have hwi' : 0 < w i := lt_of_le_of_ne (hw i hi) (Ne.symm hwi)
  have hsum : 0 < ∑ j ∈ R, w j :=
    lt_of_lt_of_le hwi' (Finset.single_le_sum (f := w) (fun j hj => hw j hj) hi)
  refine ⟨fun j hj => mul_nonneg (inv_nonneg.mpr hsum.le) (hw j hj), ?_, ?_⟩
  · rw [← Finset.mul_sum]; exact inv_mul_cancel₀ hsum.ne'
  · exact sharpe_smul R w (inv_pos.mpr hsum)

/-- **One fully invested portfolio beats every competitor.** If `Fopt > 0` bounds the
objective of every long-only portfolio with at most `k` names and `w₀ ≥ 0` on `R` has
objective at least `(1 − 2ε)·Fopt`, then the fully invested portfolio `x = w₀/Σw₀` on `R`
has Sharpe ratio at least `√(1 − 2ε)` times that of **every** long-only portfolio with at
most `k` names and positive expected excess return. -/
theorem best_pair_sharpe_uniform
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} {ε : ℝ} (hε1 : ε < 1 / 2) {Fopt : ℝ} (hFpos : 0 < Fopt)
    (hSopt : ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        objLO m d B Sf S' u ≤ Fopt)
    {R : Finset ι} {w₀ : ι → ℝ} (hw₀ : ∀ i ∈ R, 0 ≤ w₀ i)
    (hval : (1 - 2 * ε) * Fopt ≤ objLO m d B Sf R w₀) :
    (∀ i ∈ R, 0 ≤ (∑ j ∈ R, w₀ j)⁻¹ * w₀ i) ∧ ∑ i ∈ R, (∑ j ∈ R, w₀ j)⁻¹ * w₀ i = 1 ∧
      ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        0 < pRet m S' u →
        Real.sqrt (1 - 2 * ε) * sharpe m d B Sf S' u
          ≤ sharpe m d B Sf R (fun i => (∑ j ∈ R, w₀ j)⁻¹ * w₀ i) := by
  have hc : 0 < 1 - 2 * ε := by linarith
  have hobjpos : 0 < objLO m d B Sf R w₀ := lt_of_lt_of_le (mul_pos hc hFpos) hval
  obtain ⟨hrw, _⟩ := obj_le_sharpe_sq (B := B) hd hG hPS hobjpos
  obtain ⟨hx0, hx1, hxs⟩ := normalize_budget_explicit (d := d) (B := B) (Sf := Sf) hw₀ hrw
  refine ⟨hx0, hx1, fun S' hS' u hu hru => ?_⟩
  rw [hxs]
  obtain ⟨i, hi, hui⟩ := exists_ne_zero_of_pRet_pos hru
  have hvu : 0 < pVar d B Sf S' u := pVar_pos (B := B) hd hG hPS hi hui
  have hcoef : 0 ≤ pRet m S' u / pVar d B Sf S' u := div_nonneg hru.le hvu.le
  have hopt := hSopt S' hS' (fun i => (pRet m S' u / pVar d B Sf S' u) * u i)
    (fun i hi => mul_nonneg hcoef (hu i hi))
  rw [objLO_opt_scale S' u hvu] at hopt
  have hobj : (1 - 2 * ε) * (pRet m S' u ^ 2 / pVar d B Sf S' u) ≤ objLO m d B Sf R w₀ :=
    le_trans (mul_le_mul_of_nonneg_left hopt hc.le) hval
  exact (sharpe_ge_of_obj_ge (B := B) hd hG hPS (by linarith) hru hobj).2.2

/-! ### The trading theorems, from the data only -/

/-- **Trading theorem (enumeration of `K`-tuples), from the data.** For every processing
order `La`, every best pair `(R*, w*)` of the candidate family `candidatesList … La` has at
most `k` assets and objective at least `1 − 2ε` times that of every long-only portfolio
with at most `k` names; and the fully invested long-only portfolio `x* = w*/Σw*` has Sharpe
ratio at least `√(1 − 2ε)` times that of **every** long-only portfolio with at most `k`
names and positive expected excess return. No optimal support is assumed. -/
theorem trading_theorem [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω L : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    (hL0 : 0 < L) (hL : ∀ i, max (m i) 0 ^ 2 / Vmat d B Sf i i ≤ L)
    (hLatt : ∃ i, max (m i) 0 ^ 2 / Vmat d B Sf i i = L)
    {J : ℕ} (hJ : (k : ℝ) * (1 + ω) ≤ 2 ^ J)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    {R₀ : Finset (ι ⊕ κ)} (hR₀ : R₀ ∈ candidatesList m d B G k ε ω L J La) {w₀ : ι → ℝ}
    (hw₀ : ∀ i ∈ assetsOf (κ := κ) R₀, 0 ≤ w₀ i)
    (hbest : ∀ R ∈ candidatesList m d B G k ε ω L J La, ∀ w : ι → ℝ,
      (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i) →
        objLO m d B Sf (assetsOf (κ := κ) R) w ≤ objLO m d B Sf (assetsOf (κ := κ) R₀) w₀) :
    (assetsOf (κ := κ) R₀).card ≤ k
    ∧ (∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        (1 - 2 * ε) * objLO m d B Sf S' u ≤ objLO m d B Sf (assetsOf (κ := κ) R₀) w₀)
    ∧ (∀ i ∈ assetsOf (κ := κ) R₀, 0 ≤ (∑ j ∈ assetsOf (κ := κ) R₀, w₀ j)⁻¹ * w₀ i)
    ∧ ∑ i ∈ assetsOf (κ := κ) R₀, (∑ j ∈ assetsOf (κ := κ) R₀, w₀ j)⁻¹ * w₀ i = 1
    ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        0 < pRet m S' u →
        Real.sqrt (1 - 2 * ε) * sharpe m d B Sf S' u
          ≤ sharpe m d B Sf (assetsOf (κ := κ) R₀)
              (fun i => (∑ j ∈ assetsOf (κ := κ) R₀, w₀ j)⁻¹ * w₀ i) := by
  obtain ⟨S, hkS, Fopt, hFopt, hSopt⟩ := exists_optimal_support (m := m) (d := d) (B := B)
    (Sf := Sf) (P := P) (G := G) hd hG hPS k
  obtain ⟨h1, h2, _⟩ := best_pair_sharpe_of_family (m := m) (d := d) (B := B) (Sf := Sf)
    (P := P) (G := G) hd hG hPS hε1 hSopt
    (fun _ hR => card_assetsOf_le_of_mem_candidatesList hR)
    (exists_good_candidate_list (Sf := Sf) (P := P) hd hG hPS hk1 hε hε1.le hω hsys hL0
      hL hLatt hJ hnd hall hkS hFopt hSopt)
    hR₀ hw₀ hbest
  obtain ⟨i₀, hi₀⟩ := hLatt
  have hLF : L ≤ Fopt := hi₀ ▸ opt_ge_single_of_opt (B := B) hd hG hPS hk1 hSopt i₀
  obtain ⟨hx0, hx1, hxs⟩ := best_pair_sharpe_uniform (B := B) hd hG hPS hε1
    (lt_of_lt_of_le hL0 hLF) hSopt hw₀ h2
  refine ⟨h1, fun S' hS' u hu => ?_, hx0, hx1, hxs⟩
  have hub := hSopt S' hS' u hu
  have hcoef : (0:ℝ) ≤ 1 - 2 * ε := by linarith
  linarith [mul_le_mul_of_nonneg_left hub hcoef]

/-- **Trading theorem (anchor basis), from the data.** As `trading_theorem`, for the
candidate family `candidatesAnchor … La` of the anchor-basis variant (no enumeration of
`K`-tuples), for every processing order `La`. -/
theorem trading_theorem_anchor [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω L : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    (hL0 : 0 < L) (hL : ∀ i, max (m i) 0 ^ 2 / Vmat d B Sf i i ≤ L)
    (hLatt : ∃ i, max (m i) 0 ^ 2 / Vmat d B Sf i i = L)
    {J : ℕ} (hJ : (k : ℝ) * (1 + ω) ≤ 2 ^ J)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    {R₀ : Finset (ι ⊕ κ)} (hR₀ : R₀ ∈ candidatesAnchor m d B G k ε ω L J La) {w₀ : ι → ℝ}
    (hw₀ : ∀ i ∈ assetsOf (κ := κ) R₀, 0 ≤ w₀ i)
    (hbest : ∀ R ∈ candidatesAnchor m d B G k ε ω L J La, ∀ w : ι → ℝ,
      (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i) →
        objLO m d B Sf (assetsOf (κ := κ) R) w ≤ objLO m d B Sf (assetsOf (κ := κ) R₀) w₀) :
    (assetsOf (κ := κ) R₀).card ≤ k
    ∧ (∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        (1 - 2 * ε) * objLO m d B Sf S' u ≤ objLO m d B Sf (assetsOf (κ := κ) R₀) w₀)
    ∧ (∀ i ∈ assetsOf (κ := κ) R₀, 0 ≤ (∑ j ∈ assetsOf (κ := κ) R₀, w₀ j)⁻¹ * w₀ i)
    ∧ ∑ i ∈ assetsOf (κ := κ) R₀, (∑ j ∈ assetsOf (κ := κ) R₀, w₀ j)⁻¹ * w₀ i = 1
    ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        0 < pRet m S' u →
        Real.sqrt (1 - 2 * ε) * sharpe m d B Sf S' u
          ≤ sharpe m d B Sf (assetsOf (κ := κ) R₀)
              (fun i => (∑ j ∈ assetsOf (κ := κ) R₀, w₀ j)⁻¹ * w₀ i) := by
  obtain ⟨S, hkS, Fopt, hFopt, hSopt⟩ := exists_optimal_support (m := m) (d := d) (B := B)
    (Sf := Sf) (P := P) (G := G) hd hG hPS k
  obtain ⟨h1, h2, _⟩ := best_pair_sharpe_anchor (m := m) (d := d) (B := B) (Sf := Sf)
    (P := P) (G := G) hd hG hPS hk1 hε hε1 hω hsys hL0 hL hLatt hJ hnd hall hkS hFopt hSopt
    hR₀ hw₀ hbest
  obtain ⟨i₀, hi₀⟩ := hLatt
  have hLF : L ≤ Fopt := hi₀ ▸ opt_ge_single_of_opt (B := B) hd hG hPS hk1 hSopt i₀
  obtain ⟨hx0, hx1, hxs⟩ := best_pair_sharpe_uniform (B := B) hd hG hPS hε1
    (lt_of_lt_of_le hL0 hLF) hSopt hw₀ h2
  refine ⟨h1, fun S' hS' u hu => ?_, hx0, hx1, hxs⟩
  have hub := hSopt S' hS' u hu
  have hcoef : (0:ℝ) ≤ 1 - 2 * ε := by linarith
  linarith [mul_le_mul_of_nonneg_left hub hcoef]

end Orders

/-! ### Nonvacuity: the anchor-variant trading chain on a concrete instance

The instance of `trading_instance` (one asset, `m = d = 1`, `B = 0`, `Σ_f = 1`, `k = 1`,
`ε = 1/4`, `ω = 0`, `L = 1`, `J = 0`), processing order `[0]`. -/

section InstanceAnchor

theorem trading_instance_anchor :
    ∃ R₀ ∈ candidatesAnchor (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1) (fun _ (_ : Unit) => 0)
        (fun _ _ => 1) 1 (1/4) 0 1 0 [0],
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
  have hnd : ([0] : List (Fin 1)).Nodup := List.nodup_singleton 0
  have hall : ∀ i : Fin 1, i ∈ ([0] : List (Fin 1)) := by
    intro i; rw [List.mem_singleton]; exact Subsingleton.elim _ _
  have hSopt : ∀ S' : Finset (Fin 1), S'.card ≤ 1 → ∀ u : Fin 1 → ℝ, (∀ i ∈ S', 0 ≤ u i) →
      objLO m d B Sf S' u ≤ 1 := fun S' _ u hu => inst_obj_le S' u hu
  have hFopt : IsGreatest {v : ℝ | ∃ u : Fin 1 → ℝ, (∀ i ∈ (Finset.univ : Finset (Fin 1)),
      0 ≤ u i) ∧ v = objLO m d B Sf Finset.univ u} 1 := by
    refine ⟨⟨fun _ => 1, fun _ _ => zero_le_one, ?_⟩, ?_⟩
    · simp [objLO, Vmat, m, d, B]; norm_num
    · rintro v ⟨u, hu, rfl⟩
      exact inst_obj_le _ u hu
  obtain ⟨R, hR, _⟩ := exists_good_candidate_anchor (G := G) (P := P)
    hd hG hPS le_rfl (by norm_num : (0:ℝ) < 1/4) (by norm_num) le_rfl hsys one_pos hL hLatt
    hJ hnd hall (by simp : (Finset.univ : Finset (Fin 1)).card ≤ 1) hFopt hSopt
  obtain ⟨R₀, hR₀, w₀, hw₀, hbest⟩ := exists_best_pair_of_family (Sf := Sf) (P := P) hd hG hPS
    ⟨R, hR⟩
  obtain ⟨_, _, hsh⟩ := best_pair_sharpe_anchor (G := G) (P := P) hd hG hPS
    le_rfl (by norm_num : (0:ℝ) < 1/4) (by norm_num) le_rfl hsys one_pos hL hLatt hJ hnd hall
    (by simp : (Finset.univ : Finset (Fin 1)).card ≤ 1) hFopt hSopt hR₀ hw₀ hbest
  obtain ⟨x, hx, hxs, hxsh⟩ := hsh Finset.univ (by simp) (fun _ => 1) (fun _ _ => zero_le_one)
    (by simp [pRet, m])
  refine ⟨R₀, hR₀, x, hx, hxs, ?_⟩
  have hsu : sharpe m d B Sf Finset.univ (fun _ => 1) = 1 := by
    simp [sharpe, pRet, pVar, Vmat, m, d, B]
  rw [hsu, mul_one] at hxsh
  exact hxsh

/-- **The data-only trading theorems are not vacuous**: on the one-asset instance of
`trading_instance`, every hypothesis of `trading_theorem` and `trading_theorem_anchor` holds
(the best pairs exist by `exists_best_pair_of_family`), and both conclusions give a fully
invested candidate with Sharpe ratio at least `√(1/2)`. -/
theorem trading_theorems_instance :
    (∃ R₀ ∈ candidatesList (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1) (fun _ (_ : Unit) => 0)
        (fun _ _ => 1) 1 (1/4) 0 1 0 [0],
      ∃ x : Fin 1 → ℝ, (∀ i ∈ assetsOf (κ := Unit) R₀, 0 ≤ x i)
        ∧ ∑ i ∈ assetsOf (κ := Unit) R₀, x i = 1
        ∧ Real.sqrt (1 - 2 * (1/4)) ≤ sharpe (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1)
            (fun _ (_ : Unit) => 0) (fun _ _ => 1) (assetsOf (κ := Unit) R₀) x)
    ∧ (∃ R₀ ∈ candidatesAnchor (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1) (fun _ (_ : Unit) => 0)
        (fun _ _ => 1) 1 (1/4) 0 1 0 [0],
      ∃ x : Fin 1 → ℝ, (∀ i ∈ assetsOf (κ := Unit) R₀, 0 ≤ x i)
        ∧ ∑ i ∈ assetsOf (κ := Unit) R₀, x i = 1
        ∧ Real.sqrt (1 - 2 * (1/4)) ≤ sharpe (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1)
            (fun _ (_ : Unit) => 0) (fun _ _ => 1) (assetsOf (κ := Unit) R₀) x) := by
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
  have hnd : ([0] : List (Fin 1)).Nodup := List.nodup_singleton 0
  have hall : ∀ i : Fin 1, i ∈ ([0] : List (Fin 1)) := by
    intro i; rw [List.mem_singleton]; exact Subsingleton.elim _ _
  have hSopt : ∀ S' : Finset (Fin 1), S'.card ≤ 1 → ∀ u : Fin 1 → ℝ, (∀ i ∈ S', 0 ≤ u i) →
      objLO m d B Sf S' u ≤ 1 := fun S' _ u hu => inst_obj_le S' u hu
  have hFopt : IsGreatest {v : ℝ | ∃ u : Fin 1 → ℝ, (∀ i ∈ (Finset.univ : Finset (Fin 1)),
      0 ≤ u i) ∧ v = objLO m d B Sf Finset.univ u} 1 := by
    refine ⟨⟨fun _ => 1, fun _ _ => zero_le_one, ?_⟩, ?_⟩
    · simp [objLO, Vmat, m, d, B]; norm_num
    · rintro v ⟨u, hu, rfl⟩
      exact inst_obj_le _ u hu
  have hsu : sharpe m d B Sf Finset.univ (fun _ => 1) = 1 := by
    simp [sharpe, pRet, pVar, Vmat, m, d, B]
  constructor
  · obtain ⟨R, hR, _⟩ := exists_good_candidate_list (G := G) (P := P)
      hd hG hPS le_rfl (by norm_num : (0:ℝ) < 1/4) (by norm_num) le_rfl hsys one_pos hL hLatt
      hJ hnd hall (by simp : (Finset.univ : Finset (Fin 1)).card ≤ 1) hFopt hSopt
    obtain ⟨R₀, hR₀, w₀, hw₀, hbest⟩ := exists_best_pair_of_family (Sf := Sf) (P := P) hd hG
      hPS ⟨R, hR⟩
    obtain ⟨_, _, hx0, hx1, hxsh⟩ := trading_theorem (G := G) (P := P) hd hG hPS
      le_rfl (by norm_num : (0:ℝ) < 1/4) (by norm_num) le_rfl hsys one_pos hL hLatt hJ hnd
      hall hR₀ hw₀ hbest
    have hsh := hxsh Finset.univ (by simp) (fun _ => 1) (fun _ _ => zero_le_one)
      (by simp [pRet, m])
    refine ⟨R₀, hR₀, _, hx0, hx1, ?_⟩
    rw [hsu, mul_one] at hsh
    exact hsh
  · obtain ⟨R, hR, _⟩ := exists_good_candidate_anchor (G := G) (P := P)
      hd hG hPS le_rfl (by norm_num : (0:ℝ) < 1/4) (by norm_num) le_rfl hsys one_pos hL hLatt
      hJ hnd hall (by simp : (Finset.univ : Finset (Fin 1)).card ≤ 1) hFopt hSopt
    obtain ⟨R₀, hR₀, w₀, hw₀, hbest⟩ := exists_best_pair_of_family (Sf := Sf) (P := P) hd hG
      hPS ⟨R, hR⟩
    obtain ⟨_, _, hx0, hx1, hxsh⟩ := trading_theorem_anchor (G := G) (P := P) hd hG hPS
      le_rfl (by norm_num : (0:ℝ) < 1/4) (by norm_num) le_rfl hsys one_pos hL hLatt hJ hnd
      hall hR₀ hw₀ hbest
    have hsh := hxsh Finset.univ (by simp) (fun _ => 1) (fun _ _ => zero_le_one)
      (by simp [pRet, m])
    refine ⟨R₀, hR₀, _, hx0, hx1, ?_⟩
    rw [hsu, mul_one] at hsh
    exact hsh

end InstanceAnchor


/-! ### Elementary facts used in the text of the trading section -/

section Elementary

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- Choosing `ε = δ − δ²/2` turns the Sharpe guarantee `√(1 − 2ε)` into `1 − δ`. -/
lemma sqrt_one_sub_two_eps_of_delta {δ : ℝ} (h1 : δ ≤ 1) :
    Real.sqrt (1 - 2 * (δ - δ ^ 2 / 2)) = 1 - δ := by
  have h : 1 - 2 * (δ - δ ^ 2 / 2) = (1 - δ) ^ 2 := by ring
  rw [h, Real.sqrt_sq (by linarith)]

/-- **Volatility targeting.** Scaling a portfolio with positive variance by
`λ = σ/√(x'Vx)`, `σ ≥ 0`, gives volatility `σ` and expected excess return `σ·SR(x)`. -/
lemma vol_target (S : Finset ι) (x : ι → ℝ) (hv : 0 < pVar d B Sf S x) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    Real.sqrt (pVar d B Sf S (fun i => (σ / Real.sqrt (pVar d B Sf S x)) * x i)) = σ ∧
    pRet m S (fun i => (σ / Real.sqrt (pVar d B Sf S x)) * x i)
      = σ * sharpe m d B Sf S x := by
  have hs : 0 < Real.sqrt (pVar d B Sf S x) := Real.sqrt_pos.mpr hv
  constructor
  · rw [pVar_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg hσ hs.le)]
    field_simp
  · rw [pRet_smul]
    unfold sharpe
    ring

/-- **Nothing to gain without a positive expected excess return**: if `m ≤ 0` on `S`, every
long-only portfolio on `S` has objective `2m'w − w'Vw ≤ 0`, the objective of holding
nothing. -/
lemma objLO_nonpos_of_nonpos (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {S : Finset ι} {w : ι → ℝ} (hw : ∀ i ∈ S, 0 ≤ w i) (hm : ∀ i ∈ S, m i ≤ 0) :
    objLO m d B Sf S w ≤ 0 := by
  rw [objLO_eq_ret_var]
  have h1 : pRet m S w ≤ 0 := by
    show ∑ i ∈ S, m i * w i ≤ 0
    exact Finset.sum_nonpos fun i hi => mul_nonpos_of_nonpos_of_nonneg (hm i hi) (hw i hi)
  have h2 := pVar_nonneg (B := B) hd hG hPS S w
  linarith

/-- **The a posteriori certificate.** If a value `F` is at least `(1 − 2ε)` times the
objective of every long-only portfolio with at most `k` names, then every such objective is
at most `F/(1 − 2ε)`. -/
lemma obj_le_div_of_guarantee {k : ℕ} {ε F : ℝ} (hε1 : ε < 1 / 2)
    (h : ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
      (1 - 2 * ε) * objLO m d B Sf S' u ≤ F) :
    ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
      objLO m d B Sf S' u ≤ F / (1 - 2 * ε) := by
  intro S' hS' u hu
  have hpos : 0 < 1 - 2 * ε := by linarith
  rw [le_div_iff₀ hpos]
  have h' := h S' hS' u hu
  linarith [mul_comm (objLO m d B Sf S' u) (1 - 2 * ε)]

/-- `k(1 + kω) ≤ k²(1 + ω)` for `k ≥ 1`, `ω ≥ 0`: the covering constant of
`anchorCover_of_sysVar` is at most `k²` times the lower bound `1 + ω` of
`cover_const_ge_asset`. -/
lemma cover_const_le_sq_mul {k : ℕ} (hk : 1 ≤ k) {ω : ℝ} (hω : 0 ≤ ω) :
    (k : ℝ) * (1 + (k : ℝ) * ω) ≤ (k : ℝ) ^ 2 * (1 + ω) := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ k) (by linarith : (0:ℝ) ≤ k - 1),
    mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ k) (by linarith : (0:ℝ) ≤ k - 1)) hω]

end Elementary

end SparseSharpe.Factor
