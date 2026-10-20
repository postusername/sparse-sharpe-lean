import SparseSharpe.Factor.SaddleRounding
import SparseSharpe.Factor.Gordan
import SparseSharpe.Factor.Attain

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Existence of the saddle point and of a vertex with at most `K+1` fractional multipliers

No minimax theorem is used. The proof is direct:

1. `g_k` has a minimizer `t` (`exists_isMin_dualBound`: `g_k ≥ t'Pt` is coercive and continuous);
2. at `t` the finitely many smooth functions `QLO(S,·)`, `|S| = k`, active at the maximum have a convex
   combination of gradients equal to zero (`exists_weights_of_isMin`: Gordan's alternative applied to the
   gradients, and the smoothness estimate `QLO_step` excludes a common descent direction);
3. the multipliers `λ_i = Σ_S μ_S [i ∈ S]` form a saddle point with threshold `σ`
   (`exists_threshold`, `exists_saddle`);
4. among the multipliers with the same `t` and `σ` that differ from `λ` only on the fractional set, a basic
   solution of the `K+1` linear equations has at most `K+1` fractional coordinates
   (`exists_sparse_frac`, `SaddleData.exists_vertex`, `exists_saddle_vertex`).

The end results are `relaxation_rounding` (a support with exactly `k` names and loss `≤ (⌊(K+1)/2⌋ω/k)·G*_k`) and
`relaxation_bicriteria` (a support with at most `k+K` names and value `≥ G*_k`).
-/

namespace SparseSharpe.Factor

open Finset

/-! ### A vertex with few fractional coordinates -/

section Vertex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- **Basic solutions.** If `λ ∈ [0,1]^ι` and `A : ℝ^ι → V` is linear, there is `λ' ∈ [0,1]^ι` with `A λ' = A λ`,
which coincides with `λ` outside the fractional set of `λ`, and has at most `dim V` fractional coordinates. -/
theorem exists_sparse_frac (A : (ι → ℝ) →ₗ[ℝ] V) :
    ∀ (n : ℕ) (lam : ι → ℝ), (∀ i, 0 ≤ lam i ∧ lam i ≤ 1) → (fracSet lam).card = n →
      ∃ lam' : ι → ℝ, (∀ i, 0 ≤ lam' i ∧ lam' i ≤ 1) ∧ A lam' = A lam ∧
        (∀ i, i ∉ fracSet lam → lam' i = lam i) ∧ (fracSet lam').card ≤ Module.finrank ℝ V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro lam hr hn
  set F := fracSet lam with hF
  by_cases hle : F.card ≤ Module.finrank ℝ V
  · exact ⟨lam, hr, rfl, fun _ _ => rfl, hle⟩
  push Not at hle
  -- a nontrivial relation among the columns indexed by `F`
  have hnli : ¬ LinearIndependent ℝ (fun i : ↥F => A (Pi.single (i : ι) (1 : ℝ))) := by
    intro hli
    have := hli.fintype_card_le_finrank
    simp only [Fintype.card_coe] at this
    omega
  rw [Fintype.not_linearIndependent_iff] at hnli
  obtain ⟨g, hg0, i₁, hi₁⟩ := hnli
  set c : ι → ℝ := fun i => if h : i ∈ F then g ⟨i, h⟩ else 0 with hc
  have hcF : ∀ i, i ∉ F → c i = 0 := fun i hi => by simp [hc, hi]
  have hAc : A c = 0 := by
    have h1 : c = ∑ i, c i • (Pi.single i (1 : ℝ) : ι → ℝ) := by
      conv_lhs => rw [← Finset.univ_sum_single c]
      refine Finset.sum_congr rfl fun i _ => ?_
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    have h2 : A c = ∑ i, c i • A (Pi.single i (1 : ℝ)) := by
      conv_lhs => rw [h1]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
    rw [h2]
    have h3 : ∑ i, c i • A (Pi.single i (1 : ℝ)) = ∑ i ∈ F, c i • A (Pi.single i (1 : ℝ)) := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
      rw [hcF i hi, zero_smul]
    rw [h3, ← Finset.sum_coe_sort F]
    simpa [hc] using hg0
  have hc1 : c i₁.1 ≠ 0 := by simpa [hc, i₁.2] using hi₁
  -- the step to the boundary
  set E : Finset ι := F.filter fun i => c i ≠ 0 with hE
  have hEne : E.Nonempty := ⟨i₁.1, Finset.mem_filter.mpr ⟨i₁.2, hc1⟩⟩
  set r : ι → ℝ := fun i => if 0 < c i then (1 - lam i) / c i else lam i / (-c i) with hrdef
  obtain ⟨i₀, hi₀E, hi₀min⟩ := Finset.exists_min_image E r hEne
  have hFpos : ∀ i ∈ F, 0 < lam i ∧ lam i < 1 := fun i hi => mem_fracSet.mp hi
  have hrpos : ∀ i ∈ E, 0 < r i := by
    intro i hi
    obtain ⟨hiF, hci⟩ := Finset.mem_filter.mp hi
    have h := hFpos i hiF
    simp only [hrdef]
    split_ifs with hpos
    · exact div_pos (by linarith [h.2]) hpos
    · have : c i < 0 := lt_of_le_of_ne (not_lt.mp hpos) hci
      exact div_pos h.1 (by linarith)
  set τ : ℝ := r i₀ with hτ
  have hτpos : 0 < τ := hrpos i₀ hi₀E
  set lam' : ι → ℝ := fun i => lam i + τ * c i with hlam'
  have hlam'F : ∀ i, i ∉ F → lam' i = lam i := fun i hi => by simp [hlam', hcF i hi]
  have hcE : ∀ i, i ∈ F → i ∉ E → c i = 0 := fun i hi hn => by
    by_contra h; exact hn (Finset.mem_filter.mpr ⟨hi, h⟩)
  have hr' : ∀ i, 0 ≤ lam' i ∧ lam' i ≤ 1 := by
    intro i
    by_cases hiF : i ∈ F
    · by_cases hiE : i ∈ E
      · have hmin := hi₀min i hiE
        have h := hFpos i hiF
        have hci := (Finset.mem_filter.mp hiE).2
        simp only [hrdef] at hmin
        by_cases hpos : 0 < c i
        · rw [if_pos hpos] at hmin
          have h1 : τ * c i ≤ 1 - lam i := by
            have := (le_div_iff₀ hpos).mp hmin
            linarith
          constructor
          · simp only [hlam']; nlinarith [h.1, mul_pos hτpos hpos]
          · simp only [hlam']; linarith
        · rw [if_neg hpos] at hmin
          have hneg : c i < 0 := lt_of_le_of_ne (not_lt.mp hpos) hci
          have h1 : τ * (-c i) ≤ lam i := by
            have := (le_div_iff₀ (by linarith : 0 < -c i)).mp hmin
            linarith
          constructor
          · simp only [hlam']; linarith
          · simp only [hlam']; nlinarith [h.2, mul_pos hτpos (by linarith : 0 < -c i)]
      · have := hcE i hiF hiE
        simp only [hlam', this, mul_zero, add_zero]
        exact hr i
    · rw [hlam'F i hiF]; exact hr i
  have hAl : A lam' = A lam := by
    have : lam' = lam + τ • c := by funext i; simp [hlam']
    rw [this, map_add, map_smul, hAc, smul_zero, add_zero]
  have hi₀F : i₀ ∈ F := (Finset.mem_filter.mp hi₀E).1
  have hi₀ci : c i₀ ≠ 0 := (Finset.mem_filter.mp hi₀E).2
  have hi₀bdry : lam' i₀ = 0 ∨ lam' i₀ = 1 := by
    have h := hFpos i₀ hi₀F
    show lam i₀ + τ * c i₀ = 0 ∨ lam i₀ + τ * c i₀ = 1
    have hτ' : τ = r i₀ := hτ
    by_cases hpos : 0 < c i₀
    · right
      have : τ = (1 - lam i₀) / c i₀ := by rw [hτ']; simp only [hrdef, if_pos hpos]
      rw [this]
      field_simp
      ring
    · left
      have hneg : c i₀ < 0 := lt_of_le_of_ne (not_lt.mp hpos) hi₀ci
      have : τ = lam i₀ / (-c i₀) := by rw [hτ']; simp only [hrdef, if_neg hpos]
      rw [this]
      field_simp
      ring
  have hsub : fracSet lam' ⊆ F.erase i₀ := by
    intro i hi
    have hi' := mem_fracSet.mp hi
    rw [Finset.mem_erase]
    constructor
    · rintro rfl
      rcases hi₀bdry with h | h <;> linarith [hi'.1, hi'.2]
    · by_contra hiF
      rw [hlam'F i hiF] at hi'
      exact hiF (mem_fracSet.mpr hi')
  have hlt : (fracSet lam').card < n := by
    calc (fracSet lam').card ≤ (F.erase i₀).card := Finset.card_le_card hsub
      _ = F.card - 1 := Finset.card_erase_of_mem hi₀F
      _ < n := by rw [← hn]; have := Finset.card_pos.mpr ⟨i₀, hi₀F⟩; omega
  obtain ⟨lam'', hr'', hAl'', hout'', hcard''⟩ := ih _ hlt lam' hr' rfl
  refine ⟨lam'', hr'', by rw [hAl'', hAl], fun i hi => ?_, hcard''⟩
  have hi' : i ∉ fracSet lam' := fun h => hi (Finset.mem_erase.mp (hsub h)).2
  rw [hout'' i hi', hlam'F i hi]

end Vertex


/-! ### A minimizer of the dual bound -/

section Minimizer

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ} {k : ℕ}

lemma QLO_le_dualBound {S : Finset ι} (hS : S.card ≤ k) (t : κ → ℝ) :
    QLO m d B P S t ≤ dualBound m d B P k t := by
  unfold QLO dualBound
  have := Finset.le_sup' (fun S : Finset ι => ∑ i ∈ S, (max (m i - dotp (B i) t) 0) ^ 2 / d i)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩ :
      S ∈ ((Finset.univ : Finset (Finset ι)).filter fun S => S.card ≤ k))
  linarith

/-- The maximum over supports with at most `k` names is attained at a support with exactly `k` names. -/
lemma exists_card_eq_QLO_eq (hd : ∀ i, 0 < d i) (hk : k ≤ Fintype.card ι) (t : κ → ℝ) :
    ∃ S : Finset ι, S.card = k ∧ QLO m d B P S t = dualBound m d B P k t := by
  classical
  obtain ⟨S', hS', hsup⟩ := Finset.exists_mem_eq_sup' (supportsLe_nonempty (ι := ι) k)
    (fun S : Finset ι => ∑ i ∈ S, (max (m i - dotp (B i) t) 0) ^ 2 / d i)
  have hS'k : S'.card ≤ k := (Finset.mem_filter.mp hS').2
  obtain ⟨S, hSS', hSc⟩ := Finset.exists_superset_card_eq hS'k hk
  refine ⟨S, hSc, le_antisymm (QLO_le_dualBound hSc.le t) ?_⟩
  have h1 : ∑ i ∈ S', (max (m i - dotp (B i) t) 0) ^ 2 / d i
      ≤ ∑ i ∈ S, (max (m i - dotp (B i) t) 0) ^ 2 / d i :=
    Finset.sum_le_sum_of_subset_of_nonneg hSS' fun i _ _ => div_nonneg (sq_nonneg _) (hd i).le
  unfold QLO dualBound
  rw [hsup]
  linarith

lemma continuous_quadf (C : κ → κ → ℝ) : Continuous fun t : κ → ℝ => quadf C t := by
  unfold quadf
  fun_prop

lemma continuous_dualBound : Continuous fun t : κ → ℝ => dualBound m d B P k t := by
  unfold dualBound
  refine (continuous_quadf P).add ?_
  refine Continuous.finset_sup'_apply (supportsLe_nonempty (ι := ι) k) fun S _ => ?_
  refine continuous_finsetSum _ fun i _ => ?_
  have := continuous_dotp (B i)
  fun_prop

/-- Coordinates are controlled by the quadratic form: `t_j² ≤ C_j · t'Pt`. -/
lemma coord_sq_le (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (j : κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : κ → ℝ, t j ^ 2 ≤ C * quadf P t := by
  have hSP := SP_of_PS (P := P) (Sf := Sf) hPS
  refine ⟨∑ l, (∑ l', Sf j l' * G l l') ^ 2, Finset.sum_nonneg fun _ _ => sq_nonneg _, fun t => ?_⟩
  have hrep : t j = ∑ l, (∑ l', Sf j l' * G l l') * dotp (G l) t := by
    have h1 : ∀ l, (∑ l', Sf j l' * G l l') * dotp (G l) t
        = ∑ l', ∑ j', Sf j l' * (G l l' * G l j') * t j' := by
      intro l
      simp only [dotp]
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun l' _ => Finset.sum_congr rfl fun j' _ => by ring
    rw [Finset.sum_congr rfl fun l _ => h1 l, Finset.sum_comm]
    have h2 : ∀ l', ∑ l, ∑ j', Sf j l' * (G l l' * G l j') * t j'
        = ∑ j', Sf j l' * P l' j' * t j' := by
      intro l'
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [← hG l' j', Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun l' _ => h2 l', Finset.sum_comm]
    have h3 : ∀ j', ∑ l', Sf j l' * P l' j' * t j' = (if j = j' then 1 else 0) * t j' := by
      intro j'
      rw [← hSP j j', Finset.sum_mul]
    rw [Finset.sum_congr rfl fun j' _ => h3 j']
    simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ∑ l', Sf j l' * G l l')
    (fun l => dotp (G l) t)
  rw [← hrep] at hcs
  rw [quadf_eq_sum_sq hG]
  exact hcs

lemma norm_sq_le_quadf (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : κ → ℝ, ‖t‖ ^ 2 ≤ C * quadf P t := by
  choose C hC0 hC using fun j => coord_sq_le (P := P) (G := G) (Sf := Sf) hG hPS j
  refine ⟨∑ j, C j + 1, by linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hC0 j], fun t => ?_⟩
  have hq : 0 ≤ quadf P t := quadf_nonneg_of_root hG t
  have hnorm : ‖t‖ ^ 2 ≤ ∑ j, t j ^ 2 := by
    have hS0 : 0 ≤ ∑ j, t j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have : ‖t‖ ≤ Real.sqrt (∑ j, t j ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
      rw [Real.norm_eq_abs]
      exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => t j ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ j))
    calc ‖t‖ ^ 2 ≤ Real.sqrt (∑ j, t j ^ 2) ^ 2 := by gcongr
      _ = ∑ j, t j ^ 2 := Real.sq_sqrt hS0
  calc ‖t‖ ^ 2 ≤ ∑ j, t j ^ 2 := hnorm
    _ ≤ ∑ j, C j * quadf P t := Finset.sum_le_sum fun j _ => hC j t
    _ = (∑ j, C j) * quadf P t := by rw [Finset.sum_mul]
    _ ≤ (∑ j, C j + 1) * quadf P t := by nlinarith

lemma quadf_le_dualBound (t : κ → ℝ) : quadf P t ≤ dualBound m d B P k t := by
  unfold dualBound
  have := Finset.le_sup' (fun S : Finset ι => ∑ i ∈ S, (max (m i - dotp (B i) t) 0) ^ 2 / d i)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ ∅, by simp⟩ :
      (∅ : Finset ι) ∈ ((Finset.univ : Finset (Finset ι)).filter fun S => S.card ≤ k))
  simp only [Finset.sum_empty] at this
  linarith

/-- **The dual bound has a minimizer** (`G*_k = min_t g_k(t)`). -/
theorem exists_isMin_dualBound [Nonempty κ] (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) :
    ∃ t : κ → ℝ, ∀ t', dualBound m d B P k t ≤ dualBound m d B P k t' := by
  obtain ⟨C, hC, hCt⟩ := norm_sq_le_quadf (P := P) (G := G) (Sf := Sf) hG hPS
  refine Continuous.exists_forall_le (continuous_dualBound (m := m) (d := d) (B := B) (P := P) (k := k)) ?_
  have h1 : Filter.Tendsto (fun t : κ → ℝ => ‖t‖ ^ 2 / C) (Filter.cocompact (κ → ℝ)) Filter.atTop :=
    (((Filter.tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cocompact_atTop).atTop_div_const hC)
  refine Filter.tendsto_atTop_mono (fun t => ?_) h1
  have := hCt t
  have h2 : ‖t‖ ^ 2 / C ≤ quadf P t := by rw [div_le_iff₀ hC]; linarith
  exact h2.trans (quadf_le_dualBound t)

end Minimizer


/-! ### First-order condition at a minimizer of the dual bound -/

section FirstOrder

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ} {k : ℕ}

/-- Minus half the gradient of `QLO(S, ·)` at `t`: `a_S(t) = B_S' w(t) − P t`. -/
noncomputable def gradVec (m d : ι → ℝ) (B : ι → κ → ℝ) (P : κ → κ → ℝ) (S : Finset ι) (t : κ → ℝ) :
    κ → ℝ :=
  fun j => Bw B S (wclip m d B t) j - ∑ j', P j j' * t j'

open scoped Classical in
/-- The `k`-subsets at which the maximum defining `g_k(t)` is attained. -/
noncomputable def activeSets (m d : ι → ℝ) (B : ι → κ → ℝ) (P : κ → κ → ℝ) (k : ℕ) (t : κ → ℝ) :
    Finset (Finset ι) :=
  (Finset.univ : Finset (Finset ι)).filter fun S => S.card = k ∧ QLO m d B P S t = dualBound m d B P k t

lemma mem_activeSets {S : Finset ι} {t : κ → ℝ} :
    S ∈ activeSets m d B P k t ↔ S.card = k ∧ QLO m d B P S t = dualBound m d B P k t := by
  classical
  simp [activeSets]

lemma cross_eq (hG : ∀ j j', ∑ l, G l j * G l j' = P j j') (t h : κ → ℝ) :
    ∑ j, ∑ j', P j j' * (t j * h j') = ∑ j, (∑ j', P j j' * t j') * h j := by
  have hPsymm := P_symm_of_root (P := P) (G := G) hG
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j' _ => by rw [hPsymm j' j]; ring

/-- The one-sided expansion: `QLO(S, t + εh) ≤ QLO(S,t) − 2ε⟨a_S(t), h⟩ + ε²·c_S`. -/
lemma QLO_step (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (S : Finset ι) (t h : κ → ℝ) (ε : ℝ) :
    QLO m d B P S (t + ε • h)
      ≤ QLO m d B P S t - 2 * ε * dotp (gradVec m d B P S t) h
        + ε ^ 2 * ((1 + levSum d B Sf S) * quadf P h) := by
  have hsm := QLO_smooth (m := m) (d := d) (B := B) (Sf := Sf) hd hG hPS S t (ε • h)
  have e1 : quadf P (ε • h) = ε ^ 2 * quadf P h := quadf_smul ε h
  have e2 : ∑ j, ∑ j', P j j' * (t j * (ε • h) j') = ε * ∑ j, ∑ j', P j j' * (t j * h j') := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j' _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  have e3 : ∑ j, Bw B S (wclip m d B t) j * (ε • h) j = ε * ∑ j, Bw B S (wclip m d B t) j * h j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  have e4 : dotp (gradVec m d B P S t) h
      = ∑ j, Bw B S (wclip m d B t) j * h j - ∑ j, ∑ j', P j j' * (t j * h j') := by
    rw [cross_eq hG t h]
    simp only [dotp, gradVec, sub_mul, Finset.sum_sub_distrib]
  rw [e1, e2, e3] at hsm
  rw [e4]
  nlinarith [hsm]

lemma exists_pos_le_of_pos {α : Type*} (X : Finset α) (φ : α → ℝ) (hφ : ∀ x ∈ X, 0 < φ x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ X, δ ≤ φ x := by
  by_cases hne : X.Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ := Finset.exists_min_image X φ hne
    exact ⟨φ x₀, hφ x₀ hx₀, hmin⟩
  · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩

/-- **First-order condition.** At a minimizer `t` of `g_k` there are weights `μ` on the active `k`-subsets
(`QLO(S,t) = g_k(t)`) with `Σ μ_S a_S(t) = 0`, `Σ μ_S = 1`, `μ ≥ 0`. -/
theorem exists_weights_of_isMin [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (hk : k ≤ Fintype.card ι)
    {t : κ → ℝ} (hmin : ∀ t', dualBound m d B P k t ≤ dualBound m d B P k t') :
    ∃ μ : Finset ι → ℝ, (∀ S ∈ activeSets m d B P k t, 0 ≤ μ S) ∧ ∑ S ∈ activeSets m d B P k t, μ S = 1 ∧
      ∀ j, ∑ S ∈ activeSets m d B P k t, μ S * gradVec m d B P S t j = 0 := by
  classical
  set g := dualBound m d B P k t with hg
  set U := activeSets m d B P k t with hU
  have hUne : U.Nonempty := by
    obtain ⟨S, hS, hQ⟩ := exists_card_eq_QLO_eq (m := m) (d := d) (B := B) (P := P) hd hk t
    exact ⟨S, mem_activeSets.mpr ⟨hS, hQ⟩⟩
  rcases gordan (fun S : Finset ι => gradVec m d B P S t) U with ⟨h, hh⟩ | hw
  swap
  · exact hw
  exfalso
  set 𝒮 : Finset (Finset ι) := (Finset.univ : Finset (Finset ι)).filter fun S => S.card = k with h𝒮
  have hU𝒮 : ∀ S ∈ U, S ∈ 𝒮 := fun S hS => by
    rw [h𝒮, Finset.mem_filter]; exact ⟨Finset.mem_univ _, (mem_activeSets.mp hS).1⟩
  -- the constants of the step
  obtain ⟨δ, hδ, hδU⟩ := exists_pos_le_of_pos U (fun S => dotp (gradVec m d B P S t) h) hh
  obtain ⟨γ, hγ, hγU⟩ := exists_pos_le_of_pos (𝒮.filter fun S => S ∉ U) (fun S => g - QLO m d B P S t) (by
    intro S hS
    obtain ⟨hS𝒮, hSU⟩ := Finset.mem_filter.mp hS
    have hSc : S.card = k := (Finset.mem_filter.mp hS𝒮).2
    have hle := QLO_le_dualBound (m := m) (d := d) (B := B) (P := P) (k := k) hSc.le t
    have hne : QLO m d B P S t ≠ g := fun h => hSU (mem_activeSets.mpr ⟨hSc, h⟩)
    simpa using lt_of_le_of_ne hle hne)
  set A : ℝ := ∑ S ∈ 𝒮, |dotp (gradVec m d B P S t) h| with hA
  set C₀ : ℝ := ∑ S ∈ 𝒮, (1 + levSum d B Sf S) * quadf P h with hC₀
  have hqh : 0 ≤ quadf P h := quadf_nonneg_of_root hG h
  have hcnn : ∀ S ∈ 𝒮, 0 ≤ (1 + levSum d B Sf S) * quadf P h := fun S _ =>
    mul_nonneg (by linarith [levSum_nonneg (B := B) hd hG hPS S]) hqh
  have hC₀0 : 0 ≤ C₀ := Finset.sum_nonneg hcnn
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcle : ∀ S ∈ 𝒮, (1 + levSum d B Sf S) * quadf P h ≤ C₀ := fun S hS =>
    Finset.single_le_sum (f := fun S => (1 + levSum d B Sf S) * quadf P h) hcnn hS
  have hAle : ∀ S ∈ 𝒮, |dotp (gradVec m d B P S t) h| ≤ A := fun S hS =>
    Finset.single_le_sum (f := fun S => |dotp (gradVec m d B P S t) h|) (fun _ _ => abs_nonneg _) hS
  set ε : ℝ := min 1 (min (δ / (C₀ + 1)) (γ / (2 * A + C₀ + 1))) with hε
  have hεpos : 0 < ε := by
    refine lt_min one_pos (lt_min (div_pos hδ (by linarith)) (div_pos hγ (by linarith)))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε * (C₀ + 1) ≤ δ := by
    have : ε ≤ δ / (C₀ + 1) := (min_le_right _ _).trans (min_le_left _ _)
    rwa [le_div_iff₀ (by linarith)] at this
  have hε3 : ε * (2 * A + C₀ + 1) ≤ γ := by
    have : ε ≤ γ / (2 * A + C₀ + 1) := (min_le_right _ _).trans (min_le_right _ _)
    rwa [le_div_iff₀ (by linarith)] at this
  -- every `k`-subset is strictly below `g(t)` after the step
  have hall : ∀ S ∈ 𝒮, QLO m d B P S (t + ε • h) < g := by
    intro S hS
    have hSc : S.card = k := (Finset.mem_filter.mp hS).2
    have hstep := QLO_step (m := m) (d := d) (B := B) (Sf := Sf) hd hG hPS S t h ε
    have hc := hcle S hS
    have hQle := QLO_le_dualBound (m := m) (d := d) (B := B) (P := P) (k := k) hSc.le t
    by_cases hSU : S ∈ U
    · have hQ : QLO m d B P S t = g := (mem_activeSets.mp hSU).2
      have hdl := hδU S hSU
      have h1 : ε ^ 2 * ((1 + levSum d B Sf S) * quadf P h) ≤ ε ^ 2 * C₀ :=
        mul_le_mul_of_nonneg_left hc (sq_nonneg _)
      nlinarith [mul_pos hεpos hδ, mul_pos hεpos hεpos, mul_nonneg hεpos.le hC₀0]
    · have hγS := hγU S (Finset.mem_filter.mpr ⟨hS, hSU⟩)
      have hab := hAle S hS
      have h1 : ε ^ 2 * ((1 + levSum d B Sf S) * quadf P h) ≤ ε * C₀ := by
        calc ε ^ 2 * ((1 + levSum d B Sf S) * quadf P h) ≤ ε ^ 2 * C₀ :=
              mul_le_mul_of_nonneg_left hc (sq_nonneg _)
          _ ≤ ε * C₀ := by nlinarith [mul_nonneg hεpos.le hC₀0]
      have h2 : -(2 * ε * dotp (gradVec m d B P S t) h) ≤ 2 * ε * A := by
        have := neg_abs_le (dotp (gradVec m d B P S t) h)
        nlinarith [mul_le_mul_of_nonneg_left hab hεpos.le, abs_nonneg (dotp (gradVec m d B P S t) h)]
      nlinarith [mul_pos hεpos hεpos]
  obtain ⟨S', hS'c, hS'Q⟩ := exists_card_eq_QLO_eq (m := m) (d := d) (B := B) (P := P) hd hk (t + ε • h)
  have hS'𝒮 : S' ∈ 𝒮 := by rw [h𝒮, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hS'c⟩
  have := hall S' hS'𝒮
  rw [hS'Q] at this
  exact absurd (hmin (t + ε • h)) (not_le.mpr this)

end FirstOrder


/-! ### The common threshold of the maximizing `k`-subsets -/

section Threshold

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exchange: in a maximizing `k`-subset every inside value is at least every outside value. -/
lemma swap_le {v : ι → ℝ} {k : ℕ} {S : Finset ι} (hSc : S.card = k)
    (hopt : ∀ S' : Finset ι, S'.card = k → ∑ i ∈ S', v i ≤ ∑ i ∈ S, v i) {i j : ι} (hi : i ∈ S) (hj : j ∉ S) :
    v j ≤ v i := by
  have hS' : (insert j (S.erase i)).card = k := by
    rw [Finset.card_insert_of_notMem (fun h => hj (Finset.mem_of_mem_erase h)), Finset.card_erase_of_mem hi]
    have : 0 < S.card := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  have h := hopt _ hS'
  rw [Finset.sum_insert (fun h => hj (Finset.mem_of_mem_erase h))] at h
  have h2 := Finset.add_sum_erase S v hi
  linarith

/-- **All maximizing `k`-subsets cut at one threshold.** -/
lemma exists_threshold {v : ι → ℝ} {k : ℕ} (hk : 1 ≤ k) (hv : ∀ i, 0 ≤ v i) (U : Finset (Finset ι))
    (hU : U.Nonempty) (hcard : ∀ S ∈ U, S.card = k)
    (hopt : ∀ S ∈ U, ∀ S' : Finset ι, S'.card = k → ∑ i ∈ S', v i ≤ ∑ i ∈ S, v i) :
    ∃ σ : ℝ, 0 ≤ σ ∧ ∀ S ∈ U, (∀ i ∈ S, σ ≤ v i) ∧ (∀ j ∉ S, v j ≤ σ) := by
  obtain ⟨S₀, hS₀⟩ := hU
  have hne : S₀.Nonempty := Finset.card_pos.mp (by rw [hcard S₀ hS₀]; omega)
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image S₀ v hne
  refine ⟨v i₀, hv i₀, fun S hS => ⟨fun i hi => ?_, fun j hj => ?_⟩⟩
  · by_contra hlt
    push Not at hlt
    have hiS₀ : i ∉ S₀ := fun h => absurd (hmin i h) (not_le.mpr hlt)
    have hsub : S₀ ⊆ S := by
      intro i' hi'
      by_contra hi'S
      have := swap_le (hcard S hS) (hopt S hS) hi hi'S
      linarith [hmin i' hi']
    have heq : S₀ = S := Finset.eq_of_subset_of_card_le hsub (by rw [hcard S hS, hcard S₀ hS₀])
    exact hiS₀ (heq ▸ hi)
  · by_contra hlt
    push Not at hlt
    have hjS₀ : j ∈ S₀ := by
      by_contra h
      have := swap_le (hcard S₀ hS₀) (hopt S₀ hS₀) hi₀ h
      linarith
    have hnsub : ¬ S ⊆ S₀ := by
      intro hsub
      have heq : S = S₀ := Finset.eq_of_subset_of_card_le hsub (by rw [hcard S hS, hcard S₀ hS₀])
      exact hj (heq ▸ hjS₀)
    obtain ⟨i, hiS, hiS₀⟩ := Finset.not_subset.mp hnsub
    have h1 := swap_le (hcard S hS) (hopt S hS) hiS hj
    have h2 := swap_le (hcard S₀ hS₀) (hopt S₀ hS₀) hi₀ hiS₀
    linarith

end Threshold


/-! ### Multipliers from weights on subsets -/

section Weights

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `λ_i = Σ_S μ_S·[i ∈ S]`. -/
noncomputable def lamOf (U : Finset (Finset ι)) (μ : Finset ι → ℝ) (i : ι) : ℝ :=
  ∑ S ∈ U, μ S * (if i ∈ S then 1 else 0)

variable {U : Finset (Finset ι)} {μ : Finset ι → ℝ}

lemma lamOf_nonneg (hμ0 : ∀ S ∈ U, 0 ≤ μ S) (i : ι) : 0 ≤ lamOf U μ i :=
  Finset.sum_nonneg fun S hS => mul_nonneg (hμ0 S hS) (by split_ifs <;> norm_num)

lemma one_sub_lamOf (hμ1 : ∑ S ∈ U, μ S = 1) (i : ι) :
    1 - lamOf U μ i = ∑ S ∈ U, μ S * (if i ∈ S then 0 else 1) := by
  unfold lamOf
  calc 1 - ∑ S ∈ U, μ S * (if i ∈ S then (1 : ℝ) else 0)
      = ∑ S ∈ U, μ S - ∑ S ∈ U, μ S * (if i ∈ S then (1 : ℝ) else 0) := by rw [hμ1]
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun S _ => ?_
      split_ifs <;> ring

lemma lamOf_le_one (hμ0 : ∀ S ∈ U, 0 ≤ μ S) (hμ1 : ∑ S ∈ U, μ S = 1) (i : ι) : lamOf U μ i ≤ 1 := by
  have := one_sub_lamOf hμ1 i
  have h0 : 0 ≤ ∑ S ∈ U, μ S * (if i ∈ S then 0 else 1) :=
    Finset.sum_nonneg fun S hS => mul_nonneg (hμ0 S hS) (by split_ifs <;> norm_num)
  linarith

lemma sum_lamOf {k : ℕ} (hμ1 : ∑ S ∈ U, μ S = 1) (hcard : ∀ S ∈ U, S.card = k) :
    ∑ i, lamOf U μ i = k := by
  unfold lamOf
  rw [Finset.sum_comm]
  have : ∀ S ∈ U, ∑ i, μ S * (if i ∈ S then (1 : ℝ) else 0) = μ S * k := by
    intro S hS
    rw [← Finset.mul_sum]
    congr 1
    rw [← hcard S hS]
    simp
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul, hμ1, one_mul]

lemma exists_pos_weight (hμ0 : ∀ S ∈ U, 0 ≤ μ S) (hμ1 : ∑ S ∈ U, μ S = 1) : ∃ S ∈ U, 0 < μ S := by
  have : ∑ S ∈ U, μ S ≠ 0 := by rw [hμ1]; exact one_ne_zero
  obtain ⟨S, hS, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero this
  exact ⟨S, hS, lt_of_le_of_ne (hμ0 S hS) (Ne.symm hne)⟩

lemma exists_mem_of_lamOf_pos (hμ0 : ∀ S ∈ U, 0 ≤ μ S) {i : ι} (h : 0 < lamOf U μ i) :
    ∃ S ∈ U, 0 < μ S ∧ i ∈ S := by
  have hne : lamOf U μ i ≠ 0 := h.ne'
  obtain ⟨S, hS, hSne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  by_cases hi : i ∈ S
  · refine ⟨S, hS, ?_, hi⟩
    simp only [hi, if_true, mul_one] at hSne
    exact lt_of_le_of_ne (hμ0 S hS) (Ne.symm hSne)
  · simp [hi] at hSne

lemma exists_not_mem_of_lamOf_lt_one (hμ0 : ∀ S ∈ U, 0 ≤ μ S) (hμ1 : ∑ S ∈ U, μ S = 1) {i : ι}
    (h : lamOf U μ i < 1) : ∃ S ∈ U, 0 < μ S ∧ i ∉ S := by
  have hne : ∑ S ∈ U, μ S * (if i ∈ S then 0 else 1) ≠ 0 := by
    rw [← one_sub_lamOf hμ1]; linarith
  obtain ⟨S, hS, hSne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  by_cases hi : i ∈ S
  · simp [hi] at hSne
  · refine ⟨S, hS, ?_, hi⟩
    simp only [hi, if_false, mul_one] at hSne
    exact lt_of_le_of_ne (hμ0 S hS) (Ne.symm hSne)

lemma mem_of_lamOf_eq_one (hμ0 : ∀ S ∈ U, 0 ≤ μ S) (hμ1 : ∑ S ∈ U, μ S = 1) {i : ι}
    (h : lamOf U μ i = 1) : ∀ S ∈ U, 0 < μ S → i ∈ S := by
  intro S hS hpos
  by_contra hi
  have h1 := one_sub_lamOf hμ1 i
  have h2 : μ S * (if i ∈ S then (0 : ℝ) else 1) ≤ ∑ S ∈ U, μ S * (if i ∈ S then (0 : ℝ) else 1) :=
    Finset.single_le_sum (f := fun S => μ S * (if i ∈ S then (0 : ℝ) else 1))
      (fun S hS => mul_nonneg (hμ0 S hS) (by split_ifs <;> norm_num)) hS
  simp only [hi, if_false, mul_one] at h2
  rw [h] at h1
  linarith

lemma not_mem_of_lamOf_eq_zero (hμ0 : ∀ S ∈ U, 0 ≤ μ S) {i : ι}
    (h : lamOf U μ i = 0) : ∀ S ∈ U, 0 < μ S → i ∉ S := by
  intro S hS hpos hi
  have h2 : μ S * (if i ∈ S then (1 : ℝ) else 0) ≤ lamOf U μ i :=
    Finset.single_le_sum (f := fun S => μ S * (if i ∈ S then (1 : ℝ) else 0))
      (fun S hS => mul_nonneg (hμ0 S hS) (by split_ifs <;> norm_num)) hS
  simp only [hi, if_true, mul_one] at h2
  linarith

/-- `Σ_S μ_S Σ_{i∈S} f_i = Σ_i λ_i f_i`. -/
lemma sum_weights_swap (f : ι → ℝ) : ∑ S ∈ U, μ S * ∑ i ∈ S, f i = ∑ i, lamOf U μ i * f i := by
  unfold lamOf
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  have : ∀ i, μ S * (if i ∈ S then (1 : ℝ) else 0) * f i = if i ∈ S then μ S * f i else 0 :=
    fun i => by split_ifs <;> ring
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

end Weights


/-! ### Existence of a saddle point -/

section Saddle

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ} {k : ℕ}

/-- **Existence of a saddle point of the Lagrangian** `L(t, λ) = t'Pt + Σ λ_i s_i(t)` over `Λ_k × ℝ^K`
(for `1 ≤ k ≤ M`): a minimizer `t` of `g_k` and multipliers `λ` with the conditions of `SaddleData`. -/
theorem exists_saddle [Nonempty κ] (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (hk1 : 1 ≤ k)
    (hk : k ≤ Fintype.card ι) :
    ∃ (t : κ → ℝ) (lam : ι → ℝ) (σ : ℝ), (∀ t', dualBound m d B P k t ≤ dualBound m d B P k t') ∧
      SaddleData m d B P k t lam σ ∧ 0 ≤ σ := by
  classical
  obtain ⟨t, hmin⟩ := exists_isMin_dualBound (m := m) (d := d) (B := B) (P := P) (G := G) (Sf := Sf)
    (k := k) hG hPS
  obtain ⟨μ, hμ0, hμ1, hμ⟩ := exists_weights_of_isMin hd hG hPS hk hmin
  set U := activeSets m d B P k t with hU
  have hcard : ∀ S ∈ U, S.card = k := fun S hS => (mem_activeSets.mp hS).1
  obtain ⟨S₁, hS₁, hpos₁⟩ := exists_pos_weight hμ0 hμ1
  have hQ : ∀ S : Finset ι, QLO m d B P S t = quadf P t + ∑ i ∈ S, clipScore m d B t i := fun S => rfl
  have hopt : ∀ S ∈ U, ∀ S' : Finset ι, S'.card = k →
      ∑ i ∈ S', clipScore m d B t i ≤ ∑ i ∈ S, clipScore m d B t i := by
    intro S hS S' hS'
    have h1 := QLO_le_dualBound (m := m) (d := d) (B := B) (P := P) (k := k) hS'.le t
    have h2 := (mem_activeSets.mp hS).2
    rw [hQ] at h1 h2
    linarith
  obtain ⟨σ, hσ0, hσ⟩ := exists_threshold (v := clipScore m d B t) hk1 (fun i => clipScore_nonneg hd t i)
    U ⟨S₁, hS₁⟩ hcard hopt
  refine ⟨t, lamOf U μ, σ, hmin, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hσ0⟩
  · exact fun i => ⟨lamOf_nonneg hμ0 i, lamOf_le_one hμ0 hμ1 i⟩
  · exact sum_lamOf hμ1 hcard
  · intro j
    have h1 : ∑ S ∈ U, μ S * (Bw B S (wclip m d B t) j - ∑ j', P j j' * t j') = 0 := hμ j
    have h2 : ∑ S ∈ U, μ S * Bw B S (wclip m d B t) j = ∑ i, lamOf U μ i * (wclip m d B t i * B i j) := by
      rw [← sum_weights_swap (U := U) (μ := μ)]
      refine Finset.sum_congr rfl fun S _ => ?_
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    have h3 : ∑ S ∈ U, μ S * (∑ j', P j j' * t j') = ∑ j', P j j' * t j' := by
      rw [← Finset.sum_mul, hμ1, one_mul]
    simp only [mul_sub, Finset.sum_sub_distrib] at h1
    rw [h3] at h1
    have h4 : ∑ S ∈ U, μ S * Bw B S (wclip m d B t) j = ∑ j', P j j' * t j' := by linarith
    rw [← h4, h2]
    exact Finset.sum_congr rfl fun i _ => by ring
  · intro i hi
    exact (hσ S₁ hS₁).1 i (mem_of_lamOf_eq_one hμ0 hμ1 hi S₁ hS₁ hpos₁)
  · intro i hi
    exact (hσ S₁ hS₁).2 i (not_mem_of_lamOf_eq_zero hμ0 hi S₁ hS₁ hpos₁)
  · intro i h0 h1
    obtain ⟨S, hS, -, hiS⟩ := exists_mem_of_lamOf_pos hμ0 h0
    obtain ⟨S', hS', -, hiS'⟩ := exists_not_mem_of_lamOf_lt_one hμ0 hμ1 h1
    exact le_antisymm ((hσ S' hS').2 i hiS') ((hσ S hS).1 i hiS)


/-- The linear map `λ ↦ (Σ_i λ_i w_i(t) B_i, Σ_i λ_i)` whose fibres are the multipliers of a saddle point. -/
noncomputable def stationarityMap (m d : ι → ℝ) (B : ι → κ → ℝ) (t : κ → ℝ) :
    (ι → ℝ) →ₗ[ℝ] (κ → ℝ) × ℝ where
  toFun lam := (fun j => ∑ i, lam i * wclip m d B t i * B i j, ∑ i, lam i)
  map_add' x y := by
    ext j
    · simp [add_mul, Finset.sum_add_distrib]
    · simp [Finset.sum_add_distrib]
  map_smul' c x := by
    ext j
    · simp [Finset.mul_sum, mul_assoc]
    · simp [Finset.mul_sum]

variable {t : κ → ℝ} {lam : ι → ℝ} {σ : ℝ}

/-- **A saddle point with at most `K+1` fractional multipliers.** From any saddle data one passes to a
vertex of the fibre of `stationarityMap` (a basic solution), keeping `t` and `σ`. -/
theorem SaddleData.exists_vertex (hS : SaddleData m d B P k t lam σ) :
    ∃ lam' : ι → ℝ, SaddleData m d B P k t lam' σ ∧ (fracSet lam').card ≤ Fintype.card κ + 1 := by
  classical
  obtain ⟨lam', hr', hA, hout, hcard⟩ := exists_sparse_frac (stationarityMap m d B t) _ lam hS.range rfl
  have hfr : Module.finrank ℝ ((κ → ℝ) × ℝ) = Fintype.card κ + 1 := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_self]
  have hA1 : ∀ j, ∑ i, lam' i * wclip m d B t i * B i j = ∑ i, lam i * wclip m d B t i * B i j := fun j =>
    congrFun (congrArg Prod.fst hA) j
  have hA2 : ∑ i, lam' i = ∑ i, lam i := congrArg Prod.snd hA
  have hfsub : ∀ i, i ∈ fracSet lam' → i ∈ fracSet lam := by
    intro i hi
    by_contra hni
    have h := mem_fracSet.mp hi
    rw [hout i hni] at h
    exact hni (mem_fracSet.mpr h)
  refine ⟨lam', ⟨hr', by rw [hA2]; exact hS.sum, fun j => by rw [hA1 j]; exact hS.stat j, ?_, ?_, ?_⟩,
    hcard.trans_eq hfr⟩
  · intro i hi
    by_cases hF : i ∈ fracSet lam
    · have := mem_fracSet.mp hF
      exact (hS.frac i this.1 this.2).ge
    · rw [hout i hF] at hi
      exact hS.one i hi
  · intro i hi
    by_cases hF : i ∈ fracSet lam
    · have := mem_fracSet.mp hF
      exact (hS.frac i this.1 this.2).le
    · rw [hout i hF] at hi
      exact hS.zero i hi
  · intro i h0 h1
    have := mem_fracSet.mp (hfsub i (mem_fracSet.mpr ⟨h0, h1⟩))
    exact hS.frac i this.1 this.2

/-- **Existence of a saddle point with at most `K+1` fractional multipliers.** -/
theorem exists_saddle_vertex [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (hk1 : 1 ≤ k)
    (hk : k ≤ Fintype.card ι) :
    ∃ (t : κ → ℝ) (lam : ι → ℝ) (σ : ℝ), (∀ t', dualBound m d B P k t ≤ dualBound m d B P k t') ∧
      SaddleData m d B P k t lam σ ∧ 0 ≤ σ ∧ (fracSet lam).card ≤ Fintype.card κ + 1 := by
  obtain ⟨t, lam, σ, hmin, hS, hσ⟩ := exists_saddle (Sf := Sf) (G := G) hd hG hPS hk1 hk
  obtain ⟨lam', hS', hcard⟩ := hS.exists_vertex
  exact ⟨t, lam', σ, hmin, hS', hσ, hcard⟩


/-- **The relaxation rounds to a portfolio on exactly `k` names (Theorem 3.2, unconditional form).** If
`B_i'Σ_fB_i/d_i ≤ ω` for all `i`, there are a minimizer `t` of `g_k` (so `g_k(t) = G*_k ≥ OPT_LO(k)`) and a
support `R`, `|R| = k`, such that the clipped portfolio `w(t)` on `R` satisfies
`G*_k − obj(R, w(t)) ≤ (⌊(K+1)/2⌋ω/k)·G*_k`. -/
theorem relaxation_rounding [Nonempty κ] (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (hk1 : 1 ≤ k)
    (hk : k ≤ Fintype.card ι) {ω : ℝ} (hω0 : 0 ≤ ω) (hω : ∀ i, sysVar B Sf i / d i ≤ ω) :
    ∃ (t : κ → ℝ) (R : Finset ι), (∀ t', dualBound m d B P k t ≤ dualBound m d B P k t') ∧
      (∀ S : Finset ι, S.card ≤ k → ∀ w : ι → ℝ, (∀ i ∈ S, 0 ≤ w i) →
        objLO m d B Sf S w ≤ dualBound m d B P k t) ∧
      R.card = k ∧ (∀ i ∈ R, 0 ≤ wclip m d B t i) ∧
      dualBound m d B P k t - objLO m d B Sf R (wclip m d B t)
        ≤ ((((Fintype.card κ + 1) / 2 : ℕ) : ℝ) * ω / k) * dualBound m d B P k t := by
  obtain ⟨t, lam, σ, hmin, hS, hσ, hf⟩ := exists_saddle_vertex (m := m) (B := B) (Sf := Sf) (G := G) hd hG hPS hk1 hk
  obtain ⟨s, hs, -⟩ := hS.exists_s
  obtain ⟨T, -, -, hcard, hmain, hK, hchain⟩ := saddle_rounding_K hd hG hPS hS hσ hω0
    (fun i _ => hω i) hs hk1 hf
  exact ⟨t, oneSet lam ∪ T, hmin,
    fun S hS' w hw => objLO_le_dualBound (m := m) (B := B) (Sf := Sf) (P := P) (G := G) hd hG hPS hS' hw t,
    hcard, fun i _ => wclip_nonneg hd t i, hmain.trans (hK.trans hchain)⟩

/-- **The rounding, with the Sharpe-ratio guarantee.** If `⌊(K+1)/2⌋ω < k` and some long-only portfolio with at most `k`
names has a positive objective (`OPT_LO(k) > 0`), there are a minimizer `t` of `g_k` and a support `R` with `|R| = k`
such that the fully invested portfolio `x = w(t)|_R/Σ_R w(t)` has Sharpe ratio at least `√(1 − ⌊(K+1)/2⌋ω/k)` times
that of every long-only portfolio with at most `k` names and positive expected excess return. -/
theorem relaxation_rounding_sharpe [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (hk1 : 1 ≤ k)
    (hk : k ≤ Fintype.card ι) {ω : ℝ} (hω0 : 0 ≤ ω) (hω : ∀ i, sysVar B Sf i / d i ≤ ω)
    (hKω : (((Fintype.card κ + 1) / 2 : ℕ) : ℝ) * ω < k)
    (hopt : ∃ S₀ : Finset ι, S₀.card ≤ k ∧ ∃ w₀ : ι → ℝ, (∀ i ∈ S₀, 0 ≤ w₀ i) ∧ 0 < objLO m d B Sf S₀ w₀) :
    ∃ (t : κ → ℝ) (R : Finset ι), (∀ t', dualBound m d B P k t ≤ dualBound m d B P k t') ∧ R.card = k ∧
      (1 - (((Fintype.card κ + 1) / 2 : ℕ) : ℝ) * ω / k) * dualBound m d B P k t ≤ objLO m d B Sf R (wclip m d B t) ∧
      (∀ i ∈ R, 0 ≤ (∑ j ∈ R, wclip m d B t j)⁻¹ * wclip m d B t i) ∧
      ∑ i ∈ R, (∑ j ∈ R, wclip m d B t j)⁻¹ * wclip m d B t i = 1 ∧
      ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) → 0 < pRet m S' u →
        Real.sqrt (1 - (((Fintype.card κ + 1) / 2 : ℕ) : ℝ) * ω / k) * sharpe m d B Sf S' u
          ≤ sharpe m d B Sf R (fun i => (∑ j ∈ R, wclip m d B t j)⁻¹ * wclip m d B t i) := by
  obtain ⟨t, R, hmin, hweak, hRc, hRw, hloss⟩ := relaxation_rounding (m := m) (B := B) (Sf := Sf) (G := G) hd hG hPS
    hk1 hk hω0 hω
  set c : ℝ := (((Fintype.card κ + 1) / 2 : ℕ) : ℝ) * ω / k with hc
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hc1 : c < 1 := by rw [hc, div_lt_one hkpos]; exact hKω
  have hc0 : 0 ≤ c := div_nonneg (mul_nonneg (Nat.cast_nonneg _) hω0) hkpos.le
  obtain ⟨S₀, hS₀, w₀, hw₀, hpos₀⟩ := hopt
  have hgpos : 0 < dualBound m d B P k t := lt_of_lt_of_le hpos₀ (hweak S₀ hS₀ w₀ hw₀)
  have hobj : (1 - c) * dualBound m d B P k t ≤ objLO m d B Sf R (wclip m d B t) := by linarith
  have hFpos : 0 < objLO m d B Sf R (wclip m d B t) :=
    lt_of_lt_of_le (mul_pos (by linarith) hgpos) hobj
  obtain ⟨-, hx0, hx1, hsh⟩ := certificate_sharpe (m := m) (B := B) (Sf := Sf) (P := P) (G := G) hd hG hPS
    (Sh := R) hRc.le (wh := wclip m d B t) hRw hFpos t
  refine ⟨t, R, hmin, hRc, hobj, hx0, hx1, fun S' hS' u hu hru => ?_⟩
  have h1 := hsh S' hS' u hu hru
  have hratio : 1 - c ≤ objLO m d B Sf R (wclip m d B t) / dualBound m d B P k t := by
    rw [le_div_iff₀ hgpos]; exact hobj
  have hsq : Real.sqrt (1 - c) ≤ Real.sqrt (objLO m d B Sf R (wclip m d B t) / dualBound m d B P k t) :=
    Real.sqrt_le_sqrt hratio
  have hsh0 : 0 ≤ sharpe m d B Sf S' u := by
    unfold sharpe; exact div_nonneg hru.le (Real.sqrt_nonneg _)
  exact le_trans (mul_le_mul_of_nonneg_right hsq hsh0) h1

/-- **The relaxation certificate (bicriteria), unconditional.** There is a minimizer `t` of `g_k` and a support
`T` with `|T| ≤ k + K` carrying a long-only portfolio of value at least `G*_k` (so
`OPT_LO(k) ≤ G*_k ≤ F_LO(T) ≤ OPT_LO(k+K)`). -/
theorem relaxation_bicriteria [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (hk1 : 1 ≤ k)
    (hk : k ≤ Fintype.card ι) :
    ∃ (t : κ → ℝ) (T : Finset ι), (∀ t', dualBound m d B P k t ≤ dualBound m d B P k t') ∧
      (∀ S : Finset ι, S.card ≤ k → ∀ w : ι → ℝ, (∀ i ∈ S, 0 ≤ w i) →
        objLO m d B Sf S w ≤ dualBound m d B P k t) ∧
      T.card ≤ k + Fintype.card κ ∧
      ∃ w : ι → ℝ, (∀ i ∈ T, 0 ≤ w i) ∧ dualBound m d B P k t ≤ objLO m d B Sf T w := by
  classical
  obtain ⟨t, lam, σ, hmin, hS, hσ, hf⟩ := exists_saddle_vertex (m := m) (B := B) (Sf := Sf) (G := G) hd hG hPS hk1 hk
  set T : Finset ι := Finset.univ.filter fun i => 0 < lam i with hT
  have hTcard : T.card ≤ k + Fintype.card κ :=
    card_support_le_of_frac hS.range hS.sum hf
  refine ⟨t, T, hmin, fun S hS' w hw => objLO_le_dualBound (m := m) (B := B) (Sf := Sf) (P := P) (G := G) hd hG hPS hS' hw t, hTcard, ?_⟩
  have hzero : ∀ i, i ∉ T → lam i = 0 := by
    intro i hi
    have : ¬ 0 < lam i := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    exact le_antisymm (not_lt.mp this) (hS.range i).1
  have hsupp : ∀ g : ι → ℝ, ∑ i, lam i * g i = ∑ i ∈ T, lam i * g i := by
    intro g
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
    rw [hzero i hi, zero_mul]
  obtain ⟨s, hs, -⟩ := hS.exists_s
  obtain ⟨T', hT'F, hT'c⟩ := hS.exists_sub hs
  obtain ⟨-, hdb, hlamsum⟩ := hS.dualBound_eq hd hT'F (by rw [hs, hT'c])
  refine bicriteria_certificate (G := G) hd hG hPS t lam (fun i _ => hS.range i) ?_ ?_
  · intro j
    rw [hS.stat j]
    have h := hsupp (fun i => wclip m d B t i * B i j)
    calc ∑ i, lam i * wclip m d B t i * B i j = ∑ i, lam i * (wclip m d B t i * B i j) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i ∈ T, lam i * (wclip m d B t i * B i j) := h
      _ = _ := Finset.sum_congr rfl fun i _ => by ring
  · rw [hdb]
    have := hsupp (fun i => clipScore m d B t i)
    simp only [clipScore] at this hlamsum ⊢
    rw [← this, hlamsum]
end Saddle

end SparseSharpe.Factor
