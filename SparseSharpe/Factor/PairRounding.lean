import Mathlib

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Rounding of fractional multipliers (Theorem 3.2 of the analytic note)

**Rounding lemma.** Let `λ ∈ [0,1]^ι` with `Σ λ = s` and let `u_k` be arbitrary vectors of a real inner product
space. There is a probability distribution on `s`-subsets `T` of `ι` with marginals `P(k ∈ T) = λ_k` such that
`E‖Σ_{k∈T} u_k − Σ_k λ_k u_k‖² ≤ Σ_k λ_k ‖u_k‖²`; the same bound holds with the complement weights `1 − λ_k`.
Hence some `s`-subset `T` has `‖Σ_T u − Σ λ u‖² ≤ min(Σ λ‖u‖², Σ (1−λ)‖u‖²)` (`exists_set_sq_le_min`).

The distribution is built by repeated pairwise merges of two fractional coordinates (`HasRounding.stepA`,
`HasRounding.stepB`); the potential `Σ λ‖u‖²` does not increase (`potential_A`, `potential_B`), and the number of
fractional coordinates drops by one at each merge (`exists_hasRounding`). No measure theory is used: a distribution
is a finitely supported family of weights on a finite type.
-/

open Finset

namespace SparseSharpe.Factor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Variance identity for a two-point mean-zero perturbation. -/
lemma two_point_var (D c₁ c₂ : E) (q₁ q₂ : ℝ) (hq : q₁ + q₂ = 1) (h : q₁ • c₁ + q₂ • c₂ = 0) :
    q₁ * ‖D + c₁‖ ^ 2 + q₂ * ‖D + c₂‖ ^ 2 = ‖D‖ ^ 2 + (q₁ * ‖c₁‖ ^ 2 + q₂ * ‖c₂‖ ^ 2) := by
  have h1 : ‖D + c₁‖ ^ 2 = ‖D‖ ^ 2 + 2 * inner ℝ D c₁ + ‖c₁‖ ^ 2 := norm_add_sq_real D c₁
  have h2 : ‖D + c₂‖ ^ 2 = ‖D‖ ^ 2 + 2 * inner ℝ D c₂ + ‖c₂‖ ^ 2 := norm_add_sq_real D c₂
  have h3 : q₁ * inner ℝ D c₁ + q₂ * inner ℝ D c₂ = 0 := by
    have := congrArg (fun x => inner ℝ D x) h
    simpa [inner_add_right, inner_smul_right] using this
  rw [h1, h2]
  have : q₁ + q₂ = 1 := hq
  nlinarith [h3]

/-- Weighted variance identity: `c = q₁u₁ + q₂u₂`. -/
lemma convex_two_var (u₁ u₂ : E) (q₁ q₂ : ℝ) (hq : q₁ + q₂ = 1) :
    q₁ * ‖u₁‖ ^ 2 + q₂ * ‖u₂‖ ^ 2 = ‖q₁ • u₁ + q₂ • u₂‖ ^ 2 + q₁ * q₂ * ‖u₁ - u₂‖ ^ 2 := by
  have e1 : ‖q₁ • u₁ + q₂ • u₂‖ ^ 2 = q₁ ^ 2 * ‖u₁‖ ^ 2 + 2 * (q₁ * q₂) * inner ℝ u₁ u₂ + q₂ ^ 2 * ‖u₂‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right]
    simp only [mul_pow, Real.norm_eq_abs, sq_abs, conj_trivial]
    ring
  have e2 : ‖u₁ - u₂‖ ^ 2 = ‖u₁‖ ^ 2 - 2 * inner ℝ u₁ u₂ + ‖u₂‖ ^ 2 := norm_sub_sq_real u₁ u₂
  rw [e1, e2]
  have : q₂ = 1 - q₁ := by linarith
  subst this
  ring

/-- A randomized rounding of `λ` to sets of size `s` with marginals `λ` and expected squared error
`‖Σ_{k∈T} u_k − Σ_k λ_k u_k‖²` at most `Q`; the probability space is finite. -/
def HasRounding (s : ℕ) (lam : ι → ℝ) (u : ι → E) (Q : ℝ) : Prop :=
  ∃ (Ω : Type) (_ : Fintype Ω) (p : Ω → ℝ) (T : Ω → Finset ι),
    (∀ ω, 0 ≤ p ω) ∧ ∑ ω, p ω = 1 ∧ (∀ ω, p ω ≠ 0 → (T ω).card = s) ∧
    (∀ i, ∑ ω, p ω * (if i ∈ T ω then (1 : ℝ) else 0) = lam i) ∧
    ∑ ω, p ω * ‖∑ k ∈ T ω, u k - ∑ k, lam k • u k‖ ^ 2 ≤ Q

lemma HasRounding.mono {s : ℕ} {lam : ι → ℝ} {u : ι → E} {Q Q' : ℝ} (h : HasRounding s lam u Q)
    (hQ : Q ≤ Q') : HasRounding s lam u Q' := by
  obtain ⟨Ω, _, p, T, h0, h1, h2, h3, h4⟩ := h
  exact ⟨Ω, inferInstance, p, T, h0, h1, h2, h3, h4.trans hQ⟩

/-- Some atom of a rounding has squared error at most the bound. -/
lemma HasRounding.exists_set {s : ℕ} {lam : ι → ℝ} {u : ι → E} {Q : ℝ} (h : HasRounding s lam u Q) :
    ∃ T : Finset ι, T.card = s ∧ ‖∑ k ∈ T, u k - ∑ k, lam k • u k‖ ^ 2 ≤ Q := by
  classical
  obtain ⟨Ω, _, p, T, h0, h1, h2, h3, h4⟩ := h
  by_contra hcon
  push Not at hcon
  have hne : (univ.filter fun ω => p ω ≠ 0).Nonempty := by
    by_contra hh
    rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at hh
    have : ∑ ω, p ω = 0 := Finset.sum_eq_zero fun ω hω => by simpa using hh hω
    linarith
  have key : ∑ ω, p ω * Q < ∑ ω, p ω * ‖∑ k ∈ T ω, u k - ∑ k, lam k • u k‖ ^ 2 := by
    apply Finset.sum_lt_sum
    · intro ω _
      by_cases hp : p ω = 0
      · simp [hp]
      · exact mul_le_mul_of_nonneg_left (hcon _ (h2 ω hp)).le (h0 ω)
    · obtain ⟨ω, hω⟩ := hne
      rw [mem_filter] at hω
      exact ⟨ω, mem_univ _, mul_lt_mul_of_pos_left (hcon _ (h2 ω hω.2)) (lt_of_le_of_ne (h0 ω) (Ne.symm hω.2))⟩
  rw [← Finset.sum_mul, h1, one_mul] at key
  linarith

/-- A rounding gives a set whose linear functional is at least the mean: `Σ λ_i v_i ≤ Σ_{i∈T} v_i`. -/
lemma HasRounding.exists_set_ge {s : ℕ} {lam : ι → ℝ} {u : ι → E} {Q : ℝ} (h : HasRounding s lam u Q)
    (v : ι → ℝ) : ∃ T : Finset ι, T.card = s ∧ ∑ i, lam i * v i ≤ ∑ i ∈ T, v i := by
  classical
  obtain ⟨Ω, _, p, T, h0, h1, h2, h3, h4⟩ := h
  have hmean : ∑ i, lam i * v i = ∑ ω, p ω * ∑ i ∈ T ω, v i := by
    calc ∑ i, lam i * v i = ∑ i, (∑ ω, p ω * (if i ∈ T ω then (1 : ℝ) else 0)) * v i := by
          exact Finset.sum_congr rfl fun i _ => by rw [h3 i]
      _ = ∑ i, ∑ ω, p ω * ((if i ∈ T ω then (1 : ℝ) else 0) * v i) := by
          exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun ω _ => by ring
      _ = ∑ ω, ∑ i, p ω * ((if i ∈ T ω then (1 : ℝ) else 0) * v i) := Finset.sum_comm
      _ = ∑ ω, p ω * ∑ i ∈ T ω, v i := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [← Finset.mul_sum]
          congr 1
          simp only [ite_mul, one_mul, zero_mul]
          rw [Finset.sum_ite_mem, Finset.univ_inter]
  by_contra hcon
  push Not at hcon
  have hne : (univ.filter fun ω => p ω ≠ 0).Nonempty := by
    by_contra hh
    rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at hh
    have : ∑ ω, p ω = 0 := Finset.sum_eq_zero fun ω hω => by simpa using hh hω
    linarith
  have key : ∑ ω, p ω * ∑ i ∈ T ω, v i < ∑ ω, p ω * ∑ i, lam i * v i := by
    apply Finset.sum_lt_sum
    · intro ω _
      by_cases hp : p ω = 0
      · simp [hp]
      · exact mul_le_mul_of_nonneg_left (hcon _ (h2 ω hp)).le (h0 ω)
    · obtain ⟨ω, hω⟩ := hne
      rw [mem_filter] at hω
      exact ⟨ω, mem_univ _, mul_lt_mul_of_pos_left (hcon _ (h2 ω hω.2)) (lt_of_le_of_ne (h0 ω) (Ne.symm hω.2))⟩
  rw [← Finset.sum_mul, h1, one_mul, ← hmean] at key
  exact lt_irrefl _ key

lemma not_mem_of_marg_zero {Ω : Type} [Fintype Ω] {p : Ω → ℝ} {T : Ω → Finset ι} (hp : ∀ ω, 0 ≤ p ω)
    {j : ι} (h : ∑ ω, p ω * (if j ∈ T ω then (1 : ℝ) else 0) = 0) :
    ∀ ω, p ω ≠ 0 → j ∉ T ω := by
  intro ω hω hj
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun ω _ => mul_nonneg (hp ω) (by split_ifs <;> norm_num))).mp h ω (mem_univ _)
  simp [hj] at this
  exact hω this

lemma mem_of_marg_one {Ω : Type} [Fintype Ω] {p : Ω → ℝ} {T : Ω → Finset ι} (hp : ∀ ω, 0 ≤ p ω)
    (hp1 : ∑ ω, p ω = 1) {j : ι} (h : ∑ ω, p ω * (if j ∈ T ω then (1 : ℝ) else 0) = 1) :
    ∀ ω, p ω ≠ 0 → j ∈ T ω := by
  intro ω hω
  by_contra hj
  have h2 : ∑ ω, p ω * (1 - (if j ∈ T ω then (1 : ℝ) else 0)) = 0 := by
    have : ∑ ω, p ω * (1 - (if j ∈ T ω then (1 : ℝ) else 0)) = ∑ ω, p ω - ∑ ω, p ω * (if j ∈ T ω then (1 : ℝ) else 0) := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun ω _ => by ring
    rw [this, h, hp1]; ring
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun ω _ => mul_nonneg (hp ω) (by split_ifs <;> norm_num))).mp h2 ω (mem_univ _)
  simp [hj] at this
  exact hω this

/-- Base case: all `λ_k ∈ {0,1}`. -/
lemma hasRounding_base {s : ℕ} {lam : ι → ℝ} (u : ι → E) (h01 : ∀ k, lam k = 0 ∨ lam k = 1)
    (hsum : ∑ k, lam k = s) : HasRounding s lam u (∑ k, lam k * ‖u k‖ ^ 2) := by
  classical
  set T : Finset ι := univ.filter fun k => lam k = 1 with hT
  have hlam : ∀ k, lam k = if k ∈ T then 1 else 0 := by
    intro k; rcases h01 k with h | h <;> simp [hT, h]
  have hcard : T.card = s := by
    have : ∑ k, lam k = (T.card : ℝ) := by
      rw [Finset.sum_congr rfl fun k _ => hlam k]; simp
    exact_mod_cast (this.symm.trans hsum)
  refine ⟨Unit, inferInstance, fun _ => 1, fun _ => T, fun _ => zero_le_one, by simp, fun _ _ => hcard, ?_, ?_⟩
  · intro i; simp [hlam i]
  · have : ∑ k ∈ T, u k = ∑ k, lam k • u k := by
      calc ∑ k ∈ T, u k = ∑ k, (if k ∈ T then u k else 0) := by
            rw [Finset.sum_ite_mem, Finset.univ_inter]
        _ = ∑ k, lam k • u k := Finset.sum_congr rfl fun k _ => by
            rw [hlam k]; split_ifs <;> simp
    simp [this]
    exact Finset.sum_nonneg fun k _ => by
      rcases h01 k with h | h <;> simp [h]


section Updates

variable {G : Type*} [AddCommGroup G]

lemma sum_two_diff (f g : ι → G) {i j : ι} (hij : i ≠ j) (h : ∀ k, k ≠ i → k ≠ j → f k = g k) :
    ∑ k, f k = ∑ k, g k + (f i - g i) + (f j - g j) := by
  have : ∑ k, (f k - g k) = (f i - g i) + (f j - g j) :=
    Finset.sum_eq_add i j hij (fun k _ hk => by rw [h k hk.1 hk.2]; simp) (fun h => absurd (mem_univ _) h)
      (fun h => absurd (mem_univ _) h)
  rw [Finset.sum_sub_distrib] at this
  rw [add_assoc, ← this]; abel

lemma sum_update_update (f : ι → G) {i j : ι} (hij : i ≠ j) (c z : G) (S : Finset ι) (hj : j ∉ S) :
    ∑ k ∈ S, Function.update (Function.update f i c) j z k
      = ∑ k ∈ S, f k + (if i ∈ S then c - f i else 0) := by
  have h1 : ∑ k ∈ S, Function.update (Function.update f i c) j z k = ∑ k ∈ S, Function.update f i c k :=
    Finset.sum_congr rfl fun k hk => Function.update_of_ne (by rintro rfl; exact hj hk) _ _
  rw [h1]
  by_cases hi : i ∈ S
  · rw [Finset.sum_update_of_mem hi, ← Finset.add_sum_erase S f hi, sdiff_singleton_eq_erase]
    simp only [hi, ↓reduceIte]; abel
  · rw [Finset.sum_update_of_notMem hi]; simp [hi]

end Updates


/-! ### Merging step A: two items with `λ_i + λ_j ≤ 1` become one -/

/-- The set obtained from `A` (with `j ∉ A`) by reassigning the merged item to `i` or `j`. -/
def mergeSetA (i j : ι) (A : Finset ι) (b : Bool) : Finset ι :=
  if i ∈ A then (if b then A else insert j (A.erase i)) else A

section MergeSetA
variable {i j : ι} {A : Finset ι}

lemma mergeSetA_card (hij : i ≠ j) (hj : j ∉ A) (b : Bool) : (mergeSetA i j A b).card = A.card := by
  unfold mergeSetA
  by_cases hi : i ∈ A
  · by_cases hb : b
    · simp [hi, hb]
    · simp only [hi, hb, if_true, Bool.false_eq_true, if_false]
      rw [Finset.card_insert_of_notMem (fun h => hj (Finset.mem_of_mem_erase h)), Finset.card_erase_of_mem hi]
      have : 0 < A.card := Finset.card_pos.mpr ⟨i, hi⟩
      omega
  · simp [hi]

lemma mem_mergeSetA_of_ne {k : ι} (hki : k ≠ i) (hkj : k ≠ j) (b : Bool) :
    k ∈ mergeSetA i j A b ↔ k ∈ A := by
  unfold mergeSetA
  by_cases hi : i ∈ A <;> by_cases hb : b <;> simp [hi, hb, hki, hkj]

lemma mem_mergeSetA_i (hij : i ≠ j) (b : Bool) : i ∈ mergeSetA i j A b ↔ (i ∈ A ∧ b = true) := by
  unfold mergeSetA
  by_cases hi : i ∈ A <;> by_cases hb : b <;> simp [hi, hb, hij]

lemma mem_mergeSetA_j (hij : i ≠ j) (hj : j ∉ A) (b : Bool) : j ∈ mergeSetA i j A b ↔ (i ∈ A ∧ b = false) := by
  unfold mergeSetA
  by_cases hi : i ∈ A <;> by_cases hb : b <;> simp [hi, hb, hij, hj]

lemma sum_mergeSetA {G : Type*} [AddCommGroup G] (f : ι → G) (hij : i ≠ j) (hj : j ∉ A) (b : Bool) :
    ∑ k ∈ mergeSetA i j A b, f k = ∑ k ∈ A, f k + (if i ∈ A then (if b then 0 else f j - f i) else 0) := by
  unfold mergeSetA
  by_cases hi : i ∈ A
  · by_cases hb : b
    · simp [hi, hb]
    · simp only [hi, hb, if_true, Bool.false_eq_true, if_false]
      rw [Finset.sum_insert (fun h => hj (Finset.mem_of_mem_erase h)), ← Finset.add_sum_erase A f hi]
      abel
  · simp [hi]

end MergeSetA


/-- Step A of the rounding: if the merged instance has a rounding, so does the original. -/
lemma HasRounding.stepA {s : ℕ} {lam : ι → ℝ} {u : ι → E} {i j : ι} (hij : i ≠ j)
    (hi : 0 < lam i) (hj : 0 < lam j) {Q : ℝ}
    (h : HasRounding s (Function.update (Function.update lam i (lam i + lam j)) j 0)
      (Function.update (Function.update u i ((lam i + lam j)⁻¹ • (lam i • u i + lam j • u j))) j 0) Q) :
    HasRounding s lam u (Q + lam i * lam j / (lam i + lam j) * ‖u i - u j‖ ^ 2) := by
  classical
  have hL : 0 < lam i + lam j := add_pos hi hj
  set qi : ℝ := lam i / (lam i + lam j) with hqi
  set qj : ℝ := lam j / (lam i + lam j) with hqj
  have hqi0 : 0 ≤ qi := div_nonneg hi.le hL.le
  have hqj0 : 0 ≤ qj := div_nonneg hj.le hL.le
  have hq : qi + qj = 1 := by rw [hqi, hqj, ← add_div, div_self hL.ne']
  set c : E := qi • u i + qj • u j with hc
  have hc' : (lam i + lam j)⁻¹ • (lam i • u i + lam j • u j) = c := by
    rw [hc, hqi, hqj, smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]
  have hmz : qi • (u i - c) + qj • (u j - c) = 0 := by
    have : qi • (u i - c) + qj • (u j - c) = (qi • u i + qj • u j) - (qi + qj) • c := by
      simp only [smul_sub, add_smul]; abel
    rw [this, hq, one_smul, ← hc, sub_self]
  rw [hc'] at h
  obtain ⟨Ω, _, p, T, h0, h1, h2, h3, h4⟩ := h
  set lam' : ι → ℝ := Function.update (Function.update lam i (lam i + lam j)) j 0 with hlam'
  set u' : ι → E := Function.update (Function.update u i c) j 0 with hu'
  have hl_i : lam' i = lam i + lam j := by
    simp [hlam', Function.update_of_ne hij]
  have hl_j : lam' j = 0 := by simp [hlam']
  have hl_k : ∀ k, k ≠ i → k ≠ j → lam' k = lam k := by
    intro k hki hkj; simp [hlam', Function.update_of_ne hki, Function.update_of_ne hkj]
  have hu_i : u' i = c := by simp [hu', Function.update_of_ne hij]
  have hu_j : u' j = 0 := by simp [hu']
  have hu_k : ∀ k, k ≠ i → k ≠ j → u' k = u k := by
    intro k hki hkj; simp [hu', Function.update_of_ne hki, Function.update_of_ne hkj]
  -- the mean is preserved
  have hmean : ∑ k, lam' k • u' k = ∑ k, lam k • u k := by
    rw [sum_two_diff (fun k => lam' k • u' k) (fun k => lam k • u k) hij
      (fun k hki hkj => by simp only [hl_k k hki hkj, hu_k k hki hkj])]
    simp only [hl_i, hl_j, hu_i, hu_j, zero_smul, hc, smul_add, smul_smul, hqi, hqj]
    have e1 : (lam i + lam j) * (lam i / (lam i + lam j)) = lam i := by field_simp
    have e2 : (lam i + lam j) * (lam j / (lam i + lam j)) = lam j := by field_simp
    rw [e1, e2]; abel
  rw [hmean] at h4
  set ubar : E := ∑ k, lam k • u k with hubar
  -- j is never selected
  have hjT : ∀ ω, p ω ≠ 0 → j ∉ T ω := by
    apply not_mem_of_marg_zero h0
    rw [h3 j, hl_j]
  refine ⟨Ω × Bool, inferInstance, fun x => p x.1 * (if x.2 then qi else qj),
    fun x => mergeSetA i j (T x.1) x.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; exact mul_nonneg (h0 _) (by split_ifs <;> assumption)
  · simp only [Fintype.sum_prod_type, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
    simp only [← mul_add, hq, mul_one]
    exact h1
  · intro x hx
    have hp : p x.1 ≠ 0 := left_ne_zero_of_mul hx
    rw [mergeSetA_card hij (hjT _ hp)]
    exact h2 _ hp
  · intro k
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
    by_cases hki : k = i
    · subst hki
      have : ∀ ω, p ω * qi * (if k ∈ mergeSetA k j (T ω) true then (1 : ℝ) else 0)
          + p ω * qj * (if k ∈ mergeSetA k j (T ω) false then (1 : ℝ) else 0)
          = qi * (p ω * (if k ∈ T ω then (1 : ℝ) else 0)) := by
        intro ω
        simp only [mem_mergeSetA_i hij]
        by_cases hk : k ∈ T ω <;> simp [hk]; ring
      rw [Finset.sum_congr rfl fun ω _ => this ω, ← Finset.mul_sum, h3 k, hl_i, hqi]
      field_simp
    · by_cases hkj : k = j
      · subst hkj
        have : ∀ ω, p ω * qi * (if k ∈ mergeSetA i k (T ω) true then (1 : ℝ) else 0)
            + p ω * qj * (if k ∈ mergeSetA i k (T ω) false then (1 : ℝ) else 0)
            = qj * (p ω * (if i ∈ T ω then (1 : ℝ) else 0)) := by
          intro ω
          by_cases hp : p ω = 0
          · simp [hp]
          · simp only [mem_mergeSetA_j hij (hjT ω hp)]
            by_cases hk : i ∈ T ω <;> simp [hk]; ring
        rw [Finset.sum_congr rfl fun ω _ => this ω, ← Finset.mul_sum, h3 i, hl_i, hqj]
        field_simp
      · have : ∀ ω, p ω * qi * (if k ∈ mergeSetA i j (T ω) true then (1 : ℝ) else 0)
            + p ω * qj * (if k ∈ mergeSetA i j (T ω) false then (1 : ℝ) else 0)
            = p ω * (if k ∈ T ω then (1 : ℝ) else 0) := by
          intro ω
          simp only [mem_mergeSetA_of_ne hki hkj]
          by_cases hk : k ∈ T ω <;> simp [hk]
          rw [← mul_add, hq, mul_one]
        rw [Finset.sum_congr rfl fun ω _ => this ω, h3 k, hl_k k hki hkj]
  · set V : ℝ := qi * qj * ‖u i - u j‖ ^ 2 with hV
    have hVid : qi * ‖u i - c‖ ^ 2 + qj * ‖u j - c‖ ^ 2 = V := by
      have h := convex_two_var (u i - c) (u j - c) qi qj hq
      have h0 := hmz
      rw [h0, norm_zero] at h
      have : (u i - c) - (u j - c) = u i - u j := by abel
      rw [this] at h
      rw [hV]; linarith [h]
    have hpt : ∀ ω, (∑ b : Bool, p ω * (if b then qi else qj) *
          ‖∑ k ∈ mergeSetA i j (T ω) b, u k - ubar‖ ^ 2)
        = p ω * ‖∑ k ∈ T ω, u' k - ubar‖ ^ 2 + V * (p ω * (if i ∈ T ω then (1 : ℝ) else 0)) := by
      intro ω
      by_cases hp : p ω = 0
      · simp [hp]
      · have hjω := hjT ω hp
        have hD' : ∑ k ∈ T ω, u' k = ∑ k ∈ T ω, u k + (if i ∈ T ω then c - u i else 0) :=
          sum_update_update u hij c 0 (T ω) hjω
        rw [Fintype.sum_bool]
        simp only [sum_mergeSetA u hij hjω, if_true, Bool.false_eq_true, if_false]
        by_cases hiT : i ∈ T ω
        · simp only [hiT, if_true] at hD' ⊢
          rw [hD']
          have e1 : ∑ k ∈ T ω, u k + 0 - ubar = (∑ k ∈ T ω, u k + (c - u i) - ubar) + (u i - c) := by abel
          have e2 : ∑ k ∈ T ω, u k + (u j - u i) - ubar = (∑ k ∈ T ω, u k + (c - u i) - ubar) + (u j - c) := by abel
          rw [e1, e2]
          have := two_point_var (∑ k ∈ T ω, u k + (c - u i) - ubar) (u i - c) (u j - c) qi qj hq hmz
          rw [hVid] at this
          have h' := congrArg (fun x => p ω * x) this
          nlinarith [h']
        · simp only [hiT, if_false] at hD' ⊢
          rw [hD']
          have : p ω * qi * ‖∑ k ∈ T ω, u k + 0 - ubar‖ ^ 2 + p ω * qj * ‖∑ k ∈ T ω, u k + 0 - ubar‖ ^ 2
              = p ω * (qi + qj) * ‖∑ k ∈ T ω, u k + 0 - ubar‖ ^ 2 := by ring
          rw [this, hq]; ring
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun ω _ => hpt ω, Finset.sum_add_distrib,
      ← Finset.mul_sum, h3 i, hl_i]
    have : V * (lam i + lam j) = lam i * lam j / (lam i + lam j) * ‖u i - u j‖ ^ 2 := by
      rw [hV, hqi, hqj]; field_simp
    rw [this]; linarith [h4]


lemma sum_update_update_of_mem {G : Type*} [AddCommGroup G] (f : ι → G) {i j : ι} (hij : i ≠ j) (c z : G)
    (S : Finset ι) (hj : j ∈ S) :
    ∑ k ∈ S, Function.update (Function.update f i c) j z k
      = ∑ k ∈ S, f k + (z - f j) + (if i ∈ S then c - f i else 0) := by
  have h1 := Finset.add_sum_erase S (Function.update (Function.update f i c) j z) hj
  have h2 := Finset.add_sum_erase S f hj
  have h3 : ∑ k ∈ S.erase j, Function.update (Function.update f i c) j z k
      = ∑ k ∈ S.erase j, f k + (if i ∈ S.erase j then c - f i else 0) :=
    sum_update_update f hij c z (S.erase j) (Finset.notMem_erase j S)
  have hi : i ∈ S.erase j ↔ i ∈ S := by simp [hij]
  rw [← h1, h3, Function.update_self]
  simp only [hi]
  rw [← h2]; abel

/-! ### Merging step B: two items with `λ_i + λ_j ≥ 1` become one (in the complement) -/

/-- The set obtained from `A` (with `j ∈ A`) by reassigning the merged item to `i` or `j`. -/
def mergeSetB (i j : ι) (A : Finset ι) (b : Bool) : Finset ι :=
  if i ∈ A then A else (if b then insert i (A.erase j) else A)

section MergeSetB
variable {i j : ι} {A : Finset ι}

lemma mergeSetB_card (hij : i ≠ j) (hj : j ∈ A) (b : Bool) : (mergeSetB i j A b).card = A.card := by
  unfold mergeSetB
  by_cases hi : i ∈ A
  · simp [hi]
  · by_cases hb : b
    · simp only [hi, hb, if_false, if_true]
      rw [Finset.card_insert_of_notMem (fun h => hi (Finset.mem_of_mem_erase h)), Finset.card_erase_of_mem hj]
      have : 0 < A.card := Finset.card_pos.mpr ⟨j, hj⟩
      omega
    · simp [hi, hb]

lemma mem_mergeSetB_of_ne {k : ι} (hki : k ≠ i) (hkj : k ≠ j) (b : Bool) :
    k ∈ mergeSetB i j A b ↔ k ∈ A := by
  unfold mergeSetB
  by_cases hi : i ∈ A <;> by_cases hb : b <;> simp [hi, hb, hki, hkj]

lemma mem_mergeSetB_i (b : Bool) : i ∈ mergeSetB i j A b ↔ (i ∈ A ∨ b = true) := by
  unfold mergeSetB
  by_cases hi : i ∈ A <;> by_cases hb : b <;> simp [hi, hb]

lemma mem_mergeSetB_j (hij : i ≠ j) (hj : j ∈ A) (b : Bool) : j ∈ mergeSetB i j A b ↔ (i ∈ A ∨ b = false) := by
  unfold mergeSetB
  by_cases hi : i ∈ A <;> by_cases hb : b <;> simp [hi, hb, hij, hj, hij.symm]

lemma sum_mergeSetB {G : Type*} [AddCommGroup G] (f : ι → G) (hij : i ≠ j) (hj : j ∈ A) (b : Bool) :
    ∑ k ∈ mergeSetB i j A b, f k = ∑ k ∈ A, f k + (if i ∈ A then 0 else (if b then f i - f j else 0)) := by
  unfold mergeSetB
  by_cases hi : i ∈ A
  · simp [hi]
  · by_cases hb : b
    · simp only [hi, hb, if_false, if_true]
      rw [Finset.sum_insert (fun h => hi (Finset.mem_of_mem_erase h)), ← Finset.add_sum_erase A f hj]
      abel
    · simp [hi, hb]

end MergeSetB


/-- Step B of the rounding (merge in the complement). -/
lemma HasRounding.stepB {s : ℕ} {lam : ι → ℝ} {u : ι → E} {i j : ι} (hij : i ≠ j)
    (hi : lam i < 1) (hj : lam j < 1) {Q : ℝ}
    (h : HasRounding s (Function.update (Function.update lam i (lam i + lam j - 1)) j 1)
      (Function.update (Function.update u i
        ((2 - lam i - lam j)⁻¹ • ((1 - lam i) • u i + (1 - lam j) • u j))) j 0) Q) :
    HasRounding s lam u
      (Q + (1 - lam i) * (1 - lam j) / (2 - lam i - lam j) * ‖u i - u j‖ ^ 2) := by
  classical
  have hM : 0 < 2 - lam i - lam j := by linarith
  set M : ℝ := 2 - lam i - lam j with hMdef
  set qi : ℝ := (1 - lam j) / M with hqi
  set qj : ℝ := (1 - lam i) / M with hqj
  have hqi0 : 0 ≤ qi := div_nonneg (by linarith) hM.le
  have hqj0 : 0 ≤ qj := div_nonneg (by linarith) hM.le
  have hq : qi + qj = 1 := by rw [hqi, hqj, ← add_div, div_eq_one_iff_eq hM.ne']; rw [hMdef]; ring
  set c : E := qj • u i + qi • u j with hc
  have hc' : M⁻¹ • ((1 - lam i) • u i + (1 - lam j) • u j) = c := by
    rw [hc, hqi, hqj, smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]
  have hMc : M • c = (1 - lam i) • u i + (1 - lam j) • u j := by
    rw [← hc']; rw [smul_smul, mul_inv_cancel₀ hM.ne', one_smul]
  have hmz : qi • (c - u j) + qj • (c - u i) = 0 := by
    have : qi • (c - u j) + qj • (c - u i) = (qi + qj) • c - (qj • u i + qi • u j) := by
      simp only [smul_sub, add_smul]; abel
    rw [this, hq, one_smul, ← hc, sub_self]
  rw [hc'] at h
  obtain ⟨Ω, _, p, T, h0, h1, h2, h3, h4⟩ := h
  set lam' : ι → ℝ := Function.update (Function.update lam i (lam i + lam j - 1)) j 1 with hlam'
  set u' : ι → E := Function.update (Function.update u i c) j 0 with hu'
  have hl_i : lam' i = lam i + lam j - 1 := by
    simp [hlam', Function.update_of_ne hij]
  have hl_j : lam' j = 1 := by simp [hlam']
  have hl_k : ∀ k, k ≠ i → k ≠ j → lam' k = lam k := by
    intro k hki hkj; simp [hlam', Function.update_of_ne hki, Function.update_of_ne hkj]
  have hu_i : u' i = c := by simp [hu', Function.update_of_ne hij]
  have hu_j : u' j = 0 := by simp [hu']
  have hu_k : ∀ k, k ≠ i → k ≠ j → u' k = u k := by
    intro k hki hkj; simp [hu', Function.update_of_ne hki, Function.update_of_ne hkj]
  set ubar : E := ∑ k, lam k • u k with hubar
  have hmean : ∑ k, lam' k • u' k = ubar + c - u i - u j := by
    rw [sum_two_diff (fun k => lam' k • u' k) (fun k => lam k • u k) hij
      (fun k hki hkj => by simp only [hl_k k hki hkj, hu_k k hki hkj])]
    simp only [hl_i, hl_j, hu_i, hu_j, smul_zero, hubar]
    have e1 : (lam i + lam j - 1) • c = c - ((1 - lam i) • u i + (1 - lam j) • u j) := by
      rw [← hMc, show lam i + lam j - 1 = 1 - M by rw [hMdef]; ring, sub_smul, one_smul]
    rw [e1]
    simp only [sub_smul, one_smul]
    abel
  rw [hmean] at h4
  have hjT : ∀ ω, p ω ≠ 0 → j ∈ T ω := by
    apply mem_of_marg_one h0 h1
    rw [h3 j, hl_j]
  have hI : qi + qj * (lam i + lam j - 1) = lam i := by
    rw [hqi, hqj]; field_simp; rw [hMdef]; ring
  have hJ : qj + qi * (lam i + lam j - 1) = lam j := by
    rw [hqi, hqj]; field_simp; rw [hMdef]; ring
  refine ⟨Ω × Bool, inferInstance, fun x => p x.1 * (if x.2 then qi else qj),
    fun x => mergeSetB i j (T x.1) x.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; exact mul_nonneg (h0 _) (by split_ifs <;> assumption)
  · simp only [Fintype.sum_prod_type, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
    simp only [← mul_add, hq, mul_one]
    exact h1
  · intro x hx
    have hp : p x.1 ≠ 0 := left_ne_zero_of_mul hx
    rw [mergeSetB_card hij (hjT _ hp)]
    exact h2 _ hp
  · intro k
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
    by_cases hki : k = i
    · subst hki
      have : ∀ ω, p ω * qi * (if k ∈ mergeSetB k j (T ω) true then (1 : ℝ) else 0)
          + p ω * qj * (if k ∈ mergeSetB k j (T ω) false then (1 : ℝ) else 0)
          = p ω * qi + qj * (p ω * (if k ∈ T ω then (1 : ℝ) else 0)) := by
        intro ω
        simp only [mem_mergeSetB_i]
        by_cases hk : k ∈ T ω <;> simp [hk] <;> ring
      rw [Finset.sum_congr rfl fun ω _ => this ω, Finset.sum_add_distrib, ← Finset.sum_mul, h1, ← Finset.mul_sum,
        h3 k, hl_i, one_mul]
      exact hI
    · by_cases hkj : k = j
      · subst hkj
        have : ∀ ω, p ω * qi * (if k ∈ mergeSetB i k (T ω) true then (1 : ℝ) else 0)
            + p ω * qj * (if k ∈ mergeSetB i k (T ω) false then (1 : ℝ) else 0)
            = qi * (p ω * (if i ∈ T ω then (1 : ℝ) else 0)) + p ω * qj := by
          intro ω
          by_cases hp : p ω = 0
          · simp [hp]
          · simp only [mem_mergeSetB_j hij (hjT ω hp)]
            by_cases hk : i ∈ T ω <;> simp [hk] <;> ring
        rw [Finset.sum_congr rfl fun ω _ => this ω, Finset.sum_add_distrib, ← Finset.mul_sum, h3 i, hl_i,
          ← Finset.sum_mul, h1, one_mul]
        linarith [hJ]
      · have : ∀ ω, p ω * qi * (if k ∈ mergeSetB i j (T ω) true then (1 : ℝ) else 0)
            + p ω * qj * (if k ∈ mergeSetB i j (T ω) false then (1 : ℝ) else 0)
            = p ω * (if k ∈ T ω then (1 : ℝ) else 0) := by
          intro ω
          simp only [mem_mergeSetB_of_ne hki hkj]
          by_cases hk : k ∈ T ω <;> simp [hk]
          rw [← mul_add, hq, mul_one]
        rw [Finset.sum_congr rfl fun ω _ => this ω, h3 k, hl_k k hki hkj]
  · set V : ℝ := qi * qj * ‖u i - u j‖ ^ 2 with hV
    have hVid : qi * ‖c - u j‖ ^ 2 + qj * ‖c - u i‖ ^ 2 = V := by
      have h := convex_two_var (c - u j) (c - u i) qi qj hq
      rw [hmz, norm_zero] at h
      have : (c - u j) - (c - u i) = u i - u j := by abel
      rw [this] at h
      rw [hV]; linarith [h]
    have hpt : ∀ ω, (∑ b : Bool, p ω * (if b then qi else qj) *
          ‖∑ k ∈ mergeSetB i j (T ω) b, u k - ubar‖ ^ 2)
        = p ω * ‖∑ k ∈ T ω, u' k - (ubar + c - u i - u j)‖ ^ 2
          + V * (p ω * (if i ∈ T ω then (0 : ℝ) else 1)) := by
      intro ω
      by_cases hp : p ω = 0
      · simp [hp]
      · have hjω := hjT ω hp
        have hD'' : ∑ k ∈ T ω, u' k = ∑ k ∈ T ω, u k + (0 - u j) + (if i ∈ T ω then c - u i else 0) :=
          sum_update_update_of_mem u hij c 0 (T ω) hjω
        rw [Fintype.sum_bool]
        simp only [sum_mergeSetB u hij hjω, if_true, Bool.false_eq_true, if_false]
        by_cases hiT : i ∈ T ω
        · simp only [hiT, if_true] at hD'' ⊢
          have key : ∑ k ∈ T ω, u' k - (ubar + c - u i - u j) = ∑ k ∈ T ω, u k + 0 - ubar := by
            rw [hD'']; abel
          rw [key]
          calc _ = p ω * (qi + qj) * ‖∑ k ∈ T ω, u k + 0 - ubar‖ ^ 2 := by ring
            _ = _ := by rw [hq]; ring
        · simp only [hiT, if_false] at hD'' ⊢
          have e1 : ∑ k ∈ T ω, u k + (u i - u j) - ubar
              = (∑ k ∈ T ω, u' k - (ubar + c - u i - u j)) + (c - u j) := by
            rw [hD'']; abel
          have e2 : ∑ k ∈ T ω, u k + 0 - ubar
              = (∑ k ∈ T ω, u' k - (ubar + c - u i - u j)) + (c - u i) := by
            rw [hD'']; abel
          rw [e1, e2]
          have := two_point_var (∑ k ∈ T ω, u' k - (ubar + c - u i - u j)) (c - u j) (c - u i) qi qj hq hmz
          rw [hVid] at this
          have h' := congrArg (fun x => p ω * x) this
          nlinarith [h']
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun ω _ => hpt ω, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    have hsum1 : ∑ ω, p ω * (if i ∈ T ω then (0 : ℝ) else 1) = 2 - lam i - lam j := by
      have : ∀ ω, p ω * (if i ∈ T ω then (0 : ℝ) else 1) = p ω - p ω * (if i ∈ T ω then (1 : ℝ) else 0) := by
        intro ω; by_cases hk : i ∈ T ω <;> simp [hk]
      rw [Finset.sum_congr rfl fun ω _ => this ω, Finset.sum_sub_distrib, h1, h3 i, hl_i]; ring
    rw [hsum1]
    have : V * (2 - lam i - lam j) = (1 - lam i) * (1 - lam j) / (2 - lam i - lam j) * ‖u i - u j‖ ^ 2 := by
      rw [hV, hqi, hqj, hMdef]; field_simp
    rw [this]; linarith [h4]


/-! ### The potentials of the two merges -/

lemma potential_A {lam : ι → ℝ} {u : ι → E} {i j : ι} (hij : i ≠ j) (hL : 0 < lam i + lam j) :
    ∑ k, Function.update (Function.update lam i (lam i + lam j)) j 0 k *
        ‖Function.update (Function.update u i ((lam i + lam j)⁻¹ • (lam i • u i + lam j • u j))) j 0 k‖ ^ 2
      + lam i * lam j / (lam i + lam j) * ‖u i - u j‖ ^ 2 = ∑ k, lam k * ‖u k‖ ^ 2 := by
  set L := lam i + lam j with hLdef
  set c : E := L⁻¹ • (lam i • u i + lam j • u j) with hc
  have hl_i : Function.update (Function.update lam i L) j 0 i = L := by
    simp [Function.update_of_ne hij]
  have hu_i : Function.update (Function.update u i c) j 0 i = c := by
    simp [Function.update_of_ne hij]
  rw [sum_two_diff (fun k => Function.update (Function.update lam i L) j 0 k *
        ‖Function.update (Function.update u i c) j 0 k‖ ^ 2) (fun k => lam k * ‖u k‖ ^ 2) hij
      (fun k hki hkj => by simp [Function.update_of_ne hki, Function.update_of_ne hkj])]
  simp only [hl_i, hu_i, Function.update_self, norm_zero]
  have hc2 : c = (lam i / L) • u i + (lam j / L) • u j := by
    rw [hc, smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]
  have hq : lam i / L + lam j / L = 1 := by rw [← add_div, div_self hL.ne']
  have h := convex_two_var (u i) (u j) (lam i / L) (lam j / L) hq
  rw [← hc2] at h
  have e : L * (lam i / L * ‖u i‖ ^ 2 + lam j / L * ‖u j‖ ^ 2)
      = L * (‖c‖ ^ 2 + lam i / L * (lam j / L) * ‖u i - u j‖ ^ 2) := by rw [h]
  have e1 : L * (lam i / L * ‖u i‖ ^ 2 + lam j / L * ‖u j‖ ^ 2) = lam i * ‖u i‖ ^ 2 + lam j * ‖u j‖ ^ 2 := by
    field_simp
  have e2 : L * (‖c‖ ^ 2 + lam i / L * (lam j / L) * ‖u i - u j‖ ^ 2)
      = L * ‖c‖ ^ 2 + lam i * lam j / L * ‖u i - u j‖ ^ 2 := by field_simp
  rw [e1, e2] at e
  nlinarith [e]

lemma potential_B {lam : ι → ℝ} {u : ι → E} {i j : ι} (hij : i ≠ j) (hi : 1 / 2 ≤ lam i) (hj : 1 / 2 ≤ lam j)
    (hi1 : lam i < 1) (hj1 : lam j < 1) :
    ∑ k, Function.update (Function.update lam i (lam i + lam j - 1)) j 1 k *
        ‖Function.update (Function.update u i
          ((2 - lam i - lam j)⁻¹ • ((1 - lam i) • u i + (1 - lam j) • u j))) j 0 k‖ ^ 2
      + (1 - lam i) * (1 - lam j) / (2 - lam i - lam j) * ‖u i - u j‖ ^ 2 ≤ ∑ k, lam k * ‖u k‖ ^ 2 := by
  have hM : 0 < 2 - lam i - lam j := by linarith
  set M : ℝ := 2 - lam i - lam j with hMdef
  set qi : ℝ := (1 - lam j) / M with hqi
  set qj : ℝ := (1 - lam i) / M with hqj
  have hqi0 : 0 ≤ qi := div_nonneg (by linarith) hM.le
  have hqj0 : 0 ≤ qj := div_nonneg (by linarith) hM.le
  have hq : qi + qj = 1 := by rw [hqi, hqj, ← add_div, div_eq_one_iff_eq hM.ne']; rw [hMdef]; ring
  set c : E := qj • u i + qi • u j with hc
  have hc' : M⁻¹ • ((1 - lam i) • u i + (1 - lam j) • u j) = c := by
    rw [hc, hqi, hqj, smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]
  rw [hc']
  have hl_i : Function.update (Function.update lam i (lam i + lam j - 1)) j 1 i = lam i + lam j - 1 := by
    simp [Function.update_of_ne hij]
  have hu_i : Function.update (Function.update u i c) j 0 i = c := by
    simp [Function.update_of_ne hij]
  rw [sum_two_diff (fun k => Function.update (Function.update lam i (lam i + lam j - 1)) j 1 k *
        ‖Function.update (Function.update u i c) j 0 k‖ ^ 2) (fun k => lam k * ‖u k‖ ^ 2) hij
      (fun k hki hkj => by simp [Function.update_of_ne hki, Function.update_of_ne hkj])]
  simp only [hl_i, hu_i, Function.update_self, norm_zero]
  have h := convex_two_var (u i) (u j) qj qi (by linarith)
  rw [← hc] at h
  set x := ‖u i‖ ^ 2 with hx
  set y := ‖u j‖ ^ 2 with hy
  set n := ‖c‖ ^ 2 with hn
  set D := ‖u i - u j‖ ^ 2 with hD
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hn0 : 0 ≤ n := by positivity
  have hD0 : 0 ≤ D := by positivity
  have hnle : n ≤ qj * x + qi * y := by nlinarith [mul_nonneg hqj0 hqi0, mul_nonneg (mul_nonneg hqj0 hqi0) hD0]
  -- inc_B = (1-λi) x + (1-λj) y - M n
  have hinc : (1 - lam i) * (1 - lam j) / M * D = (1 - lam i) * x + (1 - lam j) * y - M * n := by
    have e : M * (qj * x + qi * y) = M * (n + qj * qi * D) := by rw [h]
    have e1 : M * (qj * x + qi * y) = (1 - lam i) * x + (1 - lam j) * y := by
      rw [hqi, hqj]; field_simp
    have e2 : M * (n + qj * qi * D) = M * n + (1 - lam i) * (1 - lam j) / M * D := by
      rw [hqi, hqj]; field_simp
    rw [e1, e2] at e; linarith
  rw [hinc]
  -- the key inequality
  have hκ : (2 * lam i + 2 * lam j - 3) * n ≤ (2 * lam i - 1) * x + (2 * lam j - 1) * y := by
    by_cases hk : 2 * lam i + 2 * lam j - 3 ≤ 0
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * lam i - 1) hx0, mul_nonneg (by linarith : (0:ℝ) ≤ 2 * lam j - 1) hy0,
        mul_nonneg (by linarith : (0:ℝ) ≤ -(2 * lam i + 2 * lam j - 3)) hn0]
    · push Not at hk
      have h1 : (2 * lam i + 2 * lam j - 3) * qj ≤ 2 * lam i - 1 := by
        rw [hqj, mul_div_assoc', div_le_iff₀ hM]; rw [hMdef]; nlinarith
      have h2 : (2 * lam i + 2 * lam j - 3) * qi ≤ 2 * lam j - 1 := by
        rw [hqi, mul_div_assoc', div_le_iff₀ hM]; rw [hMdef]; nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h1 hx0, mul_le_mul_of_nonneg_right h2 hy0,
        mul_le_mul_of_nonneg_left hnle hk.le]
  nlinarith [hκ]


/-! ### The rounding theorem -/

/-- The fractional coordinates of `λ`. -/
noncomputable def fracSet (lam : ι → ℝ) : Finset ι := univ.filter fun k => 0 < lam k ∧ lam k < 1

lemma mem_fracSet {lam : ι → ℝ} {k : ι} : k ∈ fracSet lam ↔ 0 < lam k ∧ lam k < 1 := by
  simp [fracSet]

lemma frac_sum_int {s : ℕ} {lam : ι → ℝ} (hr : ∀ k, 0 ≤ lam k ∧ lam k ≤ 1) (hs : ∑ k, lam k = s) :
    ∃ r : ℤ, ∑ k ∈ fracSet lam, lam k = r := by
  classical
  refine ⟨(s : ℤ) - (univ.filter fun k => lam k = 1).card, ?_⟩
  have h1 : ∀ k, lam k = (if k ∈ fracSet lam then lam k else 0) + (if lam k = 1 then (1 : ℝ) else 0) := by
    intro k
    by_cases hk : k ∈ fracSet lam
    · have := mem_fracSet.mp hk
      simp [hk, this.2.ne]
    · have hk' : ¬ (0 < lam k ∧ lam k < 1) := fun h => hk (mem_fracSet.mpr h)
      rcases (hr k).1.eq_or_lt with h | h
      · simp [hk, ← h]
      · have : lam k = 1 := le_antisymm (hr k).2 (by by_contra hh; push Not at hh; exact hk' ⟨h, hh⟩)
        simp [hk, this]
  have h2 : ∑ k, lam k = ∑ k ∈ fracSet lam, lam k + ((univ.filter fun k => lam k = 1).card : ℝ) := by
    calc ∑ k, lam k = ∑ k, ((if k ∈ fracSet lam then lam k else 0) + (if lam k = 1 then (1 : ℝ) else 0)) :=
          Finset.sum_congr rfl fun k _ => h1 k
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_boole]
  push_cast
  linarith [h2, hs]

theorem exists_hasRounding (s : ℕ) :
    ∀ (n : ℕ) (lam : ι → ℝ) (u : ι → E), (∀ k, 0 ≤ lam k ∧ lam k ≤ 1) → ∑ k, lam k = s →
      (fracSet lam).card = n → HasRounding s lam u (∑ k, lam k * ‖u k‖ ^ 2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro lam u hr hs hn
  by_cases hn0 : n = 0
  · subst hn0
    apply hasRounding_base u _ hs
    intro k
    have hk : k ∉ fracSet lam := by
      rw [Finset.card_eq_zero] at hn; rw [hn]; simp
    rw [mem_fracSet] at hk
    rcases (hr k).1.eq_or_lt with h | h
    · left; exact h.symm
    · right; exact le_antisymm (hr k).2 (by by_contra hh; push Not at hh; exact hk ⟨h, hh⟩)
  · by_cases hcase1 : ∃ i j, i ∈ fracSet lam ∧ j ∈ fracSet lam ∧ i ≠ j ∧ lam i + lam j ≤ 1
    · obtain ⟨i, j, hi, hj, hij, hsum⟩ := hcase1
      have hi' := mem_fracSet.mp hi
      have hj' := mem_fracSet.mp hj
      have hL : 0 < lam i + lam j := add_pos hi'.1 hj'.1
      have hr' : ∀ k, 0 ≤ Function.update (Function.update lam i (lam i + lam j)) j 0 k ∧
          Function.update (Function.update lam i (lam i + lam j)) j 0 k ≤ 1 := by
        intro k
        by_cases hkj : k = j
        · subst hkj; simp
        · by_cases hki : k = i
          · subst hki; simp [Function.update_of_ne hkj]; exact ⟨hL.le, hsum⟩
          · simp [Function.update_of_ne hkj, Function.update_of_ne hki]; exact hr k
      have hs' : ∑ k, Function.update (Function.update lam i (lam i + lam j)) j 0 k = s := by
        rw [sum_two_diff (fun k => Function.update (Function.update lam i (lam i + lam j)) j 0 k) lam hij
          (fun k hki hkj => by simp [Function.update_of_ne hki, Function.update_of_ne hkj])]
        simp [Function.update_of_ne hij]
        linarith [hs]
      have hcard : (fracSet (Function.update (Function.update lam i (lam i + lam j)) j 0)).card < n := by
        have hsub : fracSet (Function.update (Function.update lam i (lam i + lam j)) j 0) ⊆ (fracSet lam).erase j := by
          intro k hk
          rw [mem_fracSet] at hk
          rw [Finset.mem_erase]
          by_cases hkj : k = j
          · subst hkj; simp at hk
          · refine ⟨hkj, ?_⟩
            by_cases hki : k = i
            · rw [hki]; exact hi
            · rw [mem_fracSet]; simpa [Function.update_of_ne hkj, Function.update_of_ne hki] using hk
        calc _ ≤ ((fracSet lam).erase j).card := Finset.card_le_card hsub
          _ = (fracSet lam).card - 1 := Finset.card_erase_of_mem hj
          _ < n := by omega
      have h2 := (ih _ hcard _
        (Function.update (Function.update u i ((lam i + lam j)⁻¹ • (lam i • u i + lam j • u j))) j 0)
        hr' hs' rfl).stepA hij hi'.1 hj'.1
      rw [potential_A hij hL] at h2
      exact h2
    · push Not at hcase1
      obtain ⟨r, hr_int⟩ := frac_sum_int hr hs
      have hFpos : 0 < (fracSet lam).card := by omega
      have h3 : 2 < (fracSet lam).card := by
        by_contra hle
        push Not at hle
        have hc : (fracSet lam).card = 1 ∨ (fracSet lam).card = 2 := by omega
        rcases hc with hc | hc
        · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
          have haF : a ∈ fracSet lam := by rw [ha]; simp
          have h' := mem_fracSet.mp haF
          rw [ha, Finset.sum_singleton] at hr_int
          have h1 : (0 : ℝ) < r := by rw [← hr_int]; exact h'.1
          have h2 : (r : ℝ) < 1 := by rw [← hr_int]; exact h'.2
          have h1' : (0 : ℤ) < r := by exact_mod_cast h1
          have h2' : r < (1 : ℤ) := by exact_mod_cast h2
          omega
        · obtain ⟨a, b, hab, hab'⟩ := Finset.card_eq_two.mp hc
          have haF : a ∈ fracSet lam := by rw [hab']; simp
          have hbF : b ∈ fracSet lam := by rw [hab']; simp
          have ha' := mem_fracSet.mp haF
          have hb' := mem_fracSet.mp hbF
          have hp := hcase1 a b haF hbF hab
          rw [hab', Finset.sum_pair hab] at hr_int
          have h1 : (1 : ℝ) < r := by rw [← hr_int]; exact hp
          have h2 : (r : ℝ) < 2 := by rw [← hr_int]; linarith [ha'.2, hb'.2]
          have h1' : (1 : ℤ) < r := by exact_mod_cast h1
          have h2' : r < (2 : ℤ) := by exact_mod_cast h2
          omega
      obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp h3
      have pab := hcase1 a b ha hb hab
      have pac := hcase1 a c ha hc hac
      have pbc := hcase1 b c hb hc hbc
      have hB : ∃ i j, i ∈ fracSet lam ∧ j ∈ fracSet lam ∧ i ≠ j ∧ 1 / 2 ≤ lam i ∧ 1 / 2 ≤ lam j := by
        by_cases h1 : 1 / 2 ≤ lam a
        · by_cases h2 : 1 / 2 ≤ lam b
          · exact ⟨a, b, ha, hb, hab, h1, h2⟩
          · push Not at h2
            exact ⟨a, c, ha, hc, hac, h1, by linarith⟩
        · push Not at h1
          exact ⟨b, c, hb, hc, hbc, by linarith, by linarith⟩
      obtain ⟨i, j, hi, hj, hij, hi2, hj2⟩ := hB
      have hi' := mem_fracSet.mp hi
      have hj' := mem_fracSet.mp hj
      have hsum := hcase1 i j hi hj hij
      have hr' : ∀ k, 0 ≤ Function.update (Function.update lam i (lam i + lam j - 1)) j 1 k ∧
          Function.update (Function.update lam i (lam i + lam j - 1)) j 1 k ≤ 1 := by
        intro k
        by_cases hkj : k = j
        · subst hkj; simp
        · by_cases hki : k = i
          · subst hki; simp [Function.update_of_ne hkj]; constructor <;> linarith [hi'.2, hj'.2]
          · simp [Function.update_of_ne hkj, Function.update_of_ne hki]; exact hr k
      have hs' : ∑ k, Function.update (Function.update lam i (lam i + lam j - 1)) j 1 k = s := by
        rw [sum_two_diff (fun k => Function.update (Function.update lam i (lam i + lam j - 1)) j 1 k) lam hij
          (fun k hki hkj => by simp [Function.update_of_ne hki, Function.update_of_ne hkj])]
        simp [Function.update_of_ne hij]
        linarith [hs]
      have hcard : (fracSet (Function.update (Function.update lam i (lam i + lam j - 1)) j 1)).card < n := by
        have hsub : fracSet (Function.update (Function.update lam i (lam i + lam j - 1)) j 1) ⊆ (fracSet lam).erase j := by
          intro k hk
          rw [mem_fracSet] at hk
          rw [Finset.mem_erase]
          by_cases hkj : k = j
          · subst hkj; simp at hk
          · refine ⟨hkj, ?_⟩
            by_cases hki : k = i
            · rw [hki]; exact hi
            · rw [mem_fracSet]; simpa [Function.update_of_ne hkj, Function.update_of_ne hki] using hk
        calc _ ≤ ((fracSet lam).erase j).card := Finset.card_le_card hsub
          _ = (fracSet lam).card - 1 := Finset.card_erase_of_mem hj
          _ < n := by omega
      have h2 := (ih _ hcard _
        (Function.update (Function.update u i
          ((2 - lam i - lam j)⁻¹ • ((1 - lam i) • u i + (1 - lam j) • u j))) j 0)
        hr' hs' rfl).stepB hij hi'.2 hj'.2
      exact h2.mono (potential_B hij hi2 hj2 hi'.2 hj'.2)


/-- **Rounding with a variance bound.** For `λ ∈ [0,1]^ι` with integer sum `s` and any vectors `u_k`
there is a set `T` of size `s` with `‖Σ_{k∈T} u_k − Σ_k λ_k u_k‖² ≤ Σ_k λ_k‖u_k‖²`. -/
theorem exists_set_sq_le (s : ℕ) {lam : ι → ℝ} (u : ι → E) (hr : ∀ k, 0 ≤ lam k ∧ lam k ≤ 1)
    (hs : ∑ k, lam k = s) :
    ∃ T : Finset ι, T.card = s ∧ ‖∑ k ∈ T, u k - ∑ k, lam k • u k‖ ^ 2 ≤ ∑ k, lam k * ‖u k‖ ^ 2 :=
  (exists_hasRounding s _ lam u hr hs rfl).exists_set

/-- The same bound for the complement: `Σ_k (1−λ_k)‖u_k‖²`. -/
theorem exists_set_sq_le_compl (s : ℕ) {lam : ι → ℝ} (u : ι → E) (hr : ∀ k, 0 ≤ lam k ∧ lam k ≤ 1)
    (hs : ∑ k, lam k = s) :
    ∃ T : Finset ι, T.card = s ∧
      ‖∑ k ∈ T, u k - ∑ k, lam k • u k‖ ^ 2 ≤ ∑ k, (1 - lam k) * ‖u k‖ ^ 2 := by
  classical
  have hle : s ≤ Fintype.card ι := by
    have : (s : ℝ) ≤ Fintype.card ι := by
      rw [← hs]
      calc ∑ k, lam k ≤ ∑ _k : ι, (1 : ℝ) := Finset.sum_le_sum fun k _ => (hr k).2
        _ = Fintype.card ι := by simp
    exact_mod_cast this
  have hs' : ∑ k, (1 - lam k) = ((Fintype.card ι - s : ℕ) : ℝ) := by
    rw [Nat.cast_sub hle, Finset.sum_sub_distrib, hs]; simp
  obtain ⟨T', hT'c, hT'⟩ := exists_set_sq_le (Fintype.card ι - s) u
    (lam := fun k => 1 - lam k) (fun k => ⟨by linarith [(hr k).2], by linarith [(hr k).1]⟩) hs'
  refine ⟨univ \ T', ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hT'c]; omega
  · have e : ∑ k ∈ univ \ T', u k - ∑ k, lam k • u k
        = -(∑ k ∈ T', u k - ∑ k, (1 - lam k) • u k) := by
      have h1 : ∑ k ∈ univ \ T', u k = ∑ k, u k - ∑ k ∈ T', u k := by
        rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
      have h2 : ∑ k, (1 - lam k) • u k = ∑ k, u k - ∑ k, lam k • u k := by
        simp only [sub_smul, one_smul, Finset.sum_sub_distrib]
      rw [h1, h2]; abel
    rw [e, norm_neg]; exact hT'

/-- **Theorem 3.2 core (rounding of the fractional part).** One set `T` of size `s` satisfies both bounds,
hence `‖·‖² ≤ min(s, f−s)·a` if `‖u_k‖² ≤ a`, `f = |ι|`. -/
theorem exists_set_sq_le_min (s : ℕ) {lam : ι → ℝ} (u : ι → E) (hr : ∀ k, 0 ≤ lam k ∧ lam k ≤ 1)
    (hs : ∑ k, lam k = s) :
    ∃ T : Finset ι, T.card = s ∧
      ‖∑ k ∈ T, u k - ∑ k, lam k • u k‖ ^ 2 ≤ ∑ k, lam k * ‖u k‖ ^ 2 ∧
      ‖∑ k ∈ T, u k - ∑ k, lam k • u k‖ ^ 2 ≤ ∑ k, (1 - lam k) * ‖u k‖ ^ 2 := by
  classical
  obtain ⟨TA, hA, hA'⟩ := exists_set_sq_le s u hr hs
  obtain ⟨TB, hB, hB'⟩ := exists_set_sq_le_compl s u hr hs
  set cand : Finset (Finset ι) := univ.filter fun T => T.card = s with hcand
  have hne : cand.Nonempty := ⟨TA, by simp [hcand, hA]⟩
  obtain ⟨T, hT, hmin⟩ := Finset.exists_min_image cand (fun T => ‖∑ k ∈ T, u k - ∑ k, lam k • u k‖ ^ 2) hne
  have hTc : T.card = s := by simpa [hcand] using hT
  refine ⟨T, hTc, ?_, ?_⟩
  · exact (hmin TA (by simp [hcand, hA])).trans hA'
  · exact (hmin TB (by simp [hcand, hB])).trans hB'

end SparseSharpe.Factor
