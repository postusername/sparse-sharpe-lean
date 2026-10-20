import SparseSharpe.Factor.PairRounding
import SparseSharpe.Factor.Relaxation
import SparseSharpe.Factor.ClippedDP

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Theorem 3.2 of the analytic note (Theorem 5.16 of the paper): rounding at the saddle point of the relaxation

`SaddleData` collects the conditions of a saddle point `(t, λ)` of `L(t,λ) = t'Pt + Σ λ_i s_i(t)` over
`Λ_k × ℝ^K`. At such a point

* `t` minimizes `g_k` (`SaddleData.isMin`), so `g_k(t) = G*_k`;
* for `T ⊆ I' = {0 < λ < 1}` with `|T| = Σ_{I'} λ`, the loss of the clipped portfolio on `H ∪ T` against `G*_k`
  is the squared norm `‖Σ_{T} v_i − Σ_{I'} λ_i v_i‖²` (`SaddleData.loss_eq`, the defect identity);
* some `T` has loss at most `min(s, f−s)·ωσ ≤ K·ωσ ≤ (Kω/k)·G*_k` (`saddle_rounding`, `saddle_rounding_min`,
  `saddle_rounding_K`, `saddle_rounding_one`), by the rounding lemma of `PairRounding`;
* for any representation of `λ|_{I'}` as a convex combination of `s`-subsets, the average loss is at most
  `f·σ·Σ_{I'} λ_i(1−λ_i)ω_i ≤ f²ωσ/4` (`saddle_rounding_avg`), and a representation exists (`exists_isRep`).
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- The assets with `λ_i = 1` (the set `H` of the saddle point). -/
noncomputable def oneSet (lam : ι → ℝ) : Finset ι := univ.filter fun i => lam i = 1

lemma mem_oneSet {lam : ι → ℝ} {i : ι} : i ∈ oneSet lam ↔ lam i = 1 := by simp [oneSet]

/-- A saddle point `(t, λ)` of `L(t,λ) = t'Pt + Σ λ_i s_i(t)` over `Λ_k × ℝ^K`, written as the conditions
that are used: `λ ∈ [0,1]^M`, `Σλ = k`, stationarity in `t`, and `λ` maximizes the linear function
`Σλ_i s_i(t)`: `λ_i = 1` above the threshold `σ`, `λ_i = 0` below it, ties in between. -/
structure SaddleData (m d : ι → ℝ) (B : ι → κ → ℝ) (P : κ → κ → ℝ) (k : ℕ) (t : κ → ℝ)
    (lam : ι → ℝ) (σ : ℝ) : Prop where
  range : ∀ i, 0 ≤ lam i ∧ lam i ≤ 1
  sum : ∑ i, lam i = k
  stat : ∀ j, ∑ j', P j j' * t j' = ∑ i, lam i * wclip m d B t i * B i j
  one : ∀ i, lam i = 1 → σ ≤ clipScore m d B t i
  zero : ∀ i, lam i = 0 → clipScore m d B t i ≤ σ
  frac : ∀ i, 0 < lam i → lam i < 1 → clipScore m d B t i = σ

lemma sum_split {lam : ι → ℝ} (hr : ∀ k, 0 ≤ lam k ∧ lam k ≤ 1) :
    ∑ i, lam i = ∑ i ∈ fracSet lam, lam i + ((oneSet lam).card : ℝ) := by
  classical
  have h1 : ∀ k, lam k = (if k ∈ fracSet lam then lam k else 0) + (if k ∈ oneSet lam then (1 : ℝ) else 0) := by
    intro k
    by_cases hk : k ∈ fracSet lam
    · have := mem_fracSet.mp hk
      have : k ∉ oneSet lam := by rw [mem_oneSet]; exact this.2.ne
      simp [hk, this]
    · have hk' : ¬ (0 < lam k ∧ lam k < 1) := fun h => hk (mem_fracSet.mpr h)
      rcases (hr k).1.eq_or_lt with h | h
      · have : k ∉ oneSet lam := by rw [mem_oneSet]; rw [← h]; norm_num
        simp [hk, this, ← h]
      · have : lam k = 1 := le_antisymm (hr k).2 (by by_contra hh; push Not at hh; exact hk' ⟨h, hh⟩)
        have : k ∈ oneSet lam := mem_oneSet.mpr this
        simp [hk, this, ‹lam k = 1›]
  calc ∑ k, lam k = ∑ k, ((if k ∈ fracSet lam then lam k else 0) + (if k ∈ oneSet lam then (1 : ℝ) else 0)) :=
        Finset.sum_congr rfl fun k _ => h1 k
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]


/-- At a stationary point the point `Gt` is the weighted sum `Σ_i λ_i v_i(t)` of the vectors of the defect. -/
lemma dotp_G_eq_sum_lam (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {t : κ → ℝ} {lam : ι → ℝ}
    (hstat : ∀ j, ∑ j', P j j' * t j' = ∑ i, lam i * wclip m d B t i * B i j) (l : κ) :
    dotp (G l) t = ∑ i, lam i * vcoord G Sf B (wclip m d B t) i l := by
  have hSP := SP_of_PS (P := P) (Sf := Sf) hPS
  set wl : ι → ℝ := fun i => lam i * wclip m d B t i with hwl
  have hBw : ∀ j, Bw B univ wl j = ∑ j', P j j' * t j' := by
    intro j; rw [hstat j]
    exact Finset.sum_congr rfl fun i _ => by simp only [hwl]; ring
  have htw : tw Sf B univ wl = t := by
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
  have h := dotp_G_tw (G := G) (Sf := Sf) (B := B) univ wl l
  rw [htw] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => by simp only [vcoord, hwl]; ring

section Saddle
variable {k : ℕ} {t : κ → ℝ} {lam : ι → ℝ} {σ : ℝ}

lemma SaddleData.top (hS : SaddleData m d B P k t lam σ) {T : Finset ι} (hT : T ⊆ fracSet lam) :
    (∀ i ∈ oneSet lam ∪ T, σ ≤ clipScore m d B t i) ∧
      (∀ j ∉ oneSet lam ∪ T, clipScore m d B t j ≤ σ) := by
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · rcases Finset.mem_union.mp hi with h | h
    · exact hS.one i (mem_oneSet.mp h)
    · have := mem_fracSet.mp (hT h)
      exact (hS.frac i this.1 this.2).ge
  · rw [Finset.mem_union, not_or] at hj
    have h1 : lam j ≠ 1 := fun h => hj.1 (mem_oneSet.mpr h)
    rcases (hS.range j).1.eq_or_lt with h | h
    · exact hS.zero j h.symm
    · have h2 : lam j < 1 := lt_of_le_of_ne (hS.range j).2 h1
      exact (hS.frac j h h2).le

/-- The identity `g_k(t) = t'Pt + Σ_i λ_i s_i(t)` at a saddle point. -/
theorem SaddleData.dualBound_eq (hd : ∀ i, 0 < d i) (hS : SaddleData m d B P k t lam σ)
    {T : Finset ι} (hT : T ⊆ fracSet lam) (hs : ∑ i ∈ fracSet lam, lam i = T.card) :
    (oneSet lam ∪ T).card = k ∧
      dualBound m d B P k t = quadf P t + ∑ i ∈ oneSet lam ∪ T, clipScore m d B t i ∧
      ∑ i, lam i * clipScore m d B t i = ∑ i ∈ oneSet lam ∪ T, clipScore m d B t i := by
  classical
  have hdisj : Disjoint (oneSet lam) T := by
    rw [Finset.disjoint_left]
    intro i hi hiT
    have h1 := mem_oneSet.mp hi
    have h2 := mem_fracSet.mp (hT hiT)
    linarith [h2.2]
  have hcard : (oneSet lam ∪ T).card = k := by
    rw [Finset.card_union_of_disjoint hdisj]
    have := sum_split hS.range
    rw [hS.sum, hs] at this
    have hk : k = (oneSet lam).card + T.card := by
      have : (k : ℝ) = (T.card : ℝ) + (oneSet lam).card := this
      have : k = T.card + (oneSet lam).card := by exact_mod_cast this
      omega
    omega
  refine ⟨hcard, ?_⟩
  obtain ⟨hup, hlow⟩ := hS.top hT
  have htop : ∀ i ∈ oneSet lam ∪ T, ∀ j ∉ oneSet lam ∪ T,
      (max (m j - dotp (B j) t) 0) ^ 2 / d j ≤ (max (m i - dotp (B i) t) 0) ^ 2 / d i :=
    fun i hi j hj => (hlow j hj).trans (hup i hi)
  have hdb := dualBound_eq_of_top (P := P) hd t (Or.inl hcard) hcard.le htop
  refine ⟨hdb, ?_⟩
  have hdec : ∀ i, lam i * clipScore m d B t i
      = (if i ∈ oneSet lam then clipScore m d B t i else 0) + (if i ∈ fracSet lam then lam i * σ else 0) := by
    intro i
    by_cases h1 : i ∈ oneSet lam
    · have := mem_oneSet.mp h1
      have : i ∉ fracSet lam := fun h => by have := mem_fracSet.mp h; linarith [this.2]
      simp [h1, this, mem_oneSet.mp h1]
    · by_cases h2 : i ∈ fracSet lam
      · have := mem_fracSet.mp h2
        simp [h1, h2, hS.frac i this.1 this.2]
      · have hz : lam i = 0 := by
          rcases (hS.range i).1.eq_or_lt with h | h
          · exact h.symm
          · exfalso
            have h3 : lam i ≠ 1 := fun h' => h1 (mem_oneSet.mpr h')
            exact h2 (mem_fracSet.mpr ⟨h, lt_of_le_of_ne (hS.range i).2 h3⟩)
        simp [h1, h2, hz]
  rw [Finset.sum_congr rfl fun i _ => hdec i, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
    Finset.univ_inter, Finset.univ_inter, ← Finset.sum_mul, hs]
  rw [Finset.sum_union hdisj]
  have hT' : ∑ i ∈ T, clipScore m d B t i = T.card * σ := by
    rw [Finset.sum_congr rfl fun i hi => (hS.frac i (mem_fracSet.mp (hT hi)).1 (mem_fracSet.mp (hT hi)).2)]
    simp
  rw [hT']

/-- The number of ties selected: `s = k − |H|` is the sum of the fractional multipliers. -/
lemma SaddleData.exists_s (hS : SaddleData m d B P k t lam σ) :
    ∃ s : ℕ, ∑ i ∈ fracSet lam, lam i = s ∧ (oneSet lam).card + s = k := by
  have h := sum_split hS.range
  rw [hS.sum] at h
  have hnn : 0 ≤ ∑ i ∈ fracSet lam, lam i := Finset.sum_nonneg fun i _ => (hS.range i).1
  have hle : (oneSet lam).card ≤ k := by
    have : ((oneSet lam).card : ℝ) ≤ k := by linarith
    exact_mod_cast this
  refine ⟨k - (oneSet lam).card, ?_, by omega⟩
  rw [Nat.cast_sub hle]; linarith

lemma SaddleData.exists_sub (hS : SaddleData m d B P k t lam σ) {s : ℕ}
    (hs : ∑ i ∈ fracSet lam, lam i = s) : ∃ T ⊆ fracSet lam, T.card = s := by
  apply Finset.exists_subset_card_eq
  have : (s : ℝ) ≤ (fracSet lam).card := by
    rw [← hs]
    calc ∑ i ∈ fracSet lam, lam i ≤ ∑ _i ∈ fracSet lam, (1 : ℝ) :=
          Finset.sum_le_sum fun i hi => (mem_fracSet.mp hi).2.le
      _ = (fracSet lam).card := by simp
  exact_mod_cast this

/-- For `λ ∈ Λ_k` the linear function `Σ λ_i v_i` is at most the sum of `k` terms. -/
lemma exists_set_ge_of_range {s : ℕ} {lam : ι → ℝ} (hr : ∀ i, 0 ≤ lam i ∧ lam i ≤ 1)
    (hs : ∑ i, lam i = s) (v : ι → ℝ) :
    ∃ T : Finset ι, T.card = s ∧ ∑ i, lam i * v i ≤ ∑ i ∈ T, v i := by
  have h := exists_hasRounding (E := ℝ) s _ lam (fun _ => 0) hr hs rfl
  exact h.exists_set_ge v

/-- The Lagrangian `L(t, λ) = t'Pt + Σ λ_i s_i(t)` of any `λ ∈ [0,1]^M` with `Σ λ = k` is at most `g_k(t)`
(the maximum of a linear function over the hypersimplex is the sum of the `k` largest scores). -/
lemma lagrangian_le_dualBound (hr : ∀ i, 0 ≤ lam i ∧ lam i ≤ 1) (hs : ∑ i, lam i = k) :
    quadf P t + ∑ i, lam i * clipScore m d B t i ≤ dualBound m d B P k t := by
  classical
  obtain ⟨T', hT'c, hT'⟩ := exists_set_ge_of_range hr hs (fun i => clipScore m d B t i)
  have hsup : ∑ i ∈ T', clipScore m d B t i ≤ ((Finset.univ : Finset (Finset ι)).filter
      fun S => S.card ≤ k).sup' (supportsLe_nonempty k)
      (fun S => ∑ i ∈ S, (max (m i - dotp (B i) t) 0) ^ 2 / d i) :=
    Finset.le_sup' (fun S : Finset ι => ∑ i ∈ S, (max (m i - dotp (B i) t) 0) ^ 2 / d i)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ T', by rw [hT'c]⟩)
  unfold dualBound
  have : ∑ i, lam i * clipScore m d B t i ≤ ∑ i ∈ T', clipScore m d B t i := hT'
  linarith

/-- At a saddle point `g_k(t) = L(t, λ)`. -/
theorem SaddleData.dualBound_eq_lagrangian (hd : ∀ i, 0 < d i) (hS : SaddleData m d B P k t lam σ) :
    dualBound m d B P k t = quadf P t + ∑ i, lam i * clipScore m d B t i := by
  classical
  obtain ⟨s, hs, -⟩ := hS.exists_s
  obtain ⟨T, hT, hTc⟩ := hS.exists_sub hs
  have heq' := hS.dualBound_eq hd hT (by rw [hs, hTc])
  rw [heq'.2.1, heq'.2.2]

/-- **A saddle point minimizes the dual bound**: `G*_k = g_k(t)`. -/
theorem SaddleData.isMin [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hS : SaddleData m d B P k t lam σ) : ∀ t', dualBound m d B P k t ≤ dualBound m d B P k t' := by
  intro t'
  obtain ⟨s, hs, hk⟩ := hS.exists_s
  obtain ⟨T, hT, hTc⟩ := hS.exists_sub hs
  have heq' := hS.dualBound_eq hd hT (by rw [hs, hTc])
  have heq : dualBound m d B P k t = quadf P t + ∑ i, lam i * clipScore m d B t i := by
    rw [heq'.2.1, heq'.2.2]
  have hlow := saddle_lower (m := m) (d := d) (B := B) (P := P) (G := G) hd hG (T := univ) t lam
    (fun i _ => (hS.range i).1) (by simpa using hS.stat) t'
  -- Σ λ_i s_i(t') ≤ the top-k sum
  obtain ⟨T', hT'c, hT'⟩ := exists_set_ge_of_range hS.range hS.sum (fun i => clipScore m d B t' i)
  have hsup : ∑ i ∈ T', clipScore m d B t' i ≤ ((Finset.univ : Finset (Finset ι)).filter
      fun S => S.card ≤ k).sup' (supportsLe_nonempty k)
      (fun S => ∑ i ∈ S, (max (m i - dotp (B i) t') 0) ^ 2 / d i) :=
    Finset.le_sup' (fun S : Finset ι => ∑ i ∈ S, (max (m i - dotp (B i) t') 0) ^ 2 / d i)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ T', by rw [hT'c]⟩)
  have h1 : dualBound m d B P k t = quadf P t + ∑ i, lam i * clipScore m d B t i := heq
  have h2 : quadf P t' + ∑ i, lam i * clipScore m d B t' i ≤ dualBound m d B P k t' := by
    unfold dualBound
    have : ∑ i, lam i * clipScore m d B t' i ≤ ∑ i ∈ T', clipScore m d B t' i := hT'
    linarith
  have h3 : quadf P t + ∑ i, lam i * clipScore m d B t i
      ≤ quadf P t' + ∑ i, lam i * clipScore m d B t' i := hlow
  linarith


/-- The vector `v_i` of the defect as an element of Euclidean space. -/
noncomputable def vE (G Sf : κ → κ → ℝ) (B : ι → κ → ℝ) (w : ι → ℝ) (i : ι) : EuclideanSpace ℝ κ :=
  WithLp.toLp 2 (fun l => vcoord G Sf B w i l)

/-- For `i` in the fractional set, `‖v_i‖² = σ·ω_i` with `ω_i = B_i'Σ_fB_i/d_i` (`σ` the tied score). -/
lemma SaddleData.sq_norm_v_eq (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hS : SaddleData m d B P k t lam σ) {i : ι} (hi : i ∈ fracSet lam) :
    ∑ l, vcoord G Sf B (wclip m d B t) i l ^ 2 = σ * (sysVar B Sf i / d i) := by
  have hi' := mem_fracSet.mp hi
  have hsc : clipScore m d B t i = σ := hS.frac i hi'.1 hi'.2
  rw [sum_sq_vcoord hG hPS]
  have h1 : wclip m d B t i ^ 2 * sysVar B Sf i = clipScore m d B t i * (sysVar B Sf i / d i) := by
    have := d_mul_wclip_sq (m := m) (B := B) hd t i
    have hdi := (hd i).ne'
    rw [← this]; field_simp
  rw [h1, hsc]

/-- For `i` in the fractional set, `‖v_i‖² ≤ σ·ω` (with `σ` the tied score and `ω ≥ B_i'Σ_fB_i/d_i`). -/
lemma SaddleData.sq_norm_v_le (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hS : SaddleData m d B P k t lam σ) {ω : ℝ} {i : ι} (hi : i ∈ fracSet lam)
    (hω : sysVar B Sf i / d i ≤ ω) :
    ∑ l, vcoord G Sf B (wclip m d B t) i l ^ 2 ≤ σ * ω := by
  rw [hS.sq_norm_v_eq hd hG hPS hi]
  have hi' := mem_fracSet.mp hi
  have hσ : 0 ≤ σ := by rw [← hS.frac i hi'.1 hi'.2]; exact clipScore_nonneg hd t i
  exact mul_le_mul_of_nonneg_left hω hσ

/-- **The loss is the defect.** For `T ⊆ I'` with `|T| = Σ_{I'} λ_i`, the clipped portfolio on `H ∪ T` has
`g_k(t) − obj = ‖Σ_{i∈T} v_i − Σ_{i∈I'} λ_i v_i‖²`. -/
theorem SaddleData.loss_eq (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hS : SaddleData m d B P k t lam σ) {T : Finset ι} (hTF : T ⊆ fracSet lam)
    (hsT : ∑ i ∈ fracSet lam, lam i = T.card) :
    dualBound m d B P k t - objLO m d B Sf (oneSet lam ∪ T) (wclip m d B t)
      = ∑ l, (∑ i ∈ T, vcoord G Sf B (wclip m d B t) i l
          - ∑ i ∈ fracSet lam, lam i * vcoord G Sf B (wclip m d B t) i l) ^ 2 := by
  classical
  set F := fracSet lam with hF
  set w := wclip m d B t with hw
  obtain ⟨hcard, hdb, hlam⟩ := hS.dualBound_eq hd hTF hsT
  have hdef := objLO_wclip_deficit (m := m) (B := B) (Sf := Sf) hd hG hPS (oneSet lam ∪ T) t
  rw [← hw] at hdef
  have hQ : QLO m d B P (oneSet lam ∪ T) t = quadf P t + ∑ i ∈ oneSet lam ∪ T, clipScore m d B t i := rfl
  rw [hdef, hQ, hdb, defect_eq_sum_sq (Sf := Sf) (B := B) hG]
  have hdisj : Disjoint (oneSet lam) T := by
    rw [Finset.disjoint_left]
    intro i hi hiT
    have h1 := mem_oneSet.mp hi
    have h2 := mem_fracSet.mp (hTF hiT)
    linarith [h2.2]
  have hdec : ∀ l, ∑ i, lam i * vcoord G Sf B w i l
      = ∑ i ∈ oneSet lam, vcoord G Sf B w i l + ∑ i ∈ F, lam i * vcoord G Sf B w i l := by
    intro l
    have hp : ∀ i, lam i * vcoord G Sf B w i l
        = (if i ∈ oneSet lam then vcoord G Sf B w i l else 0)
          + (if i ∈ F then lam i * vcoord G Sf B w i l else 0) := by
      intro i
      by_cases h1 : i ∈ oneSet lam
      · have h1' := mem_oneSet.mp h1
        have : i ∉ F := fun h => by have := mem_fracSet.mp h; linarith [this.2]
        simp [h1, this, h1']
      · by_cases h2 : i ∈ F
        · simp [h1, h2]
        · have hz : lam i = 0 := by
            rcases (hS.range i).1.eq_or_lt with h | h
            · exact h.symm
            · exfalso
              have h3 : lam i ≠ 1 := fun h' => h1 (mem_oneSet.mpr h')
              exact h2 (mem_fracSet.mpr ⟨h, lt_of_le_of_ne (hS.range i).2 h3⟩)
          simp [h1, h2, hz]
    rw [Finset.sum_congr rfl fun i _ => hp i, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.univ_inter]
  rw [sub_sub_cancel]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [dotp_G_eq_sum_lam hG hPS hS.stat l, hdec l, Finset.sum_union hdisj]
  ring


/-- **Theorem 3.2(a) (rounding at the saddle point).** Let `(t, λ)` be a saddle point with the set `H = {λ_i = 1}`
and the fractional set `I' = {0 < λ_i < 1}`, `s = Σ_{I'} λ_i`, `f = |I'|`, and let `ω ≥ B_i'Σ_fB_i/d_i` on `I'`.
Then there is `T ⊆ I'` with `|T| = s`, `|H ∪ T| = k`, such that the clipped portfolio `w(t)` on `H ∪ T` loses
`g_k(t) − obj = ‖Σ_{i∈T} v_i − Σ_{i∈I'} λ_i v_i‖²` against the dual bound `g_k(t) = G*_k`, and this loss is at most
`s·ωσ` and at most `(f − s)·ωσ`. -/
theorem saddle_rounding (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hS : SaddleData m d B P k t lam σ) {ω : ℝ} (hω : ∀ i ∈ fracSet lam, sysVar B Sf i / d i ≤ ω) {s : ℕ}
    (hs : ∑ i ∈ fracSet lam, lam i = s) :
    ∃ T : Finset ι, T ⊆ fracSet lam ∧ T.card = s ∧ (oneSet lam ∪ T).card = k ∧
      dualBound m d B P k t - objLO m d B Sf (oneSet lam ∪ T) (wclip m d B t)
        = ∑ l, (∑ i ∈ T, vcoord G Sf B (wclip m d B t) i l
            - ∑ i ∈ fracSet lam, lam i * vcoord G Sf B (wclip m d B t) i l) ^ 2 ∧
      ∑ l, (∑ i ∈ T, vcoord G Sf B (wclip m d B t) i l
            - ∑ i ∈ fracSet lam, lam i * vcoord G Sf B (wclip m d B t) i l) ^ 2 ≤ s * (σ * ω) ∧
      ∑ l, (∑ i ∈ T, vcoord G Sf B (wclip m d B t) i l
            - ∑ i ∈ fracSet lam, lam i * vcoord G Sf B (wclip m d B t) i l) ^ 2
        ≤ ((fracSet lam).card - s : ℝ) * (σ * ω) := by
  classical
  set F := fracSet lam with hF
  set w := wclip m d B t with hw
  -- the rounding of the fractional multipliers
  let u : ↥F → EuclideanSpace ℝ κ := fun x => vE G Sf B w x.1
  let lam' : ↥F → ℝ := fun x => lam x.1
  have hr' : ∀ x : ↥F, 0 ≤ lam' x ∧ lam' x ≤ 1 := fun x => hS.range x.1
  have hs' : ∑ x : ↥F, lam' x = s := by
    simp only [lam']; rw [Finset.sum_coe_sort F lam]; exact hs
  obtain ⟨T', hT'c, hA, hB⟩ := exists_set_sq_le_min s u hr' hs'
  set T : Finset ι := T'.map (Function.Embedding.subtype _) with hTdef
  have hTF : T ⊆ F := by
    intro i hi
    rw [hTdef, Finset.mem_map] at hi
    obtain ⟨x, _, rfl⟩ := hi
    exact x.2
  have hTc : T.card = s := by rw [hTdef, Finset.card_map, hT'c]
  have hsT : ∑ i ∈ F, lam i = T.card := by rw [hs, hTc]
  obtain ⟨hcard, hdb, hlam⟩ := hS.dualBound_eq hd hTF hsT
  -- coordinates of the rounding error
  set Lc : κ → ℝ := fun l => ∑ i ∈ T, vcoord G Sf B w i l - ∑ i ∈ F, lam i * vcoord G Sf B w i l with hLc
  have hnorm : ‖∑ x ∈ T', u x - ∑ x : ↥F, lam' x • u x‖ ^ 2 = ∑ l, Lc l ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun l _ => ?_
    have e1 : (∑ x ∈ T', u x - ∑ x : ↥F, lam' x • u x).ofLp l
        = ∑ x ∈ T', vcoord G Sf B w x.1 l - ∑ x : ↥F, lam x.1 * vcoord G Sf B w x.1 l := by
      simp [u, lam', vE, WithLp.ofLp_sum, WithLp.ofLp_smul]
    have e2 : ∑ x ∈ T', vcoord G Sf B w x.1 l = ∑ i ∈ T, vcoord G Sf B w i l := by
      rw [hTdef, Finset.sum_map]; rfl
    have e3 : ∑ x : ↥F, lam x.1 * vcoord G Sf B w x.1 l = ∑ i ∈ F, lam i * vcoord G Sf B w i l :=
      Finset.sum_coe_sort F fun i => lam i * vcoord G Sf B w i l
    rw [e1, e2, e3]
  have hloss : dualBound m d B P k t - objLO m d B Sf (oneSet lam ∪ T) w = ∑ l, Lc l ^ 2 :=
    hS.loss_eq hd hG hPS hTF hsT
  -- the bounds
  have hvF : ∀ i ∈ F, ∑ l, vcoord G Sf B w i l ^ 2 ≤ σ * ω :=
    fun i hi => hS.sq_norm_v_le hd hG hPS hi (hω i hi)
  have hnu : ∀ x : ↥F, ‖u x‖ ^ 2 ≤ σ * ω := by
    intro x
    have := hvF x.1 x.2
    simp only [u, vE]
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa using this
  refine ⟨T, hTF, hTc, hcard, hloss, ?_, ?_⟩
  · have h1 : ∑ x : ↥F, lam' x * ‖u x‖ ^ 2 ≤ ∑ x : ↥F, lam' x * (σ * ω) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hnu x) (hr' x).1
    rw [← Finset.sum_mul, hs'] at h1
    rw [← hnorm]; exact hA.trans h1
  · have h1 : ∑ x : ↥F, (1 - lam' x) * ‖u x‖ ^ 2 ≤ ∑ x : ↥F, (1 - lam' x) * (σ * ω) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hnu x) (by linarith [(hr' x).2])
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, hs'] at h1
    have hcardF : ∑ _x : ↥F, (1 : ℝ) = F.card := by simp
    rw [hcardF] at h1
    rw [← hnorm]; exact hB.trans h1


/-- At a saddle point with `k ≥ 1`: `k·σ ≤ g_k(t)`. -/
lemma SaddleData.sigma_mul_le (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hS : SaddleData m d B P k t lam σ) {s : ℕ} (hs : ∑ i ∈ fracSet lam, lam i = s) :
    (k : ℝ) * σ ≤ dualBound m d B P k t := by
  classical
  obtain ⟨T, hTF, hTc⟩ := hS.exists_sub hs
  obtain ⟨hcard, hdb, -⟩ := hS.dualBound_eq hd hTF (by rw [hs, hTc])
  obtain ⟨hup, -⟩ := hS.top hTF
  rw [hdb]
  have hq : 0 ≤ quadf P t := quadf_nonneg_of_root hG t
  have : (k : ℝ) * σ ≤ ∑ i ∈ oneSet lam ∪ T, clipScore m d B t i := by
    calc (k : ℝ) * σ = ∑ _i ∈ oneSet lam ∪ T, σ := by rw [Finset.sum_const, hcard]; simp
      _ ≤ _ := Finset.sum_le_sum fun i hi => hup i hi
  linarith

/-- **Theorem 3.2(a), the form of the statement.** Let `(t, λ)` be a saddle point, `Fopt` an upper bound of the
objective of every long-only portfolio with at most `k` names (for instance `OPT_LO(k)`). Then `t` minimizes `g_k`,
and for some `T ⊆ I'` of size `s` the support `R° = H ∪ T` (`|R°| = k`) satisfies
`G*_k − Fopt ≤ G*_k − obj(R°, w(t)) ≤ min(s, f−s)·ωσ`. -/
theorem saddle_rounding_min [Nonempty κ] (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hS : SaddleData m d B P k t lam σ) {ω : ℝ} (hω : ∀ i ∈ fracSet lam, sysVar B Sf i / d i ≤ ω) {s : ℕ}
    (hs : ∑ i ∈ fracSet lam, lam i = s) {Fopt : ℝ}
    (hopt : ∀ S : Finset ι, S.card ≤ k → ∀ w : ι → ℝ, (∀ i ∈ S, 0 ≤ w i) → objLO m d B Sf S w ≤ Fopt) :
    (∀ t', dualBound m d B P k t ≤ dualBound m d B P k t') ∧
    ∃ T : Finset ι, T ⊆ fracSet lam ∧ T.card = s ∧ (oneSet lam ∪ T).card = k ∧
      dualBound m d B P k t - Fopt
        ≤ dualBound m d B P k t - objLO m d B Sf (oneSet lam ∪ T) (wclip m d B t) ∧
      dualBound m d B P k t - objLO m d B Sf (oneSet lam ∪ T) (wclip m d B t)
        ≤ min (s : ℝ) ((fracSet lam).card - s) * (σ * ω) := by
  refine ⟨hS.isMin hd hG, ?_⟩
  obtain ⟨T, hTF, hTc, hcard, hloss, hA, hB⟩ := saddle_rounding hd hG hPS hS hω hs
  refine ⟨T, hTF, hTc, hcard, ?_, ?_⟩
  · have := hopt (oneSet lam ∪ T) hcard.le (wclip m d B t) (fun i _ => wclip_nonneg hd t i)
    linarith
  · rw [hloss]
    by_cases hF : (fracSet lam).Nonempty
    · obtain ⟨i, hi⟩ := hF
      have hi' := mem_fracSet.mp hi
      have hσ : 0 ≤ σ := by rw [← hS.frac i hi'.1 hi'.2]; exact clipScore_nonneg hd t i
      have hωi : 0 ≤ ω := le_trans (div_nonneg (sysVar_nonneg hG hPS i) (hd i).le) (hω i hi)
      have hk : 0 ≤ σ * ω := mul_nonneg hσ hωi
      rcases le_total (s : ℝ) ((fracSet lam).card - s) with h | h
      · rw [min_eq_left h]; exact hA
      · rw [min_eq_right h]; exact hB
    · rw [Finset.not_nonempty_iff_eq_empty] at hF
      have hs0 : (s : ℝ) = 0 := by rw [← hs, hF]; simp
      rw [hs0] at hA
      simp only [hF, Finset.card_empty, Nat.cast_zero, zero_sub, neg_zero, hs0, min_self, zero_mul] at hA ⊢
      exact hA

/-- The chain `min(s, f−s) ≤ K` for `f ≤ K+1`. -/
lemma min_le_card {s f K : ℕ} (hK : 1 ≤ K) (hf : f ≤ K + 1) (hsf : s ≤ f) :
    min (s : ℝ) ((f : ℝ) - s) ≤ K := by
  rcases le_total (s : ℝ) ((f : ℝ) - s) with h | h
  · rw [min_eq_left h]
    have : (2 * s : ℝ) ≤ f := by linarith
    have hf' : (f : ℝ) ≤ K + 1 := by exact_mod_cast hf
    have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  · rw [min_eq_right h]
    have : (2 * ((f : ℝ) - s)) ≤ f := by linarith
    have hf' : (f : ℝ) ≤ K + 1 := by exact_mod_cast hf
    have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith


/-- **Theorem 3.2(a), the chain with `K`.** If there are at most `K+1` fractional multipliers (a vertex),
`G*_k − obj(R°) ≤ K·ωσ ≤ (Kω/k)·G*_k`. -/
theorem saddle_rounding_K [Nonempty κ] (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hS : SaddleData m d B P k t lam σ) (hσ0 : 0 ≤ σ) {ω : ℝ} (hω0 : 0 ≤ ω)
    (hω : ∀ i ∈ fracSet lam, sysVar B Sf i / d i ≤ ω) {s : ℕ}
    (hs : ∑ i ∈ fracSet lam, lam i = s) (hk : 1 ≤ k) (hf : (fracSet lam).card ≤ Fintype.card κ + 1) :
    ∃ T : Finset ι, T ⊆ fracSet lam ∧ T.card = s ∧ (oneSet lam ∪ T).card = k ∧
      dualBound m d B P k t - objLO m d B Sf (oneSet lam ∪ T) (wclip m d B t)
          ≤ min (s : ℝ) ((fracSet lam).card - s) * (σ * ω) ∧
      min (s : ℝ) ((fracSet lam).card - s) * (σ * ω) ≤ (Fintype.card κ : ℝ) * (σ * ω) ∧
      (Fintype.card κ : ℝ) * (σ * ω) ≤ ((Fintype.card κ : ℝ) * ω / k) * dualBound m d B P k t := by
  classical
  have hmin := saddle_rounding_min hd hG hPS hS hω hs (Fopt := dualBound m d B P k t)
    (fun S _ w hw => by
      have := objLO_le_dualBound (m := m) (B := B) (Sf := Sf) (P := P) (G := G) hd hG hPS (k := k) (S := S)
        ‹S.card ≤ k› hw t
      exact this)
  obtain ⟨-, T, hTF, hTc, hcard, -, hmain⟩ := hmin
  refine ⟨T, hTF, hTc, hcard, hmain, ?_, ?_⟩
  · have hKpos : 1 ≤ Fintype.card κ := Fintype.card_pos
    have hsf : s ≤ (fracSet lam).card := by
      have : (s : ℝ) ≤ (fracSet lam).card := by
        rw [← hs]
        calc ∑ i ∈ fracSet lam, lam i ≤ ∑ _i ∈ fracSet lam, (1 : ℝ) :=
              Finset.sum_le_sum fun i hi => (mem_fracSet.mp hi).2.le
          _ = (fracSet lam).card := by simp
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right (min_le_card hKpos hf hsf) (mul_nonneg hσ0 hω0)
  · have hks := hS.sigma_mul_le hd hG hs
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hσ' : σ ≤ dualBound m d B P k t / k := by rw [le_div_iff₀ hkpos]; linarith
    have hK0 : (0 : ℝ) ≤ Fintype.card κ * ω := mul_nonneg (Nat.cast_nonneg _) hω0
    calc (Fintype.card κ : ℝ) * (σ * ω) = ((Fintype.card κ : ℝ) * ω) * σ := by ring
      _ ≤ ((Fintype.card κ : ℝ) * ω) * (dualBound m d B P k t / k) := mul_le_mul_of_nonneg_left hσ' hK0
      _ = _ := by ring

/-- **Theorem 3.2(a), the factor `K` disappears for `s = 1` or `s = f − 1`:**
`G*_k − obj(R°) ≤ ωσ ≤ (ω/k)·G*_k`. -/
theorem saddle_rounding_one [Nonempty κ] (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hS : SaddleData m d B P k t lam σ) (hσ0 : 0 ≤ σ) {ω : ℝ} (hω0 : 0 ≤ ω)
    (hω : ∀ i ∈ fracSet lam, sysVar B Sf i / d i ≤ ω) {s : ℕ}
    (hs : ∑ i ∈ fracSet lam, lam i = s) (hk : 1 ≤ k)
    (h1 : s = 1 ∨ s + 1 = (fracSet lam).card) :
    ∃ T : Finset ι, T ⊆ fracSet lam ∧ T.card = s ∧ (oneSet lam ∪ T).card = k ∧
      dualBound m d B P k t - objLO m d B Sf (oneSet lam ∪ T) (wclip m d B t) ≤ σ * ω ∧
      σ * ω ≤ (ω / k) * dualBound m d B P k t := by
  classical
  have hmin := saddle_rounding_min hd hG hPS hS hω hs (Fopt := dualBound m d B P k t)
    (fun S _ w hw => by
      have := objLO_le_dualBound (m := m) (B := B) (Sf := Sf) (P := P) (G := G) hd hG hPS (k := k) (S := S)
        ‹S.card ≤ k› hw t
      exact this)
  obtain ⟨-, T, hTF, hTc, hcard, -, hmain⟩ := hmin
  refine ⟨T, hTF, hTc, hcard, ?_, ?_⟩
  · have hm : min (s : ℝ) (((fracSet lam).card : ℝ) - s) ≤ 1 := by
      rcases h1 with h | h
      · exact (min_le_left _ _).trans (by simp [h])
      · refine (min_le_right _ _).trans ?_
        have : ((fracSet lam).card : ℝ) = s + 1 := by exact_mod_cast h.symm
        linarith
    exact hmain.trans (by nlinarith [mul_nonneg hσ0 hω0])
  · have hks := hS.sigma_mul_le hd hG hs
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hσ' : σ ≤ dualBound m d B P k t / k := by rw [le_div_iff₀ hkpos]; linarith
    calc σ * ω = ω * σ := by ring
      _ ≤ ω * (dualBound m d B P k t / k) := mul_le_mul_of_nonneg_left hσ' hω0
      _ = _ := by ring

/-- Coordinatewise Cauchy–Schwarz: the loss of an arbitrary `T ⊆ I'` with `|T| = Σ_{I'} λ` is at most
`f·σ·Σ_{i∈I'} (1_T(i) − λ_i)² ω_i`, `ω_i = B_i'Σ_fB_i/d_i`. -/
lemma SaddleData.loss_le_card_mul (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hS : SaddleData m d B P k t lam σ)
    {T : Finset ι} (hTF : T ⊆ fracSet lam) (hsT : ∑ i ∈ fracSet lam, lam i = T.card) :
    dualBound m d B P k t - objLO m d B Sf (oneSet lam ∪ T) (wclip m d B t)
      ≤ (fracSet lam).card * ∑ i ∈ fracSet lam,
          ((if i ∈ T then (1 : ℝ) else 0) - lam i) ^ 2 * (σ * (sysVar B Sf i / d i)) := by
  classical
  set F := fracSet lam with hF
  set v : ι → κ → ℝ := fun i l => vcoord G Sf B (wclip m d B t) i l with hv
  rw [hS.loss_eq hd hG hPS hTF hsT]
  have h1 : ∀ l, ∑ i ∈ T, v i l - ∑ i ∈ F, lam i * v i l
      = ∑ i ∈ F, ((if i ∈ T then (1 : ℝ) else 0) - lam i) * v i l := by
    intro l
    have : ∑ i ∈ T, v i l = ∑ i ∈ F, (if i ∈ T then (1 : ℝ) else 0) * v i l := by
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hTF]
    rw [this, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∀ i ∈ F, ∑ l, v i l ^ 2 = σ * (sysVar B Sf i / d i) :=
    fun i hi => hS.sq_norm_v_eq hd hG hPS hi
  calc ∑ l, (∑ i ∈ T, vcoord G Sf B (wclip m d B t) i l - ∑ i ∈ F, lam i * vcoord G Sf B (wclip m d B t) i l) ^ 2
      = ∑ l, (∑ i ∈ F, ((if i ∈ T then (1 : ℝ) else 0) - lam i) * v i l) ^ 2 :=
        Finset.sum_congr rfl fun l _ => by rw [← h1 l]
    _ ≤ ∑ l, ((F.card : ℝ) * ∑ i ∈ F, (((if i ∈ T then (1 : ℝ) else 0) - lam i) * v i l) ^ 2) :=
        Finset.sum_le_sum fun l _ => sq_sum_le_card_mul_sum_sq
    _ = (F.card : ℝ) * ∑ i ∈ F, ((if i ∈ T then (1 : ℝ) else 0) - lam i) ^ 2 * ∑ l, v i l ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ = (F.card : ℝ) * ∑ i ∈ F, ((if i ∈ T then (1 : ℝ) else 0) - lam i) ^ 2 * (σ * (sysVar B Sf i / d i)) := by
        congr 1
        exact Finset.sum_congr rfl fun i hi => by rw [h2 i hi]

/-- A representation of the fractional multipliers as a convex combination of `s`-subsets of `I'`. -/
def IsRep (F : Finset ι) (s : ℕ) (lam : ι → ℝ) {Ω : Type} [Fintype Ω] (p : Ω → ℝ) (T : Ω → Finset ι) : Prop :=
  (∀ ω, 0 ≤ p ω) ∧ ∑ ω, p ω = 1 ∧ (∀ ω, p ω ≠ 0 → T ω ⊆ F ∧ (T ω).card = s) ∧
    ∀ i ∈ F, ∑ ω, p ω * (if i ∈ T ω then (1 : ℝ) else 0) = lam i

/-- The variance of the indicator: `Σ_ω p_ω (1_{T_ω}(i) − λ_i)² = λ_i(1 − λ_i)`. -/
lemma IsRep.var {F : Finset ι} {s : ℕ} {lam : ι → ℝ} {Ω : Type} [Fintype Ω] {p : Ω → ℝ} {T : Ω → Finset ι}
    (h : IsRep F s lam p T) {i : ι} (hi : i ∈ F) :
    ∑ ω, p ω * ((if i ∈ T ω then (1 : ℝ) else 0) - lam i) ^ 2 = lam i * (1 - lam i) := by
  have hm := h.2.2.2 i hi
  have e : ∀ ω, p ω * ((if i ∈ T ω then (1 : ℝ) else 0) - lam i) ^ 2
      = (1 - 2 * lam i) * (p ω * (if i ∈ T ω then (1 : ℝ) else 0)) + lam i ^ 2 * p ω := by
    intro ω
    by_cases hh : i ∈ T ω <;> simp [hh] <;> ring
  rw [Finset.sum_congr rfl fun ω _ => e ω, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hm, h.2.1]
  ring

/-- **Theorem 3.2(b), the average over a representation.** If `λ|_{I'}` is written as a convex combination of
`s`-subsets `T_ω ⊆ I'` (`s = Σ_{I'} λ`), then
`Σ_ω p_ω (g_k(t) − obj(H ∪ T_ω)) ≤ f·σ·Σ_{I'} λ_i(1 − λ_i) ω_i ≤ f²ωσ/4`
(`ω_i = B_i'Σ_fB_i/d_i ≤ ω` on `I'`), and some `T_ω` with `p_ω ≠ 0` is at least as good as the average. -/
theorem saddle_rounding_avg (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hS : SaddleData m d B P k t lam σ) {s : ℕ}
    (hs : ∑ i ∈ fracSet lam, lam i = s) {Ω : Type} [Fintype Ω] {p : Ω → ℝ} {T : Ω → Finset ι}
    (hrep : IsRep (fracSet lam) s lam p T) :
    ∑ a, p a * (dualBound m d B P k t - objLO m d B Sf (oneSet lam ∪ T a) (wclip m d B t))
        ≤ (fracSet lam).card * (σ * ∑ i ∈ fracSet lam, lam i * (1 - lam i) * (sysVar B Sf i / d i)) ∧
      (∀ {ω : ℝ}, (∀ i ∈ fracSet lam, sysVar B Sf i / d i ≤ ω) →
        (fracSet lam).card * (σ * ∑ i ∈ fracSet lam, lam i * (1 - lam i) * (sysVar B Sf i / d i))
          ≤ (fracSet lam).card * (fracSet lam).card / 4 * (σ * ω)) ∧
      ∃ a, p a ≠ 0 ∧ (T a ⊆ fracSet lam ∧ (T a).card = s ∧ (oneSet lam ∪ T a).card = k) ∧
        dualBound m d B P k t - objLO m d B Sf (oneSet lam ∪ T a) (wclip m d B t)
          ≤ ∑ a', p a' * (dualBound m d B P k t - objLO m d B Sf (oneSet lam ∪ T a') (wclip m d B t)) := by
  classical
  set F := fracSet lam with hF
  set loss : Ω → ℝ := fun a => dualBound m d B P k t - objLO m d B Sf (oneSet lam ∪ T a) (wclip m d B t)
    with hloss
  -- the pointwise bound
  have hpt : ∀ a, p a ≠ 0 → loss a ≤ F.card * ∑ i ∈ F,
      ((if i ∈ T a then (1 : ℝ) else 0) - lam i) ^ 2 * (σ * (sysVar B Sf i / d i)) := by
    intro a ha
    obtain ⟨hTF, hTc⟩ := hrep.2.2.1 a ha
    exact hS.loss_le_card_mul hd hG hPS hTF (by rw [hs, hTc])
  have havg : ∑ a, p a * loss a ≤ F.card * (σ * ∑ i ∈ F, lam i * (1 - lam i) * (sysVar B Sf i / d i)) := by
    calc ∑ a, p a * loss a
        ≤ ∑ a, p a * ((F.card : ℝ) * ∑ i ∈ F,
            ((if i ∈ T a then (1 : ℝ) else 0) - lam i) ^ 2 * (σ * (sysVar B Sf i / d i))) := by
          refine Finset.sum_le_sum fun a _ => ?_
          by_cases ha : p a = 0
          · simp [ha]
          · exact mul_le_mul_of_nonneg_left (hpt a ha) (hrep.1 a)
      _ = (F.card : ℝ) * ∑ i ∈ F, (∑ a, p a * ((if i ∈ T a then (1 : ℝ) else 0) - lam i) ^ 2)
            * (σ * (sysVar B Sf i / d i)) := by
          set C : ℝ := (F.card : ℝ) with hC
          calc ∑ a, p a * (C * ∑ i ∈ F, ((if i ∈ T a then (1 : ℝ) else 0) - lam i) ^ 2
                  * (σ * (sysVar B Sf i / d i)))
              = ∑ a, ∑ i ∈ F, C * (p a * ((if i ∈ T a then (1 : ℝ) else 0) - lam i) ^ 2
                  * (σ * (sysVar B Sf i / d i))) := by
                refine Finset.sum_congr rfl fun a _ => ?_
                rw [Finset.mul_sum, Finset.mul_sum]
                exact Finset.sum_congr rfl fun i _ => by ring
            _ = ∑ i ∈ F, ∑ a, C * (p a * ((if i ∈ T a then (1 : ℝ) else 0) - lam i) ^ 2
                  * (σ * (sysVar B Sf i / d i))) := Finset.sum_comm
            _ = ∑ i ∈ F, C * ((∑ a, p a * ((if i ∈ T a then (1 : ℝ) else 0) - lam i) ^ 2)
                  * (σ * (sysVar B Sf i / d i))) :=
                Finset.sum_congr rfl fun i _ => by rw [← Finset.mul_sum, ← Finset.sum_mul]
            _ = C * ∑ i ∈ F, (∑ a, p a * ((if i ∈ T a then (1 : ℝ) else 0) - lam i) ^ 2)
                  * (σ * (sysVar B Sf i / d i)) := by rw [Finset.mul_sum]
      _ = _ := by
          congr 1
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i hi => by rw [hrep.var hi]; ring
  refine ⟨havg, ?_, ?_⟩
  · intro ω hω
    by_cases hF' : F.Nonempty
    · obtain ⟨i, hi⟩ := hF'
      have hi' := mem_fracSet.mp hi
      have hσ : 0 ≤ σ := by rw [← hS.frac i hi'.1 hi'.2]; exact clipScore_nonneg hd _ i
      have hωi : ∀ i ∈ F, 0 ≤ sysVar B Sf i / d i := fun i _ =>
        div_nonneg (sysVar_nonneg hG hPS i) (hd i).le
      have hsum : ∑ i ∈ F, lam i * (1 - lam i) * (sysVar B Sf i / d i) ≤ (F.card / 4 : ℝ) * ω := by
        calc ∑ i ∈ F, lam i * (1 - lam i) * (sysVar B Sf i / d i) ≤ ∑ _i ∈ F, (1 / 4 : ℝ) * ω :=
              Finset.sum_le_sum fun i hi => by
                have h1 : lam i * (1 - lam i) ≤ 1 / 4 := by nlinarith [sq_nonneg (lam i - 1 / 2)]
                have h2 : 0 ≤ lam i * (1 - lam i) := by
                  have := mem_fracSet.mp hi; nlinarith [this.1, this.2]
                calc lam i * (1 - lam i) * (sysVar B Sf i / d i) ≤ (1 / 4) * (sysVar B Sf i / d i) :=
                      mul_le_mul_of_nonneg_right h1 (hωi i hi)
                  _ ≤ (1 / 4) * ω := mul_le_mul_of_nonneg_left (hω i hi) (by norm_num)
          _ = (F.card / 4 : ℝ) * ω := by simp; ring
      have hk : 0 ≤ (F.card : ℝ) * σ := mul_nonneg (Nat.cast_nonneg _) hσ
      calc (F.card : ℝ) * (σ * ∑ i ∈ F, lam i * (1 - lam i) * (sysVar B Sf i / d i))
          = ((F.card : ℝ) * σ) * ∑ i ∈ F, lam i * (1 - lam i) * (sysVar B Sf i / d i) := by ring
        _ ≤ ((F.card : ℝ) * σ) * ((F.card / 4 : ℝ) * ω) := mul_le_mul_of_nonneg_left hsum hk
        _ = _ := by ring
    · rw [Finset.not_nonempty_iff_eq_empty] at hF'
      simp [hF']
  · -- some `T_a` is at least as good as the average
    have hex : ∃ a, p a ≠ 0 ∧ loss a ≤ ∑ a', p a' * loss a' := by
      by_contra hcon
      push Not at hcon
      have h1 : ∑ a, p a * loss a > ∑ a, p a * (∑ a', p a' * loss a') := by
        have hle : ∀ a, p a * (∑ a', p a' * loss a') ≤ p a * loss a := by
          intro a
          by_cases ha : p a = 0
          · simp [ha]
          · exact mul_le_mul_of_nonneg_left (hcon a ha).le (hrep.1 a)
        have hlt : ∃ a, p a * (∑ a', p a' * loss a') < p a * loss a := by
          have hp1 := hrep.2.1
          have : ∃ a, p a ≠ 0 := by
            by_contra hh; push Not at hh
            have : ∑ a, p a = 0 := Finset.sum_eq_zero fun a _ => hh a
            linarith
          obtain ⟨a, ha⟩ := this
          exact ⟨a, mul_lt_mul_of_pos_left (hcon a ha) (lt_of_le_of_ne (hrep.1 a) (Ne.symm ha))⟩
        obtain ⟨a, ha⟩ := hlt
        exact Finset.sum_lt_sum (fun a _ => hle a) ⟨a, Finset.mem_univ _, ha⟩
      rw [← Finset.sum_mul, hrep.2.1, one_mul] at h1
      exact lt_irrefl _ h1
    obtain ⟨a, ha, hla⟩ := hex
    obtain ⟨hTF, hTc⟩ := hrep.2.2.1 a ha
    obtain ⟨hcard, -, -⟩ := hS.dualBound_eq hd hTF (by rw [hs, hTc])
    exact ⟨a, ha, ⟨hTF, hTc, hcard⟩, hla⟩

/-- **A representation exists**: `λ|_{I'}` with `Σ_{I'} λ = s` is a convex combination of `s`-subsets of `I'`. -/
theorem exists_isRep {lam : ι → ℝ} (hr : ∀ i, 0 ≤ lam i ∧ lam i ≤ 1) {s : ℕ}
    (hs : ∑ i ∈ fracSet lam, lam i = s) :
    ∃ (Ω : Type) (_ : Fintype Ω) (p : Ω → ℝ) (T : Ω → Finset ι), IsRep (fracSet lam) s lam p T := by
  classical
  set F := fracSet lam with hF
  let lam' : ↥F → ℝ := fun x => lam x.1
  have hr' : ∀ x : ↥F, 0 ≤ lam' x ∧ lam' x ≤ 1 := fun x => hr x.1
  have hs' : ∑ x : ↥F, lam' x = s := by
    simp only [lam']; rw [Finset.sum_coe_sort F lam]; exact hs
  obtain ⟨Ω, hΩ, p, T', hp0, hp1, hpc, hmarg, -⟩ := exists_hasRounding (E := ℝ) s _ lam' (fun _ => 0) hr' hs' rfl
  refine ⟨Ω, hΩ, p, fun ω => (T' ω).map (Function.Embedding.subtype _), hp0, hp1, fun ω hω => ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    rw [Finset.mem_map] at hi
    obtain ⟨x, _, rfl⟩ := hi
    exact x.2
  · rw [Finset.card_map]; exact hpc ω hω
  · intro i hi
    have h1 := hmarg ⟨i, hi⟩
    have h2 : ∀ ω, (i ∈ (T' ω).map (Function.Embedding.subtype _)) ↔ (⟨i, hi⟩ : ↥F) ∈ T' ω := by
      intro ω; simp only [Finset.mem_map, Function.Embedding.subtype_apply]
      constructor
      · rintro ⟨x, hx, hxi⟩
        have : x = ⟨i, hi⟩ := Subtype.ext hxi
        rwa [this] at hx
      · intro h; exact ⟨⟨i, hi⟩, h, rfl⟩
    simp only [h2]
    exact h1

/-- **Theorem 3.2 in one statement** (parts (i)–(iii) of the paper): a saddle point `(t, λ, σ)` with `σ ≥ 0`, at most
`K+1` fractional multipliers and `ω ≥ 0`, `ω ≥ B_i'Σ_fB_i/d_i` on the fractional set `I'`.
(0) `t` minimizes `g_k`. (i) For every `T ⊆ I'` with `|T| = Σ_{I'} λ` the support `H ∪ T` has `k` names and
`g_k(t) − obj = ‖Σ_T v_i − Σ_{I'} λ_i v_i‖²`. (ii) Some such `T` has loss at most
`min(s, f−s)·σω ≤ K·σω ≤ (Kω/k)·g_k(t)`, and one has loss at most `σω ≤ (ω/k)·g_k(t)` if `s = 1` or `s = f−1`.
(iii) For every representation of `λ|_{I'}` as a convex combination of `s`-subsets of `I'` the average loss is at most
`f·σ·Σλ(1−λ)ω_i ≤ f²σω/4`, some `T_a` is at least as good, and a representation exists. -/
theorem saddle_rounding_theorem [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hS : SaddleData m d B P k t lam σ) (hσ0 : 0 ≤ σ) {ω : ℝ} (hω0 : 0 ≤ ω)
    (hω : ∀ i ∈ fracSet lam, sysVar B Sf i / d i ≤ ω) {s : ℕ}
    (hs : ∑ i ∈ fracSet lam, lam i = s) (hk : 1 ≤ k) (hf : (fracSet lam).card ≤ Fintype.card κ + 1) :
    (∀ t', dualBound m d B P k t ≤ dualBound m d B P k t') ∧
    (∀ T : Finset ι, T ⊆ fracSet lam → T.card = s → (oneSet lam ∪ T).card = k ∧
      dualBound m d B P k t - objLO m d B Sf (oneSet lam ∪ T) (wclip m d B t)
        = ∑ l, (∑ i ∈ T, vcoord G Sf B (wclip m d B t) i l
            - ∑ i ∈ fracSet lam, lam i * vcoord G Sf B (wclip m d B t) i l) ^ 2) ∧
    (∃ T : Finset ι, T ⊆ fracSet lam ∧ T.card = s ∧ (oneSet lam ∪ T).card = k ∧
      dualBound m d B P k t - objLO m d B Sf (oneSet lam ∪ T) (wclip m d B t)
          ≤ min (s : ℝ) ((fracSet lam).card - s) * (σ * ω) ∧
      min (s : ℝ) ((fracSet lam).card - s) * (σ * ω) ≤ (Fintype.card κ : ℝ) * (σ * ω) ∧
      (Fintype.card κ : ℝ) * (σ * ω) ≤ ((Fintype.card κ : ℝ) * ω / k) * dualBound m d B P k t) ∧
    ((s = 1 ∨ s + 1 = (fracSet lam).card) →
      ∃ T : Finset ι, T ⊆ fracSet lam ∧ T.card = s ∧ (oneSet lam ∪ T).card = k ∧
        dualBound m d B P k t - objLO m d B Sf (oneSet lam ∪ T) (wclip m d B t) ≤ σ * ω ∧
        σ * ω ≤ (ω / k) * dualBound m d B P k t) ∧
    (∀ (Ω : Type) [Fintype Ω] (p : Ω → ℝ) (T : Ω → Finset ι), IsRep (fracSet lam) s lam p T →
      ∑ a, p a * (dualBound m d B P k t - objLO m d B Sf (oneSet lam ∪ T a) (wclip m d B t))
          ≤ (fracSet lam).card * (σ * ∑ i ∈ fracSet lam, lam i * (1 - lam i) * (sysVar B Sf i / d i)) ∧
        (fracSet lam).card * (σ * ∑ i ∈ fracSet lam, lam i * (1 - lam i) * (sysVar B Sf i / d i))
          ≤ (fracSet lam).card * (fracSet lam).card / 4 * (σ * ω) ∧
        ∃ a, p a ≠ 0 ∧ (T a ⊆ fracSet lam ∧ (T a).card = s ∧ (oneSet lam ∪ T a).card = k) ∧
          dualBound m d B P k t - objLO m d B Sf (oneSet lam ∪ T a) (wclip m d B t)
            ≤ ∑ a', p a' * (dualBound m d B P k t - objLO m d B Sf (oneSet lam ∪ T a') (wclip m d B t))) ∧
    (∃ (Ω : Type) (_ : Fintype Ω) (p : Ω → ℝ) (T : Ω → Finset ι), IsRep (fracSet lam) s lam p T) := by
  classical
  refine ⟨hS.isMin hd hG, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hTF hTc
    have hsT : ∑ i ∈ fracSet lam, lam i = T.card := by rw [hs, hTc]
    obtain ⟨hcard, -, -⟩ := hS.dualBound_eq hd hTF hsT
    exact ⟨hcard, hS.loss_eq hd hG hPS hTF hsT⟩
  · obtain ⟨T, hTF, hTc, hcard, hmain, hK, hchain⟩ := saddle_rounding_K hd hG hPS hS hσ0 hω0 hω hs hk hf
    exact ⟨T, hTF, hTc, hcard, hmain, hK, hchain⟩
  · intro h1
    exact saddle_rounding_one hd hG hPS hS hσ0 hω0 hω hs hk h1
  · intro Ω _ p T hrep
    exact saddle_rounding_avg hd hG hPS hS hs hrep |> fun h => ⟨h.1, h.2.1 hω, h.2.2⟩
  · exact exists_isRep hS.range hs

end Saddle

end SparseSharpe.Factor
