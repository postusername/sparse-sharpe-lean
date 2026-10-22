import SparseSharpe.Factor.UniversalScheme
import SparseSharpe.Factor.SchemeLS
import SparseSharpe.Factor.ClippedTrading
import Mathlib.Analysis.Convex.Radon

set_option linter.style.header false

/-!
# Оценка Хелли: догадки без данных и сильно полиномиальные схемы без `ω`

Пусть `V` — наибольшее значение носителя с не более чем `min(k, K + 1)` именами. Тогда
`V ≤ OPT(k) ≤ (k + 1)·V` — и для long-only (`objLO_le_helly`), и для long-short
(`objLO_le_helly_free`). Доказательство — теорема Хелли в `ℝ^K` (`Convex.helly_theorem'`):
множества `D_i = {t : t'Σ_f⁻¹t ≤ V, (m_i − ⟨B_i,t⟩)₊²/d_i ≤ V}` выпуклы, любые `K + 1` из них
пересекаются (в двойственной точке малого носителя), значит, пересекаются все, и в общей точке
двойственная функция носителя `S` не больше `(|S| + 1)·V`; по слабой двойственности так же
ограничена цель любого портфеля на `S`.

Поэтому вместо `J = ⌈log₂(Σ_i(m_i)₊²/(d_iL))⌉` догадок `L·2^j` хватает `J = ⌈log₂(k + 1)⌉`
догадок `V·2^j`, и семейства Теорем 5.6 и 5.13 становятся **сильно полиномиальными**: их размер
зависит только от `M`, `k`, `1/ε` и `K`, но не от величин данных (`main_theorem_univ_sp`,
`main_theorem_ls_sp`). Примеры: `univ_instance_two_sp`, `ls_instance_sp`.
-/

namespace SparseSharpe.Factor

open Finset

section HellyConvex

variable {κ : Type*} [Fintype κ]

/-- `⟨a, αx + βy⟩ = α⟨a,x⟩ + β⟨a,y⟩`. -/
lemma dotp_combo (a x y : κ → ℝ) (α β : ℝ) :
    dotp a (α • x + β • y) = α * dotp a x + β * dotp a y := by
  simp only [dotp, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Выпуклость квадрата: `(αp + βq)² ≤ αp² + βq²` при `α, β ≥ 0`, `α + β = 1`. -/
lemma sq_combo_le {α β p q : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1) :
    (α * p + β * q) ^ 2 ≤ α * p ^ 2 + β * q ^ 2 := by
  have hβ' : β = 1 - α := by linarith
  subst hβ'
  nlinarith [mul_nonneg (mul_nonneg hα hβ) (sq_nonneg (p - q))]

/-- `{t : Σ_l ⟨g_l,t⟩² ≤ V}` выпукло. -/
lemma convex_sumsq_le (g : κ → κ → ℝ) (V : ℝ) :
    Convex ℝ {t : κ → ℝ | ∑ l, (dotp (g l) t) ^ 2 ≤ V} := by
  intro x hx y hy α β hα hβ hαβ
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  calc ∑ l, (dotp (g l) (α • x + β • y)) ^ 2
      ≤ ∑ l, (α * (dotp (g l) x) ^ 2 + β * (dotp (g l) y) ^ 2) :=
        Finset.sum_le_sum fun l _ => by rw [dotp_combo]; exact sq_combo_le hα hβ hαβ
    _ = α * ∑ l, (dotp (g l) x) ^ 2 + β * ∑ l, (dotp (g l) y) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ α * V + β * V :=
        add_le_add (mul_le_mul_of_nonneg_left hx hα) (mul_le_mul_of_nonneg_left hy hβ)
    _ = V := by rw [← add_mul, hαβ, one_mul]

/-- `{t : (c − ⟨a,t⟩)₊²/δ ≤ V}` выпукло (`δ > 0`). -/
lemma convex_clip_le {c δ : ℝ} (hδ : 0 < δ) (a : κ → ℝ) (V : ℝ) :
    Convex ℝ {t : κ → ℝ | (max (c - dotp a t) 0) ^ 2 / δ ≤ V} := by
  intro x hx y hy α β hα hβ hαβ
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hp : 0 ≤ max (c - dotp a x) 0 := le_max_right _ _
  have hq : 0 ≤ max (c - dotp a y) 0 := le_max_right _ _
  have hr : c - dotp a (α • x + β • y) = α * (c - dotp a x) + β * (c - dotp a y) := by
    rw [dotp_combo]; linear_combination (-c) * hαβ
  have hm : max (c - dotp a (α • x + β • y)) 0
      ≤ α * max (c - dotp a x) 0 + β * max (c - dotp a y) 0 := by
    rw [hr]
    apply max_le
    · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hα)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hβ)
    · exact add_nonneg (mul_nonneg hα hp) (mul_nonneg hβ hq)
  have h0 : 0 ≤ max (c - dotp a (α • x + β • y)) 0 := le_max_right _ _
  have hsq : (max (c - dotp a (α • x + β • y)) 0) ^ 2
      ≤ α * (max (c - dotp a x) 0) ^ 2 + β * (max (c - dotp a y) 0) ^ 2 :=
    le_trans (pow_le_pow_left₀ h0 hm 2) (sq_combo_le hα hβ hαβ)
  calc (max (c - dotp a (α • x + β • y)) 0) ^ 2 / δ
      ≤ (α * (max (c - dotp a x) 0) ^ 2 + β * (max (c - dotp a y) 0) ^ 2) / δ :=
        div_le_div_of_nonneg_right hsq hδ.le
    _ = α * ((max (c - dotp a x) 0) ^ 2 / δ) + β * ((max (c - dotp a y) 0) ^ 2 / δ) := by ring
    _ ≤ α * V + β * V :=
        add_le_add (mul_le_mul_of_nonneg_left hx hα) (mul_le_mul_of_nonneg_left hy hβ)
    _ = V := by rw [← add_mul, hαβ, one_mul]

/-- `{t : (⟨a,t⟩ − c)² ≤ V}` выпукло. -/
lemma convex_sq_affine_le (a : κ → ℝ) (c V : ℝ) :
    Convex ℝ {t : κ → ℝ | (dotp a t - c) ^ 2 ≤ V} := by
  intro x hx y hy α β hα hβ hαβ
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hr : dotp a (α • x + β • y) - c = α * (dotp a x - c) + β * (dotp a y - c) := by
    rw [dotp_combo]; linear_combination c * hαβ
  rw [hr]
  calc (α * (dotp a x - c) + β * (dotp a y - c)) ^ 2
      ≤ α * (dotp a x - c) ^ 2 + β * (dotp a y - c) ^ 2 := sq_combo_le hα hβ hαβ
    _ ≤ α * V + β * V :=
        add_le_add (mul_le_mul_of_nonneg_left hx hα) (mul_le_mul_of_nonneg_left hy hβ)
    _ = V := by rw [← add_mul, hαβ, one_mul]

end HellyConvex

section HellyBound

variable {ι κ : Type*} [Finite ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- **Оценка Хелли, long-only.** Если у каждого подносителя `T ⊆ S` с не более чем `K + 1`
именами цель любого long-only портфеля не больше `V`, то у `S` она не больше `(|S| + 1)·V`. -/
theorem objLO_le_helly [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {S : Finset ι} {V : ℝ}
    (hsmall : ∀ T ⊆ S, T.card ≤ Fintype.card κ + 1 → ∀ w : ι → ℝ, (∀ i ∈ T, 0 ≤ w i) →
      objLO m d B Sf T w ≤ V)
    (w : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) :
    objLO m d B Sf S w ≤ (S.card + 1) * V := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hV0 : 0 ≤ V := by
    have h := hsmall ∅ (Finset.empty_subset _) (by simp) (fun _ => 0) (by simp)
    simpa [objLO] using h
  have hQ : ∀ (T : Finset ι) (t : κ → ℝ), QLO m d B P T t
      = ∑ l, (dotp (G l) t) ^ 2 + ∑ i ∈ T, (max (m i - dotp (B i) t) 0) ^ 2 / d i := by
    intro T t; simp only [QLO, quadf_eq_sum_sq hG]
  -- двойственные точки малых носителей
  have hT : ∀ T ⊆ S, T.card ≤ Fintype.card κ + 1 → ∃ t, QLO m d B P T t ≤ V := by
    intro T hTS hTc
    obtain ⟨z, hzL, hzG⟩ := isGreatest_objLO_isLeast_QLO (m := m) (B := B) (Sf := Sf) (P := P)
      (G := G) hd hG hPS T
    obtain ⟨t, ht⟩ := hzL.1
    obtain ⟨u, hu, hzu⟩ := hzG.1
    exact ⟨t, by rw [← ht, hzu]; exact hsmall T hTS hTc u hu⟩
  -- теорема Хелли
  set D : ι → Set (κ → ℝ) := fun i =>
    {t | ∑ l, (dotp (G l) t) ^ 2 ≤ V} ∩ {t | (max (m i - dotp (B i) t) 0) ^ 2 / d i ≤ V}
    with hD
  have hconv : ∀ i ∈ S, Convex ℝ (D i) := fun i _ =>
    (convex_sumsq_le G V).inter (convex_clip_le (hd i) (B i) V)
  have hinter : ∀ I ⊆ S, I.card ≤ Module.finrank ℝ (κ → ℝ) + 1 →
      (⋂ i ∈ I, D i).Nonempty := by
    intro I hIS hIc
    rw [Module.finrank_fintype_fun_eq_card] at hIc
    obtain ⟨t, ht⟩ := hT I hIS hIc
    rw [hQ] at ht
    have hs0 : 0 ≤ ∑ i ∈ I, (max (m i - dotp (B i) t) 0) ^ 2 / d i :=
      Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hd i).le
    have hq0 : 0 ≤ ∑ l, (dotp (G l) t) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    refine ⟨t, Set.mem_iInter₂.mpr fun i hi => ⟨?_, ?_⟩⟩
    · change ∑ l, (dotp (G l) t) ^ 2 ≤ V
      linarith
    · change (max (m i - dotp (B i) t) 0) ^ 2 / d i ≤ V
      have h1 := Finset.single_le_sum (f := fun j => (max (m j - dotp (B j) t) 0) ^ 2 / d j)
        (fun j _ => div_nonneg (sq_nonneg _) (hd j).le) hi
      linarith
  obtain ⟨t, ht⟩ := Convex.helly_theorem' hconv hinter
  have hmem : ∀ i ∈ S, t ∈ D i := fun i hi => Set.mem_iInter₂.mp ht i hi
  -- слабая двойственность
  have hwd : objLO m d B Sf S w ≤ QLO m d B P S t := by
    obtain ⟨z, hzL, hzG⟩ := isGreatest_objLO_isLeast_QLO (m := m) (B := B) (Sf := Sf) (P := P)
      (G := G) hd hG hPS S
    exact le_trans (hzG.2 ⟨w, hw, rfl⟩) (hzL.2 ⟨t, rfl⟩)
  rcases S.eq_empty_or_nonempty with hS | ⟨i₀, hi₀⟩
  · subst hS
    simp [objLO]
    linarith
  · have hq : ∑ l, (dotp (G l) t) ^ 2 ≤ V := (hmem i₀ hi₀).1
    have hs : ∑ i ∈ S, (max (m i - dotp (B i) t) 0) ^ 2 / d i ≤ ∑ _i ∈ S, V :=
      Finset.sum_le_sum fun i hi => (hmem i hi).2
    rw [Finset.sum_const, nsmul_eq_mul] at hs
    rw [hQ] at hwd
    nlinarith

/-- **Оценка Хелли, long-short.** То же для портфелей любого знака. -/
theorem objLO_le_helly_free (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {S : Finset ι} {V : ℝ}
    (hsmall : ∀ T ⊆ S, T.card ≤ Fintype.card κ + 1 → ∀ w : ι → ℝ,
      objLO m d B Sf T w ≤ V)
    (w : ι → ℝ) :
    objLO m d B Sf S w ≤ (S.card + 1) * V := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hV0 : 0 ≤ V := by
    have h := hsmall ∅ (Finset.empty_subset _) (by simp) (fun _ => 0)
    simpa [objLO] using h
  have hsplit : ∀ (T : Finset ι) (t : κ → ℝ),
      phi (rowsK d B G) (targetsK m d) (barK (κ := κ) T) t
        = ∑ i ∈ T, (dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) t - targetsK m d (Sum.inl i : ι ⊕ κ)) ^ 2
          + ∑ l, (dotp (G l) t) ^ 2 := by
    intro T t
    simp only [phi, barK, Finset.sum_disjSum]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [rowsK, targetsK]
  have hT : ∀ T ⊆ S, T.card ≤ Fintype.card κ + 1 →
      ∃ t, phi (rowsK d B G) (targetsK m d) (barK (κ := κ) T) t ≤ V := by
    intro T hTS hTc
    obtain ⟨th, -, hgr⟩ := isGreatest_objLO_free (m := m) (d := d) (B := B) (Sf := Sf) (P := P)
      (G := G) hd hG hPS T
    obtain ⟨u, hu⟩ := hgr.1
    exact ⟨th, by rw [hu]; exact hsmall T hTS hTc u⟩
  set D : ι → Set (κ → ℝ) := fun i =>
    {t | ∑ l, (dotp (G l) t) ^ 2 ≤ V}
      ∩ {t | (dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) t
          - targetsK m d (Sum.inl i : ι ⊕ κ)) ^ 2 ≤ V} with hD
  have hconv : ∀ i ∈ S, Convex ℝ (D i) := fun i _ =>
    (convex_sumsq_le G V).inter (convex_sq_affine_le _ _ V)
  have hinter : ∀ I ⊆ S, I.card ≤ Module.finrank ℝ (κ → ℝ) + 1 →
      (⋂ i ∈ I, D i).Nonempty := by
    intro I hIS hIc
    rw [Module.finrank_fintype_fun_eq_card] at hIc
    obtain ⟨t, ht⟩ := hT I hIS hIc
    rw [hsplit] at ht
    have hs0 : 0 ≤ ∑ i ∈ I,
        (dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) t - targetsK m d (Sum.inl i : ι ⊕ κ)) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hq0 : 0 ≤ ∑ l, (dotp (G l) t) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    refine ⟨t, Set.mem_iInter₂.mpr fun i hi => ⟨?_, ?_⟩⟩
    · change ∑ l, (dotp (G l) t) ^ 2 ≤ V
      linarith
    · change (dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) t - targetsK m d (Sum.inl i : ι ⊕ κ)) ^ 2
        ≤ V
      have h1 := Finset.single_le_sum
        (f := fun j =>
          (dotp (rowsK d B G (Sum.inl j : ι ⊕ κ)) t - targetsK m d (Sum.inl j : ι ⊕ κ)) ^ 2)
        (fun j _ => sq_nonneg _) hi
      linarith
  obtain ⟨t, ht⟩ := Convex.helly_theorem' hconv hinter
  have hmem : ∀ i ∈ S, t ∈ D i := fun i hi => Set.mem_iInter₂.mp ht i hi
  have hwd := objLO_le_phi_free (m := m) (d := d) (B := B) (Sf := Sf) (P := P) (G := G)
    hd hG hPS S w t
  rcases S.eq_empty_or_nonempty with hS | ⟨i₀, hi₀⟩
  · subst hS
    simp [objLO]
    linarith
  · have hq : ∑ l, (dotp (G l) t) ^ 2 ≤ V := (hmem i₀ hi₀).1
    have hs : ∑ i ∈ S,
        (dotp (rowsK d B G (Sum.inl i : ι ⊕ κ)) t - targetsK m d (Sum.inl i : ι ⊕ κ)) ^ 2
        ≤ ∑ _i ∈ S, V := Finset.sum_le_sum fun i hi => (hmem i hi).2
    rw [Finset.sum_const, nsmul_eq_mul] at hs
    rw [hsplit] at hwd
    nlinarith

/-- **Следствие Леммы 5.21, long-only:** если `Φ` не меньше значения любого носителя с не более
чем `min(k, K + 1)` именами, то любой носитель с не более чем `k` именами — не больше `(k + 1)Φ`. -/
theorem opt_le_helly [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {k : ℕ} {V : ℝ}
    (hVub : ∀ T : Finset ι, T.card ≤ min k (Fintype.card κ + 1) → ∀ u : ι → ℝ,
      (∀ i ∈ T, 0 ≤ u i) → objLO m d B Sf T u ≤ V)
    {S : Finset ι} (hS : S.card ≤ k) (w : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) :
    objLO m d B Sf S w ≤ (k + 1) * V := by
  classical
  have hV0 : 0 ≤ V := by
    have h := hVub ∅ (by simp) (fun _ => 0) (by simp)
    simpa [objLO] using h
  have hsmall : ∀ T ⊆ S, T.card ≤ Fintype.card κ + 1 → ∀ u : ι → ℝ, (∀ i ∈ T, 0 ≤ u i) →
      objLO m d B Sf T u ≤ V := fun T hTS hTc u hu =>
    hVub T (le_min (le_trans (Finset.card_le_card hTS) hS) hTc) u hu
  have h := objLO_le_helly (m := m) (d := d) (B := B) (Sf := Sf) (P := P) (G := G)
    hd hG hPS hsmall w hw
  have hc : ((S.card : ℝ) + 1) ≤ (k : ℝ) + 1 := by
    have := (Nat.cast_le (α := ℝ)).mpr hS; linarith
  exact le_trans h (mul_le_mul_of_nonneg_right hc hV0)

/-- **Следствие Леммы 5.21, long-short.** -/
theorem opt_le_helly_free (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {k : ℕ} {V : ℝ}
    (hVub : ∀ T : Finset ι, T.card ≤ min k (Fintype.card κ + 1) → ∀ u : ι → ℝ,
      objLO m d B Sf T u ≤ V)
    {S : Finset ι} (hS : S.card ≤ k) (w : ι → ℝ) :
    objLO m d B Sf S w ≤ (k + 1) * V := by
  classical
  have hV0 : 0 ≤ V := by
    have h := hVub ∅ (by simp) (fun _ => 0)
    simpa [objLO] using h
  have hsmall : ∀ T ⊆ S, T.card ≤ Fintype.card κ + 1 → ∀ u : ι → ℝ,
      objLO m d B Sf T u ≤ V := fun T hTS hTc u =>
    hVub T (le_min (le_trans (Finset.card_le_card hTS) hS) hTc) u
  have h := objLO_le_helly_free (m := m) (d := d) (B := B) (Sf := Sf) (P := P) (G := G)
    hd hG hPS hsmall w
  have hc : ((S.card : ℝ) + 1) ≤ (k : ℝ) + 1 := by
    have := (Nat.cast_le (α := ℝ)).mpr hS; linarith
  exact le_trans h (mul_le_mul_of_nonneg_right hc hV0)

/-- `2^{⌈log₂(k+1)⌉} ≥ k + 1`. -/
lemma le_two_pow_clog (k : ℕ) : ((k : ℝ) + 1) ≤ 2 ^ Nat.clog 2 (k + 1) := by
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) (k + 1)
  exact_mod_cast h

end HellyBound

/-! ### Сильно полиномиальные схемы без `ω` -/

section StronglyPoly

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

omit [Fintype ι] in
/-- Наибольшее значение носителя с не более чем `min(k, K + 1)` именами существует
(long-only) и не меньше значения любого одиночного актива. -/
theorem exists_small_best [Finite ι] [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {k : ℕ} (hk1 : 1 ≤ k) :
    ∃ V : ℝ, (∃ T : Finset ι, T.card ≤ min k (Fintype.card κ + 1) ∧ ∃ u : ι → ℝ,
        (∀ i ∈ T, 0 ≤ u i) ∧ objLO m d B Sf T u = V)
      ∧ (∀ T : Finset ι, T.card ≤ min k (Fintype.card κ + 1) → ∀ u : ι → ℝ,
        (∀ i ∈ T, 0 ≤ u i) → objLO m d B Sf T u ≤ V)
      ∧ ∀ i, max (m i) 0 ^ 2 / Vmat d B Sf i i ≤ V := by
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨T, hTk, V, hVG, hVall⟩ := exists_optimal_support (m := m) (d := d) (B := B)
    (Sf := Sf) (P := P) (G := G) hd hG hPS (min k (Fintype.card κ + 1))
  obtain ⟨u, hu, hVu⟩ := hVG.1
  refine ⟨V, ⟨T, hTk, u, hu, hVu.symm⟩, hVall, fun i => ?_⟩
  exact opt_ge_single_of_opt (B := B) hd hG hPS (le_min hk1 (by omega)) hVall i

omit [Fintype ι] in
/-- Наибольшее long-short значение носителя с не более чем `min(k, K + 1)` именами (веса любого
знака) существует и не меньше `m_i²/V_ii` для любого актива `i` (так что оно положительно, если
какое-то `m_i ≠ 0`). -/
theorem exists_small_best_free [Finite ι] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {k : ℕ} (hk1 : 1 ≤ k) :
    ∃ V : ℝ, (∃ T : Finset ι, T.card ≤ min k (Fintype.card κ + 1) ∧ ∃ u : ι → ℝ,
        objLO m d B Sf T u = V)
      ∧ (∀ T : Finset ι, T.card ≤ min k (Fintype.card κ + 1) → ∀ u : ι → ℝ,
        objLO m d B Sf T u ≤ V)
      ∧ ∀ i, m i ^ 2 / Vmat d B Sf i i ≤ V := by
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨T, hTk, th, -, hVG, hVall⟩ := exists_optimal_support_free (m := m) (d := d) (B := B)
    (Sf := Sf) (P := P) (G := G) hd hG hPS (min k (Fintype.card κ + 1))
  obtain ⟨u, hVu⟩ := hVG.1
  refine ⟨phi (rowsK d B G) (targetsK m d) (barK (κ := κ) T) th, ⟨T, hTk, u, hVu.symm⟩, hVall,
    fun i => ?_⟩
  exact opt_ge_single_free (B := B) hd hG hPS (le_min hk1 (by omega)) hVall i

/-- **Теорема 5.13, сильно полиномиальная форма.** Как `main_theorem_univ`, но догадки
`V·2^j`, `j ≤ J = ⌈log₂(k + 1)⌉`, где `V` — наибольшее значение носителя с не более чем
`min(k, K + 1)` именами. Размер семейства зависит только от `M`, `k`, `1/ε` и `K`. -/
theorem main_theorem_univ_sp [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε V : ℝ} (hε : 0 < ε) (hε1 : 2 * ε < 1) (hV0 : 0 < V)
    (hVatt : ∃ T : Finset ι, T.card ≤ min k (Fintype.card κ + 1) ∧ ∃ u : ι → ℝ,
      (∀ i ∈ T, 0 ≤ u i) ∧ objLO m d B Sf T u = V)
    (hVub : ∀ T : Finset ι, T.card ≤ min k (Fintype.card κ + 1) → ∀ u : ι → ℝ,
      (∀ i ∈ T, 0 ≤ u i) → objLO m d B Sf T u ≤ V)
    {J : ℕ} (hJ : J = Nat.clog 2 (k + 1))
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La) :
    (univCandidates m d B G k ε V J La).card
        ≤ (J + 1) * ((Fintype.card ι + Fintype.card κ) ^ Fintype.card κ
          * ((Fintype.card ι + Fintype.card κ) ^ Fintype.card κ
            * ((Fintype.card ι + 1) ^ (Fintype.card κ + 1)
              * ((2 * univZ κ k ε + 1) ^ Fintype.card κ * (univBoxBound κ k ε + 1)))))
    ∧ (∀ W ∈ univCandidates m d B G k ε V J La, W.card ≤ k)
    ∧ (∃ R₀ ∈ univCandidates m d B G k ε V J La, ∃ w₀ : ι → ℝ,
        (∀ i ∈ R₀, 0 ≤ w₀ i) ∧
        ∀ R ∈ univCandidates m d B G k ε V J La, ∀ w : ι → ℝ,
          (∀ i ∈ R, 0 ≤ w i) → objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀)
    ∧ ∀ R₀ ∈ univCandidates m d B G k ε V J La, ∀ w₀ : ι → ℝ,
        (∀ i ∈ R₀, 0 ≤ w₀ i) →
        (∀ R ∈ univCandidates m d B G k ε V J La, ∀ w : ι → ℝ,
          (∀ i ∈ R, 0 ≤ w i) → objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀) →
        R₀.card ≤ k
        ∧ (∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
            (1 - 2 * ε) * objLO m d B Sf S' u ≤ objLO m d B Sf R₀ w₀)
        ∧ (∀ i ∈ R₀, 0 ≤ (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i)
        ∧ ∑ i ∈ R₀, (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i = 1
        ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
            0 < pRet m S' u →
            Real.sqrt (1 - 2 * ε) * sharpe m d B Sf S' u
              ≤ sharpe m d B Sf R₀ (fun i => (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i) := by
  -- оптимум: носитель `S` и его самосогласованный подноситель `A₀`
  obtain ⟨S, hSk, Fopt, hFoptG, hSopt⟩ := exists_optimal_support (m := m) (d := d) (B := B)
    (Sf := Sf) (P := P) (G := G) hd hG hPS k
  obtain ⟨A₀, -, x₀, hA₀S, hnorm, hself, hgreat⟩ :=
    exists_optimal_selfconsistent (m := m) (d := d) (B := B) (Sf := Sf) (P := P) (G := G)
      hd hG hPS S
  have hFeq : phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀ = Fopt :=
    hgreat.unique hFoptG
  have hA₀k : A₀.card ≤ k := le_trans hA₀S hSk
  have hopt : ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
      objLO m d B Sf S' u ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀ := by
    rw [hFeq]; exact hSopt
  set F := phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀ with hF
  -- вилка `[V, (k+1)V]` по Хелли, без данных
  obtain ⟨T, hTc, u, hu, hTu⟩ := hVatt
  have hLF : V ≤ F := hTu ▸ hopt T (le_trans hTc (min_le_left _ _)) u hu
  have hFk : F ≤ (k + 1) * V := by
    obtain ⟨u', hu', hFu'⟩ := hFoptG.1
    have hsmall : ∀ T ⊆ S, T.card ≤ Fintype.card κ + 1 → ∀ w : ι → ℝ, (∀ i ∈ T, 0 ≤ w i) →
        objLO m d B Sf T w ≤ V := fun T hTS hTc w hw =>
      hVub T (le_min (le_trans (Finset.card_le_card hTS) hSk) hTc) w hw
    have h := objLO_le_helly (m := m) (d := d) (B := B) (Sf := Sf) (P := P) (G := G)
      hd hG hPS hsmall u' hu'
    have hc : ((S.card : ℝ) + 1) ≤ (k : ℝ) + 1 := by
      have := (Nat.cast_le (α := ℝ)).mpr hSk; linarith
    rw [hFeq, hFu']
    exact le_trans h (mul_le_mul_of_nonneg_right hc hV0.le)
  have hFJ : F ≤ 2 ^ (J + 1) * V := by
    have h2 : ((k : ℝ) + 1) ≤ 2 ^ J := by rw [hJ]; exact le_two_pow_clog k
    have h3 : (2:ℝ) ^ J ≤ 2 ^ (J + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ J)
    nlinarith
  obtain ⟨W, hW, w, hw, hgood⟩ := exists_good_univCandidate (Sf := Sf) (P := P) hd hG hPS hk1
    hε hV0 hnd hall hA₀k hnorm hself hLF hFJ
  refine ⟨card_univCandidates_le m d B G k ε V J La,
    fun R hR => card_le_of_mem_univCandidates hR,
    exists_best_set_of_family (P := P) (G := G) hd hG hPS ⟨W, hW⟩, ?_⟩
  intro R₀ hR₀ w₀ hw₀ hbest
  have hval : (1 - 2 * ε) * F ≤ objLO m d B Sf R₀ w₀ := le_trans hgood (hbest W hW w hw)
  obtain ⟨hx0, hx1, hxs⟩ := best_pair_sharpe_uniform (B := B) hd hG hPS
    (by linarith : ε < 1 / 2) (lt_of_lt_of_le hV0 hLF) hopt hw₀ hval
  refine ⟨card_le_of_mem_univCandidates hR₀, fun S' hS' u hu => ?_, hx0, hx1, hxs⟩
  have hub := hopt S' hS' u hu
  have hcoef : (0:ℝ) ≤ 1 - 2 * ε := by linarith
  linarith [mul_le_mul_of_nonneg_left hub hcoef]

/-- **Теорема 5.6, сильно полиномиальная форма** (long-short): догадки `V·2^j`,
`j ≤ ⌈log₂(k + 1)⌉`, где `V` — наибольшее значение носителя с не более чем `min(k, K + 1)`
именами при весах любого знака. -/
theorem main_theorem_ls_sp [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} {ε V : ℝ} (hε : 0 < ε) (hε1 : 17 * ε < 8) (hV0 : 0 < V)
    (hVatt : ∃ T : Finset ι, T.card ≤ min k (Fintype.card κ + 1) ∧ ∃ u : ι → ℝ,
      objLO m d B Sf T u = V)
    (hVub : ∀ T : Finset ι, T.card ≤ min k (Fintype.card κ + 1) → ∀ u : ι → ℝ,
      objLO m d B Sf T u ≤ V)
    {J : ℕ} (hJ : J = Nat.clog 2 (k + 1))
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La) :
    (lsCandidates m d B G k ε V J La).card
        ≤ (J + 1) * ((Fintype.card ι + Fintype.card κ) ^ Fintype.card κ
          * ((2 * lsZ (Fintype.card κ) k ε + 1) ^ Fintype.card κ
            * (lsTableBound (Fintype.card ι) (Fintype.card κ) k ε + 1)))
    ∧ (∀ R ∈ lsCandidates m d B G k ε V J La, R.card ≤ k)
    ∧ (∃ R₀ ∈ lsCandidates m d B G k ε V J La, ∃ w₀ : ι → ℝ,
        ∀ R ∈ lsCandidates m d B G k ε V J La, ∀ w : ι → ℝ,
          objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀)
    ∧ ∀ R₀ ∈ lsCandidates m d B G k ε V J La, ∀ w₀ : ι → ℝ,
        (∀ R ∈ lsCandidates m d B G k ε V J La, ∀ w : ι → ℝ,
          objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀) →
        R₀.card ≤ k
        ∧ (∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ,
            (1 - 17 * ε / 8) * objLO m d B Sf S' u ≤ objLO m d B Sf R₀ w₀)
        ∧ ∑ i ∈ R₀, |(∑ j ∈ R₀, |w₀ j|)⁻¹ * w₀ i| = 1
        ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, 0 < pRet m S' u →
            Real.sqrt (1 - 17 * ε / 8) * sharpe m d B Sf S' u
              ≤ sharpe m d B Sf R₀ (fun i => (∑ j ∈ R₀, |w₀ j|)⁻¹ * w₀ i) := by
  have hε1' : ε ≤ 1 := by linarith
  obtain ⟨S, hkS, th, hnormal, hFopt, hSopt⟩ := exists_optimal_support_free (m := m) (d := d)
    (B := B) (Sf := Sf) (P := P) (G := G) hd hG hPS k
  set Fopt := phi (rowsK d B G) (targetsK m d) (barK (κ := κ) S) th with hFoptdef
  obtain ⟨T, hTc, u, hTu⟩ := hVatt
  have hLF : V ≤ Fopt := hTu ▸ hSopt T (le_trans hTc (min_le_left _ _)) u
  have hFk : Fopt ≤ (k + 1) * V := by
    obtain ⟨u', hFu'⟩ := hFopt.1
    have hsmall : ∀ T ⊆ S, T.card ≤ Fintype.card κ + 1 → ∀ w : ι → ℝ,
        objLO m d B Sf T w ≤ V := fun T hTS hTc w =>
      hVub T (le_min (le_trans (Finset.card_le_card hTS) hkS) hTc) w
    have h := objLO_le_helly_free (m := m) (d := d) (B := B) (Sf := Sf) (P := P) (G := G)
      hd hG hPS hsmall u'
    have hc : ((S.card : ℝ) + 1) ≤ (k : ℝ) + 1 := by
      have := (Nat.cast_le (α := ℝ)).mpr hkS; linarith
    rw [hFu']
    exact le_trans h (mul_le_mul_of_nonneg_right hc hV0.le)
  have hFJ : Fopt ≤ 2 ^ (J + 1) * V := by
    have h2 : ((k : ℝ) + 1) ≤ 2 ^ J := by rw [hJ]; exact le_two_pow_clog k
    have h3 : (2:ℝ) ^ J ≤ 2 ^ (J + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ J)
    nlinarith
  obtain ⟨R, hR, w, hw⟩ := exists_good_lsCandidate (Sf := Sf) (P := P) hd hG hPS hε hε1' hV0
    hnd hall hkS hnormal hLF hFJ
  refine ⟨card_lsCandidates_le k hε hV0 J La, fun R hR => card_le_of_mem_lsCandidates hR,
    exists_best_free_of_family (P := P) (G := G) hd hG hPS ⟨R, hR⟩, ?_⟩
  intro R₀ hR₀ w₀ hbest
  have hval : (1 - 17 * ε / 8) * Fopt ≤ objLO m d B Sf R₀ w₀ := le_trans hw (hbest R hR w)
  have hc1 : 17 * ε / 8 < 1 := by linarith
  obtain ⟨hx1, hxs⟩ := best_pair_sharpe_free (B := B) hd hG hPS hc1
    (lt_of_lt_of_le hV0 hLF) hSopt hval
  refine ⟨card_le_of_mem_lsCandidates hR₀, fun S' hS' u => ?_, hx1, hxs⟩
  have hub := hSopt S' hS' u
  have hcoef : (0:ℝ) ≤ 1 - 17 * ε / 8 := by linarith
  linarith [mul_le_mul_of_nonneg_left hub hcoef]


omit [Fintype ι] in
/-- **Теорема 1.1 с догадками Хелли.** Семейство Теоремы 1.1 (`clipCandidates`) с догадками
`Φ·2^j`, `j ≤ J = ⌈log₂(k + 1)⌉`, где `Φ` — наибольшее значение носителя с не более чем
`min(k, K + 1)` именами, обладает всеми свойствами `main_theorem_clipped`: размер не больше
`(J+1)(2Z+1)^K((2Q+1)^K(k+1)+1)` (не зависит от `M`; догадок `⌈log₂(k + 1)⌉ + 1` вместо
`⌈log₂ k(1 + ω)⌉ + 1`, не больше при `ω > 0`), у каждого члена не больше
`k` имён, лучшая пара существует, и для любой лучшей пары значение не меньше `1 − 2ε` от значения
любого long-only портфеля с не более чем `k` именами, а полностью инвестированный портфель
`x = w₀/Σw₀` имеет коэффициент Шарпа не меньше `√(1−2ε)` от коэффициента Шарпа любого такого
портфеля с положительной ожидаемой доходностью. Вычисление `Φ` перебором — `O(M^{K+1})`
квадратичных задач, а догадки `L·2^j` вычисляются за время `O(M)`. -/
theorem main_theorem_clipped_helly [Finite ι] [Nonempty κ] [Nonempty ι] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω V : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω) (hV0 : 0 < V)
    (hVatt : ∃ T : Finset ι, T.card ≤ min k (Fintype.card κ + 1) ∧ ∃ u : ι → ℝ,
      (∀ i ∈ T, 0 ≤ u i) ∧ objLO m d B Sf T u = V)
    (hVub : ∀ T : Finset ι, T.card ≤ min k (Fintype.card κ + 1) → ∀ u : ι → ℝ,
      (∀ i ∈ T, 0 ≤ u i) → objLO m d B Sf T u ≤ V)
    {J : ℕ} (hJ : J = Nat.clog 2 (k + 1))
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La) :
    (clipCandidates m d B Sf G ε ω V J k La).card
        ≤ (J + 1) * ((2 * clipZ ε ω k (Fintype.card κ) + 1) ^ Fintype.card κ
          * ((2 * clipQ ε ω k (Fintype.card κ) + 1) ^ Fintype.card κ * (k + 1) + 1))
    ∧ (∀ R ∈ clipCandidates m d B Sf G ε ω V J k La, R.card ≤ k)
    ∧ (∃ R₀ ∈ clipCandidates m d B Sf G ε ω V J k La, ∃ w₀ : ι → ℝ,
        (∀ i ∈ R₀, 0 ≤ w₀ i) ∧
        ∀ R ∈ clipCandidates m d B Sf G ε ω V J k La, ∀ w : ι → ℝ,
          (∀ i ∈ R, 0 ≤ w i) → objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀)
    ∧ ∀ R₀ ∈ clipCandidates m d B Sf G ε ω V J k La, ∀ w₀ : ι → ℝ,
        (∀ i ∈ R₀, 0 ≤ w₀ i) →
        (∀ R ∈ clipCandidates m d B Sf G ε ω V J k La, ∀ w : ι → ℝ,
          (∀ i ∈ R, 0 ≤ w i) → objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀) →
        R₀.card ≤ k
        ∧ (∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
            (1 - 2 * ε) * objLO m d B Sf S' u ≤ objLO m d B Sf R₀ w₀)
        ∧ (∀ i ∈ R₀, 0 ≤ (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i)
        ∧ ∑ i ∈ R₀, (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i = 1
        ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
            0 < pRet m S' u →
            Real.sqrt (1 - 2 * ε) * sharpe m d B Sf S' u
              ≤ sharpe m d B Sf R₀ (fun i => (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i) := by
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨S, hSk, Fopt, hFoptG, hSopt⟩ := exists_optimal_support (m := m) (d := d) (B := B)
    (Sf := Sf) (P := P) (G := G) hd hG hPS k
  obtain ⟨T, hTc, u, hu, hTu⟩ := hVatt
  have hLF : V ≤ Fopt := hTu ▸ hSopt T (le_trans hTc (min_le_left _ _)) u hu
  have hFk : Fopt ≤ (k + 1) * V := by
    obtain ⟨u', hu', hFu'⟩ := hFoptG.1
    rw [hFu']
    exact opt_le_helly (m := m) (d := d) (B := B) (Sf := Sf) (P := P) (G := G)
      hd hG hPS hVub hSk u' hu'
  have hFJ : Fopt ≤ 2 ^ (J + 1) * V := by
    have h2 : ((k : ℝ) + 1) ≤ 2 ^ J := by rw [hJ]; exact le_two_pow_clog k
    have h3 : (2:ℝ) ^ J ≤ 2 ^ (J + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ J)
    nlinarith
  obtain ⟨R, hR, -, w, hw, hobj⟩ := exists_good_clipCandidate_bracket (Sf := Sf) (P := P)
    hd hG hPS hk1 hε hε1.le hω hsys hV0 hnd hall hSk hFoptG hLF hFJ
  refine ⟨card_clipCandidates_le m d B Sf G ε ω V J k La,
    fun R hR => card_le_of_mem_clipCandidates hR,
    exists_best_set_of_family (m := m) (d := d) (B := B) (Sf := Sf) (P := P) (G := G) hd hG hPS
      ⟨R, hR⟩, ?_⟩
  intro R₀ hR₀ w₀ hw₀ hbest
  have hval : (1 - 2 * ε) * Fopt ≤ objLO m d B Sf R₀ w₀ :=
    le_trans hobj (hbest R hR w (fun i _ => hw i))
  obtain ⟨hx0, hx1, hxs⟩ := best_pair_sharpe_uniform (B := B) hd hG hPS hε1
    (lt_of_lt_of_le hV0 hLF) hSopt hw₀ hval
  refine ⟨card_le_of_mem_clipCandidates hR₀, fun S' hS' u hu => ?_, hx0, hx1, hxs⟩
  have hub := hSopt S' hS' u hu
  have hcoef : (0 : ℝ) ≤ 1 - 2 * ε := by linarith
  linarith [mul_le_mul_of_nonneg_left hub hcoef]

/-! ### Примеры -/

/-- **Пример (сильно полиномиальная форма Теоремы 5.13).** Данные `univ_instance_two` (`K = 2`,
`k = 2`, `ε = 1/10`): `V = 2/3` — лучший носитель из не более чем `min(k, K + 1) = 2` имён,
`J = ⌈log₂ 3⌉`; лучшая пара семейства имеет цель не меньше `8/15`. -/
theorem univ_instance_two_sp :
    ∃ R₀ ∈ univCandidates twoOnes twoOnes twoBK k2I 2 (1 / 10) (2 / 3) (Nat.clog 2 (2 + 1))
        [0, 1],
      ∃ w₀ : Fin 2 → ℝ, (∀ i ∈ R₀, 0 ≤ w₀ i) ∧
        (8 / 15 : ℝ) ≤ objLO twoOnes twoOnes twoBK k2I R₀ w₀ := by
  have hd : ∀ i, 0 < twoOnes i := fun _ => one_pos
  have hG : ∀ j j' : Fin 2, ∑ l : Fin 2, k2I l j * k2I l j' = k2I j j' := by
    intro j j'; fin_cases j <;> fin_cases j' <;> simp [k2I]
  have hPS : ∀ j j' : Fin 2, ∑ l : Fin 2, k2I j l * k2I l j' = if j = j' then 1 else 0 := by
    intro j j'; fin_cases j <;> fin_cases j' <;> simp [k2I]
  have hobj : objLO twoOnes twoOnes twoBK k2I Finset.univ (fun _ => 1 / 3) = 2 / 3 := by
    simp [objLO, Vmat, twoOnes, twoBK, k2I, Fin.sum_univ_two]; norm_num
  obtain ⟨-, -, -, hub, -⟩ := univ_instance_two_small
  have hVatt : ∃ T : Finset (Fin 2), T.card ≤ min 2 (Fintype.card (Fin 2) + 1) ∧
      ∃ u : Fin 2 → ℝ, (∀ i ∈ T, 0 ≤ u i) ∧ objLO twoOnes twoOnes twoBK k2I T u = 2 / 3 :=
    ⟨Finset.univ, by simp, fun _ => 1 / 3, fun _ _ => by norm_num, hobj⟩
  have hVub : ∀ T : Finset (Fin 2), T.card ≤ min 2 (Fintype.card (Fin 2) + 1) →
      ∀ u : Fin 2 → ℝ, (∀ i ∈ T, 0 ≤ u i) → objLO twoOnes twoOnes twoBK k2I T u ≤ 2 / 3 :=
    fun T hT u hu => hub T (le_trans hT (min_le_left _ _)) u hu
  have hnd : ([0, 1] : List (Fin 2)).Nodup := by decide
  have hall : ∀ i : Fin 2, i ∈ ([0, 1] : List (Fin 2)) := by decide
  obtain ⟨_, _, ⟨R₀, hR₀, w₀, hw₀, hbest⟩, hall4⟩ := main_theorem_univ_sp (m := twoOnes)
    (d := twoOnes) (B := twoBK) (Sf := k2I) (P := k2I) (G := k2I) hd hG hPS (k := 2)
    (by norm_num) (ε := 1 / 10) (by norm_num) (by norm_num) (by norm_num : (0:ℝ) < 2 / 3)
    hVatt hVub rfl hnd hall
  obtain ⟨_, hval, _⟩ := hall4 R₀ hR₀ w₀ hw₀ hbest
  refine ⟨R₀, hR₀, w₀, hw₀, ?_⟩
  have h1 := hval Finset.univ (by simp) (fun _ => 1 / 3) (fun _ _ => by norm_num)
  rw [hobj] at h1
  linarith

/-- **Пример (сильно полиномиальная форма Теоремы 5.6).** Данные `ls_instance`: один актив,
`m = d = 1`, `B = 0`, `k = 1`, `ε = 1/4`; `V = 1`, `J = ⌈log₂ 2⌉`. Портфель с единичной валовой
позицией и коэффициентом Шарпа не меньше `√(1 − 17/32)`. -/
theorem ls_instance_sp :
    ∃ R₀ ∈ lsCandidates (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1) (fun _ (_ : Unit) => 0)
        (fun _ _ => 1) 1 (1/4) 1 (Nat.clog 2 (1 + 1)) [0],
      ∃ x : Fin 1 → ℝ, ∑ i ∈ R₀, |x i| = 1
        ∧ Real.sqrt (1 - 17 * (1/4) / 8) ≤ sharpe (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1)
            (fun _ (_ : Unit) => 0) (fun _ _ => 1) R₀ x := by
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
  have hobj : ∀ u : Fin 1 → ℝ, objLO m d B Sf Finset.univ u = 2 * u 0 - u 0 * u 0 := by
    intro u; simp [objLO, Vmat, m, d, B]
  have hVatt : ∃ T : Finset (Fin 1), T.card ≤ min 1 (Fintype.card Unit + 1) ∧
      ∃ u : Fin 1 → ℝ, objLO m d B Sf T u = 1 :=
    ⟨Finset.univ, by simp, fun _ => 1, by rw [hobj]; norm_num⟩
  have hVub : ∀ T : Finset (Fin 1), T.card ≤ min 1 (Fintype.card Unit + 1) →
      ∀ u : Fin 1 → ℝ, objLO m d B Sf T u ≤ 1 := by
    intro T _ u
    rcases T.eq_empty_or_nonempty with hT | hT
    · subst hT; simp [objLO]
    · have hTu : T = Finset.univ := Finset.eq_univ_of_card T (by
        have := Finset.card_pos.mpr hT
        have h1 : T.card ≤ 1 := by simpa using Finset.card_le_univ T
        simp; omega)
      subst hTu
      rw [hobj]
      nlinarith [sq_nonneg (u 0 - 1)]
  have hnd : ([0] : List (Fin 1)).Nodup := List.nodup_singleton 0
  have hall : ∀ i : Fin 1, i ∈ ([0] : List (Fin 1)) := by
    intro i; rw [List.mem_singleton]; exact Subsingleton.elim _ _
  have hsu : sharpe m d B Sf Finset.univ (fun _ => 1) = 1 := by
    simp [sharpe, pRet, pVar, Vmat, m, d, B]
  obtain ⟨_, _, ⟨R₀, hR₀, w₀, hbest⟩, h4⟩ := main_theorem_ls_sp (G := G) (P := P) (Sf := Sf)
    hd hG hPS (k := 1) (by norm_num : (0:ℝ) < 1/4) (by norm_num) one_pos hVatt hVub rfl hnd hall
  obtain ⟨_, _, hx1, hxsh⟩ := h4 R₀ hR₀ w₀ hbest
  have hsh := hxsh Finset.univ (by simp) (fun _ => 1) (by simp [pRet, m])
  refine ⟨R₀, hR₀, _, hx1, ?_⟩
  rw [hsu, mul_one] at hsh
  exact hsh

/-- **Пример (Теорема 1.1 с догадками Хелли).** Одноактивный инстанс `clipped_instance`
(`m = d = 1`, `B = 0`, `Σ_f = G = P = 1`, `k = 1`, `ε = 1/4`, `ω = 0`): `Φ = 1`,
`J = ⌈log₂ 2⌉`, порядок `[0]`. Все гипотезы `main_theorem_clipped_helly` выполнены, заключение
даёт полностью инвестированный портфель с коэффициентом Шарпа не меньше `√(1/2)`. -/
theorem clipped_instance_helly :
    ∃ R₀ ∈ clipCandidates (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1) (fun _ (_ : Unit) => 0)
        (fun _ _ => 1) (fun _ _ => 1) (1/4) 0 1 (Nat.clog 2 (1 + 1)) 1 [0],
      ∃ x : Fin 1 → ℝ, (∀ i ∈ R₀, 0 ≤ x i) ∧ ∑ i ∈ R₀, x i = 1
        ∧ Real.sqrt (1 - 2 * (1/4)) ≤ sharpe (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1)
            (fun _ (_ : Unit) => 0) (fun _ _ => 1) R₀ x := by
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
  have hobj : ∀ u : Fin 1 → ℝ, objLO m d B Sf Finset.univ u = 2 * u 0 - u 0 * u 0 := by
    intro u; simp [objLO, Vmat, m, d, B]
  have hVatt : ∃ T : Finset (Fin 1), T.card ≤ min 1 (Fintype.card Unit + 1) ∧
      ∃ u : Fin 1 → ℝ, (∀ i ∈ T, 0 ≤ u i) ∧ objLO m d B Sf T u = 1 :=
    ⟨Finset.univ, by simp, fun _ => 1, fun _ _ => zero_le_one, by rw [hobj]; norm_num⟩
  have hVub : ∀ T : Finset (Fin 1), T.card ≤ min 1 (Fintype.card Unit + 1) →
      ∀ u : Fin 1 → ℝ, (∀ i ∈ T, 0 ≤ u i) → objLO m d B Sf T u ≤ 1 := by
    intro T _ u _
    rcases T.eq_empty_or_nonempty with hT | hT
    · subst hT; simp [objLO]
    · have hTu : T = Finset.univ := Finset.eq_univ_of_card T (by
        have := Finset.card_pos.mpr hT
        have h1 : T.card ≤ 1 := by simpa using Finset.card_le_univ T
        simp; omega)
      subst hTu
      rw [hobj]
      nlinarith [sq_nonneg (u 0 - 1)]
  have hnd : ([0] : List (Fin 1)).Nodup := List.nodup_singleton 0
  have hall : ∀ i : Fin 1, i ∈ ([0] : List (Fin 1)) := by
    intro i; rw [List.mem_singleton]; exact Subsingleton.elim _ _
  have hsu : sharpe m d B Sf Finset.univ (fun _ => 1) = 1 := by
    simp [sharpe, pRet, pVar, Vmat, m, d, B]
  have hcard : (Finset.univ : Finset (Fin 1)).card ≤ 1 := by simp
  have hw1 : ∀ i ∈ (Finset.univ : Finset (Fin 1)), (0:ℝ) ≤ (fun _ => (1:ℝ)) i :=
    fun _ _ => zero_le_one
  obtain ⟨_, _, ⟨R₀, hR₀, w₀, hw₀, hbest⟩, h4⟩ := main_theorem_clipped_helly (G := G) (P := P)
    (Sf := Sf) hd hG hPS le_rfl (by norm_num : (0:ℝ) < 1/4) (by norm_num) le_rfl hsys
    one_pos hVatt hVub rfl hnd hall
  obtain ⟨_, _, hx0, hx1, hxsh⟩ := h4 R₀ hR₀ w₀ hw₀ hbest
  have hsh := hxsh Finset.univ hcard (fun _ => 1) hw1 (by simp [pRet, m])
  refine ⟨R₀, hR₀, _, hx0, hx1, ?_⟩
  rw [hsu, mul_one] at hsh
  exact hsh

end StronglyPoly

end SparseSharpe.Factor
