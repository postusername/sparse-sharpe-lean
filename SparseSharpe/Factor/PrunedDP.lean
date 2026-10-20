import SparseSharpe.Factor.Localize

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Pruning inside the dynamic program (session 25, task 2.3 of TZ v0.25, Lemma P1)

`knapF` is the knapsack `knap` of `Factor/AdditiveKey.lean` with one more filter: after the step for the asset
`i` (the head of `i :: rest`; `knap` processes `rest` first), a set `U` is kept only if
`θ ≤ val U + ub A (key U)`, where `A = univ \ (i :: rest)` is the set of the assets that are processed later.

* `knapF_spec` — fix a set `S` such that `θ ≤ val U + ub A (key U)` whenever `U ⊆ S` and `S \ U ⊆ A`. If the
  keys of all subsets of `S` lie in the box, the final table contains a set with the key of `S` and at least
  its value. The invariant is the one of `knap_spec`, for the part of `S` that is already processed.
* `knapF_card_le` — still at most `|box| + 1` sets.
* `clipTableF` — the table at a node `τ` with the pruning bound
  `τ'Pτ + Σ_{i∈U} s_i(τ) + (the sum of the k − |U| largest scores among the assets processed later) ≥ θ`;
  `topSum` is that sum, written without sorting as a maximum over subsets (`topSum_eq_sum_top`: it is the sum
  of the largest scores).
* `clipTableF_rep` — the table keeps a representative of every `S` with `|S| ≤ k`, `Q_S(τ) ≥ θ` and keys in the
  box (Lemma P1).
* `trading_theorem_localized_pruned` — L4 + P1 from the data: the heuristic support and the pruned tables at the
  localized nodes; every best pair has the guarantee of Theorem 4.11.
-/

namespace SparseSharpe.Factor

open Finset

section PrunedKnapsack

variable {ι Key : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid Key] [DecidableEq Key]

/-- **The knapsack with pruning.** -/
noncomputable def knapF (s : ι → ℝ) (c : ι → Key) (box : Finset Key) (θ : ℝ)
    (ub : Finset ι → Key → ℝ) : List ι → Finset (Finset ι)
  | [] => {∅}
  | i :: rest =>
      kPrune (fun U => ∑ j ∈ U, s j) (fun U => ∑ j ∈ U, c j)
        (((knapF s c box θ ub rest) ∪ (knapF s c box θ ub rest).image (insert i)).filter
          (fun U => ∑ j ∈ U, c j ∈ box ∧
            θ ≤ ∑ j ∈ U, s j + ub (univ \ (i :: rest).toFinset) (∑ j ∈ U, c j)))

lemma knapF_cons (s : ι → ℝ) (c : ι → Key) (box : Finset Key) (θ : ℝ) (ub : Finset ι → Key → ℝ)
    (i : ι) (rest : List ι) :
    knapF s c box θ ub (i :: rest)
      = kPrune (fun U => ∑ j ∈ U, s j) (fun U => ∑ j ∈ U, c j)
        (((knapF s c box θ ub rest) ∪ (knapF s c box θ ub rest).image (insert i)).filter
          (fun U => ∑ j ∈ U, c j ∈ box ∧
            θ ≤ ∑ j ∈ U, s j + ub (univ \ (i :: rest).toFinset) (∑ j ∈ U, c j))) := rfl

/-- What lies in the pruned table: subsets of `L`. -/
theorem knapF_mem (s : ι → ℝ) (c : ι → Key) (box : Finset Key) (θ : ℝ) (ub : Finset ι → Key → ℝ) :
    ∀ (L : List ι), ∀ R ∈ knapF s c box θ ub L, R ⊆ L.toFinset := by
  intro L
  induction L with
  | nil =>
      intro R hR
      rw [knapF, Finset.mem_singleton] at hR
      subst hR
      simp
  | cons i rest ih =>
      intro R hR
      rw [knapF_cons] at hR
      have hRE := Finset.mem_of_mem_filter _ (kPrune_subset hR)
      rcases Finset.mem_union.mp hRE with h | h
      · exact le_trans (ih R h) (by
          intro x hx; simp only [List.mem_toFinset] at hx ⊢; exact List.mem_cons_of_mem _ hx)
      · obtain ⟨R', hR', rfl⟩ := Finset.mem_image.mp h
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · simp
        · have := ih R' hR' hx
          simp only [List.mem_toFinset] at this ⊢
          exact List.mem_cons_of_mem _ this

/-- The keys of the kept sets lie in the box (except the empty set of the empty list). -/
theorem knapF_key_mem (s : ι → ℝ) (c : ι → Key) (box : Finset Key) (θ : ℝ) (ub : Finset ι → Key → ℝ)
    (L : List ι) : ∀ R ∈ knapF s c box θ ub L, R = ∅ ∨ ∑ j ∈ R, c j ∈ box := by
  intro R hR
  cases L with
  | nil =>
      rw [knapF, Finset.mem_singleton] at hR
      exact Or.inl hR
  | cons i rest =>
      rw [knapF_cons] at hR
      exact Or.inr (Finset.mem_filter.mp (kPrune_subset hR)).2.1

lemma key_injOn_knapF (s : ι → ℝ) (c : ι → Key) (box : Finset Key) (θ : ℝ) (ub : Finset ι → Key → ℝ) :
    ∀ L : List ι, Set.InjOn (fun U : Finset ι => ∑ j ∈ U, c j) ↑(knapF s c box θ ub L) := by
  intro L
  cases L with
  | nil =>
      intro R₁ h₁ R₂ h₂ _
      rw [knapF] at h₁ h₂
      have e₁ : R₁ = ∅ := Finset.mem_singleton.mp (by simpa using h₁)
      have e₂ : R₂ = ∅ := Finset.mem_singleton.mp (by simpa using h₂)
      rw [e₁, e₂]
  | cons i rest =>
      rw [knapF_cons]
      exact key_injOn_kPrune

/-- **The size of the pruned table:** at most `|box| + 1`, whatever the data. -/
theorem knapF_card_le (s : ι → ℝ) (c : ι → Key) (box : Finset Key) (θ : ℝ) (ub : Finset ι → Key → ℝ)
    (L : List ι) : (knapF s c box θ ub L).card ≤ box.card + 1 := by
  rw [← Finset.card_image_of_injOn (key_injOn_knapF s c box θ ub L)]
  have hsub : (knapF s c box θ ub L).image (fun U : Finset ι => ∑ j ∈ U, c j)
      ⊆ insert (∑ j ∈ (∅ : Finset ι), c j) box := by
    intro k hk
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hk
    rcases knapF_key_mem s c box θ ub L R hR with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem h
  refine le_trans (Finset.card_le_card hsub) ?_
  exact le_trans (Finset.card_insert_le _ _) (by omega)

/-- **The invariant of the pruned knapsack (Lemma P1, abstract form).** Fix `S` such that
`θ ≤ val U + ub A (key U)` whenever `U ⊆ S` and `S \ U ⊆ A`. For every list `L` without repetitions such that
the keys of all subsets of `S ∩ L` lie in the box, the table contains a set with the key of `S ∩ L` and at least
its value. -/
theorem knapF_spec (s : ι → ℝ) (c : ι → Key) (box : Finset Key) (θ : ℝ) (ub : Finset ι → Key → ℝ)
    (S : Finset ι)
    (hkeep : ∀ A U : Finset ι, U ⊆ S → S \ U ⊆ A → θ ≤ ∑ j ∈ U, s j + ub A (∑ j ∈ U, c j)) :
    ∀ L : List ι, L.Nodup → (∀ U ⊆ S ∩ L.toFinset, ∑ j ∈ U, c j ∈ box) →
    ∃ R ∈ knapF s c box θ ub L, ∑ j ∈ R, c j = ∑ j ∈ S ∩ L.toFinset, c j ∧
      ∑ j ∈ S ∩ L.toFinset, s j ≤ ∑ j ∈ R, s j := by
  intro L
  induction L with
  | nil =>
      intro _ _
      refine ⟨∅, by rw [knapF]; exact Finset.mem_singleton_self _, ?_, ?_⟩ <;> simp
  | cons i rest ih =>
      intro hnd hbox
      have hndrest : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hirest : i ∉ rest := (List.nodup_cons.mp hnd).1
      set F := knapF s c box θ ub rest with hF
      set A : Finset ι := univ \ (i :: rest).toFinset with hA
      set U : Finset ι := S ∩ (i :: rest).toFinset with hU
      have hUS : U ⊆ S := Finset.inter_subset_left
      have hSUA : S \ U ⊆ A := by
        intro x hx
        rw [Finset.mem_sdiff] at hx
        rw [hA, Finset.mem_sdiff]
        refine ⟨Finset.mem_univ x, fun hxL => hx.2 ?_⟩
        exact Finset.mem_inter.mpr ⟨hx.1, hxL⟩
      have hkeepU := hkeep A U hUS hSUA
      have hsub : S ∩ rest.toFinset ⊆ U := by
        intro x hx
        rw [Finset.mem_inter] at hx ⊢
        refine ⟨hx.1, ?_⟩
        simp only [List.toFinset_cons, Finset.mem_insert]
        exact Or.inr hx.2
      obtain ⟨R₀, hR₀, hkey, hval⟩ := ih hndrest (fun U' hU' => hbox U' (le_trans hU' hsub))
      have hiR₀ : i ∉ R₀ := fun h => hirest (List.mem_toFinset.mp (knapF_mem s c box θ ub rest R₀ hR₀ h))
      by_cases hiS : i ∈ S
      · -- the step «take `i`»
        have hUins : U = insert i (S ∩ rest.toFinset) := by
          ext x
          simp only [hU, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset]
          constructor
          · rintro ⟨hxS, rfl | hx⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hxS, hx⟩
          · rintro (rfl | ⟨hxS, hx⟩)
            · exact ⟨hiS, Or.inl rfl⟩
            · exact ⟨hxS, Or.inr hx⟩
        have hinot : i ∉ S ∩ rest.toFinset := fun h =>
          hirest (List.mem_toFinset.mp (Finset.mem_inter.mp h).2)
        have hkeyU : ∑ j ∈ insert i R₀, c j = ∑ j ∈ U, c j := by
          rw [hUins, Finset.sum_insert hiR₀, Finset.sum_insert hinot, hkey]
        have hvalU : ∑ j ∈ U, s j ≤ ∑ j ∈ insert i R₀, s j := by
          rw [hUins, Finset.sum_insert hiR₀, Finset.sum_insert hinot]
          linarith
        have hmemE : insert i R₀ ∈ (F ∪ F.image (insert i)).filter
            (fun V => ∑ j ∈ V, c j ∈ box ∧
              θ ≤ ∑ j ∈ V, s j + ub (univ \ (i :: rest).toFinset) (∑ j ∈ V, c j)) := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨R₀, hR₀, rfl⟩), ?_, ?_⟩
          · rw [hkeyU]; exact hbox U (Finset.Subset.refl _)
          · rw [hkeyU]; linarith
        obtain ⟨hmem, hk, hge⟩ := kRep_spec
          (val := fun V => ∑ j ∈ V, s j) (key := fun V => ∑ j ∈ V, c j) hmemE
        refine ⟨kRep (fun V => ∑ j ∈ V, s j) (fun V => ∑ j ∈ V, c j)
          ((F ∪ F.image (insert i)).filter (fun V => ∑ j ∈ V, c j ∈ box ∧
            θ ≤ ∑ j ∈ V, s j + ub (univ \ (i :: rest).toFinset) (∑ j ∈ V, c j)))
          (∑ j ∈ insert i R₀, c j), ?_, ?_, ?_⟩
        · rw [knapF_cons, ← hF]
          exact mem_kPrune hmemE
        · rw [hk, hkeyU]
        · exact le_trans hvalU hge
      · -- the step «skip `i`»
        have hUeq : U = S ∩ rest.toFinset := by
          ext x
          simp only [hU, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset]
          constructor
          · rintro ⟨hxS, rfl | hx⟩
            · exact absurd hxS hiS
            · exact ⟨hxS, hx⟩
          · rintro ⟨hxS, hx⟩
            exact ⟨hxS, Or.inr hx⟩
        have hmemE : R₀ ∈ (F ∪ F.image (insert i)).filter
            (fun V => ∑ j ∈ V, c j ∈ box ∧
              θ ≤ ∑ j ∈ V, s j + ub (univ \ (i :: rest).toFinset) (∑ j ∈ V, c j)) := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hR₀, ?_, ?_⟩
          · rw [hkey, ← hUeq]; exact hbox U (Finset.Subset.refl _)
          · rw [hkey, ← hUeq]
            rw [← hUeq] at hval
            linarith
        obtain ⟨hmem, hk, hge⟩ := kRep_spec
          (val := fun V => ∑ j ∈ V, s j) (key := fun V => ∑ j ∈ V, c j) hmemE
        refine ⟨kRep (fun V => ∑ j ∈ V, s j) (fun V => ∑ j ∈ V, c j)
          ((F ∪ F.image (insert i)).filter (fun V => ∑ j ∈ V, c j ∈ box ∧
            θ ≤ ∑ j ∈ V, s j + ub (univ \ (i :: rest).toFinset) (∑ j ∈ V, c j)))
          (∑ j ∈ R₀, c j), ?_, ?_, ?_⟩
        · rw [knapF_cons, ← hF]
          exact mem_kPrune hmemE
        · rw [hk, hkey, ← hUeq]
        · rw [← hUeq] at hval
          exact le_trans hval hge

end PrunedKnapsack

/-! ### The largest sum of at most `r` scores -/

section TopSum

variable {ι : Type*} [DecidableEq ι]

/-- The largest sum of at most `r` values of `v` on `A`, as a maximum over subsets (no sorting). -/
noncomputable def topSum (v : ι → ℝ) (A : Finset ι) (r : ℕ) : ℝ :=
  (A.powerset.filter fun T => T.card ≤ r).sup' ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset A,
    by simp⟩⟩ fun T => ∑ i ∈ T, v i

lemma le_topSum (v : ι → ℝ) {A T : Finset ι} {r : ℕ} (hT : T ⊆ A) (hTr : T.card ≤ r) :
    ∑ i ∈ T, v i ≤ topSum v A r :=
  Finset.le_sup' (fun T => ∑ i ∈ T, v i) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hT, hTr⟩)

/-- **`topSum` is the sum of the `r` largest values** (for nonnegative values): if `T₀ ⊆ A` has `r` elements
(or is all of `A`) and no value outside `T₀` exceeds a value inside, then `topSum v A r = Σ_{T₀} v`. This is how
the bound of the pruning is computed: suffix sums of the `r ≤ k` largest scores, `O(Mk)` in all. -/
theorem topSum_eq_sum_top {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) {A T₀ : Finset ι} {r : ℕ} (hT₀ : T₀ ⊆ A)
    (hcard : T₀.card = r ∨ T₀ = A) (hr : T₀.card ≤ r)
    (htop : ∀ i ∈ T₀, ∀ j ∈ A, j ∉ T₀ → v j ≤ v i) :
    topSum v A r = ∑ i ∈ T₀, v i := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun T hT => ?_
    have hT' := Finset.mem_filter.mp hT
    have hTA : T ⊆ A := Finset.mem_powerset.mp hT'.1
    refine sum_le_sum_top hv hTA ?_ htop
    rcases hcard with h | h
    · exact Or.inl (by rw [h]; exact hT'.2)
    · exact Or.inr h
  · exact le_topSum v hT₀ hr

end TopSum

/-! ### The pruned table at a node -/

section PrunedTable

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- **The table at a node `τ` with pruning by `θ`:** after the step for an asset, a set `U` is discarded if
`τ'Pτ + Σ_{i∈U} s_i(τ) + (the largest sum of k − |U| scores among the assets processed later) < θ`. -/
noncomputable def clipTableF (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf P G : κ → κ → ℝ) (η : ℝ) (Q k : ℕ)
    (θ : ℝ) (L : List ι) (τ : κ → ℝ) : Finset (Finset ι) :=
  knapF (fun i => clipScore m d B τ i) (clipKeyItem m d B Sf G η τ) (clipBox κ Q k) (θ - quadf P τ)
    (fun A key => topSum (fun i => clipScore m d B τ i) A (k - key.2)) L

theorem card_clipTableF_le (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf P G : κ → κ → ℝ) (η : ℝ) (Q k : ℕ)
    (θ : ℝ) (L : List ι) (τ : κ → ℝ) :
    (clipTableF m d B Sf P G η Q k θ L τ).card ≤ (2 * Q + 1) ^ Fintype.card κ * (k + 1) + 1 := by
  have := knapF_card_le (fun i => clipScore m d B τ i) (clipKeyItem m d B Sf G η τ) (clipBox κ Q k)
    (θ - quadf P τ) (fun A key => topSum (fun i => clipScore m d B τ i) A (k - key.2)) L
  rw [card_clipBox] at this
  exact this

theorem card_le_of_mem_clipTableF {η : ℝ} {Q k : ℕ} {θ : ℝ} {L : List ι} {τ : κ → ℝ} {R : Finset ι}
    (hR : R ∈ clipTableF m d B Sf P G η Q k θ L τ) : R.card ≤ k := by
  rcases knapF_key_mem _ _ _ _ _ L R hR with h | h
  · simp [h]
  · rw [clipBox, Finset.mem_product, Finset.mem_range] at h
    have h2 := h.2
    rw [sum_clipKeyItem_snd] at h2
    omega

/-- **Lemma P1.** If `|S| ≤ k`, `Q_S(τ) ≥ θ` and the keys of all subsets of `S` lie in the box, the pruned
table at `τ` contains a set with the key of `S` and at least its sum of scores (as in Lemma 4.5(b)). -/
theorem clipTableF_rep {η : ℝ} {Q k : ℕ} {θ : ℝ} {S : Finset ι} (hSk : S.card ≤ k)
    {τ : κ → ℝ} (hθ : θ ≤ QLO m d B P S τ)
    (hbox : ∀ U ⊆ S, ∀ l, |∑ i ∈ U, ⌊vcoord G Sf B (wclip m d B τ) i l / η⌋| ≤ (Q : ℤ))
    {L : List ι} (hnd : L.Nodup) (hL : ∀ i, i ∈ L) :
    ∃ R ∈ clipTableF m d B Sf P G η Q k θ L τ,
      ∑ i ∈ R, clipKeyItem m d B Sf G η τ i = ∑ i ∈ S, clipKeyItem m d B Sf G η τ i ∧
      ∑ i ∈ S, clipScore m d B τ i ≤ ∑ i ∈ R, clipScore m d B τ i := by
  classical
  have hSL : S ∩ L.toFinset = S := Finset.inter_eq_left.mpr fun i _ => List.mem_toFinset.mpr (hL i)
  have hbox' : ∀ U' ⊆ S ∩ L.toFinset, ∑ j ∈ U', clipKeyItem m d B Sf G η τ j ∈ clipBox κ Q k := by
    rw [hSL]
    intro U' hU'
    rw [clipBox, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun l => ?_, ?_⟩
    · rw [Finset.mem_Icc, ← abs_le, sum_clipKeyItem_fst]
      exact hbox U' hU' l
    · rw [sum_clipKeyItem_snd]
      have := Finset.card_le_card hU'
      omega
  -- the bound of the pruning holds along `S`
  have hkeep : ∀ A U : Finset ι, U ⊆ S → S \ U ⊆ A →
      θ - quadf P τ ≤ ∑ j ∈ U, clipScore m d B τ j
        + topSum (fun i => clipScore m d B τ i) A (k - (∑ j ∈ U, clipKeyItem m d B Sf G η τ j).2) := by
    intro A U hUS hSUA
    rw [sum_clipKeyItem_snd]
    have hcardSU : (S \ U).card ≤ k - U.card := by
      rw [Finset.card_sdiff_of_subset hUS]
      omega
    have htop := le_topSum (fun i => clipScore m d B τ i) hSUA hcardSU
    have hsplit : ∑ j ∈ S, clipScore m d B τ j
        = ∑ j ∈ S \ U, clipScore m d B τ j + ∑ j ∈ U, clipScore m d B τ j :=
      (Finset.sum_sdiff hUS).symm
    have hQ : QLO m d B P S τ = quadf P τ + ∑ j ∈ S, clipScore m d B τ j := rfl
    linarith
  obtain ⟨R, hR, hkey, hval⟩ := knapF_spec (fun i => clipScore m d B τ i) (clipKeyItem m d B Sf G η τ)
    (clipBox κ Q k) (θ - quadf P τ) (fun A key => topSum (fun i => clipScore m d B τ i) A (k - key.2)) S
    hkeep L hnd hbox'
  rw [hSL] at hkey hval
  exact ⟨R, hR, hkey, hval⟩

/-! ### L4 + P1: the pruned tables at the localized nodes -/

/-- The localized family at one guess `V` with the pruned tables. -/
noncomputable def locFamilyF (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf P G : κ → κ → ℝ) (ε ω V : ℝ) (k : ℕ)
    (L : List ι) (that : κ → ℝ) (θ : ℝ) : Finset (Finset ι) :=
  (locNodes m d B P G k (clipStep ε V ω k (Fintype.card κ)) (clipZ ε ω k (Fintype.card κ)) that θ).biUnion
    fun z => clipTableF m d B Sf P G (clipEta ε V k (Fintype.card κ)) (clipQ ε ω k (Fintype.card κ)) k θ L
      (nodeOf G (clipStep ε V ω k (Fintype.card κ)) z)

/-- The localized candidates with pruning for the guesses `L·2^j`, `j ≤ J`. -/
noncomputable def locCandidatesF (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf P G : κ → κ → ℝ) (ε ω L : ℝ)
    (J k : ℕ) (La : List ι) (that : κ → ℝ) (θ : ℝ) : Finset (Finset ι) :=
  (Finset.range (J + 1)).biUnion fun j => locFamilyF m d B Sf P G ε ω (L * 2 ^ j) k La that θ

/-- **L4 + P1 for one guess.** Under the hypotheses of `clip_one_guess` and `θ < F_LO(S)`, the pruned tables
at the localized nodes contain `R`, `|R| ≤ k`, with a portfolio `w ≥ 0` of objective at least
`(1 − 2ε)·F_LO(S)`. -/
theorem clip_one_guess_loc_pruned [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {ω : ℝ} (hω : 0 ≤ ω) (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    {S : Finset ι} (hSk : S.card ≤ k) {t₀ : κ → ℝ}
    (hmin : ∀ t, QLO m d B P S t₀ ≤ QLO m d B P S t)
    {V : ℝ} (hV : 0 < V) (hVF : V ≤ QLO m d B P S t₀) (hFV : QLO m d B P S t₀ ≤ 2 * V)
    {θ : ℝ} (hθ : θ < QLO m d B P S t₀) (that : κ → ℝ)
    {L : List ι} (hnd : L.Nodup) (hL : ∀ i, i ∈ L) :
    ∃ R ∈ locFamilyF m d B Sf P G ε ω V k L that θ, R.card ≤ k ∧
      ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (1 - 2 * ε) * QLO m d B P S t₀ ≤ objLO m d B Sf R w := by
  obtain ⟨z, hzZ, hz, R, hR, hRk, w, hw, hobj⟩ := one_guess_of_rep (m := m) (B := B) (Sf := Sf)
    (P := P) (G := G) hd hG hPS hk hε hε2 hω hsys hSk hmin hV hVF hFV
    (fun τ => clipTableF m d B Sf P G (clipEta ε V k (Fintype.card κ)) (clipQ ε ω k (Fintype.card κ)) k θ
      L τ)
    (fun τ hbox => clipTableF_rep hSk (le_trans hθ.le (hmin τ)) hbox hnd hL)
  have hspos : 0 < clipStep ε V ω k (Fintype.card κ) := by
    have hKpos : 0 < (Fintype.card κ : ℝ) := by exact_mod_cast Fintype.card_pos
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    exact div_pos (Real.sqrt_pos.mpr (by positivity))
      (mul_pos (by nlinarith [mul_nonneg hkpos.le hω]) (Real.sqrt_pos.mpr hKpos))
  have hzloc := node_mem_locNodes (m := m) (d := d) (B := B) (Sf := Sf) hd hG hPS hSk hmin hθ that
    hspos hzZ hz
  refine ⟨R, ?_, hRk, w, hw, hobj⟩
  rw [locFamilyF, Finset.mem_biUnion]
  exact ⟨z, hzloc, hR⟩

theorem card_le_of_mem_locCandidatesF {ε ω L : ℝ} {J k : ℕ} {La : List ι} {that : κ → ℝ} {θ : ℝ}
    {R : Finset ι} (hR : R ∈ locCandidatesF m d B Sf P G ε ω L J k La that θ) : R.card ≤ k := by
  rw [locCandidatesF, Finset.mem_biUnion] at hR
  obtain ⟨j, _, hj⟩ := hR
  rw [locFamilyF, Finset.mem_biUnion] at hj
  obtain ⟨z, _, hz⟩ := hj
  exact card_le_of_mem_clipTableF hz

theorem locCandidatesF_eq_empty {ε ω L : ℝ} {J k : ℕ} {La : List ι} {that : κ → ℝ} {θ : ℝ}
    (h : dualBound m d B P k that ≤ θ) : locCandidatesF m d B Sf P G ε ω L J k La that θ = ∅ := by
  rw [locCandidatesF]
  ext R
  simp only [Finset.mem_biUnion, Finset.notMem_empty, iff_false, not_exists, not_and]
  intro j _ hR
  rw [locFamilyF, locNodes_eq_empty h, Finset.biUnion_empty] at hR
  exact Finset.notMem_empty _ hR

/-- The size of the localized family with pruning at one guess. -/
theorem card_locFamilyF_le (ε ω V : ℝ) (k : ℕ) (La : List ι) (that : κ → ℝ) (θ : ℝ) :
    (locFamilyF m d B Sf P G ε ω V k La that θ).card
      ≤ (locNodes m d B P G k (clipStep ε V ω k (Fintype.card κ)) (clipZ ε ω k (Fintype.card κ))
          that θ).card
        * ((2 * clipQ ε ω k (Fintype.card κ) + 1) ^ Fintype.card κ * (k + 1) + 1) := by
  refine le_trans Finset.card_biUnion_le ?_
  rw [← smul_eq_mul]
  exact Finset.sum_le_card_nsmul _ _ _ fun z _ => card_clipTableF_le _ _ _ _ _ _ _ _ _ _ _ _

/-- **L4 + P1 from the data.** As `trading_theorem_localized`, with the tables pruned by the same threshold
`θ` (`(1 − 2ε)θ ≤ obj(S_h, w_h)`, for instance `θ = F_h/(1 − 2ε)`): for every order of the assets, every best
pair `(R*, w*)` of `{S_h} ∪` (the pruned tables at the localized nodes of the guesses `L·2^j`, `j ≤ J`) has at
most `k` names, objective at least `1 − 2ε` times that of every long-only portfolio with at most `k` names, and
the fully invested `x* = w*/Σw*` has a Sharpe ratio at least `√(1 − 2ε)` times that of every such portfolio
with positive expected excess return. The family is `{S_h}` if `g_k(t̂) ≤ θ`; it has at most
`1 + Σ_j |nodes_j|·((2Q+1)^K(k+1)+1)` members. -/
theorem trading_theorem_localized_pruned [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    {Sh : Finset ι} (hSh : Sh.card ≤ k) {wh : ι → ℝ} (hwh : ∀ i ∈ Sh, 0 ≤ wh i)
    {L : ℝ} (hL0 : 0 < L) (hLh : L ≤ objLO m d B Sf Sh wh)
    {θ : ℝ} (hθ : (1 - 2 * ε) * θ ≤ objLO m d B Sf Sh wh)
    {that : κ → ℝ} {J : ℕ} (hJ : dualBound m d B P k that ≤ 2 ^ (J + 1) * L)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La) :
    (insert Sh (locCandidatesF m d B Sf P G ε ω L J k La that θ)).card
        ≤ 1 + ∑ j ∈ Finset.range (J + 1),
          (locNodes m d B P G k (clipStep ε (L * 2 ^ j) ω k (Fintype.card κ))
            (clipZ ε ω k (Fintype.card κ)) that θ).card
          * ((2 * clipQ ε ω k (Fintype.card κ) + 1) ^ Fintype.card κ * (k + 1) + 1)
    ∧ (dualBound m d B P k that ≤ θ →
        insert Sh (locCandidatesF m d B Sf P G ε ω L J k La that θ) = {Sh})
    ∧ (∀ R ∈ insert Sh (locCandidatesF m d B Sf P G ε ω L J k La that θ), R.card ≤ k)
    ∧ ∀ R₀ ∈ insert Sh (locCandidatesF m d B Sf P G ε ω L J k La that θ), ∀ w₀ : ι → ℝ,
        (∀ i ∈ R₀, 0 ≤ w₀ i) →
        (∀ R ∈ insert Sh (locCandidatesF m d B Sf P G ε ω L J k La that θ), ∀ w : ι → ℝ,
          (∀ i ∈ R, 0 ≤ w i) → objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀) →
        (∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
            (1 - 2 * ε) * objLO m d B Sf S' u ≤ objLO m d B Sf R₀ w₀)
        ∧ (∀ i ∈ R₀, 0 ≤ (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i)
        ∧ ∑ i ∈ R₀, (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i = 1
        ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
            0 < pRet m S' u →
            Real.sqrt (1 - 2 * ε) * sharpe m d B Sf S' u
              ≤ sharpe m d B Sf R₀ (fun i => (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i) := by
  set Fam := insert Sh (locCandidatesF m d B Sf P G ε ω L J k La that θ) with hFam
  have hcardFam : ∀ R ∈ Fam, R.card ≤ k := by
    intro R hR
    rcases Finset.mem_insert.mp hR with h | h
    · rw [h]; exact hSh
    · exact card_le_of_mem_locCandidatesF h
  refine ⟨?_, ?_, hcardFam, ?_⟩
  · refine le_trans (Finset.card_insert_le _ _) ?_
    rw [add_comm]
    refine Nat.add_le_add_left (le_trans Finset.card_biUnion_le ?_) 1
    exact Finset.sum_le_sum fun j _ => card_locFamilyF_le ε ω _ k La that θ
  · intro h
    rw [hFam, locCandidatesF_eq_empty h]
    rfl
  intro R₀ hR₀ w₀ hw₀ hbest
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
      obtain ⟨R, hR, -, w, hw, hobj⟩ := clip_one_guess_loc_pruned (m := m) (B := B) (Sf := Sf)
        (P := P) (G := G) hd hG hPS hk1 hε hε1.le hω hsys hkS hmin hV (by rw [hF]; exact hVF)
        (by rw [hF]; exact hFV) (by rw [hF]; exact hθF) that hnd hall
      have hRmem : R ∈ Fam := by
        refine Finset.mem_insert_of_mem ?_
        rw [locCandidatesF, Finset.mem_biUnion]
        exact ⟨j, Finset.mem_range.mpr (by omega), hR⟩
      rw [← hF]
      exact le_trans hobj (hbest R hRmem w (fun i _ => hw i))
  have hLF : L ≤ Fopt := le_trans hLh (hSopt Sh hSh wh hwh)
  obtain ⟨hx0, hx1, hxs⟩ := best_pair_sharpe_uniform (B := B) hd hG hPS hε1
    (lt_of_lt_of_le hL0 hLF) hSopt hw₀ hgood
  refine ⟨fun S' hS' u hu => ?_, hx0, hx1, hxs⟩
  have hub := hSopt S' hS' u hu
  linarith [mul_le_mul_of_nonneg_left hub hc]

/-! ### Nonemptiness

The one-asset instance of `clipped_instance` (`m = d = 1`, `B = 0`, `Σ_f = G = P = 1`, `k = 1`, `ε = 1/4`,
`ω = 0`), with the heuristic `S_h = {0}`, `w_h = 1` (value `1`), `L = 1/2`, the threshold `θ = 1/2 < g_1(0) = 1`
(so the localized nodes are not empty by definition), `t̂ = 0`, `J = 0` and the order `[0]`: all hypotheses of
`trading_theorem_localized_pruned` hold (those of `trading_theorem_localized` are the same), and the conclusion
gives a fully invested portfolio with Sharpe ratio at least `√(1/2)`. -/

theorem localized_pruned_instance :
    ∃ R₀ ∈ insert (Finset.univ : Finset (Fin 1)) (locCandidatesF (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1)
        (fun _ (_ : Unit) => 0) (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1) (1/4) 0 (1/2) 0 1 [0]
        (fun _ => 0) (1/2)),
      ∃ x : Fin 1 → ℝ, (∀ i ∈ R₀, 0 ≤ x i) ∧ ∑ i ∈ R₀, x i = 1
        ∧ Real.sqrt (1 - 2 * (1/4)) ≤ sharpe (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1)
            (fun _ (_ : Unit) => 0) (fun _ _ => 1) R₀ x
      ∧ (1 / 2 : ℝ) < dualBound (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1) (fun _ (_ : Unit) => 0)
            (fun _ _ => 1) 1 (fun _ => 0) := by
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
  have hnd : ([0] : List (Fin 1)).Nodup := List.nodup_singleton 0
  have hall : ∀ i : Fin 1, i ∈ ([0] : List (Fin 1)) := by
    intro i; rw [List.mem_singleton]; exact Subsingleton.elim _ _
  have hsu : sharpe m d B Sf Finset.univ (fun _ => 1) = 1 := by
    simp [sharpe, pRet, pVar, Vmat, m, d, B]
  have hcard : (Finset.univ : Finset (Fin 1)).card ≤ 1 := by simp
  have hw1 : ∀ i ∈ (Finset.univ : Finset (Fin 1)), (0:ℝ) ≤ (fun _ => (1:ℝ)) i :=
    fun _ _ => zero_le_one
  have hobj : objLO m d B Sf Finset.univ (fun _ => 1) = 1 := by
    simp [objLO, Vmat, m, d, B]; norm_num
  have hJ : dualBound m d B P 1 (fun _ => 0) ≤ 2 ^ (0 + 1) * (1 / 2 : ℝ) := by
    have := dualBound_zero_le (m := m) (d := d) (B := B) (Sf := Sf) (P := P) (G := G) hd hG hPS
      le_rfl hsys zero_le_one hL 1
    norm_num at this ⊢
    exact this
  have hg : (1 / 2 : ℝ) < dualBound m d B P 1 (fun _ => 0) := by
    have := objLO_le_dualBound (m := m) (B := B) (Sf := Sf) (P := P) (G := G) hd hG hPS hcard hw1
      (fun _ => 0)
    rw [hobj] at this
    linarith
  obtain ⟨-, -, -, h4⟩ := trading_theorem_localized_pruned (G := G) (P := P) (Sf := Sf) hd hG hPS
    le_rfl (by norm_num : (0:ℝ) < 1/4) (by norm_num) le_rfl hsys hcard hw1 (L := 1 / 2)
    (by norm_num) (by rw [hobj]; norm_num) (θ := 1 / 2) (by rw [hobj]; norm_num) hJ hnd hall
  obtain ⟨R₀, hR₀, w₀, hw₀, hbest⟩ := exists_best_set_of_family (m := m) (d := d) (B := B) (Sf := Sf)
    (P := P) (G := G) hd hG hPS
    ⟨Finset.univ, Finset.mem_insert_self _ (locCandidatesF m d B Sf P G (1/4) 0 (1/2) 0 1 [0]
      (fun _ => 0) (1/2))⟩
  obtain ⟨-, hx0, hx1, hxsh⟩ := h4 R₀ hR₀ w₀ hw₀ hbest
  have hsh := hxsh Finset.univ hcard (fun _ => 1) hw1 (by simp [pRet, m])
  refine ⟨R₀, hR₀, _, hx0, hx1, ?_, hg⟩
  rw [hsu, mul_one] at hsh
  exact hsh

end PrunedTable

end SparseSharpe.Factor
