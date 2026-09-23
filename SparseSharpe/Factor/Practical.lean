import SparseSharpe.Factor.TradingAnchor

set_option linter.style.header false

/-!
# Smaller constants, a dual certificate and the Main Theorem in its simple form

* **Symmetric key** (`keyOf_symm`, `survivorsBox_card_le_sym`, `card_symKeys_keyBox_le`,
  `card_symKeys_boxOf_le`). The Gram part of the key of the dynamic program is a symmetric
  matrix, so a table has at most as many entries as the key box has *symmetric* keys. In
  the table bound the exponent `K²` of the Gram factor becomes `(K+1).choose 2 = K(K+1)/2`
  (`card_anchorTable_le_sym`, `card_candidatesAnchor_le_sym`,
  `card_schemeTableList_le_sym`, `card_candidatesList_le_sym`).
* **Dual bound** (`dualBound`, `objLO_le_dualBound`, `dualBound_eq_of_top`). For every
  point `t`, `g(t) = t'Pt + max_{|S| ≤ k} Σ_{i∈S} (m_i − B_i't)_+²/d_i` bounds the objective of
  every long-only portfolio with at most `k` names (weak duality of Theorem D, with the
  maximum over supports taken outside the minimum over `t`); the maximum over supports is
  the sum of the `k` largest terms.
* **Certificate** (`certificate_sharpe`, `certificate_sharpe_eps`). A long-only portfolio
  with at most `k` names and objective `F_h > 0` has, after normalization to a fully
  invested portfolio, Sharpe ratio at least `√(F_h/g(t))` times that of every long-only
  portfolio with at most `k` names. If `F_h ≥ (1 − 2ε)·g(t)`, it carries the guarantee of
  the trading theorem without any search.
* **Adaptive guesses** (`exists_good_candidate_anchor_bracket`,
  `exists_good_candidate_list_bracket`, `trading_theorem_anchor_adaptive`,
  `trading_theorem_adaptive`). The doubling grid of guesses may start at the value `L` of
  any long-only portfolio with at most `k` names and use `J + 1` guesses, where `J` is the
  first index with `g(t) ≤ 2^(J+1)·L` (one guess when `g(t) ≤ 2L`);
  `dualBound_zero_le` shows that this is never worse than the data-only choice
  `k(1 + ω) ≤ 2^J`.
* **Polynomial size** (`polyConst`, `guess_count_spec`, `NK_le_poly`,
  `card_candidatesAnchor_poly`). With `J = ⌈log₂ k(1+ω)⌉` guesses (`k(1+ω) ≤ 2^J ≤ 2k(1+ω)`)
  and `0 < ε ≤ 1`, the size of the anchor family is at most
  `C_K·M^(K+K(K+1)/2)·(1/ε)^K·(k(1+ω))^(2+4K+K(K+1))`.
* **The Main Theorem in its simple form** (`main_theorem_simple`): an explicit family of
  candidate supports with at most `k` assets each, of explicitly and polynomially bounded
  size, a best pair of which exists and, for every such pair, the fully invested portfolio
  has at most `k` names and Sharpe ratio at least `√(1 − 2ε)` times that of every
  long-only portfolio with at most `k` names.
-/

namespace SparseSharpe.Factor

open Finset

set_option linter.unusedSectionVars false

/-! ### The symmetric key -/

section SymKey

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι]

/-- The keys of a box whose Gram part is a symmetric matrix. -/
def symKeys (box : Finset ((κ → ℤ) × (κ → κ → ℤ) × ℕ)) :
    Finset ((κ → ℤ) × (κ → κ → ℤ) × ℕ) :=
  box.filter fun q => ∀ l l', q.2.1 l l' = q.2.1 l' l

omit [DecidableEq ι] in
/-- The Gram part of every key is symmetric. -/
lemma keyOf_symm (a : ι → κ → ℝ) (y : ι → ℝ) (T : κ → ι) (t : κ → ℝ) (η ξ : ℝ)
    (U : Finset ι) (l l' : κ) :
    (keyOf a y T t η ξ U).2.1 l l' = (keyOf a y T t η ξ U).2.1 l' l := by
  change ⌊gramK2 a T U l l' / ξ⌋ = ⌊gramK2 a T U l' l / ξ⌋
  unfold gramK2
  rw [Finset.sum_congr rfl fun i _ => mul_comm (cf a T i l) (cf a T i l')]

omit [DecidableEq κ] in
/-- **Table size with the symmetric key**: if the Gram part of every key is symmetric,
a table of the dynamic program has at most as many entries as the box has symmetric keys,
plus one. -/
theorem survivorsBox_card_le_sym (val : Finset ι → ℝ)
    (key : Finset ι → (κ → ℤ) × (κ → κ → ℤ) × ℕ) (adm : ι → Bool)
    (box : Finset ((κ → ℤ) × (κ → κ → ℤ) × ℕ)) (base : Finset ι) (L : List ι)
    (hsym : ∀ U : Finset ι, ∀ l l', (key U).2.1 l l' = (key U).2.1 l' l) :
    (survivorsBox val key adm box base L).card ≤ (symKeys box).card + 1 := by
  classical
  rw [← Finset.card_image_of_injOn (key_injOn_survivorsBox val key adm box base L)]
  have hsub : (survivorsBox val key adm box base L).image key
      ⊆ insert (key base) (symKeys box) := by
    intro q hq
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hq
    rcases survivorsBox_key_mem val key adm box base L R hR with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h, hsym R⟩)
  exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)

/-- **Number of symmetric keys of a key box.** The Gram part of a symmetric key is
determined by its entries on unordered pairs of factors, of which there are
`(K+1).choose 2 = K(K+1)/2`. -/
theorem card_symKeys_keyBox_le (cM cK : ℤ) (n : ℕ) :
    (symKeys (keyBox (κ := κ) cM cK n)).card
      ≤ (2 * cM + 1).toNat ^ Fintype.card κ
        * ((2 * cK + 1).toNat ^ (Fintype.card κ + 1).choose 2 * (n + 1)) := by
  classical
  set tgt : Finset ((κ → ℤ) × (Sym2 κ → ℤ) × ℕ) :=
    (Fintype.piFinset fun _ => Finset.Icc (-cM) cM) ×ˢ
      ((Fintype.piFinset fun _ => Finset.Icc (-cK) cK) ×ˢ Finset.range (n + 1)) with htgt
  have hcard : tgt.card = (2 * cM + 1).toNat ^ Fintype.card κ
      * ((2 * cK + 1).toNat ^ (Fintype.card κ + 1).choose 2 * (n + 1)) := by
    simp only [htgt, Finset.card_product, Fintype.card_piFinset, Int.card_Icc,
      Finset.card_range]
    simp_rw [show (cM + 1 - -cM) = 2 * cM + 1 by omega,
      show (cK + 1 - -cK) = 2 * cK + 1 by omega]
    simp [Finset.prod_const, Finset.card_univ, Sym2.card]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (fun q => (q.1, fun s : Sym2 κ => q.2.1 (Quot.out s).1 (Quot.out s).2, q.2.2)) ?_ ?_
  · intro q hq
    have hq' := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).1
    simp only [keyBox, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range] at hq'
    rw [Finset.mem_coe, htgt]
    simp only [Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]
    exact ⟨hq'.1, fun s => hq'.2.1 _ _, hq'.2.2⟩
  · intro q hq q' hq' hqq
    have hs := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
    have hs' := (Finset.mem_filter.mp (Finset.mem_coe.mp hq')).2
    simp only [Prod.mk.injEq] at hqq
    obtain ⟨h1, h2, h3⟩ := hqq
    have hG : q.2.1 = q'.2.1 := by
      funext l l'
      have hp : s((Quot.out s(l, l')).1, (Quot.out s(l, l')).2) = s(l, l') :=
        Quot.out_eq _
      have hc := congrFun h2 s(l, l')
      rcases Sym2.eq_iff.mp hp with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · simp only [e1, e2] at hc
        exact hc
      · simp only [e1, e2] at hc
        rw [hs l l', hs' l l']
        exact hc
    exact Prod.ext h1 (Prod.ext hG h3)

/-- **Symmetric keys of the canonical box through the input quantities.** As
`card_boxOf_le`, with the exponent `K²` of the Gram factor replaced by `(K+1).choose 2`. -/
theorem card_symKeys_boxOf_le {ε c V η ξ ρ : ℝ} {N Mn : ℕ}
    (hε : 0 < ε) (hc : 0 < c) (hV : 0 < V) (hN : 0 < N) (hM : 0 < Mn)
    (hKc : 0 < Fintype.card κ) (hρ : 0 ≤ ρ)
    (hηdef : η = theta0B ε V c / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Mn : ℝ)))
    (hξdef : ξ = 1 / (8 * (Mn : ℝ) * (Fintype.card κ : ℝ))) :
    (symKeys (boxOf κ ρ V η ξ N Mn)).card
      ≤ (2 * ⌈ρ * (48 * (Mn : ℝ) * Real.sqrt (Fintype.card κ : ℝ)
            * Real.sqrt ((N : ℝ) * c / ε)) + (Mn : ℝ)⌉ + 1).toNat ^ Fintype.card κ
        * ((2 * ⌈8 * (N : ℝ) * (Mn : ℝ) * (Fintype.card κ : ℝ) * ρ ^ 2 + (Mn : ℝ)⌉ + 1).toNat
            ^ (Fintype.card κ + 1).choose 2 * (N + 1)) := by
  have hM0 : (0:ℝ) < (Mn : ℝ) := by exact_mod_cast hM
  have hK0 : (0:ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast hKc
  have hηpos : 0 < η := by
    rw [hηdef]
    have : 0 < theta0B ε V c := Real.sqrt_pos.mpr (by positivity)
    have : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr hK0
    positivity
  have hξpos : 0 < ξ := by rw [hξdef]; positivity
  unfold boxOf
  refine le_trans (card_symKeys_keyBox_le _ _ _) ?_
  have hD := momRange_over_eta_le_block (Sc := N) (Mn := Mn) (Kc := Fintype.card κ)
    (Q := 4 * V) hε hc hV hN hKc hM hηdef (by positivity) le_rfl le_rfl
  have h1 : (ρ * Real.sqrt ((N : ℝ) * (4 * V)) + (Mn : ℝ) * η) / η
      ≤ ρ * (48 * (Mn : ℝ) * Real.sqrt (Fintype.card κ : ℝ)
            * Real.sqrt ((N : ℝ) * c / ε)) + (Mn : ℝ) := by
    rw [add_div, mul_div_assoc, mul_div_assoc, div_self hηpos.ne', mul_one]
    have := mul_le_mul_of_nonneg_left hD hρ
    linarith
  have h2 : ((N : ℝ) * ρ ^ 2 + (Mn : ℝ) * ξ) / ξ
      = 8 * (N : ℝ) * (Mn : ℝ) * (Fintype.card κ : ℝ) * ρ ^ 2 + (Mn : ℝ) := by
    rw [hξdef]; field_simp
  rw [h2]
  have hA := toNat_two_ceil_mono h1
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hA _)

end SymKey

/-! ### Table and family bounds with the symmetric key -/

section Tables

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- Size bound of one table of the anchor variant with the symmetric key: as
`tableBoundAnchor`, with the exponent `K²` replaced by `(K+1).choose 2 = K(K+1)/2`. -/
noncomputable def tableBoundAnchorSym (Mc Kc k : ℕ) (ε ω : ℝ) : ℕ :=
  (2 * ⌈Real.sqrt (max 1 ω) * (48 * (Mc : ℝ) * Real.sqrt (Kc : ℝ)
      * Real.sqrt (((k + Kc : ℕ) : ℝ) * ((k : ℝ) * (1 + (k : ℝ) * ω)) / ε))
      + (Mc : ℝ)⌉ + 1).toNat ^ Kc
    * ((2 * ⌈8 * ((k + Kc : ℕ) : ℝ) * (Mc : ℝ) * (Kc : ℝ) * Real.sqrt (max 1 ω) ^ 2
        + (Mc : ℝ)⌉ + 1).toNat ^ (Kc + 1).choose 2 * (k + Kc + 1))

/-- Size bound of one table of the enumeration variant with the symmetric key: as
`tableBound`, with the exponent `K²` replaced by `(K+1).choose 2 = K(K+1)/2`. -/
noncomputable def tableBoundSym (Mc Kc k : ℕ) (ε ω : ℝ) : ℕ :=
  (2 * ⌈1 * (48 * (Mc : ℝ) * Real.sqrt (Kc : ℝ)
      * Real.sqrt (((k + Kc : ℕ) : ℝ) * ((k : ℝ) * (1 + (k : ℝ) * ω)) / ε))
      + (Mc : ℝ)⌉ + 1).toNat ^ Kc
    * ((2 * ⌈8 * ((k + Kc : ℕ) : ℝ) * (Mc : ℝ) * (Kc : ℝ) * 1 ^ 2 + (Mc : ℝ)⌉ + 1).toNat
        ^ (Kc + 1).choose 2 * (k + Kc + 1))

/-- `(K+1).choose 2 = K(K+1)/2`. -/
lemma choose_succ_two (K : ℕ) : (K + 1).choose 2 = K * (K + 1) / 2 := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm]

/-- Every table of the anchor variant has at most `tableBoundAnchorSym + 1` entries. -/
lemma card_anchorTable_le_sym [Nonempty κ] [Nonempty ι] {k : ℕ} (hk1 : 1 ≤ k) {ε ω V : ℝ}
    (hε : 0 < ε) (hω : 0 ≤ ω) (hV : 0 < V) (La : List ι) (t : κ → ℝ) :
    (anchorTable m d B G k ε ω V La t).card
      ≤ tableBoundAnchorSym (Fintype.card ι) (Fintype.card κ) k ε ω + 1 := by
  have hK0 : 0 < Fintype.card κ := Fintype.card_pos
  have hM0 : 0 < Fintype.card ι := Fintype.card_pos
  have hc : (0:ℝ) < (k : ℝ) * (1 + (k : ℝ) * ω) := by
    have hk : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have : (0:ℝ) ≤ (k : ℝ) * ω := mul_nonneg (by linarith) hω
    nlinarith
  have hN : 0 < k + Fintype.card κ := by omega
  have hbox := card_symKeys_boxOf_le (κ := κ) (ε := ε) (c := (k : ℝ) * (1 + (k : ℝ) * ω))
    (V := V) (ρ := Real.sqrt (max 1 ω)) (N := k + Fintype.card κ) (Mn := Fintype.card ι)
    hε hc hV hN hM0 hK0 (Real.sqrt_nonneg _) rfl rfl
  unfold anchorTable
  refine le_trans (survivorsBox_card_le_sym _ _ _ _ _ _
    (fun U l l' => keyOf_symm _ _ _ _ _ _ U l l')) ?_
  unfold tableBoundAnchorSym
  push_cast at hbox ⊢
  omega

/-- **Size of the candidate family of the anchor variant with the symmetric key**: at most
`(J+1)·(2Z+1)^K·(tableBoundAnchorSym+1)`. -/
theorem card_candidatesAnchor_le_sym [Nonempty κ] [Nonempty ι] {k : ℕ} (hk1 : 1 ≤ k)
    {ε ω L : ℝ} (hε : 0 < ε) (hω : 0 ≤ ω) (hL0 : 0 < L) (J : ℕ) (La : List ι) :
    (candidatesAnchor m d B G k ε ω L J La).card
      ≤ (J + 1) * ((2 * anchorZ (Fintype.card κ) k ε ω + 1) ^ Fintype.card κ
          * (tableBoundAnchorSym (Fintype.card ι) (Fintype.card κ) k ε ω + 1)) := by
  unfold candidatesAnchor
  refine le_trans Finset.card_biUnion_le ?_
  have h1 : ∀ j ∈ Finset.range (J + 1),
      ((nodeBox (κ := κ) (anchorZ (Fintype.card κ) k ε ω)).biUnion fun z =>
          anchorTable m d B G k ε ω (L * 2 ^ j) La
            (nodePoint (rowsK d B G) (targetsK m d) (fun l => (Sum.inr l : ι ⊕ κ))
              (anchorStep (Fintype.card κ) k ε ω (L * 2 ^ j)) z)).card
      ≤ (2 * anchorZ (Fintype.card κ) k ε ω + 1) ^ Fintype.card κ
          * (tableBoundAnchorSym (Fintype.card ι) (Fintype.card κ) k ε ω + 1) := by
    intro j _
    have hV : (0:ℝ) < L * 2 ^ j := by positivity
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _
      (tableBoundAnchorSym (Fintype.card ι) (Fintype.card κ) k ε ω + 1)
      (fun z _ => card_anchorTable_le_sym (m := m) (d := d) (B := B) (G := G) hk1 hε hω hV
        La _)) ?_
    rw [card_nodeBox, smul_eq_mul]
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ h1) ?_
  rw [Finset.card_range, smul_eq_mul]

/-- Every table of the enumeration variant has at most `tableBoundSym + 1` entries. -/
lemma card_schemeTableList_le_sym [Nonempty κ] [Nonempty ι] {k : ℕ} (hk1 : 1 ≤ k)
    {ε ω V : ℝ} (hε : 0 < ε) (hω : 0 ≤ ω) (hV : 0 < V) (La : List ι) (T : κ → (ι ⊕ κ))
    (t : κ → ℝ) :
    (schemeTableList m d B G k ε ω V La T t).card
      ≤ tableBoundSym (Fintype.card ι) (Fintype.card κ) k ε ω + 1 := by
  have hK0 : 0 < Fintype.card κ := Fintype.card_pos
  have hM0 : 0 < Fintype.card ι := Fintype.card_pos
  have hc : (0:ℝ) < (k : ℝ) * (1 + (k : ℝ) * ω) := by
    have hk : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have : (0:ℝ) ≤ (k : ℝ) * ω := mul_nonneg (by linarith) hω
    nlinarith
  have hN : 0 < k + Fintype.card κ := by omega
  have hbox := card_symKeys_boxOf_le (κ := κ) (ε := ε) (c := (k : ℝ) * (1 + (k : ℝ) * ω))
    (V := V) (ρ := 1) (N := k + Fintype.card κ) (Mn := Fintype.card ι) hε hc hV hN hM0 hK0
    zero_le_one rfl rfl
  unfold schemeTableList
  refine le_trans (survivorsBox_card_le_sym _ _ _ _ _ _
    (fun U l l' => keyOf_symm _ _ _ _ _ _ U l l')) ?_
  unfold tableBoundSym
  push_cast at hbox ⊢
  omega

/-- **Size of the candidate family of the enumeration variant with the symmetric key**:
at most `(J+1)·(M+K)^K·(2Z+1)^K·(tableBoundSym+1)`. -/
theorem card_candidatesList_le_sym [Nonempty κ] [Nonempty ι] {k : ℕ} (hk1 : 1 ≤ k)
    {ε ω L : ℝ} (hε : 0 < ε) (hω : 0 ≤ ω) (hL0 : 0 < L) (J : ℕ) (La : List ι) :
    (candidatesList m d B G k ε ω L J La).card
      ≤ (J + 1) * ((Fintype.card ι + Fintype.card κ) ^ Fintype.card κ
        * ((2 * schemeZ (Fintype.card κ) k ε ω + 1) ^ Fintype.card κ
          * (tableBoundSym (Fintype.card ι) (Fintype.card κ) k ε ω + 1))) := by
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
          * (tableBoundSym (Fintype.card ι) (Fintype.card κ) k ε ω + 1)) := by
    intro j _
    have hV : (0:ℝ) < L * 2 ^ j := by positivity
    refine le_trans Finset.card_biUnion_le ?_
    have h2 : ∀ T ∈ (Finset.univ : Finset (κ → (ι ⊕ κ))),
        ((nodeBox (κ := κ) (schemeZ (Fintype.card κ) k ε ω)).biUnion fun z =>
          schemeTableList m d B G k ε ω (L * 2 ^ j) La T
            (nodePoint (rowsK d B G) (targetsK m d) T
              (schemeStep (Fintype.card κ) k ε ω (L * 2 ^ j)) z)).card
        ≤ (2 * schemeZ (Fintype.card κ) k ε ω + 1) ^ Fintype.card κ
          * (tableBoundSym (Fintype.card ι) (Fintype.card κ) k ε ω + 1) := by
      intro T _
      refine le_trans Finset.card_biUnion_le ?_
      refine le_trans (Finset.sum_le_card_nsmul _ _
        (tableBoundSym (Fintype.card ι) (Fintype.card κ) k ε ω + 1)
        (fun z _ => card_schemeTableList_le_sym (m := m) (d := d) (B := B) (G := G) hk1 hε
          hω hV La T _)) ?_
      rw [card_nodeBox, smul_eq_mul]
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ h2) ?_
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_sum, smul_eq_mul]
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ h1) ?_
  rw [Finset.card_range, smul_eq_mul]

end Tables

/-! ### The dual bound and the certificate -/

section Dual

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

omit [DecidableEq ι] in
/-- The supports with at most `k` assets form a nonempty family (it contains `∅`). -/
lemma supportsLe_nonempty (k : ℕ) :
    ((Finset.univ : Finset (Finset ι)).filter fun S => S.card ≤ k).Nonempty :=
  ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩⟩

/-- **The dual bound** at a point `t`:
`g(t) = t'Pt + max_{|S| ≤ k} Σ_{i∈S} (m_i − B_i't)_+²/d_i`. -/
noncomputable def dualBound (m d : ι → ℝ) (B : ι → κ → ℝ) (P : κ → κ → ℝ) (k : ℕ)
    (t : κ → ℝ) : ℝ :=
  quadf P t + ((Finset.univ : Finset (Finset ι)).filter fun S => S.card ≤ k).sup'
    (supportsLe_nonempty k) fun S => ∑ i ∈ S, (max (m i - dotp (B i) t) 0) ^ 2 / d i

/-- **Weak duality over all supports.** For every point `t`, the dual bound `g(t)` bounds
the objective of every long-only portfolio with at most `k` names. -/
theorem objLO_le_dualBound (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {k : ℕ}
    {S : Finset ι} (hS : S.card ≤ k) {w : ι → ℝ} (hw : ∀ i ∈ S, 0 ≤ w i) (t : κ → ℝ) :
    objLO m d B Sf S w ≤ dualBound m d B P k t := by
  have h1 := objLO_le_QLO (m := m) (B := B) (Sf := Sf) (P := P) (G := G) hd hG hPS hw t
  have h2 : (fun S : Finset ι => ∑ i ∈ S, (max (m i - dotp (B i) t) 0) ^ 2 / d i) S
      ≤ ((Finset.univ : Finset (Finset ι)).filter fun S => S.card ≤ k).sup'
          (supportsLe_nonempty k)
          (fun S => ∑ i ∈ S, (max (m i - dotp (B i) t) 0) ^ 2 / d i) :=
    Finset.le_sup' (fun S : Finset ι => ∑ i ∈ S, (max (m i - dotp (B i) t) 0) ^ 2 / d i)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩)
  unfold QLO at h1
  unfold dualBound
  simp only at h2
  linarith

omit [DecidableEq ι] [DecidableEq κ] in
/-- **The maximum over supports is the sum of the `k` largest terms.** If `S₀` has `k`
elements (or contains all assets) and no term outside `S₀` exceeds a term inside, then
`g(t) = t'Pt + Σ_{i∈S₀} (m_i − B_i't)_+²/d_i`. This is how `g(t)` is computed. -/
theorem dualBound_eq_of_top (hd : ∀ i, 0 < d i) {k : ℕ} (t : κ → ℝ) {S₀ : Finset ι}
    (hS₀ : S₀.card = k ∨ S₀ = Finset.univ) (hk : S₀.card ≤ k)
    (htop : ∀ i ∈ S₀, ∀ j ∉ S₀, (max (m j - dotp (B j) t) 0) ^ 2 / d j
      ≤ (max (m i - dotp (B i) t) 0) ^ 2 / d i) :
    dualBound m d B P k t
      = quadf P t + ∑ i ∈ S₀, (max (m i - dotp (B i) t) 0) ^ 2 / d i := by
  classical
  set v : ι → ℝ := fun i => (max (m i - dotp (B i) t) 0) ^ 2 / d i with hv
  have hv0 : ∀ i, 0 ≤ v i := fun i => div_nonneg (sq_nonneg _) (hd i).le
  unfold dualBound
  congr 1
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun S hS => ?_
    have hSk : S.card ≤ k := (Finset.mem_filter.mp hS).2
    change ∑ i ∈ S, v i ≤ ∑ i ∈ S₀, v i
    rcases hS₀ with hcard | huniv
    · -- exchange: `S \ S₀` has at most as many elements as `S₀ \ S`, and its terms are
      -- no larger than any term of `S₀ \ S`
      rw [← Finset.sum_sdiff (Finset.inter_subset_left : S ∩ S₀ ⊆ S),
        ← Finset.sum_sdiff (Finset.inter_subset_right : S ∩ S₀ ⊆ S₀)]
      have hcardle : (S \ (S ∩ S₀)).card ≤ (S₀ \ (S ∩ S₀)).card := by
        rw [Finset.card_sdiff_of_subset Finset.inter_subset_left,
          Finset.card_sdiff_of_subset Finset.inter_subset_right]
        omega
      have hexch : ∑ i ∈ S \ (S ∩ S₀), v i ≤ ∑ i ∈ S₀ \ (S ∩ S₀), v i := by
        rcases (S₀ \ (S ∩ S₀)).eq_empty_or_nonempty with he | hne
        · rw [he, Finset.card_empty, Nat.le_zero, Finset.card_eq_zero] at hcardle
          rw [hcardle, he]
        · obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image _ v hne
          have hi₀S₀ : i₀ ∈ S₀ := (Finset.mem_sdiff.mp hi₀).1
          calc ∑ i ∈ S \ (S ∩ S₀), v i ≤ ∑ _i ∈ S \ (S ∩ S₀), v i₀ := by
                refine Finset.sum_le_sum fun j hj => htop i₀ hi₀S₀ j ?_
                intro hjS₀
                have hjS := (Finset.mem_sdiff.mp hj).1
                exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_inter.mpr ⟨hjS, hjS₀⟩)
            _ = ((S \ (S ∩ S₀)).card : ℝ) * v i₀ := by simp
            _ ≤ ((S₀ \ (S ∩ S₀)).card : ℝ) * v i₀ :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hcardle) (hv0 i₀)
            _ = ∑ _i ∈ S₀ \ (S ∩ S₀), v i₀ := by simp
            _ ≤ ∑ i ∈ S₀ \ (S ∩ S₀), v i := Finset.sum_le_sum fun i hi => hmin i hi
      linarith
    · rw [huniv]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun i _ _ => hv0 i)
  · exact Finset.le_sup' (fun S : Finset ι => ∑ i ∈ S, v i)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ S₀, hk⟩)

/-- At `t = 0` the dual bound is at most `k(1+ω)L`, the data-only upper bracket of
`exists_guess_of_opt`. Hence adaptive guesses (with a heuristic value `≥ L` and a point
`t` with `g(t) ≤ g(0)`) never need more guesses than the data-only grid. -/
theorem dualBound_zero_le (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {ω L : ℝ} (hω : 0 ≤ ω) (hsys : ∀ i, sysVar B Sf i / d i ≤ ω) (hL0 : 0 ≤ L)
    (hL : ∀ i, max (m i) 0 ^ 2 / Vmat d B Sf i i ≤ L) (k : ℕ) :
    dualBound m d B P k (fun _ => 0) ≤ (k : ℝ) * (1 + ω) * L := by
  unfold dualBound
  have hq : quadf P (fun _ => 0) = 0 := by simp [quadf]
  rw [hq, zero_add]
  refine Finset.sup'_le _ _ fun S hS => ?_
  have hSk : S.card ≤ k := (Finset.mem_filter.mp hS).2
  have hz : ∀ i, dotp (B i) (fun _ => 0) = 0 := fun i => by simp [dotp]
  simp only [hz, sub_zero]
  exact sum_posPart_le (B := B) (Sf := Sf) (P := P) (G := G) hd hG hPS hω hsys hL0 hL hSk

/-- **Certificate from the dual bound.** Let `w_h ≥ 0` on `S_h`, `|S_h| ≤ k`, have
objective `F_h > 0`, and let `t` be any point. Then `F_h ≤ g(t)`, the portfolio
`x_h = w_h/Σw_h` is long-only and fully invested, and its Sharpe ratio is at least
`√(F_h/g(t))` times that of every long-only portfolio with at most `k` names and positive
expected excess return. -/
theorem certificate_sharpe (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {k : ℕ}
    {Sh : Finset ι} (hSh : Sh.card ≤ k) {wh : ι → ℝ} (hwh : ∀ i ∈ Sh, 0 ≤ wh i)
    (hpos : 0 < objLO m d B Sf Sh wh) (t : κ → ℝ) :
    objLO m d B Sf Sh wh ≤ dualBound m d B P k t
    ∧ (∀ i ∈ Sh, 0 ≤ (∑ j ∈ Sh, wh j)⁻¹ * wh i)
    ∧ ∑ i ∈ Sh, (∑ j ∈ Sh, wh j)⁻¹ * wh i = 1
    ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        0 < pRet m S' u →
        Real.sqrt (objLO m d B Sf Sh wh / dualBound m d B P k t) * sharpe m d B Sf S' u
          ≤ sharpe m d B Sf Sh (fun i => (∑ j ∈ Sh, wh j)⁻¹ * wh i) := by
  have hFU : objLO m d B Sf Sh wh ≤ dualBound m d B P k t :=
    objLO_le_dualBound hd hG hPS hSh hwh t
  have hUpos : 0 < dualBound m d B P k t := lt_of_lt_of_le hpos hFU
  have hq : 0 < objLO m d B Sf Sh wh / dualBound m d B P k t := div_pos hpos hUpos
  have hε'1 : (1 - objLO m d B Sf Sh wh / dualBound m d B P k t) / 2 < 1 / 2 := by linarith
  have h12 : 1 - 2 * ((1 - objLO m d B Sf Sh wh / dualBound m d B P k t) / 2)
      = objLO m d B Sf Sh wh / dualBound m d B P k t := by ring
  have hval : (1 - 2 * ((1 - objLO m d B Sf Sh wh / dualBound m d B P k t) / 2))
      * dualBound m d B P k t ≤ objLO m d B Sf Sh wh := by
    rw [h12, div_mul_cancel₀ _ hUpos.ne']
  obtain ⟨hx0, hx1, hxs⟩ := best_pair_sharpe_uniform (B := B) hd hG hPS hε'1 hUpos
    (fun S' hS' u hu => objLO_le_dualBound hd hG hPS hS' hu t) hwh hval
  refine ⟨hFU, hx0, hx1, fun S' hS' u hu hru => ?_⟩
  have := hxs S' hS' u hu hru
  rwa [h12] at this

/-- **Certificate with a prescribed accuracy.** If, in addition,
`F_h ≥ (1 − 2ε)·g(t)`, then the objective of `w_h` is at least `1 − 2ε` times that of every
long-only portfolio with at most `k` names, and `x_h = w_h/Σw_h` has Sharpe ratio at least
`√(1 − 2ε)` times that of every such portfolio with positive expected excess return: the
conclusions of the trading theorem hold without running the scheme. -/
theorem certificate_sharpe_eps (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {k : ℕ} {ε : ℝ}
    (hε1 : ε < 1 / 2) {Sh : Finset ι} (hSh : Sh.card ≤ k) {wh : ι → ℝ}
    (hwh : ∀ i ∈ Sh, 0 ≤ wh i) (hpos : 0 < objLO m d B Sf Sh wh) (t : κ → ℝ)
    (hcert : (1 - 2 * ε) * dualBound m d B P k t ≤ objLO m d B Sf Sh wh) :
    (∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        (1 - 2 * ε) * objLO m d B Sf S' u ≤ objLO m d B Sf Sh wh)
    ∧ (∀ i ∈ Sh, 0 ≤ (∑ j ∈ Sh, wh j)⁻¹ * wh i)
    ∧ ∑ i ∈ Sh, (∑ j ∈ Sh, wh j)⁻¹ * wh i = 1
    ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        0 < pRet m S' u →
        Real.sqrt (1 - 2 * ε) * sharpe m d B Sf S' u
          ≤ sharpe m d B Sf Sh (fun i => (∑ j ∈ Sh, wh j)⁻¹ * wh i) := by
  have hFU : objLO m d B Sf Sh wh ≤ dualBound m d B P k t :=
    objLO_le_dualBound hd hG hPS hSh hwh t
  have hUpos : 0 < dualBound m d B P k t := lt_of_lt_of_le hpos hFU
  have hSopt : ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
      objLO m d B Sf S' u ≤ dualBound m d B P k t :=
    fun S' hS' u hu => objLO_le_dualBound hd hG hPS hS' hu t
  obtain ⟨hx0, hx1, hxs⟩ := best_pair_sharpe_uniform (B := B) hd hG hPS hε1 hUpos hSopt
    hwh hcert
  refine ⟨fun S' hS' u hu => ?_, hx0, hx1, hxs⟩
  have hcoef : (0:ℝ) ≤ 1 - 2 * ε := by linarith
  linarith [mul_le_mul_of_nonneg_left (hSopt S' hS' u hu) hcoef]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
/-- **Exchange lemma for the `k` largest terms.** Let `v ≥ 0`, let `T₀` consist of largest
values of `v` on `R` (no value on `R \ T₀` exceeds a value on `T₀`), and let `A ⊆ R` have
at most `|T₀|` elements, or `T₀ = R`. Then `Σ_A v ≤ Σ_{T₀} v`. -/
theorem sum_le_sum_top {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) {R T₀ A : Finset ι}
    (hAR : A ⊆ R) (hcard : A.card ≤ T₀.card ∨ T₀ = R)
    (htop : ∀ i ∈ T₀, ∀ j ∈ R, j ∉ T₀ → v j ≤ v i) :
    ∑ i ∈ A, v i ≤ ∑ i ∈ T₀, v i := by
  classical
  rcases hcard with hcard | hR
  · rw [← Finset.sum_sdiff (Finset.inter_subset_left : A ∩ T₀ ⊆ A),
      ← Finset.sum_sdiff (Finset.inter_subset_right : A ∩ T₀ ⊆ T₀)]
    have hcardle : (A \ (A ∩ T₀)).card ≤ (T₀ \ (A ∩ T₀)).card := by
      rw [Finset.card_sdiff_of_subset Finset.inter_subset_left,
        Finset.card_sdiff_of_subset Finset.inter_subset_right]
      omega
    have hexch : ∑ i ∈ A \ (A ∩ T₀), v i ≤ ∑ i ∈ T₀ \ (A ∩ T₀), v i := by
      rcases (T₀ \ (A ∩ T₀)).eq_empty_or_nonempty with he | hne
      · rw [he, Finset.card_empty, Nat.le_zero, Finset.card_eq_zero] at hcardle
        rw [hcardle, he]
      · obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image _ v hne
        have hi₀T : i₀ ∈ T₀ := (Finset.mem_sdiff.mp hi₀).1
        calc ∑ i ∈ A \ (A ∩ T₀), v i ≤ ∑ _i ∈ A \ (A ∩ T₀), v i₀ := by
              refine Finset.sum_le_sum fun j hj => htop i₀ hi₀T j
                (hAR (Finset.mem_sdiff.mp hj).1) ?_
              intro hjT
              exact (Finset.mem_sdiff.mp hj).2
                (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hj).1, hjT⟩)
          _ = ((A \ (A ∩ T₀)).card : ℝ) * v i₀ := by simp
          _ ≤ ((T₀ \ (A ∩ T₀)).card : ℝ) * v i₀ :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hcardle) (hv i₀)
          _ = ∑ _i ∈ T₀ \ (A ∩ T₀), v i₀ := by simp
          _ ≤ ∑ i ∈ T₀ \ (A ∩ T₀), v i := Finset.sum_le_sum fun i hi => hmin i hi
    linarith
  · rw [hR]
    exact Finset.sum_le_sum_of_subset_of_nonneg hAR (fun i _ _ => hv i)

set_option linter.unusedFintypeInType false in
/-- **Bound for a node of branch and bound.** Let the assets of `F` be fixed in and those
of `R` be free, let `r` more assets be allowed, and let `T₀` consist of `r` largest scores
`(m_j − B_j't)_+²/d_j` on `R` (or `T₀ = R`). Then every long-only portfolio on a support `S`
with `F ⊆ S ⊆ F ∪ R` and `|S \ F| ≤ r` has objective at most
`t'Pt + Σ_{i∈F} s_i(t) + Σ_{j∈T₀} s_j(t)`, for every point `t`. -/
theorem objLO_le_nodeBound (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (t : κ → ℝ) {F R T₀ S : Finset ι} {r : ℕ}
    (hT₀ : T₀.card = r ∨ T₀ = R)
    (htop : ∀ i ∈ T₀, ∀ j ∈ R, j ∉ T₀ → (max (m j - dotp (B j) t) 0) ^ 2 / d j
      ≤ (max (m i - dotp (B i) t) 0) ^ 2 / d i)
    (hFS : F ⊆ S) (hSFR : S ⊆ F ∪ R) (hSr : (S \ F).card ≤ r)
    {w : ι → ℝ} (hw : ∀ i ∈ S, 0 ≤ w i) :
    objLO m d B Sf S w
      ≤ quadf P t + ∑ i ∈ F, (max (m i - dotp (B i) t) 0) ^ 2 / d i
        + ∑ i ∈ T₀, (max (m i - dotp (B i) t) 0) ^ 2 / d i := by
  have h1 := objLO_le_QLO (m := m) (B := B) (Sf := Sf) (P := P) (G := G) hd hG hPS hw t
  unfold QLO at h1
  have hsplit : ∑ i ∈ S \ F, (max (m i - dotp (B i) t) 0) ^ 2 / d i
      + ∑ i ∈ F, (max (m i - dotp (B i) t) 0) ^ 2 / d i
      = ∑ i ∈ S, (max (m i - dotp (B i) t) 0) ^ 2 / d i := Finset.sum_sdiff hFS
  have hSR : S \ F ⊆ R := by
    intro i hi
    rcases Finset.mem_union.mp (hSFR (Finset.mem_sdiff.mp hi).1) with h | h
    · exact absurd h (Finset.mem_sdiff.mp hi).2
    · exact h
  have hex : ∑ i ∈ S \ F, (max (m i - dotp (B i) t) 0) ^ 2 / d i
      ≤ ∑ i ∈ T₀, (max (m i - dotp (B i) t) 0) ^ 2 / d i :=
    sum_le_sum_top (v := fun i => (max (m i - dotp (B i) t) 0) ^ 2 / d i)
      (fun i => div_nonneg (sq_nonneg _) (hd i).le) hSR
      (by rcases hT₀ with h | h
          · left; omega
          · right; exact h) htop
  linarith

/-- **Optimality test at the dual point.** Let `w ≥ 0` on `S`, `|S| ≤ k`, and let `t` be a
dual point of `S`: `Q(S, t) ≤ F(S, w)` (by Theorem D such a point exists for an optimal
`w`). If `S` has `k` elements (or contains all assets) and its scores
`(m_i − B_i't)_+²/d_i` are `k` largest ones, then `g(t) = F(S, w)` and `w` is optimal: its
objective is at least that of every long-only portfolio with at most `k` names, and the
fully invested portfolio `w/Σw` has the largest Sharpe ratio among them. For one factor
this is the cut-off rule of Elton, Gruber and Padberg, with a cardinality bound. -/
theorem optimal_of_top_at_dual (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {k : ℕ}
    {S : Finset ι} (hS : S.card ≤ k) (hS₀ : S.card = k ∨ S = Finset.univ) {w : ι → ℝ}
    (hw : ∀ i ∈ S, 0 ≤ w i) {t : κ → ℝ} (hdual : QLO m d B P S t ≤ objLO m d B Sf S w)
    (htop : ∀ i ∈ S, ∀ j ∉ S, (max (m j - dotp (B j) t) 0) ^ 2 / d j
      ≤ (max (m i - dotp (B i) t) 0) ^ 2 / d i) :
    dualBound m d B P k t = objLO m d B Sf S w
    ∧ (∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        objLO m d B Sf S' u ≤ objLO m d B Sf S w)
    ∧ (0 < objLO m d B Sf S w →
        ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
          0 < pRet m S' u →
          sharpe m d B Sf S' u ≤ sharpe m d B Sf S (fun i => (∑ j ∈ S, w j)⁻¹ * w i)) := by
  have heq := dualBound_eq_of_top (m := m) (B := B) (P := P) hd t hS₀ hS htop
  have hle : objLO m d B Sf S w ≤ QLO m d B P S t :=
    objLO_le_QLO (B := B) (Sf := Sf) (P := P) (G := G) hd hG hPS hw t
  have hQ : QLO m d B P S t = dualBound m d B P k t := by rw [heq]; rfl
  have hopt : ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
      objLO m d B Sf S' u ≤ objLO m d B Sf S w := by
    intro S' hS' u hu
    have := objLO_le_dualBound (m := m) (B := B) (Sf := Sf) (G := G) hd hG hPS hS' hu t
    linarith
  refine ⟨by linarith, hopt, fun hpos S' hS' u hu hru => ?_⟩
  obtain ⟨_, _, hxs⟩ := best_pair_sharpe_uniform (B := B) hd hG hPS
    (by norm_num : (0:ℝ) < 1 / 2) hpos hopt hw (by linarith)
  have := hxs S' hS' u hu hru
  simpa using this

end Dual

/-! ### Adaptive guesses -/

section Adaptive

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- **`J + 1` guesses cover the bracket `[L, 2^(J+1)·L]`.** If `L ≤ F ≤ 2^(J+1)·L`, some
`j ≤ J` satisfies `L·2^j ≤ F ≤ 2·L·2^j` (the intervals `[L·2^j, L·2^(j+1)]`, `j ≤ J`,
cover the bracket); one guess suffices when `F ≤ 2L`. -/
lemma exists_doubling_guess_succ (J : ℕ) {L F : ℝ} (hL : 0 < L) (hLF : L ≤ F)
    (hFJ : F ≤ 2 ^ (J + 1) * L) : ∃ j ≤ J, L * 2 ^ j ≤ F ∧ F ≤ 2 * (L * 2 ^ j) := by
  obtain ⟨j, hj, h1, h2⟩ := exists_doubling_guess (J + 1) hL hLF hFJ
  rcases Nat.lt_or_ge j (J + 1) with hlt | hge
  · exact ⟨j, by omega, h1, h2⟩
  · have hjJ : j = J + 1 := by omega
    subst hjJ
    refine ⟨J, le_rfl, ?_, ?_⟩
    · have : L * 2 ^ J ≤ L * 2 ^ (J + 1) := by
        rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) J]
      linarith
    · have : 2 ^ (J + 1) * L = 2 * (L * 2 ^ J) := by rw [pow_succ]; ring
      linarith

/-- **The anchor family contains a near-optimal support for every bracket**
`L ≤ OPT ≤ 2^(J+1)·L` (not only for the data-only bracket of `exists_guess_of_opt`); the
family uses the `J + 1` guesses `L·2^j`, `j ≤ J`. -/
theorem exists_good_candidate_anchor_bracket [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω) (hL0 : 0 < L) {J : ℕ}
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    {S : Finset ι} (hkS : S.card ≤ k) {Fopt : ℝ}
    (hFopt : IsGreatest {v : ℝ | ∃ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i)
        ∧ v = objLO m d B Sf S u} Fopt)
    (hLF : L ≤ Fopt) (hFJ : Fopt ≤ 2 ^ (J + 1) * L) :
    ∃ R ∈ candidatesAnchor m d B G k ε ω L J La, ∃ w : ι → ℝ,
      (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i)
      ∧ (1 - 2 * ε) * Fopt ≤ objLO m d B Sf (assetsOf (κ := κ) R) w := by
  obtain ⟨j, hjJ, hVF, hFV⟩ := exists_doubling_guess_succ J hL0 hLF hFJ
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

/-- **The enumeration family contains a near-optimal support for every bracket**
`L ≤ OPT ≤ 2^(J+1)·L`. -/
theorem exists_good_candidate_list_bracket [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω) (hL0 : 0 < L) {J : ℕ}
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    {S : Finset ι} (hkS : S.card ≤ k) {Fopt : ℝ}
    (hFopt : IsGreatest {v : ℝ | ∃ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i)
        ∧ v = objLO m d B Sf S u} Fopt)
    (hLF : L ≤ Fopt) (hFJ : Fopt ≤ 2 ^ (J + 1) * L) :
    ∃ R ∈ candidatesList m d B G k ε ω L J La, ∃ w : ι → ℝ,
      (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i)
      ∧ (1 - 2 * ε) * Fopt ≤ objLO m d B Sf (assetsOf (κ := κ) R) w := by
  obtain ⟨j, hjJ, hVF, hFV⟩ := exists_doubling_guess_succ J hL0 hLF hFJ
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

/-- The optimum lies in the bracket `[L, 2^(J+1)·L]` given by a heuristic portfolio with
value at least `L` and a point `t` with `g(t) ≤ 2^(J+1)·L`. -/
lemma opt_mem_bracket (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {k : ℕ}
    {S : Finset ι} (hkS : S.card ≤ k) {Fopt : ℝ}
    (hFopt : IsGreatest {v : ℝ | ∃ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i)
        ∧ v = objLO m d B Sf S u} Fopt)
    (hSopt : ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        objLO m d B Sf S' u ≤ Fopt)
    {Sh : Finset ι} (hSh : Sh.card ≤ k) {wh : ι → ℝ} (hwh : ∀ i ∈ Sh, 0 ≤ wh i)
    {L : ℝ} (hLh : L ≤ objLO m d B Sf Sh wh)
    {t : κ → ℝ} {J : ℕ} (hJ : dualBound m d B P k t ≤ 2 ^ (J + 1) * L) :
    L ≤ Fopt ∧ Fopt ≤ 2 ^ (J + 1) * L := by
  refine ⟨le_trans hLh (hSopt Sh hSh wh hwh), ?_⟩
  obtain ⟨u, hu, hFu⟩ := hFopt.1
  rw [hFu]
  exact le_trans (objLO_le_dualBound hd hG hPS hkS hu t) hJ

/-- **Trading theorem with adaptive guesses (anchor basis).** Let `(S_h, w_h)` be any
long-only portfolio with at most `k` names (for instance a greedy one) with objective at
least `L > 0`, and let `t` be any point with `g(t) ≤ 2^(J+1)·L`. Then for every processing
order every best pair `(R*, w*)` of `candidatesAnchor … L J La` has at most `k` assets,
objective at least `1 − 2ε` times that of every long-only portfolio with at most `k`
names, and the fully invested portfolio `x* = w*/Σw*` has Sharpe ratio at least
`√(1 − 2ε)` times that of every long-only portfolio with at most `k` names and positive
expected excess return. -/
theorem trading_theorem_anchor_adaptive [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    {Sh : Finset ι} (hSh : Sh.card ≤ k) {wh : ι → ℝ} (hwh : ∀ i ∈ Sh, 0 ≤ wh i)
    {L : ℝ} (hL0 : 0 < L) (hLh : L ≤ objLO m d B Sf Sh wh)
    {t : κ → ℝ} {J : ℕ} (hJ : dualBound m d B P k t ≤ 2 ^ (J + 1) * L)
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
  obtain ⟨hLF, hFJ⟩ := opt_mem_bracket hd hG hPS hkS hFopt hSopt hSh hwh hLh hJ
  obtain ⟨h1, h2, _⟩ := best_pair_sharpe_of_family (m := m) (d := d) (B := B) (Sf := Sf)
    (P := P) (G := G) hd hG hPS hε1 hSopt
    (fun _ hR => card_assetsOf_le_of_mem_candidatesAnchor hR)
    (exists_good_candidate_anchor_bracket (Sf := Sf) (P := P) hd hG hPS hk1 hε hε1.le hω
      hsys hL0 hnd hall hkS hFopt hLF hFJ)
    hR₀ hw₀ hbest
  obtain ⟨hx0, hx1, hxs⟩ := best_pair_sharpe_uniform (B := B) hd hG hPS hε1
    (lt_of_lt_of_le hL0 hLF) hSopt hw₀ h2
  refine ⟨h1, fun S' hS' u hu => ?_, hx0, hx1, hxs⟩
  have hub := hSopt S' hS' u hu
  have hcoef : (0:ℝ) ≤ 1 - 2 * ε := by linarith
  linarith [mul_le_mul_of_nonneg_left hub hcoef]

/-- **Trading theorem with adaptive guesses (enumeration of `K`-tuples).** As
`trading_theorem_anchor_adaptive`, for the family `candidatesList … L J La`. -/
theorem trading_theorem_adaptive [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    {Sh : Finset ι} (hSh : Sh.card ≤ k) {wh : ι → ℝ} (hwh : ∀ i ∈ Sh, 0 ≤ wh i)
    {L : ℝ} (hL0 : 0 < L) (hLh : L ≤ objLO m d B Sf Sh wh)
    {t : κ → ℝ} {J : ℕ} (hJ : dualBound m d B P k t ≤ 2 ^ (J + 1) * L)
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
  obtain ⟨hLF, hFJ⟩ := opt_mem_bracket hd hG hPS hkS hFopt hSopt hSh hwh hLh hJ
  obtain ⟨h1, h2, _⟩ := best_pair_sharpe_of_family (m := m) (d := d) (B := B) (Sf := Sf)
    (P := P) (G := G) hd hG hPS hε1 hSopt
    (fun _ hR => card_assetsOf_le_of_mem_candidatesList hR)
    (exists_good_candidate_list_bracket (Sf := Sf) (P := P) hd hG hPS hk1 hε hε1.le hω
      hsys hL0 hnd hall hkS hFopt hLF hFJ)
    hR₀ hw₀ hbest
  obtain ⟨hx0, hx1, hxs⟩ := best_pair_sharpe_uniform (B := B) hd hG hPS hε1
    (lt_of_lt_of_le hL0 hLF) hSopt hw₀ h2
  refine ⟨h1, fun S' hS' u hu => ?_, hx0, hx1, hxs⟩
  have hub := hSopt S' hS' u hu
  have hcoef : (0:ℝ) ≤ 1 - 2 * ε := by linarith
  linarith [mul_le_mul_of_nonneg_left hub hcoef]

end Adaptive

/-! ### An explicit polynomial bound on the size of the anchor family -/

section Poly

/-- The constant `C_K = 8K·(12K)^K·(141K)^K·(37K²)^(K(K+1)/2)` of the polynomial bound on the
size of the anchor family. -/
def polyConst (K : ℕ) : ℕ :=
  8 * K * (12 * K) ^ K * (141 * K) ^ K * (37 * K ^ 2) ^ (K + 1).choose 2

/-- **The data-only number of guesses.** For `q ≥ 1`, `J = ⌈log₂ q⌉` satisfies
`q ≤ 2^J ≤ 2q`. -/
lemma guess_count_spec {q : ℝ} (hq : 1 ≤ q) :
    q ≤ 2 ^ ⌈Real.logb 2 q⌉₊ ∧ (2:ℝ) ^ ⌈Real.logb 2 q⌉₊ ≤ 2 * q := by
  have hq0 : 0 < q := by linarith
  have hlog : 0 ≤ Real.logb 2 q := Real.logb_nonneg (by norm_num) hq
  have hrp : (2:ℝ) ^ Real.logb 2 q = q := Real.rpow_logb (by norm_num) (by norm_num) hq0
  constructor
  · calc q = (2:ℝ) ^ Real.logb 2 q := hrp.symm
      _ ≤ (2:ℝ) ^ ((⌈Real.logb 2 q⌉₊ : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
      _ = (2:ℝ) ^ ⌈Real.logb 2 q⌉₊ := Real.rpow_natCast _ _
  · have h1 : ((⌈Real.logb 2 q⌉₊ : ℕ) : ℝ) ≤ Real.logb 2 q + 1 :=
      (Nat.ceil_lt_add_one hlog).le
    calc (2:ℝ) ^ ⌈Real.logb 2 q⌉₊ = (2:ℝ) ^ ((⌈Real.logb 2 q⌉₊ : ℕ) : ℝ) :=
          (Real.rpow_natCast _ _).symm
      _ ≤ (2:ℝ) ^ (Real.logb 2 q + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = 2 * q := by rw [Real.rpow_add (by norm_num), Real.rpow_one, hrp]; ring

/-- `2⌈x⌉ + 1 ≤ 2x + 3` for `x ≥ 0`, through `Int.toNat`. -/
lemma cast_toNat_two_ceil_le {x : ℝ} (hx : 0 ≤ x) :
    (((2 * ⌈x⌉ + 1).toNat : ℕ) : ℝ) ≤ 2 * x + 3 := by
  have hc : (0:ℤ) ≤ ⌈x⌉ := Int.ceil_nonneg hx
  have h1 : (((2 * ⌈x⌉ + 1).toNat : ℕ) : ℤ) = 2 * ⌈x⌉ + 1 := Int.toNat_of_nonneg (by omega)
  have h2 : (((2 * ⌈x⌉ + 1).toNat : ℕ) : ℝ) = 2 * (⌈x⌉ : ℝ) + 1 := by
    have := congrArg (fun z : ℤ => (z : ℝ)) h1
    push_cast at this
    exact this
  rw [h2]
  have := Int.ceil_lt_add_one x
  linarith

/-- **`N_K` is bounded by a polynomial.** With `q = k(1+ω)`, `0 < ε ≤ 1` and `2^J ≤ 2q`,

    (J+1)·(2Z_A+1)^K·(T_A+1) ≤ C_K · M^(K + K(K+1)/2) · (1/ε)^K · q^(2 + 4K + K(K+1)),

where `Z_A = anchorZ` and `T_A = tableBoundAnchorSym`: the degree in `M` is `K(K+3)/2`, in
`1/ε` it is `K`, and in `k(1+ω)` it is `K² + 5K + 2`. -/
theorem NK_le_poly {M K k : ℕ} (hM : 1 ≤ M) (hK : 1 ≤ K) (hk1 : 1 ≤ k) {ε ω : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hω : 0 ≤ ω) {J : ℕ}
    (hJ2 : (2 : ℝ) ^ J ≤ 2 * ((k : ℝ) * (1 + ω))) :
    (((J + 1) * ((2 * anchorZ K k ε ω + 1) ^ K * (tableBoundAnchorSym M K k ε ω + 1)) : ℕ)
        : ℝ)
      ≤ (polyConst K : ℝ) * (M : ℝ) ^ (K + (K + 1).choose 2) * (1 / ε) ^ K
        * ((k : ℝ) * (1 + ω)) ^ (2 + 4 * K + 2 * (K + 1).choose 2) := by
  set q : ℝ := (k : ℝ) * (1 + ω) with hqdef
  set C := (K + 1).choose 2 with hCdef
  set s : ℝ := Real.sqrt (1 / ε) with hsdef
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk1
  have hq1 : 1 ≤ q := by
    rw [hqdef]; nlinarith
  have hq0 : 0 < q := by linarith
  have hkq : (k : ℝ) ≤ q := by
    rw [hqdef]; nlinarith
  have hs2 : s ^ 2 = 1 / ε := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by
    rw [hsdef, Real.one_le_sqrt, le_div_iff₀ hε]; linarith
  have hc0 : 0 < (k : ℝ) * (1 + (k : ℝ) * ω) := by positivity
  have hc : (k : ℝ) * (1 + (k : ℝ) * ω) ≤ q ^ 2 := by
    have h1 : (k : ℝ) * (1 + (k : ℝ) * ω) ≤ (k : ℝ) * q := by
      rw [hqdef]; apply mul_le_mul_of_nonneg_left _ (by linarith); nlinarith
    have h2 : (k : ℝ) * q ≤ q ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_right hkq hq0.le
    linarith
  have hCK : (K : ℝ) + (k : ℝ) * ω ≤ K * q := by
    rw [hqdef]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ K) (by linarith : (0:ℝ) ≤ k - 1),
      mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ k) hω) (by linarith : (0:ℝ) ≤ K - 1)]
  have hmax : max 1 ω ≤ q := max_le hq1 (by rw [hqdef]; nlinarith)
  have hKq : (K : ℝ) ≤ K * q := by nlinarith
  have hqKq : q ≤ K * q := by nlinarith
  have hkK : (((k + K : ℕ) : ℝ)) ≤ 2 * K * q := by push_cast; linarith
  have hKqs : 1 ≤ (K : ℝ) * q ^ 2 * s :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hKr (one_le_pow₀ hq1)) hs1
  have hMKqs : (M : ℝ) ≤ M * K * q ^ 2 * s := by
    have : (M : ℝ) * 1 ≤ M * (K * q ^ 2 * s) := mul_le_mul_of_nonneg_left hKqs (by positivity)
    linarith [show (M : ℝ) * K * q ^ 2 * s = M * (K * q ^ 2 * s) by ring]
  -- the node count
  have hZ : 2 * (anchorZ K k ε ω : ℝ) + 1 ≤ 12 * K * q ^ 2 * s := by
    unfold anchorZ
    set x := Real.sqrt ((K : ℝ) * ((K : ℝ) + (k : ℝ) * ω)
      / (2 * (ε / (32 * ((k : ℝ) * (1 + (k : ℝ) * ω)))))) with hx
    have hx0 : 0 ≤ x := Real.sqrt_nonneg _
    have hxle : x ≤ 4 * K * q ^ 2 * s := by
      rw [hx, Real.sqrt_le_left (by positivity)]
      have e1 : (K : ℝ) * ((K : ℝ) + (k : ℝ) * ω)
            / (2 * (ε / (32 * ((k : ℝ) * (1 + (k : ℝ) * ω)))))
          = 16 * (((K : ℝ) * ((K : ℝ) + (k : ℝ) * ω)) * ((k : ℝ) * (1 + (k : ℝ) * ω)))
            * (1 / ε) := by
        field_simp
        ring
      have hA1 : (K : ℝ) * ((K : ℝ) + (k : ℝ) * ω) ≤ K * (K * q) :=
        mul_le_mul_of_nonneg_left hCK (by positivity)
      have hprod : ((K : ℝ) * ((K : ℝ) + (k : ℝ) * ω)) * ((k : ℝ) * (1 + (k : ℝ) * ω))
          ≤ (K * (K * q)) * q ^ 2 * q :=
        le_trans (mul_le_mul hA1 hc (by positivity) (by positivity))
          (le_mul_of_one_le_right (by positivity) hq1)
      rw [e1, show (4 * (K : ℝ) * q ^ 2 * s) ^ 2 = 16 * ((K * (K * q)) * q ^ 2 * q) * s ^ 2 by
        ring, hs2]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by norm_num))
        (by positivity)
    have hceil : (⌈x + 1 / 2⌉₊ : ℝ) < x + 1 / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    nlinarith
  have hN : (k : ℝ) + K + 1 ≤ 3 * K * q := by linarith
  have hJ1 : (J : ℝ) + 1 ≤ 2 * q := by
    have h1 : J + 1 ≤ 2 ^ J := Nat.lt_two_pow_self
    have h2 : ((J + 1 : ℕ) : ℝ) ≤ ((2 ^ J : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have h1MKqs : (1 : ℝ) ≤ M * K * q ^ 2 * s := le_trans hMr hMKqs
  have hMKq2 : (M : ℝ) ≤ M * K ^ 2 * q ^ 2 := by
    have hK2q2 : (1 : ℝ) ≤ K ^ 2 * q ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hKr) (one_le_pow₀ hq1)
    have : (M : ℝ) * 1 ≤ M * (K ^ 2 * q ^ 2) := mul_le_mul_of_nonneg_left hK2q2 (by positivity)
    linarith [show (M : ℝ) * K ^ 2 * q ^ 2 = M * (K ^ 2 * q ^ 2) by ring]
  have h1MKq2 : (1 : ℝ) ≤ M * K ^ 2 * q ^ 2 := le_trans hMr hMKq2
  -- the table bound
  have hT : ((tableBoundAnchorSym M K k ε ω : ℕ) : ℝ) + 1
      ≤ 4 * K * q * ((141 * M * K * q ^ 2 * s) ^ K * (37 * M * K ^ 2 * q ^ 2) ^ C) := by
    unfold tableBoundAnchorSym
    rw [← hCdef]
    generalize hAeq : (2 * ⌈Real.sqrt (max 1 ω) * (48 * (M : ℝ) * Real.sqrt (K : ℝ)
      * Real.sqrt (((k + K : ℕ) : ℝ) * ((k : ℝ) * (1 + (k : ℝ) * ω)) / ε))
      + (M : ℝ)⌉ + 1).toNat = A
    generalize hBeq : (2 * ⌈8 * ((k + K : ℕ) : ℝ) * (M : ℝ) * (K : ℝ)
      * Real.sqrt (max 1 ω) ^ 2 + (M : ℝ)⌉ + 1).toNat = B'
    have hA : (A : ℝ) ≤ 141 * M * K * q ^ 2 * s := by
      rw [← hAeq]
      set y := Real.sqrt (max 1 ω) * (48 * (M : ℝ) * Real.sqrt (K : ℝ)
        * Real.sqrt (((k + K : ℕ) : ℝ) * ((k : ℝ) * (1 + (k : ℝ) * ω)) / ε)) with hy
      have hy0 : 0 ≤ y := by positivity
      have hy2 : y ^ 2 = max 1 ω * (48 * (M : ℝ)) ^ 2 * K
          * (((k + K : ℕ) : ℝ) * ((k : ℝ) * (1 + (k : ℝ) * ω)) / ε) := by
        rw [hy, mul_pow, mul_pow, mul_pow,
          Real.sq_sqrt (le_trans zero_le_one (le_max_left _ _)),
          Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
        ring
      have hp : max 1 ω * ((k + K : ℕ) : ℝ) * ((k : ℝ) * (1 + (k : ℝ) * ω))
          ≤ q * (2 * K * q) * q ^ 2 :=
        mul_le_mul (mul_le_mul hmax hkK (by positivity) hq0.le) hc (by positivity)
          (by positivity)
      have hbound : y ^ 2 ≤ (68 * M * K * q ^ 2 * s) ^ 2 := by
        rw [hy2]
        calc max 1 ω * (48 * (M : ℝ)) ^ 2 * K
              * (((k + K : ℕ) : ℝ) * ((k : ℝ) * (1 + (k : ℝ) * ω)) / ε)
            = (max 1 ω * ((k + K : ℕ) : ℝ) * ((k : ℝ) * (1 + (k : ℝ) * ω)))
              * (2304 * (M : ℝ) ^ 2 * K * (1 / ε)) := by ring
          _ ≤ (q * (2 * K * q) * q ^ 2) * (2304 * (M : ℝ) ^ 2 * K * (1 / ε)) :=
              mul_le_mul_of_nonneg_right hp (by positivity)
          _ = 4608 * ((M : ℝ) ^ 2 * K ^ 2 * q ^ 4 * (1 / ε)) := by ring
          _ ≤ 4624 * ((M : ℝ) ^ 2 * K ^ 2 * q ^ 4 * (1 / ε)) :=
              mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
          _ = (68 * M * K * q ^ 2 * s) ^ 2 := by rw [← hs2]; ring
      have hyle : y ≤ 68 * M * K * q ^ 2 * s :=
        (pow_le_pow_iff_left₀ hy0 (by positivity) (by norm_num)).1 hbound
      have := cast_toNat_two_ceil_le (x := y + M) (by positivity)
      linarith
    have hB : (B' : ℝ) ≤ 37 * M * K ^ 2 * q ^ 2 := by
      rw [← hBeq]
      have h0 : 0 ≤ 8 * ((k + K : ℕ) : ℝ) * (M : ℝ) * (K : ℝ) * Real.sqrt (max 1 ω) ^ 2
          + (M : ℝ) := by positivity
      have h1 := cast_toNat_two_ceil_le h0
      have hp : ((k + K : ℕ) : ℝ) * max 1 ω ≤ (2 * K * q) * q :=
        mul_le_mul hkK hmax (by positivity) (by positivity)
      have h2 : 8 * ((k + K : ℕ) : ℝ) * (M : ℝ) * (K : ℝ) * Real.sqrt (max 1 ω) ^ 2
          ≤ 16 * M * K ^ 2 * q ^ 2 := by
        rw [Real.sq_sqrt (le_trans zero_le_one (le_max_left _ _))]
        calc 8 * ((k + K : ℕ) : ℝ) * (M : ℝ) * (K : ℝ) * max 1 ω
            = (8 * M * K) * (((k + K : ℕ) : ℝ) * max 1 ω) := by ring
          _ ≤ (8 * M * K) * ((2 * K * q) * q) := mul_le_mul_of_nonneg_left hp (by positivity)
          _ = 16 * M * K ^ 2 * q ^ 2 := by ring
      linarith
    have hP1 : 1 ≤ (141 * M * K * q ^ 2 * s) ^ K * (37 * M * K ^ 2 * q ^ 2) ^ C :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ (by linarith))
    have hKq1 : (1 : ℝ) ≤ K * q := le_trans hKr hKq
    have hKqP : 1 ≤ K * q * ((141 * M * K * q ^ 2 * s) ^ K * (37 * M * K ^ 2 * q ^ 2) ^ C) :=
      one_le_mul_of_one_le_of_one_le hKq1 hP1
    push_cast
    calc (A : ℝ) ^ K * ((B' : ℝ) ^ C * ((k : ℝ) + K + 1)) + 1
        ≤ (141 * M * K * q ^ 2 * s) ^ K * ((37 * M * K ^ 2 * q ^ 2) ^ C * (3 * K * q)) + 1 := by
          gcongr
      _ ≤ 4 * K * q * ((141 * M * K * q ^ 2 * s) ^ K * (37 * M * K ^ 2 * q ^ 2) ^ C) := by
          nlinarith
  push_cast
  calc ((J : ℝ) + 1) * ((2 * (anchorZ K k ε ω : ℝ) + 1) ^ K
        * ((tableBoundAnchorSym M K k ε ω : ℝ) + 1))
      ≤ (2 * q) * ((12 * K * q ^ 2 * s) ^ K
        * (4 * K * q * ((141 * M * K * q ^ 2 * s) ^ K * (37 * M * K ^ 2 * q ^ 2) ^ C))) := by
        gcongr
    _ = (polyConst K : ℝ) * (M : ℝ) ^ (K + C) * (1 / ε) ^ K * q ^ (2 + 4 * K + 2 * C) := by
        rw [← hs2]
        unfold polyConst
        rw [← hCdef]
        push_cast
        ring_nf

end Poly

section PolyFamily

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {G : κ → κ → ℝ}

/-- **The anchor family has polynomial size.** For `0 < ε ≤ 1` and `2^J ≤ 2k(1+ω)`,

    |candidatesAnchor| ≤ C_K · M^(K + K(K+1)/2) · (1/ε)^K · (k(1+ω))^(2 + 4K + K(K+1)). -/
theorem card_candidatesAnchor_poly [Nonempty κ] [Nonempty ι] {k : ℕ} (hk1 : 1 ≤ k)
    {ε ω L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hω : 0 ≤ ω) (hL0 : 0 < L) {J : ℕ}
    (hJ2 : (2 : ℝ) ^ J ≤ 2 * ((k : ℝ) * (1 + ω))) (La : List ι) :
    ((candidatesAnchor m d B G k ε ω L J La).card : ℝ)
      ≤ (polyConst (Fintype.card κ) : ℝ)
        * (Fintype.card ι : ℝ) ^ (Fintype.card κ + (Fintype.card κ + 1).choose 2)
        * (1 / ε) ^ Fintype.card κ
        * ((k : ℝ) * (1 + ω)) ^ (2 + 4 * Fintype.card κ + 2 * (Fintype.card κ + 1).choose 2) :=
  le_trans (by exact_mod_cast card_candidatesAnchor_le_sym hk1 hε hω hL0 J La)
    (NK_le_poly Fintype.card_pos Fintype.card_pos hk1 hε hε1 hω hJ2)

end PolyFamily

/-! ### The Main Theorem in its simple form -/

section Simple

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- **Main Theorem (simple form).** Data: `d > 0`, `G'G = Σ_f⁻¹`, `k ≥ 1`, `0 < ε < 1/2`,
`ω ≥ B_i'Σ_fB_i/d_i` for all assets, `L = max_i (m_i)_+²/V_ii > 0` (the squared Sharpe
ratio of the best single asset), the number of guesses `J = ⌈log₂ k(1+ω)⌉`, and any
processing order `La`. The candidate family `candidatesAnchor … La` (the supports of the
tables of the dynamic program over the guesses and the grid nodes)

1. has at most `N_K = (J+1)·(2Z+1)^K·(tableBoundAnchorSym+1)` members, and
   `|family| ≤ C_K·M^(K+K(K+1)/2)·(1/ε)^K·(k(1+ω))^(2+4K+K(K+1))` (`polyConst`);
2. consists of supports with at most `k` assets;
3. has a best pair `(R*, w*)`: a member and a long-only portfolio on it whose objective
   is at least that of every member with every long-only portfolio on it;
4. for every best pair, `R*` has at most `k` assets and the fully invested long-only
   portfolio `x* = w*/Σw*` has Sharpe ratio at least `√(1 − 2ε)` times that of every
   long-only portfolio with at most `k` names and positive expected excess return. -/
theorem main_theorem_simple [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω L : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    (hL0 : 0 < L) (hL : ∀ i, max (m i) 0 ^ 2 / Vmat d B Sf i i ≤ L)
    (hLatt : ∃ i, max (m i) 0 ^ 2 / Vmat d B Sf i i = L)
    {J : ℕ} (hJ : J = ⌈Real.logb 2 ((k : ℝ) * (1 + ω))⌉₊)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La) :
    (candidatesAnchor m d B G k ε ω L J La).card
        ≤ (J + 1) * ((2 * anchorZ (Fintype.card κ) k ε ω + 1) ^ Fintype.card κ
          * (tableBoundAnchorSym (Fintype.card ι) (Fintype.card κ) k ε ω + 1))
    ∧ ((candidatesAnchor m d B G k ε ω L J La).card : ℝ)
        ≤ (polyConst (Fintype.card κ) : ℝ)
          * (Fintype.card ι : ℝ) ^ (Fintype.card κ + (Fintype.card κ + 1).choose 2)
          * (1 / ε) ^ Fintype.card κ
          * ((k : ℝ) * (1 + ω)) ^ (2 + 4 * Fintype.card κ + 2 * (Fintype.card κ + 1).choose 2)
    ∧ (∀ R ∈ candidatesAnchor m d B G k ε ω L J La, (assetsOf (κ := κ) R).card ≤ k)
    ∧ (∃ R₀ ∈ candidatesAnchor m d B G k ε ω L J La, ∃ w₀ : ι → ℝ,
        (∀ i ∈ assetsOf (κ := κ) R₀, 0 ≤ w₀ i) ∧
        ∀ R ∈ candidatesAnchor m d B G k ε ω L J La, ∀ w : ι → ℝ,
          (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i) →
            objLO m d B Sf (assetsOf (κ := κ) R) w
              ≤ objLO m d B Sf (assetsOf (κ := κ) R₀) w₀)
    ∧ ∀ R₀ ∈ candidatesAnchor m d B G k ε ω L J La, ∀ w₀ : ι → ℝ,
        (∀ i ∈ assetsOf (κ := κ) R₀, 0 ≤ w₀ i) →
        (∀ R ∈ candidatesAnchor m d B G k ε ω L J La, ∀ w : ι → ℝ,
          (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i) →
            objLO m d B Sf (assetsOf (κ := κ) R) w
              ≤ objLO m d B Sf (assetsOf (κ := κ) R₀) w₀) →
        (assetsOf (κ := κ) R₀).card ≤ k
        ∧ (∀ i ∈ assetsOf (κ := κ) R₀, 0 ≤ (∑ j ∈ assetsOf (κ := κ) R₀, w₀ j)⁻¹ * w₀ i)
        ∧ ∑ i ∈ assetsOf (κ := κ) R₀, (∑ j ∈ assetsOf (κ := κ) R₀, w₀ j)⁻¹ * w₀ i = 1
        ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
            0 < pRet m S' u →
            Real.sqrt (1 - 2 * ε) * sharpe m d B Sf S' u
              ≤ sharpe m d B Sf (assetsOf (κ := κ) R₀)
                  (fun i => (∑ j ∈ assetsOf (κ := κ) R₀, w₀ j)⁻¹ * w₀ i) := by
  have hq1 : (1:ℝ) ≤ (k : ℝ) * (1 + ω) := by
    have : (1:ℝ) ≤ k := by exact_mod_cast hk1
    nlinarith
  obtain ⟨hJa, hJb⟩ := guess_count_spec hq1
  rw [← hJ] at hJa hJb
  refine ⟨card_candidatesAnchor_le_sym hk1 hε hω hL0 J La,
    card_candidatesAnchor_poly hk1 hε (by linarith) hω hL0 hJb La,
    fun R hR => card_assetsOf_le_of_mem_candidatesAnchor hR, ?_, ?_⟩
  · obtain ⟨S, hkS, Fopt, hFopt, hSopt⟩ := exists_optimal_support (m := m) (d := d) (B := B)
      (Sf := Sf) (P := P) (G := G) hd hG hPS k
    obtain ⟨R, hR, _⟩ := exists_good_candidate_anchor (Sf := Sf) (P := P) hd hG hPS hk1 hε
      hε1.le hω hsys hL0 hL hLatt hJa hnd hall hkS hFopt hSopt
    exact exists_best_pair_of_family (m := m) (d := d) (B := B) (Sf := Sf) (P := P) (G := G)
      hd hG hPS ⟨R, hR⟩
  · intro R₀ hR₀ w₀ hw₀ hbest
    obtain ⟨h1, _, h3, h4, h5⟩ := trading_theorem_anchor (m := m) (d := d) (B := B)
      (Sf := Sf) (P := P) (G := G) hd hG hPS hk1 hε hε1 hω hsys hL0 hL hLatt hJa hnd hall hR₀
      hw₀ hbest
    exact ⟨h1, h3, h4, h5⟩

end Simple

/-! ### Nonvacuity of the new end-to-end statements

The instance of `trading_instance` (one asset, `m = d = 1`, `B = 0`, `Σ_f = 1`, `k = 1`,
`ε = 1/4`, `ω = 0`, `L = 1`, `J = 0`), processing order `[0]`; the heuristic portfolio is the
whole universe with weight `1`, and the dual point is `t = 0`. -/

section InstancePractical

/-- **The new end-to-end statements are not vacuous.** On the one-asset instance every
hypothesis of `main_theorem_simple`, of `certificate_sharpe_eps` and of
`trading_theorem_anchor_adaptive` holds, and each conclusion gives a fully invested
long-only portfolio with Sharpe ratio at least `√(1/2)`. -/
theorem practical_instance :
    (∃ R₀ ∈ candidatesAnchor (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1) (fun _ (_ : Unit) => 0)
        (fun _ _ => 1) 1 (1/4) 0 1 0 [0],
      ∃ x : Fin 1 → ℝ, (∀ i ∈ assetsOf (κ := Unit) R₀, 0 ≤ x i)
        ∧ ∑ i ∈ assetsOf (κ := Unit) R₀, x i = 1
        ∧ Real.sqrt (1 - 2 * (1/4)) ≤ sharpe (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1)
            (fun _ (_ : Unit) => 0) (fun _ _ => 1) (assetsOf (κ := Unit) R₀) x)
    ∧ (∃ x : Fin 1 → ℝ, (∀ i ∈ (Finset.univ : Finset (Fin 1)), 0 ≤ x i)
        ∧ ∑ i ∈ (Finset.univ : Finset (Fin 1)), x i = 1
        ∧ Real.sqrt (1 - 2 * (1/4)) ≤ sharpe (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1)
            (fun _ (_ : Unit) => 0) (fun _ _ => 1) Finset.univ x)
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
  have hJlog : (0:ℕ) = ⌈Real.logb 2 (((1:ℕ) : ℝ) * (1 + 0))⌉₊ := by simp
  have hnd : ([0] : List (Fin 1)).Nodup := List.nodup_singleton 0
  have hall : ∀ i : Fin 1, i ∈ ([0] : List (Fin 1)) := by
    intro i; rw [List.mem_singleton]; exact Subsingleton.elim _ _
  have hsu : sharpe m d B Sf Finset.univ (fun _ => 1) = 1 := by
    simp [sharpe, pRet, pVar, Vmat, m, d, B]
  have hobj1 : objLO m d B Sf Finset.univ (fun _ => 1) = 1 := by
    simp [objLO, Vmat, m, d, B]; norm_num
  have hcard : (Finset.univ : Finset (Fin 1)).card ≤ 1 := by simp
  have hw1 : ∀ i ∈ (Finset.univ : Finset (Fin 1)), (0:ℝ) ≤ (fun _ => (1:ℝ)) i :=
    fun _ _ => zero_le_one
  have hg : dualBound m d B P 1 (fun _ => 0) ≤ 1 := by
    have := dualBound_zero_le (m := m) (d := d) (B := B) (Sf := Sf) (P := P) (G := G) hd hG
      hPS (le_refl (0:ℝ)) hsys zero_le_one hL 1
    norm_num at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨_, _, _, ⟨R₀, hR₀, w₀, hw₀, hbest⟩, h3⟩ := main_theorem_simple (G := G) (P := P)
      (Sf := Sf) hd hG hPS le_rfl (by norm_num : (0:ℝ) < 1/4) (by norm_num) le_rfl hsys
      one_pos hL hLatt hJlog hnd hall
    obtain ⟨_, hx0, hx1, hxsh⟩ := h3 R₀ hR₀ w₀ hw₀ hbest
    have hsh := hxsh Finset.univ hcard (fun _ => 1) hw1 (by simp [pRet, m])
    refine ⟨R₀, hR₀, _, hx0, hx1, ?_⟩
    rw [hsu, mul_one] at hsh
    exact hsh
  · have hcert : (1 - 2 * (1/4 : ℝ)) * dualBound m d B P 1 (fun _ => 0)
        ≤ objLO m d B Sf Finset.univ (fun _ => 1) := by
      rw [hobj1]; linarith
    obtain ⟨_, hx0, hx1, hxsh⟩ := certificate_sharpe_eps (G := G) hd hG hPS
      (by norm_num : (1/4 : ℝ) < 1/2) hcard hw1 (by rw [hobj1]; exact one_pos) _ hcert
    have hsh := hxsh Finset.univ hcard (fun _ => 1) hw1 (by simp [pRet, m])
    refine ⟨_, hx0, hx1, ?_⟩
    rw [hsu, mul_one] at hsh
    exact hsh
  · have hSopt : ∀ S' : Finset (Fin 1), S'.card ≤ 1 → ∀ u : Fin 1 → ℝ,
        (∀ i ∈ S', 0 ≤ u i) → objLO m d B Sf S' u ≤ 1 := fun S' _ u hu => inst_obj_le S' u hu
    have hFopt : IsGreatest {v : ℝ | ∃ u : Fin 1 → ℝ, (∀ i ∈ (Finset.univ : Finset (Fin 1)),
        0 ≤ u i) ∧ v = objLO m d B Sf Finset.univ u} 1 :=
      ⟨⟨fun _ => 1, hw1, hobj1.symm⟩, by rintro v ⟨u, hu, rfl⟩; exact inst_obj_le _ u hu⟩
    have hJ0 : dualBound m d B P 1 (fun _ => 0) ≤ 2 ^ ((0:ℕ) + 1) * 1 := by
      norm_num; linarith
    obtain ⟨R, hR, _⟩ := exists_good_candidate_anchor_bracket (G := G) (P := P) (J := 0)
      (La := [0]) hd hG hPS le_rfl (by norm_num : (0:ℝ) < 1/4) (by norm_num) le_rfl hsys
      one_pos hnd hall hcard hFopt le_rfl (by norm_num)
    obtain ⟨R₀, hR₀, w₀, hw₀, hbest⟩ := exists_best_pair_of_family (Sf := Sf) (P := P) hd hG
      hPS ⟨R, hR⟩
    obtain ⟨_, _, hx0, hx1, hxsh⟩ := trading_theorem_anchor_adaptive (G := G) (P := P) hd hG
      hPS le_rfl (by norm_num : (0:ℝ) < 1/4) (by norm_num) le_rfl hsys hcard hw1 one_pos
      (by rw [hobj1]) hJ0 hnd hall hR₀ hw₀ hbest
    have hsh := hxsh Finset.univ hcard (fun _ => 1) hw1 (by simp [pRet, m])
    refine ⟨R₀, hR₀, _, hx0, hx1, ?_⟩
    rw [hsu, mul_one] at hsh
    exact hsh

end InstancePractical

end SparseSharpe.Factor
