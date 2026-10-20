import SparseSharpe.Factor.ClippedDP
import SparseSharpe.Factor.Practical

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Главная теорема: динамика без матрицы Грама (сессия 23)

Сквозные утверждения для семейства `clipFamily` (`Factor/ClippedDP.lean`): узлы сетки
`Gτ ∈ s·ℤ^K`, в каждом — рюкзак по счетам `s_i(τ)` с аддитивным ключом `(Σ⌊v_i/η⌋, |R|)`.

* `card_clipCandidates_le` — размер семейства **не зависит от числа активов `M`**:
  `(J+1)·(2Z+1)^K·((2Q+1)^K(k+1)+1)`, `Z = ⌈(1+kω)√(K/ε)+1/2⌉`, `Q = k + ⌈√(5ωk³K/ε)⌉`;
* `exists_good_clipCandidate` — в семействе есть набор с портфелем `w ≥ 0`,
  `objLO ≥ (1−2ε)·OPT`;
* `main_theorem_clipped` — Main Theorem в данных задачи, для любого порядка активов:
  размер, `≤ k` активов у каждого члена, существование лучшей пары, гарантия
  `√(1−2ε)` для коэффициента Шарпа полностью инвестированного портфеля.

Старое семейство `candidatesAnchor` (`Factor/TradingAnchor.lean`, `main_theorem_simple`)
остаётся в проекте: оно доказывает ту же гарантию другим путём (динамика по моментам и
матрице Грама с фильтром и константой покрытия) и даёт худшие границы (`M^{K(K+3)/2}`).
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- **Семейство кандидатов по всем догадкам** `V_j = L·2^j`, `j ≤ J`. -/
noncomputable def clipCandidates (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf G : κ → κ → ℝ)
    (ε ω L : ℝ) (J k : ℕ) (La : List ι) : Finset (Finset ι) :=
  (Finset.range (J + 1)).biUnion (fun j => clipFamily m d B Sf G ε ω (L * 2 ^ j) k La)

/-- Размер семейства по всем догадкам. -/
theorem card_clipCandidates_le (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf G : κ → κ → ℝ)
    (ε ω L : ℝ) (J k : ℕ) (La : List ι) :
    (clipCandidates m d B Sf G ε ω L J k La).card
      ≤ (J + 1) * ((2 * clipZ ε ω k (Fintype.card κ) + 1) ^ Fintype.card κ
        * ((2 * clipQ ε ω k (Fintype.card κ) + 1) ^ Fintype.card κ * (k + 1) + 1)) := by
  refine le_trans Finset.card_biUnion_le ?_
  calc ∑ j ∈ Finset.range (J + 1), (clipFamily m d B Sf G ε ω (L * 2 ^ j) k La).card
      ≤ ∑ _j ∈ Finset.range (J + 1),
          ((2 * clipZ ε ω k (Fintype.card κ) + 1) ^ Fintype.card κ
            * ((2 * clipQ ε ω k (Fintype.card κ) + 1) ^ Fintype.card κ * (k + 1) + 1)) :=
        Finset.sum_le_sum fun j _ => card_clipFamily_le m d B Sf G ε ω _ k La
    _ = (J + 1) * ((2 * clipZ ε ω k (Fintype.card κ) + 1) ^ Fintype.card κ
          * ((2 * clipQ ε ω k (Fintype.card κ) + 1) ^ Fintype.card κ * (k + 1) + 1)) := by
        simp

/-- У каждого члена семейства не больше `k` активов. -/
theorem card_le_of_mem_clipCandidates {ε ω L : ℝ} {J k : ℕ} {La : List ι} {R : Finset ι}
    (hR : R ∈ clipCandidates m d B Sf G ε ω L J k La) : R.card ≤ k := by
  rw [clipCandidates, Finset.mem_biUnion] at hR
  obtain ⟨j, _, hj⟩ := hR
  rw [clipFamily, Finset.mem_biUnion] at hj
  obtain ⟨z, _, hz⟩ := hj
  exact card_le_of_mem_clipTable m d B Sf G _ _ k La _ hz

/-- **В семействе есть хороший кандидат.** Для любого оптимального носителя `S`
(`|S| ≤ k`, значение `Fopt`) и любой догадки в сетке `L·2^j` есть набор `R` с `|R| ≤ k` и
портфелем `w ≥ 0`, `objLO(R,w) ≥ (1−2ε)·Fopt`. -/
theorem exists_good_clipCandidate [Nonempty κ] [Nonempty ι]
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
    ∃ R ∈ clipCandidates m d B Sf G ε ω L J k La, R.card ≤ k ∧
      ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (1 - 2 * ε) * Fopt ≤ objLO m d B Sf R w := by
  obtain ⟨j, hj, hjL, hjF⟩ := exists_guess_of_opt (m := m) (B := B) (Sf := Sf) (P := P)
    (G := G) hd hG hPS hk1 hω hsys hL0 hL hLatt hJ hkS hFopt hSopt
  obtain ⟨z, hzmin, hzmax⟩ := isGreatest_objLO_isLeast_QLO (m := m) (B := B) (Sf := Sf)
    (P := P) (G := G) hd hG hPS S
  have hz : z = Fopt := hzmax.unique hFopt
  obtain ⟨t₀, ht₀⟩ := hzmin.1
  have hmin : ∀ t, QLO m d B P S t₀ ≤ QLO m d B P S t := by
    intro t; rw [← ht₀]; exact hzmin.2 ⟨t, rfl⟩
  have hF : QLO m d B P S t₀ = Fopt := by rw [← ht₀, hz]
  have hV : 0 < L * 2 ^ j := by positivity
  obtain ⟨R, hR, hRk, w, hw, hobj⟩ := clip_one_guess (m := m) (B := B) (Sf := Sf) (P := P)
    (G := G) hd hG hPS hk1 hε hε1 hω hsys hkS hmin hV (by rw [hF]; exact hjL)
    (by rw [hF]; exact hjF) hnd hall
  refine ⟨R, ?_, hRk, w, hw, by rw [← hF]; exact hobj⟩
  rw [clipCandidates, Finset.mem_biUnion]
  exact ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hj), hR⟩

/-- **Адаптивные догадки.** Если `L ≤ Fopt ≤ 2^(J+1)·L` (скобка `[L, 2^{J+1}L]` от эвристики и
двойственной границы), то в `clipCandidates … L J` есть набор `R`, `|R| ≤ k`, с портфелем
`w ≥ 0`, `objLO(R,w) ≥ (1−2ε)·Fopt`. -/
theorem exists_good_clipCandidate_bracket [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω) (hL0 : 0 < L) {J : ℕ}
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    {S : Finset ι} (hkS : S.card ≤ k) {Fopt : ℝ}
    (hFopt : IsGreatest {v : ℝ | ∃ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i)
        ∧ v = objLO m d B Sf S u} Fopt)
    (hLF : L ≤ Fopt) (hFJ : Fopt ≤ 2 ^ (J + 1) * L) :
    ∃ R ∈ clipCandidates m d B Sf G ε ω L J k La, R.card ≤ k ∧
      ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (1 - 2 * ε) * Fopt ≤ objLO m d B Sf R w := by
  obtain ⟨j, hjJ, hVF, hFV⟩ := exists_doubling_guess_succ J hL0 hLF hFJ
  obtain ⟨z, hzmin, hzmax⟩ := isGreatest_objLO_isLeast_QLO (m := m) (B := B) (Sf := Sf)
    (P := P) (G := G) hd hG hPS S
  have hz : z = Fopt := hzmax.unique hFopt
  obtain ⟨t₀, ht₀⟩ := hzmin.1
  have hmin : ∀ t, QLO m d B P S t₀ ≤ QLO m d B P S t := by
    intro t; rw [← ht₀]; exact hzmin.2 ⟨t, rfl⟩
  have hF : QLO m d B P S t₀ = Fopt := by rw [← ht₀, hz]
  have hV : 0 < L * 2 ^ j := by positivity
  obtain ⟨R, hR, hRk, w, hw, hobj⟩ := clip_one_guess (m := m) (B := B) (Sf := Sf) (P := P)
    (G := G) hd hG hPS hk1 hε hε1 hω hsys hkS hmin hV (by rw [hF]; exact hVF)
    (by rw [hF]; exact hFV) hnd hall
  refine ⟨R, ?_, hRk, w, hw, by rw [← hF]; exact hobj⟩
  rw [clipCandidates, Finset.mem_biUnion]
  exact ⟨j, Finset.mem_range.mpr (by omega), hR⟩

/-- **Торговая теорема с адаптивными догадками (динамика без матрицы Грама).** Пусть `(S_h, w_h)` —
любой long-only портфель с не более чем `k` именами (например, жадный) со значением не меньше
`L > 0`, а `t` — любая точка с `g(t) ≤ 2^(J+1)·L`. Тогда для любого порядка активов каждая
лучшая пара `(R*, w*)` семейства `clipCandidates … L J` имеет не более `k` активов, значение не
меньше `1−2ε` от значения любого long-only портфеля с не более чем `k` именами, а полностью
инвестированный портфель `x* = w*/Σw*` имеет коэффициент Шарпа не меньше `√(1−2ε)` от
коэффициента Шарпа любого такого портфеля с положительной ожидаемой доходностью. -/
theorem trading_theorem_clipped_adaptive [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    {Sh : Finset ι} (hSh : Sh.card ≤ k) {wh : ι → ℝ} (hwh : ∀ i ∈ Sh, 0 ≤ wh i)
    {L : ℝ} (hL0 : 0 < L) (hLh : L ≤ objLO m d B Sf Sh wh)
    {t : κ → ℝ} {J : ℕ} (hJ : dualBound m d B P k t ≤ 2 ^ (J + 1) * L)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    {R₀ : Finset ι} (hR₀ : R₀ ∈ clipCandidates m d B Sf G ε ω L J k La) {w₀ : ι → ℝ}
    (hw₀ : ∀ i ∈ R₀, 0 ≤ w₀ i)
    (hbest : ∀ R ∈ clipCandidates m d B Sf G ε ω L J k La, ∀ w : ι → ℝ,
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
  obtain ⟨hLF, hFJ⟩ := opt_mem_bracket hd hG hPS hkS hFopt hSopt hSh hwh hLh hJ
  obtain ⟨R, hR, hRk, w, hw, hobj⟩ := exists_good_clipCandidate_bracket (Sf := Sf) (P := P) hd hG
    hPS hk1 hε hε1.le hω hsys hL0 hnd hall hkS hFopt hLF hFJ
  have hval : (1 - 2 * ε) * Fopt ≤ objLO m d B Sf R₀ w₀ :=
    le_trans hobj (hbest R hR w (fun i _ => hw i))
  obtain ⟨hx0, hx1, hxs⟩ := best_pair_sharpe_uniform (B := B) hd hG hPS hε1
    (lt_of_lt_of_le hL0 hLF) hSopt hw₀ hval
  refine ⟨card_le_of_mem_clipCandidates hR₀, fun S' hS' u hu => ?_, hx0, hx1, hxs⟩
  have hub := hSopt S' hS' u hu
  have hcoef : (0 : ℝ) ≤ 1 - 2 * ε := by linarith
  linarith [mul_le_mul_of_nonneg_left hub hcoef]

/-- **Торговая форма (динамика без матрицы Грама), из данных.** Для любого порядка активов
каждая лучшая пара `(R*, w*)` семейства `clipCandidates … L J` с `k(1+ω) ≤ 2^J` имеет не более `k`
активов, значение не меньше `1−2ε` от значения любого long-only портфеля с не более чем `k`
именами, а полностью инвестированный портфель `x* = w*/Σw*` — коэффициент Шарпа не меньше `√(1−2ε)`
от коэффициента Шарпа любого такого портфеля с положительной ожидаемой доходностью. -/
theorem trading_theorem_clipped [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω L : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    (hL0 : 0 < L) (hL : ∀ i, max (m i) 0 ^ 2 / Vmat d B Sf i i ≤ L)
    (hLatt : ∃ i, max (m i) 0 ^ 2 / Vmat d B Sf i i = L)
    {J : ℕ} (hJ : (k : ℝ) * (1 + ω) ≤ 2 ^ J)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    {R₀ : Finset ι} (hR₀ : R₀ ∈ clipCandidates m d B Sf G ε ω L J k La) {w₀ : ι → ℝ}
    (hw₀ : ∀ i ∈ R₀, 0 ≤ w₀ i)
    (hbest : ∀ R ∈ clipCandidates m d B Sf G ε ω L J k La, ∀ w : ι → ℝ,
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
  obtain ⟨R, hR, hRk, w, hw, hobj⟩ := exists_good_clipCandidate (Sf := Sf) (P := P) hd hG hPS
    hk1 hε hε1.le hω hsys hL0 hL hLatt hJ hnd hall hkS hFopt hSopt
  obtain ⟨i₀, hi₀⟩ := hLatt
  have hLF : L ≤ Fopt := hi₀ ▸ opt_ge_single_of_opt (B := B) hd hG hPS hk1 hSopt i₀
  have hval : (1 - 2 * ε) * Fopt ≤ objLO m d B Sf R₀ w₀ :=
    le_trans hobj (hbest R hR w (fun i _ => hw i))
  obtain ⟨hx0, hx1, hxs⟩ := best_pair_sharpe_uniform (B := B) hd hG hPS hε1
    (lt_of_lt_of_le hL0 hLF) hSopt hw₀ hval
  refine ⟨card_le_of_mem_clipCandidates hR₀, fun S' hS' u hu => ?_, hx0, hx1, hxs⟩
  have hub := hSopt S' hS' u hu
  have hcoef : (0 : ℝ) ≤ 1 - 2 * ε := by linarith
  linarith [mul_le_mul_of_nonneg_left hub hcoef]

/-- **Лучшая пара в любом непустом семействе подмножеств существует.** -/
theorem exists_best_set_of_family [Nonempty κ]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {Fam : Finset (Finset ι)} (hne : Fam.Nonempty) :
    ∃ R₀ ∈ Fam, ∃ w₀ : ι → ℝ,
      (∀ i ∈ R₀, 0 ≤ w₀ i) ∧
      ∀ R ∈ Fam, ∀ w : ι → ℝ, (∀ i ∈ R, 0 ≤ w i) →
        objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀ := by
  classical
  have hval : ∀ R : Finset ι, ∃ z : ℝ,
      IsGreatest {v : ℝ | ∃ w : ι → ℝ, (∀ i ∈ R, 0 ≤ w i) ∧ v = objLO m d B Sf R w} z := by
    intro R
    obtain ⟨z, _, hz⟩ := isGreatest_objLO_isLeast_QLO (m := m) (B := B) (Sf := Sf) (P := P)
      (G := G) hd hG hPS R
    exact ⟨z, hz⟩
  choose val hvalG using hval
  obtain ⟨R₀, hR₀, hmax⟩ := Finset.exists_max_image _ val hne
  obtain ⟨w₀, hw₀, hw₀v⟩ := (hvalG R₀).1
  refine ⟨R₀, hR₀, w₀, hw₀, fun R hR w hw => ?_⟩
  rw [← hw₀v]
  exact le_trans ((hvalG R).2 ⟨w, hw, rfl⟩) (hmax R hR)

/-- **Главная теорема, из данных задачи (динамика без матрицы Грама).**

Пусть `V = diag(d) + BΣ_fB'`, `d > 0`, `G'G = Σ_f⁻¹`, `K ≥ 1`, `k ≥ 1`, `0 < ε < 1/2`,
`ω ≥ B_i'Σ_fB_i/d_i` для каждого актива, `L = max_i (m_i)_+²/V_ii > 0`,
`J = ⌈log₂ k(1+ω)⌉`. Для любого порядка активов `La` семейство `clipCandidates` обладает
свойствами: (1) размер не больше `(J+1)(2Z+1)^K((2Q+1)^K(k+1)+1)` — число не зависит от
числа активов; (2) у каждого члена не больше `k` активов; (3) лучшая пара существует;
(4) для любой лучшей пары полностью инвестированный портфель `x = w₀/Σw₀` имеет не больше
`k` имён и коэффициент Шарпа не меньше `√(1−2ε)` от коэффициента Шарпа **любого** long-only
портфеля с не более чем `k` именами и положительной ожидаемой доходностью. -/
theorem main_theorem_clipped [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω L : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    (hL0 : 0 < L) (hL : ∀ i, max (m i) 0 ^ 2 / Vmat d B Sf i i ≤ L)
    (hLatt : ∃ i, max (m i) 0 ^ 2 / Vmat d B Sf i i = L)
    {J : ℕ} (hJ : J = ⌈Real.logb 2 ((k : ℝ) * (1 + ω))⌉₊)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La) :
    (clipCandidates m d B Sf G ε ω L J k La).card
        ≤ (J + 1) * ((2 * clipZ ε ω k (Fintype.card κ) + 1) ^ Fintype.card κ
          * ((2 * clipQ ε ω k (Fintype.card κ) + 1) ^ Fintype.card κ * (k + 1) + 1))
    ∧ (∀ R ∈ clipCandidates m d B Sf G ε ω L J k La, R.card ≤ k)
    ∧ (∃ R₀ ∈ clipCandidates m d B Sf G ε ω L J k La, ∃ w₀ : ι → ℝ,
        (∀ i ∈ R₀, 0 ≤ w₀ i) ∧
        ∀ R ∈ clipCandidates m d B Sf G ε ω L J k La, ∀ w : ι → ℝ,
          (∀ i ∈ R, 0 ≤ w i) → objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀)
    ∧ ∀ R₀ ∈ clipCandidates m d B Sf G ε ω L J k La, ∀ w₀ : ι → ℝ,
        (∀ i ∈ R₀, 0 ≤ w₀ i) →
        (∀ R ∈ clipCandidates m d B Sf G ε ω L J k La, ∀ w : ι → ℝ,
          (∀ i ∈ R, 0 ≤ w i) → objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀) →
        R₀.card ≤ k
        ∧ (∀ i ∈ R₀, 0 ≤ (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i)
        ∧ ∑ i ∈ R₀, (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i = 1
        ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
            0 < pRet m S' u →
            Real.sqrt (1 - 2 * ε) * sharpe m d B Sf S' u
              ≤ sharpe m d B Sf R₀ (fun i => (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i) := by
  have hq1 : (1 : ℝ) ≤ (k : ℝ) * (1 + ω) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    nlinarith
  obtain ⟨hJa, _⟩ := guess_count_spec hq1
  rw [← hJ] at hJa
  obtain ⟨S, hkS, Fopt, hFopt, hSopt⟩ := exists_optimal_support (m := m) (d := d) (B := B)
    (Sf := Sf) (P := P) (G := G) hd hG hPS k
  obtain ⟨R, hR, hRk, w, hw, hobj⟩ := exists_good_clipCandidate (Sf := Sf) (P := P) hd hG hPS
    hk1 hε hε1.le hω hsys hL0 hL hLatt hJa hnd hall hkS hFopt hSopt
  obtain ⟨i₀, hi₀⟩ := hLatt
  have hLF : L ≤ Fopt := hi₀ ▸ opt_ge_single_of_opt (B := B) hd hG hPS hk1 hSopt i₀
  refine ⟨card_clipCandidates_le m d B Sf G ε ω L J k La, fun R hR => card_le_of_mem_clipCandidates hR,
    exists_best_set_of_family (m := m) (d := d) (B := B) (Sf := Sf) (P := P) (G := G) hd hG hPS
      ⟨R, hR⟩, ?_⟩
  intro R₀ hR₀ w₀ hw₀ hbest
  have hval : (1 - 2 * ε) * Fopt ≤ objLO m d B Sf R₀ w₀ :=
    le_trans hobj (hbest R hR w (fun i _ => hw i))
  obtain ⟨hx0, hx1, hxs⟩ := best_pair_sharpe_uniform (B := B) hd hG hPS hε1
    (lt_of_lt_of_le hL0 hLF) hSopt hw₀ hval
  refine ⟨card_le_of_mem_clipCandidates hR₀, hx0, hx1, fun S' hS' u hu hru => ?_⟩
  exact hxs S' hS' u hu hru

/-! ### Непустота

Одноактивный инстанс `trading_instance`: `m = d = 1`, `B = 0`, `Σ_f = G = P = 1`, `k = 1`,
`ε = 1/4`, `ω = 0`, `L = 1`, `J = 0`, порядок `[0]`. Все гипотезы `main_theorem_clipped`
выполнены, заключение даёт полностью инвестированный портфель с коэффициентом Шарпа
не меньше `√(1/2)`. -/

theorem clipped_instance :
    ∃ R₀ ∈ clipCandidates (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1) (fun _ (_ : Unit) => 0)
        (fun _ _ => 1) (fun _ _ => 1) (1/4) 0 1 0 1 [0],
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
  have hVd : ∀ i, Vmat d B Sf i i = 1 := by intro i; simp [Vmat, d, B]
  have hL : ∀ i, max (m i) 0 ^ 2 / Vmat d B Sf i i ≤ 1 := by intro i; simp [hVd, m]
  have hLatt : ∃ i, max (m i) 0 ^ 2 / Vmat d B Sf i i = 1 := ⟨0, by simp [hVd, m]⟩
  have hJlog : (0:ℕ) = ⌈Real.logb 2 (((1:ℕ) : ℝ) * (1 + 0))⌉₊ := by simp
  have hnd : ([0] : List (Fin 1)).Nodup := List.nodup_singleton 0
  have hall : ∀ i : Fin 1, i ∈ ([0] : List (Fin 1)) := by
    intro i; rw [List.mem_singleton]; exact Subsingleton.elim _ _
  have hsu : sharpe m d B Sf Finset.univ (fun _ => 1) = 1 := by
    simp [sharpe, pRet, pVar, Vmat, m, d, B]
  have hcard : (Finset.univ : Finset (Fin 1)).card ≤ 1 := by simp
  have hw1 : ∀ i ∈ (Finset.univ : Finset (Fin 1)), (0:ℝ) ≤ (fun _ => (1:ℝ)) i :=
    fun _ _ => zero_le_one
  obtain ⟨_, _, ⟨R₀, hR₀, w₀, hw₀, hbest⟩, h4⟩ := main_theorem_clipped (G := G) (P := P)
    (Sf := Sf) hd hG hPS le_rfl (by norm_num : (0:ℝ) < 1/4) (by norm_num) le_rfl hsys
    one_pos hL hLatt hJlog hnd hall
  obtain ⟨_, hx0, hx1, hxsh⟩ := h4 R₀ hR₀ w₀ hw₀ hbest
  have hsh := hxsh Finset.univ hcard (fun _ => 1) hw1 (by simp [pRet, m])
  refine ⟨R₀, hR₀, _, hx0, hx1, ?_⟩
  rw [hsu, mul_one] at hsh
  exact hsh

/-! ### Полиномиальная форма оценки размера

С `q = k(1+ω)` и `J = ⌈log₂ q⌉` (`q ≤ 2^J ≤ 2q`): размер семейства не больше
`8·(60K)^K·ε^{-K}·q^{3K+2}` — полином от `k`, `1+ω`, `1/ε` степени `3K+2`, **без `M`**. -/

lemma two_Z_le {k K : ℕ} (hk : 1 ≤ k) (hK : 1 ≤ K) {ε ω : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hω : 0 ≤ ω) :
    (2 * (clipZ ε ω k K : ℝ) + 1) ≤ 6 * ((k : ℝ) * (1 + ω)) * Real.sqrt ((K : ℝ) / ε) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hx1 : 1 ≤ Real.sqrt ((K : ℝ) / ε) := by
    rw [Real.one_le_sqrt]
    rw [le_div_iff₀ hε]; linarith
  have hq1 : 1 ≤ (k : ℝ) * (1 + ω) := by nlinarith
  have hνq : 1 + (k : ℝ) * ω ≤ (k : ℝ) * (1 + ω) := by nlinarith
  have hceil : (clipZ ε ω k K : ℝ) ≤ (1 + (k : ℝ) * ω) * Real.sqrt ((K : ℝ) / ε) + 1 / 2 + 1 := by
    have := Nat.ceil_lt_add_one (a := (1 + (k : ℝ) * ω) * Real.sqrt ((K : ℝ) / ε) + 1 / 2)
      (by positivity)
    rw [clipZ]; linarith
  set x := Real.sqrt ((K : ℝ) / ε)
  have h1 : (1 + (k : ℝ) * ω) * x ≤ (k : ℝ) * (1 + ω) * x :=
    mul_le_mul_of_nonneg_right hνq (by linarith)
  have h2 : (1 : ℝ) ≤ (k : ℝ) * (1 + ω) * x := by nlinarith
  linarith

lemma two_Q_le {k K : ℕ} (hk : 1 ≤ k) (hK : 1 ≤ K) {ε ω : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hω : 0 ≤ ω) :
    (2 * (clipQ ε ω k K : ℝ) + 1)
      ≤ 10 * ((k : ℝ) * (1 + ω)) ^ 2 * Real.sqrt ((K : ℝ) / ε) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hx1 : 1 ≤ Real.sqrt ((K : ℝ) / ε) := by
    rw [Real.one_le_sqrt]
    rw [le_div_iff₀ hε]; linarith
  set x := Real.sqrt ((K : ℝ) / ε) with hx
  have hx2 : x ^ 2 = (K : ℝ) / ε := Real.sq_sqrt (by positivity)
  set q := (k : ℝ) * (1 + ω) with hq
  have hq1 : 1 ≤ q := by rw [hq]; nlinarith
  have hkq : (k : ℝ) ≤ q := by rw [hq]; nlinarith
  set y := Real.sqrt (5 * ω * (k : ℝ) ^ 3 * K / ε) with hy
  -- `ω k³ ≤ q³`
  have hωk : ω * (k : ℝ) ^ 3 ≤ q ^ 3 := by
    rw [hq, mul_pow]
    have : ω ≤ (1 + ω) ^ 3 := by nlinarith [sq_nonneg ω, mul_nonneg hω (sq_nonneg ω)]
    nlinarith [pow_pos (show (0 : ℝ) < k by linarith) 3]
  have hy2 : y ^ 2 ≤ (Real.sqrt 5 * q ^ 2 * x) ^ 2 := by
    rw [hy, Real.sq_sqrt (by positivity), mul_pow, mul_pow, Real.sq_sqrt (by norm_num), hx2]
    have h1 : 5 * ω * (k : ℝ) ^ 3 * K / ε = 5 * (ω * (k : ℝ) ^ 3) * ((K : ℝ) / ε) := by ring
    rw [h1]
    have h2 : ω * (k : ℝ) ^ 3 ≤ q ^ 4 := by
      have : q ^ 3 ≤ q ^ 4 := pow_le_pow_right₀ hq1 (by norm_num)
      linarith
    have h3 : 0 ≤ (K : ℝ) / ε := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h2 h3]
  have hy1 : y ≤ Real.sqrt 5 * q ^ 2 * x := by
    have h0 : 0 ≤ Real.sqrt 5 * q ^ 2 * x := by positivity
    exact abs_le_of_sq_le_sq' hy2 h0 |>.2
  have hs5 : Real.sqrt 5 ≤ 9 / 4 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hy3 : y ≤ 9 / 4 * q ^ 2 * x := by
    have : Real.sqrt 5 * q ^ 2 * x ≤ 9 / 4 * q ^ 2 * x := by
      have hq2x : 0 ≤ q ^ 2 * x := by positivity
      nlinarith
    linarith
  have hceil : (clipQ ε ω k K : ℝ) ≤ k + y + 1 := by
    have := Nat.ceil_lt_add_one (a := y) (Real.sqrt_nonneg _)
    rw [clipQ]; push_cast; linarith
  have hqq : q ≤ q ^ 2 * x := by nlinarith
  have h1' : (1 : ℝ) ≤ q ^ 2 * x := by nlinarith
  linarith

/-- **Полиномиальная оценка размера семейства (без `M`).** Для `k ≥ 1`, `0 < ε ≤ 1`, `ω ≥ 0`,
`K ≥ 1` и `2^J ≤ 2k(1+ω)`:

    |clipCandidates| ≤ 8·(60K)^K·ε^{-K}·(k(1+ω))^{3K+2}. -/
theorem card_clipCandidates_poly (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf G : κ → κ → ℝ)
    [Nonempty κ] {k : ℕ} (hk : 1 ≤ k) {ε ω L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hω : 0 ≤ ω)
    {J : ℕ} (hJ : (2 : ℝ) ^ J ≤ 2 * ((k : ℝ) * (1 + ω))) (La : List ι) :
    ((clipCandidates m d B Sf G ε ω L J k La).card : ℝ)
      ≤ 8 * (60 * (Fintype.card κ : ℝ)) ^ Fintype.card κ * (1 / ε) ^ Fintype.card κ
        * ((k : ℝ) * (1 + ω)) ^ (3 * Fintype.card κ + 2) := by
  have hK : 1 ≤ Fintype.card κ := Fintype.card_pos
  set K := Fintype.card κ with hKdef
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set q := (k : ℝ) * (1 + ω) with hq
  have hq1 : 1 ≤ q := by rw [hq]; nlinarith
  set x := Real.sqrt ((K : ℝ) / ε) with hx
  have hx1 : 1 ≤ x := by
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    rw [hx, Real.one_le_sqrt, le_div_iff₀ hε]; linarith
  have hx2 : x ^ 2 = (K : ℝ) / ε := Real.sq_sqrt (by positivity)
  have hZ := two_Z_le (K := K) hk hK hε hε1 hω
  have hQ := two_Q_le (K := K) hk hK hε hε1 hω
  refine le_trans (Nat.cast_le.mpr (card_clipCandidates_le m d B Sf G ε ω L J k La)) ?_
  push_cast
  set Zr : ℝ := 2 * (clipZ ε ω k K : ℝ) + 1 with hZr
  set Qr : ℝ := 2 * (clipQ ε ω k K : ℝ) + 1 with hQr
  have hZ0 : 0 ≤ Zr := by positivity
  have hQ0 : 0 ≤ Qr := by positivity
  have hJ1 : ((J : ℝ) + 1) ≤ 2 * q := by
    have : (J : ℝ) + 1 ≤ 2 ^ J := by
      have h := Nat.lt_two_pow_self (n := J)
      exact_mod_cast Nat.succ_le_of_lt h
    linarith
  have hk1' : ((k : ℝ) + 1) ≤ 2 * q := by
    have : (k : ℝ) ≤ q := by rw [hq]; nlinarith
    linarith
  have hQK : Qr ^ K ≤ (10 * q ^ 2 * x) ^ K := pow_le_pow_left₀ hQ0 hQ K
  have hZK : Zr ^ K ≤ (6 * q * x) ^ K := pow_le_pow_left₀ hZ0 hZ K
  have hbig : 1 ≤ Qr ^ K * ((k : ℝ) + 1) := by
    have hQ1 : 1 ≤ Qr := by rw [hQr]; have : (0 : ℝ) ≤ clipQ ε ω k K := by positivity
                            linarith
    have := one_le_pow₀ hQ1 (n := K)
    nlinarith
  have hinner : Qr ^ K * ((k : ℝ) + 1) + 1 ≤ 2 * ((10 * q ^ 2 * x) ^ K * (2 * q)) := by
    have h1 : Qr ^ K * ((k : ℝ) + 1) ≤ (10 * q ^ 2 * x) ^ K * (2 * q) :=
      mul_le_mul hQK hk1' (by positivity) (by positivity)
    linarith
  have hstep : ((J : ℝ) + 1) * (Zr ^ K * (Qr ^ K * ((k : ℝ) + 1) + 1))
      ≤ (2 * q) * ((6 * q * x) ^ K * (2 * ((10 * q ^ 2 * x) ^ K * (2 * q)))) := by
    apply mul_le_mul hJ1 _ (by positivity) (by positivity)
    exact mul_le_mul hZK hinner (by positivity) (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  -- `8·60^K·K^K·ε^{-K}·q^{3K+2}`
  have hx2K : x ^ K * x ^ K = ((K : ℝ) / ε) ^ K := by
    rw [← mul_pow, ← pow_two, hx2]
  have e1 : (6 * q * x) ^ K = 6 ^ K * q ^ K * x ^ K := by rw [mul_pow, mul_pow]
  have e2 : (10 * q ^ 2 * x) ^ K = 10 ^ K * q ^ (2 * K) * x ^ K := by
    rw [mul_pow, mul_pow, ← pow_mul]
  have e3 : 8 * (60 * (K : ℝ)) ^ K * (1 / ε) ^ K = 8 * 60 ^ K * ((K : ℝ) / ε) ^ K := by
    simp only [div_pow, mul_pow, one_pow]; ring
  rw [e3, ← hx2K, e1, e2]
  have e4 : ((60 : ℝ) ^ K) = 6 ^ K * 10 ^ K := by rw [← mul_pow]; norm_num
  rw [e4]
  have e5 : q ^ (3 * K + 2) = q * q * q ^ K * q ^ (2 * K) := by
    rw [show 3 * K + 2 = 1 + 1 + K + 2 * K by ring, pow_add, pow_add, pow_add, pow_one]
  rw [e5]
  ring

/-- **Полиномиальная оценка с `J = ⌈log₂ k(1+ω)⌉`** (число догадок логарифмично): размер семейства
не больше `8·(60K)^K·ε^{-K}·(k(1+ω))^{3K+2}`; гипотезы — как у `main_theorem_clipped`. -/
theorem card_clipCandidates_poly_of_J [Nonempty κ] {k : ℕ} (hk1 : 1 ≤ k) {ε ω L : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1 / 2) (hω : 0 ≤ ω) {J : ℕ}
    (hJ : J = ⌈Real.logb 2 ((k : ℝ) * (1 + ω))⌉₊) (m d : ι → ℝ) (B : ι → κ → ℝ)
    (Sf G : κ → κ → ℝ) (La : List ι) :
    ((clipCandidates m d B Sf G ε ω L J k La).card : ℝ)
      ≤ 8 * (60 * (Fintype.card κ : ℝ)) ^ Fintype.card κ * (1 / ε) ^ Fintype.card κ
        * ((k : ℝ) * (1 + ω)) ^ (3 * Fintype.card κ + 2) := by
  have hq1 : (1 : ℝ) ≤ (k : ℝ) * (1 + ω) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    nlinarith
  obtain ⟨_, hJb⟩ := guess_count_spec hq1
  rw [← hJ] at hJb
  exact card_clipCandidates_poly m d B Sf G hk1 hε (by linarith) hω hJb La

end SparseSharpe.Factor
