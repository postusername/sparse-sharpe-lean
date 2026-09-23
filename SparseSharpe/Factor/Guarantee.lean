import SparseSharpe.Factor.Duality
import SparseSharpe.Factor.DPRun

set_option linter.style.header false

/-!
# Сквозная гарантия в языке задачи

`lo_fptas` (`Factor/DPRun.lean`) сформулирована в строковой записи: вывод —
набор строк `R ⊆ ι ⊕ κ` и неравенство про `psiC`. Практику нужен другой
язык: носитель активов `|R| ≤ k`, портфель `w ≥ 0` и неравенство про
`2m'w − w'Vw`. Здесь перевод сделан.

Три технических моста:

* `barK_assetsOf` — всякий набор динамики имеет вид `barK R₀` («носитель плюс
  якоря»), потому что якоря входят в `base`, а список обрабатываемых строк
  состоит из активов. Поэтому `assetsOf R` — настоящий носитель, и
  `|R| = |assetsOf R| + K`.
* `isGreatest_objLO_phi_of_selfconsistent` — на самосогласованном носителе
  незажатое значение `φ` (то, что считает ключ динамики) совпадает с
  портфельным максимумом.
* `exists_optimal_selfconsistent` — Теорема X в языке задачи: long-only
  оптимум **любого** носителя достигается на самосогласованном подносителе
  с незажатым значением.

Итог — `lo_fptas_portfolio`: в сетке есть узел, в котором динамика возвращает
носитель нужной мощности, а обрезанный вес на нём даёт
`2m'w − w'Vw ≥ (1−2ε)·OPT_LO`. Портфель выписан явно.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-! ### Носитель набора строк -/

/-- Активы набора строк: `assetsOf R = {i : a_i ∈ R}`. -/
noncomputable def assetsOf (R : Finset (ι ⊕ κ)) : Finset ι :=
  Finset.univ.filter (fun i => (Sum.inl i : ι ⊕ κ) ∈ R)

lemma mem_assetsOf {R : Finset (ι ⊕ κ)} {i : ι} :
    i ∈ assetsOf (κ := κ) R ↔ (Sum.inl i : ι ⊕ κ) ∈ R := by
  simp [assetsOf]

/-- Набор строк, содержащий все якоря, — это «носитель плюс якоря». -/
lemma barK_assetsOf {R : Finset (ι ⊕ κ)} (hb : anchorRows ι κ ⊆ R) :
    R = barK (assetsOf (κ := κ) R) := by
  ext x
  rcases x with i | l
  · simp [barK, Finset.inl_mem_disjSum, mem_assetsOf]
  · simp only [barK, Finset.inr_mem_disjSum, Finset.mem_univ, iff_true]
    exact hb (inr_mem_anchorRows l)

@[simp] lemma assetsOf_barK (S : Finset ι) : assetsOf (κ := κ) (barK (κ := κ) S) = S := by
  ext i; simp [mem_assetsOf, barK, Finset.inl_mem_disjSum]

lemma card_barK (S : Finset ι) :
    (barK (κ := κ) S).card = S.card + Fintype.card κ := by
  simp [barK, Finset.card_disjSum]

/-- Мощность набора динамики переводится в мощность носителя. -/
lemma card_assetsOf_eq {R A : Finset (ι ⊕ κ)} (hR : anchorRows ι κ ⊆ R)
    (hA : anchorRows ι κ ⊆ A) (h : R.card = A.card) :
    (assetsOf (κ := κ) R).card = (assetsOf (κ := κ) A).card := by
  have h1 := congrArg Finset.card (barK_assetsOf hR)
  have h2 := congrArg Finset.card (barK_assetsOf hA)
  rw [card_barK] at h1 h2
  omega

/-! ### На самосогласованном носителе `φ` — это портфельный максимум -/

/-- Если носитель самосогласован в своей неподвижной точке, то незажатое
значение `φ_{Ā}(t̂)` — то самое, которое хранит ключ динамики, — равно
`max{2m'w − w'Vw : w ≥ 0}` на этом носителе. -/
theorem isGreatest_objLO_phi_of_selfconsistent [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {A₀ : Finset ι} {th : κ → ℝ}
    (hnormal : IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) th)
    (hself : ∀ x ∈ barK (κ := κ) A₀, (Sum.isLeft x) →
      0 ≤ targetsK m d x - dotp (rowsK d B G x) th) :
    IsGreatest {v : ℝ | ∃ w : ι → ℝ, (∀ i ∈ A₀, 0 ≤ w i) ∧ v = objLO m d B Sf A₀ w}
      (phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) th) := by
  obtain ⟨t₀, hleast, hgreat⟩ :=
    isGreatest_objLO_psiC (Sf := Sf) (P := P) (G := G) hd hG hPS A₀
  have hleast' := isLeast_psiC_of_selfconsistent (a := rowsK d B G) (y := targetsK m d)
    (cl := fun r => r.isLeft) (S := barK (κ := κ) A₀) hnormal hself
  have : phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) th
      = psiC (rowsK d B G) (targetsK m d) (fun r => r.isLeft) (barK (κ := κ) A₀) t₀ :=
    le_antisymm (hleast'.2 hleast.1) (hleast.2 hleast'.1)
  rw [this]
  exact hgreat

/-! ### Теорема X в языке задачи -/

/-- **Long-only оптимум носителя достигается на самосогласованном подносителе,
и там он равен незажатому значению.** Это Теорема X, переписанная так, что обе
части — величины задачи, а не строковой записи. -/
theorem exists_optimal_selfconsistent [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (S : Finset ι) :
    ∃ A₀ ⊆ S, ∃ th : κ → ℝ,
      A₀.card ≤ S.card
      ∧ IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) th
      ∧ (∀ x ∈ barK (κ := κ) A₀, (Sum.isLeft x) →
          0 ≤ targetsK m d x - dotp (rowsK d B G x) th)
      ∧ IsGreatest {v : ℝ | ∃ w : ι → ℝ, (∀ i ∈ S, 0 ≤ w i) ∧ v = objLO m d B Sf S w}
          (phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) th) := by
  obtain ⟨A, hAS, _hcard, hanchA, th, hnormal, hself, _hleastA, hleastS⟩ :=
    exists_selfconsistent_subset_of_det (a := rowsK d B G) (y := targetsK m d)
      (cl := fun r => r.isLeft) (S := barK (κ := κ) S) (base := anchorRows ι κ)
      (Ta := fun l => (Sum.inr l : ι ⊕ κ))
      (anchorRows_subset_barK S) (fun _ hx => not_isLeft_of_mem_anchorRows hx)
      (fun _ hx => targets_eq_zero_of_mem_anchorRows hx)
      (fun l => inr_mem_anchorRows l)
      (det_anchor_ne_zero (d := d) (B := B) (P := P) (Sf := Sf) hG hPS)
  -- `A` содержит все якоря, значит имеет вид `barK A₀`
  have hbA : anchorRows ι κ ⊆ A := by
    intro x hx
    exact hanchA x (anchorRows_subset_barK S hx) (not_isLeft_of_mem_anchorRows hx)
  have hAeq : A = barK (assetsOf (κ := κ) A) := barK_assetsOf hbA
  set A₀ := assetsOf (κ := κ) A with hA₀
  have hA₀S : A₀ ⊆ S := by
    intro i hi
    have : (Sum.inl i : ι ⊕ κ) ∈ A := mem_assetsOf.mp hi
    have := hAS this
    simpa [barK, Finset.inl_mem_disjSum] using this
  refine ⟨A₀, hA₀S, th, Finset.card_le_card hA₀S, ?_, ?_, ?_⟩
  · rw [← hAeq]; exact hnormal
  · rw [← hAeq]; exact hself
  · -- `φ_{Ā₀}(th) = min ψ_{S̄} = max objLO` на `S`
    obtain ⟨t₀, hleast₀, hgreat₀⟩ :=
      isGreatest_objLO_psiC (Sf := Sf) (P := P) (G := G) hd hG hPS S
    have heq : phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) th
        = psiC (rowsK d B G) (targetsK m d) (fun r => r.isLeft) (barK (κ := κ) S) t₀ := by
      rw [← hAeq]
      exact le_antisymm (hleastS.2 hleast₀.1) (hleast₀.2 hleastS.1)
    rw [heq]
    exact hgreat₀

/-! ### Сквозная теорема в языке задачи -/

/-- **FPTAS для long-only, в терминах портфеля.**

`cand` — множество активов-кандидатов, `La` — список активов, по которому идёт
динамика, `A₀` — самосогласованный носитель (по `exists_optimal_selfconsistent`
именно такой реализует `OPT_LO`), `T` — его максимально-объёмная `K`-ка.
Калибровка — ровно как в `lo_fptas`.

Вывод: в сетке есть узел, в котором фильтр порога `−θ₀` допускает все активы
`A₀`, динамика возвращает носитель той же мощности, и на нём есть **явный
допустимый портфель** `w ≥ 0` с

    2·m'w − w'Vw  ≥  (1 − 2ε)·(long-only оптимум на `A₀`). -/
theorem lo_fptas_portfolio [Nonempty κ]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {cand A₀ : Finset ι} {La : List ι} {T : κ → (ι ⊕ κ)} {thA : κ → ℝ}
    {η ξ γ ε V C s : ℝ} {n : ℕ}
    (hmax : MaxVol (rowsK d B G) (barK (κ := κ) A₀) T)
    (hdet : (rowMat (rowsK d B G) T).det ≠ 0)
    (hnormA : IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA)
    (hC : ((barK (κ := κ) A₀).card * Fintype.card κ : ℝ) ≤ C) (hCpos : 0 < C)
    (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hV : 0 < V)
    (hVF : V ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA)
    (hFV : phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA ≤ 2 * V)
    (hKc : 0 < (Fintype.card κ : ℝ)) (hn : 0 < n)
    (hnS : 2 * ((barK (κ := κ) cand).card : ℝ) ≤ (n : ℝ))
    (hs : s = 2 * Real.sqrt ((ε ^ 2 * γ / (1024 * (n : ℝ))) * V
      / ((Fintype.card κ : ℝ) * C)))
    (hselfA : ∀ x ∈ barK (κ := κ) A₀, (Sum.isLeft x) →
      0 ≤ targetsK m d x - dotp (rowsK d B G x) thA)
    (hη : 0 < η) (hξ : 0 < ξ)
    (hnd : La.Nodup) (hA₀La : A₀ ⊆ La.toFinset) (hLcand : ∀ i ∈ La, i ∈ cand)
    (hcondS : ∀ v : κ → ℝ, γ * gram (rowsK d B G) (barK (κ := κ) cand) v
      ≤ gram (rowsK d B G) (anchorSet (fun r => Sum.isLeft r) (barK (κ := κ) cand)) v)
    (hA₀cand : A₀ ⊆ cand)
    (hηθ : 8 * (Real.sqrt (Fintype.card κ : ℝ) * ((La.length : ℝ) * η))
      ≤ theta0 ε γ V n)
    (hζ8 : ((La.length : ℝ) * ξ) * (Fintype.card κ : ℝ) ≤ 1/8) :
    ∃ z : κ → ℤ,
      (∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C
        / (2 * (ε ^ 2 * γ / (1024 * (n : ℝ))))) + 1 / 2) ∧
      ∀ t : κ → ℝ, (∀ l, dotp (rowsK d B G (T l)) t
          = targetsK m d (T l) + s * (z l : ℝ)) →
        ∃ adm : (ι ⊕ κ) → Bool,
          (∀ x, adm x → -theta0 ε γ V n
            ≤ targetsK m d x - dotp (rowsK d B G x) t) ∧
          (∀ x ∈ barK (κ := κ) A₀, x ∉ anchorRows ι κ → adm x) ∧
          ∃ R ∈ survivors (fun W => phi (rowsK d B G) (targetsK m d) W t)
              (keyOf (rowsK d B G) (targetsK m d) T t η ξ) adm (anchorRows ι κ)
              (La.map Sum.inl),
            (assetsOf (κ := κ) R).card = A₀.card
            ∧ ∃ w : ι → ℝ, (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i)
              ∧ (1 - 2 * ε) * phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA
                ≤ objLO m d B Sf (assetsOf (κ := κ) R) w := by
  classical
  set a := rowsK d B G with ha
  set y := targetsK m d with hy
  set L : List (ι ⊕ κ) := La.map Sum.inl with hL
  -- список строк-активов: без повторов, не пересекается с якорями, лежит в `barK cand`
  have hndL : L.Nodup := hnd.map (fun _ _ h => by injection h)
  have hdisj : ∀ x ∈ L, x ∉ anchorRows ι κ := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    intro hc
    exact (not_isLeft_of_mem_anchorRows hc) (by simp)
  have hbA : anchorRows ι κ ⊆ barK (κ := κ) A₀ := anchorRows_subset_barK A₀
  have hAL : barK (κ := κ) A₀ ⊆ anchorRows ι κ ∪ L.toFinset := by
    intro x hx
    rcases x with i | l
    · refine Finset.mem_union_right _ ?_
      have hiA : i ∈ A₀ := by simpa [barK, Finset.inl_mem_disjSum] using hx
      refine List.mem_toFinset.mpr ?_
      exact List.mem_map.mpr ⟨i, List.mem_toFinset.mp (hA₀La hiA), rfl⟩
    · exact Finset.mem_union_left _ (inr_mem_anchorRows l)
  have hAS : barK (κ := κ) A₀ ⊆ barK (κ := κ) cand := by
    intro x hx
    rcases x with i | l
    · have : i ∈ A₀ := by simpa [barK, Finset.inl_mem_disjSum] using hx
      simpa [barK, Finset.inl_mem_disjSum] using hA₀cand this
    · exact inr_mem_barK cand l
  have hbaseS : anchorRows ι κ ⊆ barK (κ := κ) cand := anchorRows_subset_barK cand
  have hLS : ∀ x ∈ L.toFinset, x ∈ barK (κ := κ) cand := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    simpa [barK, Finset.inl_mem_disjSum] using hLcand i hi
  have hanch : ∀ x : ι ⊕ κ, ¬ (Sum.isLeft x) → y x = 0 := by
    intro x hx
    rcases x with i | l
    · simp at hx
    · simp [hy, targetsK]
  have hanchBase : anchorSet (fun r : ι ⊕ κ => Sum.isLeft r) (barK (κ := κ) cand)
      ⊆ anchorRows ι κ := by
    intro x hx
    obtain ⟨_, hx2⟩ := Finset.mem_filter.mp hx
    rcases x with i | l
    · simp at hx2
    · exact inr_mem_anchorRows l
  have hbaseAnch : ∀ x ∈ anchorRows ι κ, ¬ (Sum.isLeft x) :=
    fun _ hx => not_isLeft_of_mem_anchorRows hx
  obtain ⟨z, hz1, hz2⟩ := lo_fptas (a := a) (y := y) (cl := fun r => Sum.isLeft r)
    (S := barK (κ := κ) cand) (A := barK (κ := κ) A₀) (base := anchorRows ι κ)
    (T := T) (thA := thA) (η := η) (ξ := ξ) (γ := γ) (ε := ε) (V := V) (C := C) (s := s)
    (n := n) (L := L) (Tb := fun l => (Sum.inr l : ι ⊕ κ))
    hmax hdet hnormA hC hCpos hε hε1 hγ hγ1 hV hVF hFV hKc hn hnS hs hselfA hη hξ
    hndL hdisj hbA hAL hAS hbaseS hLS hanch hanchBase hbaseAnch hcondS
    (fun l => inr_mem_anchorRows l)
    (det_anchor_ne_zero (d := d) (B := B) (P := P) (Sf := Sf) hG hPS)
    (by rwa [hL, List.length_map]) (by rwa [hL, List.length_map])
  refine ⟨z, hz1, fun t ht => ?_⟩
  obtain ⟨adm, hadm1, hadm2, R, hR, hcard, hval⟩ := hz2 t ht
  refine ⟨adm, hadm1, hadm2, R, hR, ?_, ?_⟩
  · have := card_assetsOf_eq (survivors_mem _ _ adm _ L R hR).1 hbA hcard
    rwa [assetsOf_barK] at this
  · -- перевод `psiC` на строках в портфельное значение
    set R₀ := assetsOf (κ := κ) R with hR₀
    have hReq : R = barK (κ := κ) R₀ :=
      barK_assetsOf (survivors_mem _ _ adm _ L R hR).1
    obtain ⟨zv, hleast, hgreat⟩ :=
      isGreatest_objLO_isLeast_QLO (Sf := Sf) (P := P) (G := G) hd hG hPS R₀
    obtain ⟨t₁, ht₁⟩ := hleast.1
    obtain ⟨w, hw, hwv⟩ := hgreat.1
    refine ⟨w, hw, ?_⟩
    rw [← hwv, ht₁, ← QLO_eq_psiC (P := P) hd hG]
    have := hval t₁
    rwa [hReq] at this

/-- **Гарантия относительно настоящего оптимума.**

`hopt` — это вывод `exists_optimal_selfconsistent`: `A₀` реализует long-only
оптимум носителя `S` незажатым значением. Тогда портфель `w`, который алгоритм
строит на возвращённом носителе, не хуже `(1−2ε)`-доли **любого** допустимого
портфеля на `S`:

    ∀ u ≥ 0 на S :   (1−2ε)·(2m'u − u'Vu)  ≤  2m'w − w'Vw .

Носитель при этом не длиннее `S` (`|assetsOf R| = |A₀| ≤ |S|`), то есть
ограничение на число активов соблюдено. -/
theorem lo_fptas_portfolio_opt [Nonempty κ]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {cand Sopt A₀ : Finset ι} {La : List ι} {T : κ → (ι ⊕ κ)} {thA : κ → ℝ}
    {η ξ γ ε V C s : ℝ} {n : ℕ}
    (hopt : IsGreatest {v : ℝ | ∃ u : ι → ℝ, (∀ i ∈ Sopt, 0 ≤ u i)
        ∧ v = objLO m d B Sf Sopt u}
      (phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA))
    (hA₀Sopt : A₀ ⊆ Sopt)
    (hmax : MaxVol (rowsK d B G) (barK (κ := κ) A₀) T)
    (hdet : (rowMat (rowsK d B G) T).det ≠ 0)
    (hnormA : IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA)
    (hC : ((barK (κ := κ) A₀).card * Fintype.card κ : ℝ) ≤ C) (hCpos : 0 < C)
    (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hV : 0 < V)
    (hVF : V ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA)
    (hFV : phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA ≤ 2 * V)
    (hKc : 0 < (Fintype.card κ : ℝ)) (hn : 0 < n)
    (hnS : 2 * ((barK (κ := κ) cand).card : ℝ) ≤ (n : ℝ))
    (hs : s = 2 * Real.sqrt ((ε ^ 2 * γ / (1024 * (n : ℝ))) * V
      / ((Fintype.card κ : ℝ) * C)))
    (hselfA : ∀ x ∈ barK (κ := κ) A₀, (Sum.isLeft x) →
      0 ≤ targetsK m d x - dotp (rowsK d B G x) thA)
    (hη : 0 < η) (hξ : 0 < ξ)
    (hnd : La.Nodup) (hA₀La : A₀ ⊆ La.toFinset) (hLcand : ∀ i ∈ La, i ∈ cand)
    (hcondS : ∀ v : κ → ℝ, γ * gram (rowsK d B G) (barK (κ := κ) cand) v
      ≤ gram (rowsK d B G) (anchorSet (fun r => Sum.isLeft r) (barK (κ := κ) cand)) v)
    (hA₀cand : A₀ ⊆ cand)
    (hηθ : 8 * (Real.sqrt (Fintype.card κ : ℝ) * ((La.length : ℝ) * η))
      ≤ theta0 ε γ V n)
    (hζ8 : ((La.length : ℝ) * ξ) * (Fintype.card κ : ℝ) ≤ 1/8) :
    ∃ z : κ → ℤ,
      (∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C
        / (2 * (ε ^ 2 * γ / (1024 * (n : ℝ))))) + 1 / 2) ∧
      ∀ t : κ → ℝ, (∀ l, dotp (rowsK d B G (T l)) t
          = targetsK m d (T l) + s * (z l : ℝ)) →
        ∃ adm : (ι ⊕ κ) → Bool,
          (∀ x ∈ barK (κ := κ) A₀, x ∉ anchorRows ι κ → adm x) ∧
          ∃ R ∈ survivors (fun W => phi (rowsK d B G) (targetsK m d) W t)
              (keyOf (rowsK d B G) (targetsK m d) T t η ξ) adm (anchorRows ι κ)
              (La.map Sum.inl),
            (assetsOf (κ := κ) R).card ≤ Sopt.card
            ∧ ∃ w : ι → ℝ, (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i)
              ∧ ∀ u : ι → ℝ, (∀ i ∈ Sopt, 0 ≤ u i) →
                  (1 - 2 * ε) * objLO m d B Sf Sopt u
                    ≤ objLO m d B Sf (assetsOf (κ := κ) R) w := by
  obtain ⟨z, hz1, hz2⟩ := lo_fptas_portfolio (P := P) hd hG hPS hmax hdet hnormA hC hCpos
    hε hε1 hγ hγ1 hV hVF hFV hKc hn hnS hs hselfA hη hξ hnd hA₀La hLcand hcondS hA₀cand
    hηθ hζ8
  refine ⟨z, hz1, fun t ht => ?_⟩
  obtain ⟨adm, _hadm1, hadm2, R, hR, hcard, w, hw, hval⟩ := hz2 t ht
  refine ⟨adm, hadm2, R, hR, ?_, w, hw, fun u hu => ?_⟩
  · rw [hcard]; exact Finset.card_le_card hA₀Sopt
  · have hub : objLO m d B Sf Sopt u
        ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA :=
      hopt.2 ⟨u, hu, rfl⟩
    have hcoef : (0:ℝ) ≤ 1 - 2 * ε := by linarith
    have := mul_le_mul_of_nonneg_left hub hcoef
    linarith

/-! ### Непустота калибровки

Главная опасность этой теоремы — не неверная формулировка, а невыполнимая
гипотеза: в §12.3 заметки записан случай, когда калибровка выводилась из
`F(base) = 0` и потому вынуждала `θ₀ = 0`. Поэтому явный инстанс, в котором
`0 < V ≤ F ≤ 2V` выполнено **вместе** с нормальными уравнениями и
самосогласованностью.

`K = 1`, один актив: `m = 1`, `d = 1`, `B = 0`, `Σ_f = Σ_f⁻¹ = G = 1`.
Здесь `φ_{Ā₀}(t) = 1 + t²`, неподвижная точка `t̂ = 0`, `F = 1 > 0`. -/

private def mG : Fin 1 → ℝ := fun _ => 1
private def dG : Fin 1 → ℝ := fun _ => 1
private def BG : Fin 1 → Fin 1 → ℝ := fun _ _ => 0
private def GG : Fin 1 → Fin 1 → ℝ := fun _ _ => 1

example : ∃ (A₀ : Finset (Fin 1)) (th : Fin 1 → ℝ) (V : ℝ),
    0 < V
    ∧ IsNormal (rowsK dG BG GG) (targetsK mG dG) (barK (κ := Fin 1) A₀) th
    ∧ (∀ x ∈ barK (κ := Fin 1) A₀, (Sum.isLeft x) →
        0 ≤ targetsK mG dG x - dotp (rowsK dG BG GG x) th)
    ∧ V ≤ phi (rowsK dG BG GG) (targetsK mG dG) (barK (κ := Fin 1) A₀) th
    ∧ phi (rowsK dG BG GG) (targetsK mG dG) (barK (κ := Fin 1) A₀) th ≤ 2 * V := by
  refine ⟨Finset.univ, fun _ => 0, 1/2, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro v
    simp [mom, barK, Finset.sum_disjSum, rowsK, targetsK, mG, dG, BG, GG, dotp,
      Fin.sum_univ_one]
  · intro x _ hleft
    rcases x with i | l
    · simp [targetsK, rowsK, mG, dG, BG, dotp, Fin.sum_univ_one]
    · exact absurd hleft (by simp)
  · simp only [phi, barK, Finset.sum_disjSum, rowsK, targetsK, mG, dG, BG, GG, dotp,
      Fin.sum_univ_one, Sum.elim_inl, Sum.elim_inr]
    norm_num
  · simp only [phi, barK, Finset.sum_disjSum, rowsK, targetsK, mG, dG, BG, GG, dotp,
      Fin.sum_univ_one, Sum.elim_inl, Sum.elim_inr]
    norm_num

end SparseSharpe.Factor
