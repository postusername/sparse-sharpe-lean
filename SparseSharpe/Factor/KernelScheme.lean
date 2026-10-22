import SparseSharpe.Factor.Kernel
import SparseSharpe.Factor.UniversalScheme
import SparseSharpe.Factor.RootExists

set_option linter.style.header false

/-!
# Ядро и схема без `ω` (Теорема 5.13) на нём

Схема `univCandidates` (Определение 5.12), построенная по активам ядра `kerK`
(`Factor/Kernel.lean`): семейство `kerCandidates`. Сквозная теорема
`main_theorem_kernel`: размер семейства — как у Теоремы 5.13 с числом активов `|kerK|`
вместо `M`, а `|kerK| ≤ k(1 + 2(K'+1)L(2G+1)^{K'})` (`card_kerK_le`); при одном факторе
(`K' = 0`) это `k(1 + 2L)` — не зависит ни от `M`, ни от `ω`, кроме логарифма `L` числа
классов масштаба. Гарантия — `(1 − 2ε)(1 − 4ε)` от любого long-only портфеля с не более чем
`k` именами.
-/

namespace SparseSharpe.Factor

open Finset

section KernelScheme

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Продолжение весов с подтипа нулём. -/
noncomputable def extW {p : ι → Prop} [DecidablePred p] (w : {i // p i} → ℝ) : ι → ℝ :=
  fun i => if h : p i then w ⟨i, h⟩ else 0

omit [Fintype ι] [DecidableEq κ] in
/-- Цель на подтипе равна цели на образе носителя. -/
lemma objLO_subtype {p : ι → Prop} [DecidablePred p] (m d : ι → ℝ) (B : ι → κ → ℝ)
    (Sf : κ → κ → ℝ) (R : Finset {i // p i}) (w : {i // p i} → ℝ) :
    objLO (fun i => m i.1) (fun i => d i.1) (fun i => B i.1) Sf R w
      = objLO m d B Sf (R.map (Function.Embedding.subtype p)) (extW w) := by
  have hext : ∀ i : {i // p i}, extW w i.1 = w i := fun i => by simp [extW, i.2]
  have hV : ∀ i i' : {i // p i}, Vmat (fun i : {i // p i} => d i.1) (fun i => B i.1) Sf i i'
      = Vmat d B Sf i.1 i'.1 := by
    intro i i'
    simp only [Vmat]
    congr 1
    by_cases h : i = i'
    · subst h; simp
    · have h' : i.1 ≠ i'.1 := fun h'' => h (Subtype.ext h'')
      simp [h, h']
  simp only [objLO, Finset.sum_map, Function.Embedding.coe_subtype, hext, hV]

omit [Fintype ι] [DecidableEq κ] in
/-- Цель зависит только от весов на носителе. -/
lemma objLO_congr_w (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf : κ → κ → ℝ) (S : Finset ι)
    {w w' : ι → ℝ} (h : ∀ i ∈ S, w i = w' i) :
    objLO m d B Sf S w = objLO m d B Sf S w' := by
  simp only [objLO]
  congr 1
  · congr 1; exact Finset.sum_congr rfl fun i hi => by rw [h i hi]
  · exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun i' hi' => by
      rw [h i hi, h i' hi']

variable {K' : ℕ}

/-- **Семейство на ядре**: кандидаты схемы Определения 5.12, построенной по активам ядра. -/
noncomputable def kerCandidates (m d : ι → ℝ) (B : ι → Fin (K' + 1) → ℝ) (k : ℕ) (ε L : ℝ)
    (J : ℕ) (La : List {i // i ∈ kerK m d B k ε}) : Finset (Finset ι) :=
  (univCandidates (fun i : {i // i ∈ kerK m d B k ε} => m i.1) (fun i => d i.1)
      (fun i => B i.1) (opI (Fin (K' + 1))) k ε L J La).image
    (fun R => R.map (Function.Embedding.subtype _))

/-- **Сквозная теорема: ядро и схема без `ω`.** Для `Σ_f = I` (после замены факторов
`B ← BG⁻¹`), `d > 0`, `k ≥ 1`, `0 < ε ≤ 1/4`, значения `L > 0` одного актива ядра и
`J = ⌈log₂(Σ_{i∈ядро}(m_i)_+²/(d_iL))⌉`:
(i) размер семейства — как в Теореме 5.13 с `|kerK|` активами; (ii) каждый кандидат лежит в
ядре и имеет не более `k` имён; (iii) в семействе есть пара с целью не меньше
`(1 − 2ε)(1 − 4ε)` цели любого long-only портфеля с не более чем `k` именами, и этим же
свойством обладает любая лучшая пара семейства. -/
theorem main_theorem_kernel {m d : ι → ℝ} (hd : ∀ i, 0 < d i) (B : ι → Fin (K' + 1) → ℝ)
    {k : ℕ} (hk : 1 ≤ k) {ε L : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hL0 : 0 < L)
    (hLatt : ∃ i ∈ kerK m d B k ε, max (m i) 0 ^ 2 / Vmat d B (opI (Fin (K' + 1))) i i = L)
    {J : ℕ} (hJ : J = ⌈Real.logb 2
      ((∑ i ∈ kerK m d B k ε, max (m i) 0 ^ 2 / d i) / L)⌉₊)
    {La : List {i // i ∈ kerK m d B k ε}} (hnd : La.Nodup) (hall : ∀ i, i ∈ La) :
    (kerCandidates m d B k ε L J La).card
        ≤ (J + 1) * (((kerK m d B k ε).card + (K' + 1)) ^ (K' + 1)
          * (((kerK m d B k ε).card + (K' + 1)) ^ (K' + 1)
            * (((kerK m d B k ε).card + 1) ^ (K' + 1 + 1)
              * ((2 * univZ (Fin (K' + 1)) k ε + 1) ^ (K' + 1)
                * (univBoxBound (Fin (K' + 1)) k ε + 1)))))
    ∧ (∀ W ∈ kerCandidates m d B k ε L J La, W ⊆ kerK m d B k ε ∧ W.card ≤ k)
    ∧ (∃ R₀ ∈ kerCandidates m d B k ε L J La, ∃ w₀ : ι → ℝ, (∀ i ∈ R₀, 0 ≤ w₀ i) ∧
        ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
          (1 - 2 * ε) * (1 - 4 * ε) * objLO m d B (opI (Fin (K' + 1))) S' u
            ≤ objLO m d B (opI (Fin (K' + 1))) R₀ w₀)
    ∧ ∀ R₀ ∈ kerCandidates m d B k ε L J La, ∀ w₀ : ι → ℝ, (∀ i ∈ R₀, 0 ≤ w₀ i) →
        (∀ R ∈ kerCandidates m d B k ε L J La, ∀ w : ι → ℝ, (∀ i ∈ R, 0 ≤ w i) →
          objLO m d B (opI (Fin (K' + 1))) R w ≤ objLO m d B (opI (Fin (K' + 1))) R₀ w₀) →
        ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
          (1 - 2 * ε) * (1 - 4 * ε) * objLO m d B (opI (Fin (K' + 1))) S' u
            ≤ objLO m d B (opI (Fin (K' + 1))) R₀ w₀ := by
  -- данные на подтипе
  have hd' : ∀ i : {i // i ∈ (kerK m d B k ε)}, 0 < d i.1 := fun i => hd i.1
  have hLatt' : ∃ i : {i // i ∈ (kerK m d B k ε)}, max (m i.1) 0 ^ 2
      / Vmat (fun i : {i // i ∈ (kerK m d B k ε)} => d i.1) (fun i => B i.1)
        (opI (Fin (K' + 1))) i i = L := by
    obtain ⟨i, hi, hL⟩ := hLatt
    exact ⟨⟨i, hi⟩, by simpa [Vmat] using hL⟩
  have hJ' : J = ⌈Real.logb 2
      ((∑ i : {i // i ∈ (kerK m d B k ε)}, max (m i.1) 0 ^ 2 / d i.1) / L)⌉₊ := by
    rw [hJ, Finset.sum_coe_sort (kerK m d B k ε) (fun i => max (m i) 0 ^ 2 / d i)]
  have hε1 : 2 * ε < 1 := by linarith
  obtain ⟨hcard, hk', ⟨R₀', hR₀', w₀', hw₀', hbest'⟩, hall4⟩ :=
    main_theorem_univ (m := fun i : {i // i ∈ (kerK m d B k ε)} => m i.1) (d := fun i => d i.1)
      (B := fun i => B i.1) (Sf := opI (Fin (K' + 1))) (P := opI (Fin (K' + 1)))
      (G := opI (Fin (K' + 1))) hd' (opI_hG _) (opI_hPS _) hk hε hε1 hL0 hLatt' hJ' hnd hall
  -- гарантия для пары из подтипа
  have hguar : ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
      (1 - 2 * ε) * (1 - 4 * ε) * objLO m d B (opI (Fin (K' + 1))) S' u
        ≤ objLO m d B (opI (Fin (K' + 1))) (R₀'.map (Function.Embedding.subtype _))
          (extW w₀') := by
    intro S' hS' u hu
    obtain ⟨U', hU'K, hU'card, w', hw', hval⟩ := kernel_value hd B hk hε hε4 hS' hu
    -- перенос `(U', w')` на подтип
    set S'' : Finset {i // i ∈ (kerK m d B k ε)} := U'.subtype (· ∈ (kerK m d B k ε)) with hS''
    have hmap : S''.map (Function.Embedding.subtype _) = U' := by
      rw [hS'', Finset.subtype_map]
      exact Finset.filter_true_of_mem fun x hx => hU'K hx
    have hS''card : S''.card ≤ k := by
      rw [← Finset.card_map (Function.Embedding.subtype _), hmap]; omega
    have hval' : objLO (fun i : {i // i ∈ (kerK m d B k ε)} => m i.1) (fun i => d i.1)
        (fun i => B i.1)
        (opI (Fin (K' + 1))) S'' (fun i => w' i.1) = objLO m d B (opI (Fin (K' + 1))) U' w' := by
      rw [objLO_subtype, hmap]
      refine objLO_congr_w _ _ _ _ _ fun i hi => ?_
      simp [extW, hU'K hi]
    obtain ⟨-, hge, -⟩ := hall4 R₀' hR₀' w₀' hw₀' hbest'
    have h1 := hge S'' hS''card (fun i => w' i.1) (fun i hi => by
      have : i.1 ∈ U' := by rw [← hmap]; exact Finset.mem_map_of_mem _ hi
      exact hw' _ this)
    rw [hval', objLO_subtype] at h1
    have h2 : 0 ≤ 1 - 2 * ε := by linarith
    calc (1 - 2 * ε) * (1 - 4 * ε) * objLO m d B (opI (Fin (K' + 1))) S' u
        = (1 - 2 * ε) * ((1 - 4 * ε) * objLO m d B (opI (Fin (K' + 1))) S' u) := by ring
      _ ≤ (1 - 2 * ε) * objLO m d B (opI (Fin (K' + 1))) U' w' :=
          mul_le_mul_of_nonneg_left hval h2
      _ ≤ _ := h1
  have hw₀ext : ∀ i ∈ R₀'.map (Function.Embedding.subtype _), 0 ≤ extW w₀' i := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    have : extW w₀' (Function.Embedding.subtype _ j) = w₀' j := by
      simp [extW, j.2]
    rw [this]
    exact hw₀' j hj
  have hR₀mem : R₀'.map (Function.Embedding.subtype _) ∈ kerCandidates m d B k ε L J La :=
    Finset.mem_image_of_mem _ hR₀'
  refine ⟨?_, ?_, ⟨_, hR₀mem, extW w₀', hw₀ext, hguar⟩, ?_⟩
  · refine (Finset.card_image_le).trans ?_
    have := hcard
    simp only [Fintype.card_coe, Fintype.card_fin] at this
    exact this
  · intro W hW
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hW
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hx; exact j.2
    · rw [Finset.card_map]; exact hk' R hR
  · intro R₀ _ w₀ _ hbest S' hS' u hu
    exact (hguar S' hS' u hu).trans (hbest _ hR₀mem _ hw₀ext)

/-! ### Пример: ядро отбрасывает актив, теорема применима

Один фактор, `Σ_f = I`, два актива с `B_i = 1`, `d_i = 1`, `m = (1, 2)`; `k = 1`, `ε = 1/8`.
Оба актива в одной ячейке (знак `+`, класс масштаба `0`), счёт `m_i`, и ядро — `{1}`
(`kerK_ex`). Теорема даёт кандидата с целью не меньше `(3/4)(1/2)·2 = 3/4`, где `2` — цель
актива `1` с весом `1`. -/

/-- Данные примера. -/
noncomputable def kexM : Fin 2 → ℝ := ![1, 2]
noncomputable def kexD : Fin 2 → ℝ := fun _ => 1
noncomputable def kexB : Fin 2 → Fin 1 → ℝ := fun _ _ => 1

lemma krho_ex (i : Fin 2) : krho kexD kexB i = 1 := by
  simp [krho, krow, kexB, kexD]

lemma kcell_ex (i : Fin 2) :
    kcell kexD kexB 1 (1 / 8) i = kcell kexD kexB 1 (1 / 8) 0 := by
  have h1 : ∀ j, kcell kexD kexB 1 (1 / 8) j
      = some (0, true, 0, fun x => Fin.elim0 x) := by
    intro j
    simp only [kcell, krho_ex, one_ne_zero, ite_false, Option.some.injEq, Prod.mk.injEq]
    refine ⟨Fin.fin_one_eq_zero _, ?_, ?_, funext fun x => Fin.elim0 x⟩
    · simp [ksgn, krow, kexB, kexD]
    · simp [kcls]
  rw [h1, h1]

lemma kscore_ex (i : Fin 2) : kscore kexM kexD kexB i = kexM i := by
  simp [kscore, krho_ex, ky, kexD]

lemma kerK_ex : kerK kexM kexD kexB 1 (1 / 8) = {1} := by
  have hkey : kkey kexM kexD kexB 0 < kkey kexM kexD kexB 1 := by
    simp only [kkey]
    apply (Prod.Lex.toLex_lt_toLex).mpr
    left
    rw [kscore_ex, kscore_ex]; simp [kexM]
  ext i
  simp only [kerK, mem_topK, Finset.mem_singleton]
  fin_cases i
  · -- над активом `0` стоит актив `1`
    simp only [Fin.zero_eta, Fin.isValue, zero_ne_one, iff_false, not_lt]
    apply Finset.card_pos.mpr
    exact ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, kcell_ex 1, hkey⟩⟩
  · -- над активом `1` никого
    simp only [Fin.mk_one, Fin.isValue, iff_true]
    have : aboveK (kcell kexD kexB 1 (1 / 8)) (kkey kexM kexD kexB) 1 = ∅ := by
      ext x
      simp only [aboveK, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_and, not_lt]
      intro _
      fin_cases x
      · exact hkey.le
      · exact le_rfl
    rw [this, Finset.card_empty]; exact Nat.one_pos

theorem kernel_instance :
    ∃ R₀ ∈ kerCandidates kexM kexD kexB 1 (1 / 8) 2 1
        [⟨1, by rw [kerK_ex]; exact Finset.mem_singleton_self 1⟩],
      ∃ w₀ : Fin 2 → ℝ, (∀ i ∈ R₀, 0 ≤ w₀ i) ∧
        (3 / 4 : ℝ) ≤ objLO kexM kexD kexB (opI (Fin (0 + 1))) R₀ w₀ := by
  have hd : ∀ i, 0 < kexD i := fun _ => one_pos
  have hmem1 : (1 : Fin 2) ∈ kerK kexM kexD kexB 1 (1 / 8) := by
    rw [kerK_ex]; exact Finset.mem_singleton_self 1
  have hV : Vmat kexD kexB (opI (Fin (0 + 1))) 1 1 = 2 := by
    simp [Vmat, kexD, kexB, opI]; norm_num
  have hLatt : ∃ i ∈ kerK kexM kexD kexB 1 (1 / 8),
      max (kexM i) 0 ^ 2 / Vmat kexD kexB (opI (Fin (0 + 1))) i i = 2 :=
    ⟨1, hmem1, by rw [hV]; simp [kexM]; norm_num⟩
  have hJ : (1 : ℕ) = ⌈Real.logb 2
      ((∑ i ∈ kerK kexM kexD kexB 1 (1 / 8), max (kexM i) 0 ^ 2 / kexD i) / 2)⌉₊ := by
    rw [kerK_ex, Finset.sum_singleton]
    simp [kexM, kexD]
    norm_num
  set La : List {i // i ∈ kerK kexM kexD kexB 1 (1 / 8)} := [⟨1, hmem1⟩] with hLa
  have hnd : La.Nodup := by simp [hLa]
  have hall : ∀ i, i ∈ La := by
    intro i
    have h : i.1 ∈ ({1} : Finset (Fin 2)) := by rw [← kerK_ex]; exact i.2
    have : i.1 = 1 := Finset.mem_singleton.mp h
    simp only [hLa, List.mem_singleton]
    exact Subtype.ext this
  obtain ⟨-, -, ⟨R₀, hR₀, w₀, hw₀, hg⟩, -⟩ := main_theorem_kernel (K' := 0) hd kexB
    (k := 1) le_rfl (ε := 1 / 8) (by norm_num) (by norm_num) (by norm_num : (0:ℝ) < 2)
    hLatt hJ hnd hall
  refine ⟨R₀, hR₀, w₀, hw₀, ?_⟩
  have h1 := hg {1} (by simp) (fun _ => 1) (fun _ _ => zero_le_one)
  have h2 : objLO kexM kexD kexB (opI (Fin (0 + 1))) {1} (fun _ => 1) = 2 := by
    simp [objLO, Vmat, kexM, kexD, kexB, opI]; norm_num
  rw [h2] at h1
  linarith

end KernelScheme

section FactorChange

variable {ι : Type*} [DecidableEq ι] {κ κ' : Type*} [Fintype κ] [Fintype κ'] [DecidableEq κ']

/-- **Замена переменных `Σ_f → I`.** Если `Σ_l F_{jl} F_{j'l} = (Σ_f)_{jj'}` (то есть
`FFᵀ = Σ_f`), то цель с нагрузками `B` и ковариацией факторов `Σ_f` равна цели с нагрузками `BF`
и `Σ_f = I`; так Теоремы 5.17–5.18, сформулированные при `Σ_f = I`, применяются к любой `Σ_f`. -/
theorem objLO_factor (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf : κ → κ → ℝ) (F : κ → κ' → ℝ)
    (hF : ∀ j j', ∑ l, F j l * F j' l = Sf j j') (S : Finset ι) (w : ι → ℝ) :
    objLO m d B Sf S w = objLO m d (fun i l => ∑ j, B i j * F j l) (opI κ') S w := by
  have hV : ∀ i i', Vmat d B Sf i i'
      = Vmat d (fun i l => ∑ j, B i j * F j l) (opI κ') i i' := by
    intro i i'
    simp only [Vmat]
    rw [sum_opI_mul]
    congr 1
    have e1 : ∀ j j', B i j * (Sf j j' * B i' j') = ∑ l, B i j * F j l * (B i' j' * F j' l) := by
      intro j j'
      rw [← hF j j', Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    simp_rw [e1, Finset.sum_mul_sum]
    calc ∑ j, ∑ j', ∑ l, B i j * F j l * (B i' j' * F j' l)
        = ∑ j, ∑ l, ∑ j', B i j * F j l * (B i' j' * F j' l) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ l, ∑ j, ∑ j', B i j * F j l * (B i' j' * F j' l) := Finset.sum_comm
  simp only [objLO, hV]

omit [DecidableEq ι] in
/-- Такое `F` есть у любой положительно полуопределённой `Σ_f`. -/
theorem exists_factor_root (Sf : κ → κ → ℝ) (hSf : (Matrix.of Sf).PosSemidef) :
    ∃ F : κ → κ → ℝ, ∀ j j', ∑ l, F j l * F j' l = Sf j j' := by
  classical
  obtain ⟨G, hG⟩ := exists_root_of_posSemidef (Matrix.of Sf) hSf
  refine ⟨fun j l => G l j, fun j j' => ?_⟩
  have := congrFun (congrFun hG j) j'
  simpa [Matrix.mul_apply] using this

end FactorChange

end SparseSharpe.Factor
