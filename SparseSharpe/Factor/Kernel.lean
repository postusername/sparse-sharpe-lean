import SparseSharpe.Factor.Duality
import SparseSharpe.Factor.OnePassLower

set_option linter.style.header false

/-!
# Ядро: в каждой ячейке — `k` лучших активов

Общая часть (`topK`, `card_topK_le`, `exchange_topK`): активы разбиты на ячейки функцией
`cell`, внутри ячейки упорядочены инъективным ключом `key`; ядро `topK` оставляет в каждой
ячейке `k` активов с наибольшим ключом. Если в каждой ячейке актив с большим ключом
доминирует актив с меньшим (`h i ≤ g i'`), то любой носитель из не более чем `k` активов
обменивается на носитель из ядра той же мощности, сумма `g` по которому не меньше суммы `g`
по активам исходного носителя из ядра и суммы `h` по остальным.

Конкретные ячейки и доминирование для факторной модели — ниже (раздел `KernelCells`).
-/

namespace SparseSharpe.Factor

open Finset

section Exchange

variable {ι γ β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq γ] [LinearOrder β]

/-- Активы ячейки `i`, стоящие выше `i`. -/
def aboveK (cell : ι → γ) (key : ι → β) (i : ι) : Finset ι :=
  univ.filter fun i' => cell i' = cell i ∧ key i < key i'

/-- **Ядро**: активы, над которыми в их ячейке меньше `k` активов. -/
def topK (cell : ι → γ) (key : ι → β) (k : ℕ) : Finset ι :=
  univ.filter fun i => (aboveK cell key i).card < k

omit [DecidableEq ι] in
lemma mem_topK {cell : ι → γ} {key : ι → β} {k : ℕ} {i : ι} :
    i ∈ topK cell key k ↔ (aboveK cell key i).card < k := by
  simp [topK]

omit [DecidableEq ι] in
/-- Над активом выше `i` (в той же ячейке) стоит строго меньше активов, чем над `i`. -/
lemma card_aboveK_lt {cell : ι → γ} {key : ι → β} {i i' : ι} (hc : cell i' = cell i)
    (hlt : key i < key i') : (aboveK cell key i').card < (aboveK cell key i).card := by
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [aboveK, mem_filter, mem_univ, true_and] at hx ⊢
    exact ⟨hx.1.trans hc, hlt.trans hx.2⟩
  · have : i' ∈ aboveK cell key i := by simp [aboveK, hc, hlt]
    have h2 := hsub this
    simp [aboveK] at h2

omit [DecidableEq ι] in
/-- **Размер ядра**: не больше `k` активов на ячейку. -/
theorem card_topK_le (cell : ι → γ) (key : ι → β) (hkey : Function.Injective key) (k : ℕ) :
    (topK cell key k).card ≤ k * (univ.image cell).card := by
  classical
  have hcover : topK cell key k
      = (univ.image cell).biUnion fun c => (topK cell key k).filter fun i => cell i = c := by
    ext i; simp
  rw [hcover]
  refine (Finset.card_biUnion_le).trans ?_
  rw [mul_comm]
  refine Finset.sum_le_card_nsmul _ _ _ fun c _ => ?_
  -- инъекция `i ↦ #(выше i)` в `range k`
  have hmaps : ∀ i ∈ (topK cell key k).filter (fun i => cell i = c),
      (aboveK cell key i).card ∈ Finset.range k := by
    intro i hi
    rw [Finset.mem_filter] at hi
    exact Finset.mem_range.mpr (mem_topK.mp hi.1)
  have hinj : Set.InjOn (fun i => (aboveK cell key i).card)
      ((topK cell key k).filter (fun i => cell i = c) : Set ι) := by
    intro i₁ hi₁ i₂ hi₂ heq
    simp only [coe_filter] at hi₁ hi₂
    have hc : cell i₁ = cell i₂ := hi₁.2.trans hi₂.2.symm
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (hkey h)) with hlt | hlt
    · exact absurd heq (ne_of_gt (card_aboveK_lt hc.symm hlt))
    · exact absurd heq (ne_of_lt (card_aboveK_lt hc hlt))
  have := Finset.card_le_card_of_injOn (fun i => (aboveK cell key i).card) hmaps hinj
  simpa using this

/-- **Обмен в ядро.** Если в каждой ячейке актив с бо́льшим ключом доминирует (`h i ≤ g i'`
на множестве `Ball`), то любой носитель `U` из не более чем `k` активов заменяется носителем
`U' ⊆ topK` той же мощности с `Σ_{U∩topK} g + Σ_{U∖topK} h ≤ Σ_{U'} g` на `Ball`. -/
theorem exchange_topK (cell : ι → γ) (key : ι → β) (k : ℕ) {τ : Type*} (g h : ι → τ → ℝ)
    (Ball : τ → Prop)
    (hdom : ∀ i i', cell i = cell i' → key i < key i' → ∀ t, Ball t → h i t ≤ g i' t) :
    ∀ U : Finset ι, U.card ≤ k → ∃ U' ⊆ topK cell key k, U'.card = U.card ∧
      ∀ t, Ball t → ∑ i ∈ U ∩ topK cell key k, g i t + ∑ i ∈ U \ topK cell key k, h i t
        ≤ ∑ i ∈ U', g i t := by
  intro U
  induction hn : (U \ topK cell key k).card using Nat.strong_induction_on generalizing U with
  | _ n ih =>
  intro hUk
  by_cases hempty : U \ topK cell key k = ∅
  · refine ⟨U, fun x hx => ?_, rfl, fun t _ => ?_⟩
    · by_contra hx'
      have : x ∈ U \ topK cell key k := mem_sdiff.mpr ⟨hx, hx'⟩
      rw [hempty] at this; simp at this
    · rw [hempty, Finset.sum_empty, add_zero]
      have : U ∩ topK cell key k = U := by
        ext x; constructor
        · intro hx; exact (mem_inter.mp hx).1
        · intro hx
          refine mem_inter.mpr ⟨hx, ?_⟩
          by_contra hx'
          have : x ∈ U \ topK cell key k := mem_sdiff.mpr ⟨hx, hx'⟩
          rw [hempty] at this; simp at this
      rw [this]
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hiU : i ∈ U := (mem_sdiff.mp hi).1
    have hiK : i ∉ topK cell key k := (mem_sdiff.mp hi).2
    have hA : k ≤ (aboveK cell key i).card := by
      rw [mem_topK] at hiK; omega
    -- в `aboveK i` есть актив вне `U`
    have hUA : (U ∩ aboveK cell key i).card < k := by
      have hsub : U ∩ aboveK cell key i ⊆ U.erase i := by
        intro x hx
        refine mem_erase.mpr ⟨fun hxi => ?_, (mem_inter.mp hx).1⟩
        subst hxi
        have := (mem_inter.mp hx).2
        simp [aboveK] at this
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hiU] at this
      have : 0 < U.card := Finset.card_pos.mpr ⟨i, hiU⟩
      omega
    have hne : (aboveK cell key i \ U).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hcon
      have : aboveK cell key i ⊆ U ∩ aboveK cell key i := fun x hx => mem_inter.mpr ⟨hcon hx, hx⟩
      have := Finset.card_le_card this
      omega
    obtain ⟨i', hi'mem, hi'max⟩ := Finset.exists_max_image _ key hne
    have hi'A : i' ∈ aboveK cell key i := (mem_sdiff.mp hi'mem).1
    have hi'U : i' ∉ U := (mem_sdiff.mp hi'mem).2
    have hci' : cell i' = cell i ∧ key i < key i' := by simpa [aboveK] using hi'A
    -- `i'` в ядре: над ним только активы из `U ∩ aboveK i`
    have hi'K : i' ∈ topK cell key k := by
      rw [mem_topK]
      have hsub : aboveK cell key i' ⊆ U ∩ aboveK cell key i := by
        intro x hx
        simp only [aboveK, mem_filter, mem_univ, true_and] at hx
        have hxA : x ∈ aboveK cell key i := by
          simp only [aboveK, mem_filter, mem_univ, true_and]
          exact ⟨hx.1.trans hci'.1, hci'.2.trans hx.2⟩
        refine mem_inter.mpr ⟨?_, hxA⟩
        by_contra hxU
        have := hi'max x (mem_sdiff.mpr ⟨hxA, hxU⟩)
        exact absurd hx.2 (not_lt.mpr this)
      exact lt_of_le_of_lt (Finset.card_le_card hsub) hUA
    set U₁ := insert i' (U.erase i) with hU₁
    have hU₁card : U₁.card = U.card := by
      rw [hU₁, Finset.card_insert_of_notMem (fun h => hi'U (mem_of_mem_erase h)),
        Finset.card_erase_of_mem hiU]
      have : 0 < U.card := Finset.card_pos.mpr ⟨i, hiU⟩
      omega
    have hU₁diff : U₁ \ topK cell key k = (U \ topK cell key k).erase i := by
      ext x
      simp only [hU₁, mem_sdiff, mem_insert, mem_erase]
      constructor
      · rintro ⟨hx | ⟨hxi, hxU⟩, hxK⟩
        · subst hx; exact absurd hi'K hxK
        · exact ⟨hxi, hxU, hxK⟩
      · rintro ⟨hxi, hxU, hxK⟩
        exact ⟨Or.inr ⟨hxi, hxU⟩, hxK⟩
    have hU₁inter : U₁ ∩ topK cell key k = insert i' (U ∩ topK cell key k) := by
      ext x
      simp only [hU₁, mem_inter, mem_insert, mem_erase]
      constructor
      · rintro ⟨hx | ⟨hxi, hxU⟩, hxK⟩
        · exact Or.inl hx
        · exact Or.inr ⟨hxU, hxK⟩
      · rintro (hx | ⟨hxU, hxK⟩)
        · subst hx; exact ⟨Or.inl rfl, hi'K⟩
        · refine ⟨Or.inr ⟨fun hxi => ?_, hxU⟩, hxK⟩
          subst hxi; exact hiK hxK
    have hlt : (U₁ \ topK cell key k).card < n := by
      rw [hU₁diff, Finset.card_erase_of_mem hi, ← hn]
      have : 0 < (U \ topK cell key k).card := Finset.card_pos.mpr ⟨i, hi⟩
      omega
    obtain ⟨U', hU'K, hU'card, hU'sum⟩ := ih _ hlt U₁ rfl (by omega)
    refine ⟨U', hU'K, hU'card.trans hU₁card, fun t ht => ?_⟩
    have h1 := hU'sum t ht
    rw [hU₁inter, hU₁diff] at h1
    rw [Finset.sum_insert (fun h => hi'U (mem_inter.mp h).1)] at h1
    have h2 : ∑ x ∈ U \ topK cell key k, h x t
        = h i t + ∑ x ∈ (U \ topK cell key k).erase i, h x t :=
      (Finset.add_sum_erase _ _ hi).symm
    have h3 := hdom i i' hci'.1.symm hci'.2 t ht
    linarith

end Exchange

/-! ## Ячейки факторной модели (`Σ_f = I`)

Строки `a_i = B_i/√d_i ∈ ℝ^{K'+1}`, цели `y_i = m_i/√d_i`. Для `a_i ≠ 0`: `l_i` — координата
наибольшего модуля, `ρ_i = |a_{i,l_i}|`, знак `a_{i,l_i}`, класс масштаба
`σ_i = ⌊log ρ_i / log(1+ε)⌋`, `u_σ = (1+ε)^{σ+1}` и угловая сетка шага
`θ_σ = ε/(√(2k)(K'+1)u_σ)` по остальным `K'` координатам `a_{ij}/ρ_i`. Строки `a_i = 0` —
одна ячейка. Счёт `y_i/ρ_i` (у нулевых строк `y_i`), ничьи — по номеру актива. -/

section KernelCells

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K' : ℕ}

/-- Строка актива `a_i = B_i/√d_i` (при `Σ_f = I`). -/
noncomputable def krow (d : ι → ℝ) (B : ι → Fin (K' + 1) → ℝ) (i : ι) : Fin (K' + 1) → ℝ :=
  fun j => B i j / Real.sqrt (d i)

/-- Цель `y_i = m_i/√d_i`. -/
noncomputable def ky (m d : ι → ℝ) (i : ι) : ℝ := m i / Real.sqrt (d i)

/-- Координата наибольшего модуля строки. -/
noncomputable def kl (d : ι → ℝ) (B : ι → Fin (K' + 1) → ℝ) (i : ι) : Fin (K' + 1) :=
  Classical.choose (Finset.exists_max_image Finset.univ (fun j => |krow d B i j|)
    Finset.univ_nonempty)

omit [Fintype ι] [DecidableEq ι] in
lemma kl_spec (d : ι → ℝ) (B : ι → Fin (K' + 1) → ℝ) (i : ι) (j : Fin (K' + 1)) :
    |krow d B i j| ≤ |krow d B i (kl d B i)| :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ (fun j => |krow d B i j|)
    Finset.univ_nonempty)).2 j (Finset.mem_univ j)

/-- `ρ_i = max_j |a_ij|`. -/
noncomputable def krho (d : ι → ℝ) (B : ι → Fin (K' + 1) → ℝ) (i : ι) : ℝ :=
  |krow d B i (kl d B i)|

omit [Fintype ι] [DecidableEq ι] in
lemma krho_nonneg (d : ι → ℝ) (B : ι → Fin (K' + 1) → ℝ) (i : ι) : 0 ≤ krho d B i :=
  abs_nonneg _

/-- Знак старшей координаты. -/
noncomputable def ksgn (d : ι → ℝ) (B : ι → Fin (K' + 1) → ℝ) (i : ι) : Bool :=
  decide (0 ≤ krow d B i (kl d B i))

/-- Класс масштаба `σ = ⌊log ρ / log(1+ε)⌋`. -/
noncomputable def kcls (ε : ℝ) (ρ : ℝ) : ℤ := ⌊Real.log ρ / Real.log (1 + ε)⌋

/-- Верхний край класса `u_σ = (1+ε)^{σ+1}`. -/
noncomputable def kup (ε : ℝ) (σ : ℤ) : ℝ := Real.exp ((σ + 1) * Real.log (1 + ε))

/-- Шаг угловой сетки `θ_σ = ε/(√(2k)(K'+1)u_σ)`. -/
noncomputable def kth (K' k : ℕ) (ε : ℝ) (σ : ℤ) : ℝ :=
  ε / (Real.sqrt (2 * k) * (K' + 1) * kup ε σ)

/-- Угловая сетка: `⌊(a_{ij}/ρ_i)/θ⌋` по координатам `j ≠ l_i`. -/
noncomputable def kgrid (d : ι → ℝ) (B : ι → Fin (K' + 1) → ℝ) (k : ℕ) (ε : ℝ) (i : ι) :
    Fin K' → ℤ :=
  fun j => ⌊krow d B i ((kl d B i).succAbove j) / krho d B i
    / kth K' k ε (kcls ε (krho d B i))⌋

/-- **Ячейка** актива. -/
noncomputable def kcell (d : ι → ℝ) (B : ι → Fin (K' + 1) → ℝ) (k : ℕ) (ε : ℝ) (i : ι) :
    Option (Fin (K' + 1) × Bool × ℤ × (Fin K' → ℤ)) :=
  if krho d B i = 0 then none
  else some (kl d B i, ksgn d B i, kcls ε (krho d B i), kgrid d B k ε i)

/-- Счёт `y_i/ρ_i` (у нулевых строк `y_i`). -/
noncomputable def kscore (m d : ι → ℝ) (B : ι → Fin (K' + 1) → ℝ) (i : ι) : ℝ :=
  if krho d B i = 0 then ky m d i else ky m d i / krho d B i

/-- Ключ: счёт, ничьи — по номеру актива. -/
noncomputable def kkey (m d : ι → ℝ) (B : ι → Fin (K' + 1) → ℝ) (i : ι) : ℝ ×ₗ ℕ :=
  toLex (kscore m d B i, ((Fintype.equivFin ι i : Fin (Fintype.card ι)) : ℕ))

omit [DecidableEq ι] in
lemma kkey_injective (m d : ι → ℝ) (B : ι → Fin (K' + 1) → ℝ) :
    Function.Injective (kkey m d B) := by
  intro i i' h
  have h2 := congrArg (fun x => (ofLex x).2) h
  simp only [kkey, ofLex_toLex] at h2
  exact (Fintype.equivFin ι).injective (Fin.ext h2)

omit [DecidableEq ι] in
lemma kscore_le_of_key_lt {m d : ι → ℝ} {B : ι → Fin (K' + 1) → ℝ} {i i' : ι}
    (h : kkey m d B i < kkey m d B i') : kscore m d B i ≤ kscore m d B i' := by
  rcases (Prod.Lex.toLex_lt_toLex).mp h with h1 | ⟨h1, _⟩
  · exact h1.le
  · exact h1.le

/-- **Ядро** факторной модели. -/
noncomputable def kerK (m d : ι → ℝ) (B : ι → Fin (K' + 1) → ℝ) (k : ℕ) (ε : ℝ) : Finset ι :=
  topK (kcell d B k ε) (kkey m d B) k

/-! ### Границы класса масштаба -/

lemma kcls_bounds {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    Real.exp (kcls ε ρ * Real.log (1 + ε)) ≤ ρ ∧ ρ < kup ε (kcls ε ρ) := by
  have hL : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  have h1 := Int.floor_le (Real.log ρ / Real.log (1 + ε))
  have h2 := Int.lt_floor_add_one (Real.log ρ / Real.log (1 + ε))
  have e1 : (kcls ε ρ : ℝ) * Real.log (1 + ε) ≤ Real.log ρ := by
    have := mul_le_mul_of_nonneg_right h1 hL.le
    rwa [div_mul_cancel₀ _ hL.ne'] at this
  have e2 : Real.log ρ < ((kcls ε ρ : ℝ) + 1) * Real.log (1 + ε) := by
    have := mul_lt_mul_of_pos_right h2 hL
    rwa [div_mul_cancel₀ _ hL.ne'] at this
  constructor
  · calc Real.exp (kcls ε ρ * Real.log (1 + ε)) ≤ Real.exp (Real.log ρ) := Real.exp_le_exp.mpr e1
      _ = ρ := Real.exp_log hρ
  · calc ρ = Real.exp (Real.log ρ) := (Real.exp_log hρ).symm
      _ < kup ε (kcls ε ρ) := Real.exp_lt_exp.mpr e2

lemma kup_eq {ε : ℝ} (hε : 0 < ε) (σ : ℤ) :
    kup ε σ = (1 + ε) * Real.exp (σ * Real.log (1 + ε)) := by
  rw [kup, add_mul, one_mul, Real.exp_add, Real.exp_log (by linarith)]
  ring

lemma kup_pos (ε : ℝ) (σ : ℤ) : 0 < kup ε σ := Real.exp_pos _

/-- Два масштаба одного класса отличаются меньше чем в `1 + ε` раз. -/
lemma kcls_ratio {ε ρ ρ' : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hρ' : 0 < ρ')
    (h : kcls ε ρ = kcls ε ρ') : ρ < (1 + ε) * ρ' := by
  have h1 := (kcls_bounds hε hρ).2
  have h2 := (kcls_bounds hε hρ').1
  rw [h, kup_eq hε] at h1
  have : (1 + ε) * Real.exp (kcls ε ρ' * Real.log (1 + ε)) ≤ (1 + ε) * ρ' :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  linarith

/-! ### Доминирование внутри ячейки -/

omit [Fintype ι] [DecidableEq ι] in
lemma dotp_krow (d : ι → ℝ) (B : ι → Fin (K' + 1) → ℝ) (i : ι) (t : Fin (K' + 1) → ℝ) :
    dotp (krow d B i) t = dotp (B i) t / Real.sqrt (d i) := by
  simp only [dotp, krow, Finset.sum_div]
  exact Finset.sum_congr rfl fun _ _ => by ring

omit [Fintype ι] [DecidableEq ι] in
/-- Нулевая строка: `ρ_i = 0 ⇒ a_i = 0`. -/
lemma krow_eq_zero {d : ι → ℝ} {B : ι → Fin (K' + 1) → ℝ} {i : ι} (h : krho d B i = 0)
    (j : Fin (K' + 1)) : krow d B i j = 0 := by
  have := kl_spec d B i j
  rw [show |krow d B i (kl d B i)| = krho d B i from rfl, h] at this
  exact abs_nonpos_iff.mp this

omit [Fintype ι] [DecidableEq ι] in
/-- Старшие координаты двух строк одной ячейки после деления на масштаб совпадают. -/
lemma klead_eq {d : ι → ℝ} {B : ι → Fin (K' + 1) → ℝ} {i i' : ι}
    (hl : kl d B i = kl d B i') (hs : ksgn d B i = ksgn d B i')
    (hρ : 0 < krho d B i) (hρ' : 0 < krho d B i') :
    krow d B i (kl d B i) / krho d B i = krow d B i' (kl d B i) / krho d B i' := by
  have hsgn : (0 ≤ krow d B i (kl d B i)) ↔ (0 ≤ krow d B i' (kl d B i)) := by
    have := hs
    simp only [ksgn, decide_eq_decide] at this
    rw [← hl] at this
    exact this
  have e1 : |krow d B i (kl d B i)| = krho d B i := rfl
  have e2 : |krow d B i' (kl d B i)| = krho d B i' := by rw [hl]; rfl
  by_cases hpos : 0 ≤ krow d B i (kl d B i)
  · have hpos' := hsgn.mp hpos
    rw [abs_of_nonneg hpos] at e1; rw [abs_of_nonneg hpos'] at e2
    rw [e1, e2, div_self hρ.ne', div_self hρ'.ne']
  · have hneg : krow d B i (kl d B i) < 0 := lt_of_not_ge hpos
    have hneg' : krow d B i' (kl d B i) < 0 := lt_of_not_ge (fun h => hpos (hsgn.mpr h))
    rw [abs_of_neg hneg] at e1; rw [abs_of_neg hneg'] at e2
    have a1 : krow d B i (kl d B i) = -krho d B i := by linarith
    have a2 : krow d B i' (kl d B i) = -krho d B i' := by linarith
    rw [a1, a2, neg_div, neg_div, div_self hρ.ne', div_self hρ'.ne']

/-- Шаг угловой сетки положителен. -/
lemma kth_pos (K' k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) (σ : ℤ) : 0 < kth K' k ε σ := by
  rw [kth]
  have : 0 < Real.sqrt (2 * k) := Real.sqrt_pos.mpr (by positivity)
  have := kup_pos ε σ
  positivity

omit [Fintype ι] [DecidableEq ι] in
/-- Направления двух строк одной ячейки различаются покоординатно не больше чем на `θ`. -/
lemma kdir_close {d : ι → ℝ} {B : ι → Fin (K' + 1) → ℝ} {k : ℕ} {ε : ℝ} (hk : 1 ≤ k)
    (hε : 0 < ε) {i i' : ι}
    (hl : kl d B i = kl d B i') (hs : ksgn d B i = ksgn d B i')
    (hσ : kcls ε (krho d B i) = kcls ε (krho d B i'))
    (hg : kgrid d B k ε i = kgrid d B k ε i')
    (hρ : 0 < krho d B i) (hρ' : 0 < krho d B i') (j : Fin (K' + 1)) :
    |krow d B i j / krho d B i - krow d B i' j / krho d B i'|
      ≤ kth K' k ε (kcls ε (krho d B i)) := by
  have hθ := kth_pos K' k hk hε (kcls ε (krho d B i))
  by_cases hjl : j = kl d B i
  · rw [hjl, klead_eq hl hs hρ hρ', sub_self, abs_zero]; exact hθ.le
  · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hjl
    have hgj := congrFun hg j'
    simp only [kgrid] at hgj
    rw [← hl, ← hσ] at hgj
    have hlt := Int.abs_sub_lt_one_of_floor_eq_floor hgj
    rw [← sub_div, abs_div, abs_of_pos hθ, div_lt_one hθ] at hlt
    exact hlt.le

omit [DecidableEq ι] in
/-- **Доминирование.** Если `i` и `i'` в одной ячейке и ключ `i'` больше, то на шаре
`Σ t_j² ≤ v` обрезанная невязка `i'` не меньше обрезанной невязки `i`, делённой на `1 + ε`,
минус `ε√(v/2k)`. -/
theorem kdom {m d : ι → ℝ} {B : ι → Fin (K' + 1) → ℝ} {k : ℕ} {ε v : ℝ}
    (hε : 0 < ε) (hk : 1 ≤ k) (hv : 0 ≤ v) {i i' : ι}
    (hc : kcell d B k ε i = kcell d B k ε i') (hkey : kkey m d B i < kkey m d B i')
    {t : Fin (K' + 1) → ℝ} (ht : ∑ j, t j ^ 2 ≤ v) :
    max (ky m d i - dotp (krow d B i) t) 0 / (1 + ε) - ε * Real.sqrt (v / (2 * k))
      ≤ max (ky m d i' - dotp (krow d B i') t) 0 := by
  have hsc := kscore_le_of_key_lt hkey
  have he : 0 ≤ ε * Real.sqrt (v / (2 * k)) := mul_nonneg hε.le (Real.sqrt_nonneg _)
  have h1ε : (1 : ℝ) ≤ 1 + ε := by linarith
  by_cases h0 : krho d B i = 0
  · -- нулевые строки
    have h0' : krho d B i' = 0 := by
      by_contra hne
      simp [kcell, h0, hne] at hc
    have hz : ∀ i₀, krho d B i₀ = 0 → dotp (krow d B i₀) t = 0 := by
      intro i₀ hi₀
      simp only [dotp]
      exact Finset.sum_eq_zero fun j _ => by rw [krow_eq_zero hi₀ j, zero_mul]
    rw [hz i h0, hz i' h0', sub_zero, sub_zero]
    simp only [kscore, h0, h0', ite_true] at hsc
    have hmx : max (ky m d i) 0 ≤ max (ky m d i') 0 := max_le_max hsc le_rfl
    have : max (ky m d i) 0 / (1 + ε) ≤ max (ky m d i) 0 :=
      div_le_self (le_max_right _ _) h1ε
    linarith
  · have h0' : krho d B i' ≠ 0 := by
      intro hne
      simp [kcell, h0, hne] at hc
    simp only [kcell, h0, h0', ite_false, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨hl, hs, hσ, hg⟩ := hc
    have hρ : 0 < krho d B i := lt_of_le_of_ne (krho_nonneg d B i) (Ne.symm h0)
    have hρ' : 0 < krho d B i' := lt_of_le_of_ne (krho_nonneg d B i') (Ne.symm h0')
    have hθ := kth_pos K' k hk hε (kcls ε (krho d B i))
    have hclose := kdir_close hk hε hl hs hσ hg hρ hρ'
    have hsc' : ky m d i / krho d B i ≤ ky m d i' / krho d B i' := by
      simpa [kscore, h0, h0'] using hsc
    set ρ := krho d B i with hρdef
    set ρ' := krho d B i' with hρ'def
    set θ := kth K' k ε (kcls ε ρ) with hθdef
    -- `|t_j| ≤ √v`
    have htj : ∀ j, |t j| ≤ Real.sqrt v := by
      intro j
      apply Real.abs_le_sqrt
      calc t j ^ 2 ≤ ∑ j', t j' ^ 2 :=
            Finset.single_le_sum (f := fun j' => t j' ^ 2) (fun _ _ => sq_nonneg _)
              (Finset.mem_univ j)
        _ ≤ v := ht
    -- невязки через направления
    have hr₁ : ky m d i - dotp (krow d B i) t
        = ρ * (ky m d i / ρ - ∑ j, krow d B i j / ρ * t j) := by
      simp only [dotp]
      rw [mul_sub, mul_div_cancel₀ _ hρ.ne', Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by field_simp
    have hr₂ : ky m d i' - dotp (krow d B i') t
        = ρ' * (ky m d i' / ρ' - ∑ j, krow d B i' j / ρ' * t j) := by
      simp only [dotp]
      rw [mul_sub, mul_div_cancel₀ _ hρ'.ne', Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by field_simp
    set q := ky m d i / ρ - ∑ j, krow d B i j / ρ * t j with hq
    set q' := ky m d i' / ρ' - ∑ j, krow d B i' j / ρ' * t j with hq'
    have hdiff : q - (K' + 1) * θ * Real.sqrt v ≤ q' := by
      have hsum : ∑ _j : Fin (K' + 1), -(θ * Real.sqrt v)
          ≤ ∑ j, (krow d B i j / ρ - krow d B i' j / ρ') * t j := by
        refine Finset.sum_le_sum fun j _ => ?_
        have : |(krow d B i j / ρ - krow d B i' j / ρ') * t j| ≤ θ * Real.sqrt v := by
          rw [abs_mul]; exact mul_le_mul (hclose j) (htj j) (abs_nonneg _) hθ.le
        exact neg_le_of_abs_le this
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
      have hsplit : ∑ j, krow d B i' j / ρ' * t j
          = ∑ j, krow d B i j / ρ * t j
            - ∑ j, (krow d B i j / ρ - krow d B i' j / ρ') * t j := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hq, hq', hsplit]
      push_cast at hsum
      linarith
    -- ошибка не больше `ε√(v/2k)`
    have hρ'u : ρ' < kup ε (kcls ε ρ) := by
      have := (kcls_bounds hε hρ').2
      rwa [← hσ] at this
    have herr : ρ' * ((K' + 1) * θ * Real.sqrt v) ≤ ε * Real.sqrt (v / (2 * k)) := by
      have hs2k : 0 < Real.sqrt (2 * k) := Real.sqrt_pos.mpr (by positivity)
      have hsplit : Real.sqrt (v / (2 * k)) = Real.sqrt v / Real.sqrt (2 * k) := by
        rw [Real.sqrt_div hv]
      have hup := kup_pos ε (kcls ε ρ)
      have hK : (0 : ℝ) < K' + 1 := by positivity
      have heq : ρ' * ((K' + 1) * θ * Real.sqrt v)
          = (ρ' / kup ε (kcls ε ρ)) * (ε * Real.sqrt v / Real.sqrt (2 * k)) := by
        rw [hθdef, kth]; field_simp
      rw [heq, hsplit]
      have h1 : ρ' / kup ε (kcls ε ρ) ≤ 1 := (div_le_one hup).mpr hρ'u.le
      have h2 : 0 ≤ ε * Real.sqrt v / Real.sqrt (2 * k) := by positivity
      calc ρ' / kup ε (kcls ε ρ) * (ε * Real.sqrt v / Real.sqrt (2 * k))
          ≤ 1 * (ε * Real.sqrt v / Real.sqrt (2 * k)) := mul_le_mul_of_nonneg_right h1 h2
        _ = ε * (Real.sqrt v / Real.sqrt (2 * k)) := by ring
    have hratio : ρ < (1 + ε) * ρ' := kcls_ratio hε hρ hρ' hσ
    -- итог
    by_cases hq0 : q ≤ 0
    · have : max (ky m d i - dotp (krow d B i) t) 0 = 0 := by
        rw [hr₁]; exact max_eq_right (mul_nonpos_of_nonneg_of_nonpos hρ.le hq0)
      rw [this, zero_div, zero_sub]
      linarith [le_max_right (ky m d i' - dotp (krow d B i') t) 0]
    · have hq0' : 0 < q := lt_of_not_ge hq0
      have hmax : max (ky m d i - dotp (krow d B i) t) 0 = ρ * q := by
        rw [hr₁]; exact max_eq_left (by positivity)
      rw [hmax]
      have hstep : ρ * q / (1 + ε) ≤ ρ' * q := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      have : ρ' * q - ε * Real.sqrt (v / (2 * k)) ≤ ky m d i' - dotp (krow d B i') t := by
        rw [hr₂]
        have := mul_le_mul_of_nonneg_left hdiff hρ'.le
        nlinarith
      linarith [le_max_left (ky m d i' - dotp (krow d B i') t) 0]

/-! ### Значение носителя из ядра -/

/-- `t'It = Σ t_j²`. -/
lemma quadf_opI {κ : Type*} [Fintype κ] [DecidableEq κ] (t : κ → ℝ) :
    quadf (opI κ) t = ∑ j, t j ^ 2 := by
  simp only [quadf]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j]
  · simp [opI, sq]
  · intro b _ hb; simp [opI, Ne.symm hb]
  · simp

omit [Fintype ι] [DecidableEq ι] in
/-- Слагаемое двойственной функции через строку:
`((m_i − ⟨B_i,t⟩)_+)²/d_i = ((y_i − ⟨a_i,t⟩)_+)²`. -/
lemma term_krow {m d : ι → ℝ} (hd : ∀ i, 0 < d i) (B : ι → Fin (K' + 1) → ℝ) (i : ι)
    (t : Fin (K' + 1) → ℝ) :
    max (m i - dotp (B i) t) 0 ^ 2 / d i = max (ky m d i - dotp (krow d B i) t) 0 ^ 2 := by
  have hs : 0 < Real.sqrt (d i) := Real.sqrt_pos.mpr (hd i)
  have hmax : max ((m i - dotp (B i) t) / Real.sqrt (d i)) 0
      = max (m i - dotp (B i) t) 0 / Real.sqrt (d i) := by
    rcases le_or_gt (m i - dotp (B i) t) 0 with h | h
    · rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg h hs.le), max_eq_right h, zero_div]
    · rw [max_eq_left (div_pos h hs).le, max_eq_left h.le]
  rw [dotp_krow, ky, ← sub_div, hmax, div_pow, Real.sq_sqrt (hd i).le]

omit [Fintype ι] [DecidableEq ι] in
/-- Двойственная функция при `Σ_f = I` через строки. -/
lemma QLO_opI_eq {m d : ι → ℝ} (hd : ∀ i, 0 < d i) (B : ι → Fin (K' + 1) → ℝ)
    (S : Finset ι) (t : Fin (K' + 1) → ℝ) :
    QLO m d B (opI (Fin (K' + 1))) S t
      = ∑ j, t j ^ 2 + ∑ i ∈ S, max (ky m d i - dotp (krow d B i) t) 0 ^ 2 := by
  rw [QLO, quadf_opI]
  congr 1
  exact Finset.sum_congr rfl fun i _ => term_krow hd B i t

/-- Оценка снизу для обрезки с потерей: `x²/(1+ε)² − εx² − e²/ε ≤ ((x/(1+ε) − e)_+)²`. -/
lemma clip_loss_lower {x e ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    x ^ 2 / (1 + ε) ^ 2 - ε * x ^ 2 - e ^ 2 / ε ≤ max (x / (1 + ε) - e) 0 ^ 2 := by
  have h1ε : 0 < 1 + ε := by linarith
  set a := x / (1 + ε) with ha
  have ha0 : 0 ≤ a := div_nonneg hx h1ε.le
  have ha2 : a ^ 2 = x ^ 2 / (1 + ε) ^ 2 := by rw [ha, div_pow]
  have hax : a ≤ x := div_le_self hx (by linarith)
  have hax2 : a ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ ha0 hax 2
  have hamgm : 2 * a * e ≤ ε * a ^ 2 + e ^ 2 / ε := by
    have h := sq_nonneg (ε * a - e)
    have : ε * (ε * a ^ 2 + e ^ 2 / ε - 2 * a * e) = (ε * a - e) ^ 2 := by
      field_simp; ring
    nlinarith
  rw [← ha2]
  rcases le_or_gt e a with hea | hea
  · rw [max_eq_left (by linarith)]
    nlinarith
  · rw [max_eq_right (by linarith)]
    have he2 : a ^ 2 < e ^ 2 := by nlinarith
    have : e ^ 2 ≤ e ^ 2 / ε := by
      rw [le_div_iff₀ hε]; nlinarith [sq_nonneg e]
    nlinarith [sq_nonneg x]

/-- **Значение ядра.** Для любого long-only портфеля `(U, w)` с `|U| ≤ k` в ядре есть носитель
`U'`, `|U'| ≤ |U|`, и long-only веса на нём с целью не меньше `(1 − 4ε)` цели `(U, w)`. -/
theorem kernel_value {m d : ι → ℝ} (hd : ∀ i, 0 < d i) (B : ι → Fin (K' + 1) → ℝ) {k : ℕ}
    (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) {U : Finset ι} (hU : U.card ≤ k)
    {w : ι → ℝ} (hw : ∀ i ∈ U, 0 ≤ w i) :
    ∃ U' ⊆ kerK m d B k ε, U'.card ≤ U.card ∧ ∃ w' : ι → ℝ, (∀ i ∈ U', 0 ≤ w' i) ∧
      (1 - 4 * ε) * objLO m d B (opI (Fin (K' + 1))) U w
        ≤ objLO m d B (opI (Fin (K' + 1))) U' w' := by
  set v := objLO m d B (opI (Fin (K' + 1))) U w with hvdef
  have h14 : 0 ≤ 1 - 4 * ε := by linarith
  by_cases hv0 : v ≤ 0
  · refine ⟨∅, Finset.empty_subset _, by simp, fun _ => 0, by simp, ?_⟩
    have : objLO m d B (opI (Fin (K' + 1))) ∅ (fun _ => 0) = 0 := by simp [objLO]
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos h14 hv0
  have hv : 0 < v := lt_of_not_ge hv0
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set e := ε * Real.sqrt (v / (2 * k)) with hedef
  have he : 0 ≤ e := mul_nonneg hε.le (Real.sqrt_nonneg _)
  have he2 : e ^ 2 = ε ^ 2 * v / (2 * k) := by
    rw [hedef, mul_pow, Real.sq_sqrt (by positivity)]; ring
  -- функции обмена
  set g : ι → (Fin (K' + 1) → ℝ) → ℝ := fun i t => max (ky m d i - dotp (krow d B i) t) 0 ^ 2
    with hgdef
  set h : ι → (Fin (K' + 1) → ℝ) → ℝ :=
    fun i t => max (max (ky m d i - dotp (krow d B i) t) 0 / (1 + ε) - e) 0 ^ 2 with hhdef
  have hhg : ∀ i t, h i t ≤ g i t := by
    intro i t
    simp only [hhdef, hgdef]
    have hx := le_max_right (ky m d i - dotp (krow d B i) t) 0
    apply pow_le_pow_left₀ (le_max_right _ _)
    apply max_le _ hx
    have : max (ky m d i - dotp (krow d B i) t) 0 / (1 + ε)
        ≤ max (ky m d i - dotp (krow d B i) t) 0 := div_le_self hx (by linarith)
    linarith
  have hdom : ∀ i i', kcell d B k ε i = kcell d B k ε i' → kkey m d B i < kkey m d B i' →
      ∀ t, (∑ j, t j ^ 2 ≤ v) → h i t ≤ g i' t := by
    intro i i' hc hkey t ht
    have := kdom (m := m) hε hk hv.le hc hkey ht
    simp only [hhdef, hgdef]
    apply pow_le_pow_left₀ (le_max_right _ _)
    exact max_le this (le_max_right _ _)
  obtain ⟨U', hU'K, hU'card, hU'sum⟩ := exchange_topK (kcell d B k ε) (kkey m d B) k g h
    (fun t => ∑ j, t j ^ 2 ≤ v) hdom U hU
  refine ⟨U', hU'K, hU'card.le, ?_⟩
  -- сильная двойственность на `U'`
  obtain ⟨z, ⟨⟨t₀, hz⟩, hleast⟩, ⟨⟨w', hw', hzw⟩, -⟩⟩ :=
    isGreatest_objLO_isLeast_QLO (m := m) (d := d) (B := B) (Sf := opI (Fin (K' + 1)))
      (P := opI (Fin (K' + 1))) (G := opI (Fin (K' + 1))) hd (opI_hG _) (opI_hPS _) U'
  refine ⟨w', hw', ?_⟩
  rw [← hzw, hz, QLO_opI_eq hd]
  -- слабая двойственность на `U`
  have hweak := objLO_le_QLO (m := m) (d := d) (B := B) (Sf := opI (Fin (K' + 1)))
    (P := opI (Fin (K' + 1))) (G := opI (Fin (K' + 1))) hd (opI_hG _) (opI_hPS _) hw t₀
  rw [QLO_opI_eq hd] at hweak
  have hgU' : 0 ≤ ∑ i ∈ U', g i t₀ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hT0 : 0 ≤ ∑ j, t₀ j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hball : v ≤ ∑ j, t₀ j ^ 2
  · have : (1 - 4 * ε) * v ≤ v := by nlinarith
    change (1 - 4 * ε) * v ≤ ∑ j, t₀ j ^ 2 + ∑ i ∈ U', g i t₀
    linarith
  · have hb : ∑ j, t₀ j ^ 2 ≤ v := le_of_not_ge hball
    have hsum := hU'sum t₀ hb
    have hUh : ∑ i ∈ U, h i t₀ ≤ ∑ i ∈ U', g i t₀ := by
      have hsplit := Finset.sum_inter_add_sum_sdiff U (kerK m d B k ε) (fun i => h i t₀)
      have hle : ∑ i ∈ U ∩ kerK m d B k ε, h i t₀ ≤ ∑ i ∈ U ∩ kerK m d B k ε, g i t₀ :=
        Finset.sum_le_sum fun i _ => hhg i t₀
      unfold kerK at hsplit hle
      linarith
    -- поточечная оценка `h ≥ g/(1+ε)² − εg − e²/ε`
    have hterm : ∀ i ∈ U, g i t₀ / (1 + ε) ^ 2 - ε * g i t₀ - e ^ 2 / ε ≤ h i t₀ := by
      intro i _
      simp only [hgdef, hhdef]
      exact clip_loss_lower (le_max_right _ _) hε (by linarith)
    have hsumterm := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.sum_div, ← Finset.mul_sum] at hsumterm
    set G := ∑ i ∈ U, g i t₀ with hGdef
    have hcard : (U.card : ℝ) * (e ^ 2 / ε) ≤ ε * v / 2 := by
      rw [he2]
      have hUk : (U.card : ℝ) ≤ k := by exact_mod_cast hU
      have hkpos : (0 : ℝ) < k := by linarith
      have : (U.card : ℝ) * (ε ^ 2 * v / (2 * k) / ε) = ε * v / 2 * ((U.card : ℝ) / k) := by
        field_simp
      rw [this]
      have : (U.card : ℝ) / k ≤ 1 := (div_le_one hkpos).mpr hUk
      have : 0 ≤ ε * v / 2 := by positivity
      nlinarith
    -- `c = 1/(1+ε)² − ε ∈ [1 − 3ε, 1]`
    have hc1 : 1 - 2 * ε ≤ 1 / (1 + ε) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg ε, mul_pos hε hε]
    have hc2 : 1 / (1 + ε) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have hGdiv : G / (1 + ε) ^ 2 = (1 / (1 + ε) ^ 2) * G := by ring
    have hG0 : 0 ≤ G := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hT0c : (1 / (1 + ε) ^ 2 - ε) * ∑ j, t₀ j ^ 2 ≤ ∑ j, t₀ j ^ 2 := by
      nlinarith
    have hchain : (1 / (1 + ε) ^ 2 - ε) * (∑ j, t₀ j ^ 2 + G) - ε * v / 2
        ≤ ∑ j, t₀ j ^ 2 + ∑ i ∈ U', g i t₀ := by
      nlinarith
    have hcv : (1 / (1 + ε) ^ 2 - ε) * v ≤ (1 / (1 + ε) ^ 2 - ε) * (∑ j, t₀ j ^ 2 + G) := by
      apply mul_le_mul_of_nonneg_left hweak
      linarith
    nlinarith

/-! ### Размер ядра -/

/-- Коробка меток ячеек: `none` и кортежи с классом масштаба в `[σ₀, σ₁]` и угловой сеткой
в `[−G, G]^{K'}`. -/
noncomputable def kbox (K' : ℕ) (σ₀ σ₁ : ℤ) (G : ℕ) :
    Finset (Option (Fin (K' + 1) × Bool × ℤ × (Fin K' → ℤ))) :=
  insert none ((Finset.univ ×ˢ Finset.univ ×ˢ Finset.Icc σ₀ σ₁
    ×ˢ Fintype.piFinset (fun _ : Fin K' => Finset.Icc (-(G : ℤ)) G)).map
      ⟨some, Option.some_injective _⟩)

lemma card_kbox (K' : ℕ) (σ₀ σ₁ : ℤ) (G : ℕ) :
    (kbox K' σ₀ σ₁ G).card ≤ 1 + (K' + 1) * 2 * (σ₁ + 1 - σ₀).toNat * (2 * G + 1) ^ K' := by
  refine (Finset.card_insert_le _ _).trans ?_
  rw [Finset.card_map, Finset.card_product, Finset.card_product, Finset.card_product,
    Fintype.card_piFinset, Finset.card_univ, Finset.card_univ, Fintype.card_fin,
    Fintype.card_bool, Int.card_Icc]
  have : ∏ _j : Fin K', (Finset.Icc (-(G : ℤ)) G).card = (2 * G + 1) ^ K' := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]
    congr 1
    omega
  rw [this]
  ring_nf
  omega

omit [Fintype ι] [DecidableEq ι] in
/-- Класс масштаба монотонен. -/
lemma kcls_mono {ε ρ ρ' : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (h : ρ ≤ ρ') : kcls ε ρ ≤ kcls ε ρ' := by
  have hL : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  exact Int.floor_le_floor (div_le_div_of_nonneg_right (Real.log_le_log hρ h) hL.le)

/-- Граница угловой сетки. -/
noncomputable def kG (K' k : ℕ) (ε R₁ : ℝ) : ℕ :=
  ⌈(1 + ε) * R₁ * Real.sqrt (2 * k) * (K' + 1) / ε⌉₊

omit [Fintype ι] [DecidableEq ι] in
/-- **Каждая ячейка лежит в коробке**, если масштабы ненулевых строк лежат в `[R₀, R₁]`. -/
lemma kcell_mem_kbox {d : ι → ℝ} {B : ι → Fin (K' + 1) → ℝ} {k : ℕ} {ε R₀ R₁ : ℝ}
    (hk : 1 ≤ k) (hε : 0 < ε) (hR₀ : 0 < R₀)
    (hR : ∀ i, krho d B i ≠ 0 → R₀ ≤ krho d B i ∧ krho d B i ≤ R₁) (i : ι) :
    kcell d B k ε i ∈ kbox K' (kcls ε R₀) (kcls ε R₁) (kG K' k ε R₁) := by
  by_cases h0 : krho d B i = 0
  · simp [kcell, h0, kbox]
  · have hρ : 0 < krho d B i := lt_of_le_of_ne (krho_nonneg d B i) (Ne.symm h0)
    obtain ⟨h1, h2⟩ := hR i h0
    simp only [kcell, h0, ite_false, kbox, Finset.mem_insert, reduceCtorEq, false_or,
      Finset.mem_map, Function.Embedding.coeFn_mk, Option.some.injEq]
    refine ⟨_, ?_, rfl⟩
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc,
      Fintype.mem_piFinset]
    refine ⟨⟨kcls_mono hε hR₀ h1, kcls_mono hε hρ h2⟩, fun j => ?_⟩
    set σ := kcls ε (krho d B i)
    have hθ := kth_pos K' k hk hε σ
    set x := krow d B i ((kl d B i).succAbove j) / krho d B i / kth K' k ε σ with hx
    -- `|a_j/ρ| ≤ 1`
    have hdir : |krow d B i ((kl d B i).succAbove j) / krho d B i| ≤ 1 := by
      rw [abs_div, abs_of_pos hρ, div_le_one hρ]
      exact kl_spec d B i _
    -- `1/θ ≤ (1+ε)R₁√(2k)(K'+1)/ε`
    have hup : kup ε σ ≤ (1 + ε) * R₁ := by
      rw [kup_eq hε]
      have := (kcls_bounds hε hρ).1
      have : Real.exp (σ * Real.log (1 + ε)) ≤ R₁ := this.trans h2
      exact mul_le_mul_of_nonneg_left this (by linarith)
    have hinv : 1 / kth K' k ε σ ≤ (1 + ε) * R₁ * Real.sqrt (2 * k) * (K' + 1) / ε := by
      rw [kth, one_div_div]
      have hs : 0 ≤ Real.sqrt (2 * k) := Real.sqrt_nonneg _
      have hK : (0 : ℝ) ≤ K' + 1 := by positivity
      rw [div_le_div_iff_of_pos_right hε]
      calc Real.sqrt (2 * k) * (K' + 1) * kup ε σ
          ≤ Real.sqrt (2 * k) * (K' + 1) * ((1 + ε) * R₁) :=
            mul_le_mul_of_nonneg_left hup (by positivity)
        _ = (1 + ε) * R₁ * Real.sqrt (2 * k) * (K' + 1) := by ring
    have hxabs : |x| ≤ (kG K' k ε R₁ : ℝ) := by
      rw [hx, abs_div, abs_of_pos hθ]
      calc |krow d B i ((kl d B i).succAbove j) / krho d B i| / kth K' k ε σ
          ≤ 1 / kth K' k ε σ := div_le_div_of_nonneg_right hdir hθ.le
        _ ≤ _ := hinv
        _ ≤ (kG K' k ε R₁ : ℝ) := Nat.le_ceil _
    obtain ⟨hlo, hhi⟩ := abs_le.mp hxabs
    constructor
    · exact Int.le_floor.mpr (by push_cast; linarith)
    · have : (⌊x⌋ : ℝ) ≤ (kG K' k ε R₁ : ℝ) := (Int.floor_le x).trans hhi
      exact_mod_cast this

omit [DecidableEq ι] in
/-- **Размер ядра.** Если масштабы ненулевых строк лежат в `[R₀, R₁]`, то в ядре не больше
`k(1 + 2(K'+1)L(2G+1)^{K'})` активов, где `L` — число классов масштаба между `R₀` и `R₁`, а
`G = ⌈(1+ε)R₁√(2k)(K'+1)/ε⌉`. -/
theorem card_kerK_le {m d : ι → ℝ} {B : ι → Fin (K' + 1) → ℝ} {k : ℕ} {ε R₀ R₁ : ℝ}
    (hk : 1 ≤ k) (hε : 0 < ε) (hR₀ : 0 < R₀)
    (hR : ∀ i, krho d B i ≠ 0 → R₀ ≤ krho d B i ∧ krho d B i ≤ R₁) :
    (kerK m d B k ε).card ≤ k * (1 + (K' + 1) * 2 * (kcls ε R₁ + 1 - kcls ε R₀).toNat
      * (2 * kG K' k ε R₁ + 1) ^ K') := by
  refine (card_topK_le _ _ (kkey_injective m d B) k).trans ?_
  apply Nat.mul_le_mul_left
  refine (Finset.card_le_card ?_).trans (card_kbox K' _ _ _)
  intro c hc
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc
  exact kcell_mem_kbox hk hε hR₀ hR i

omit [Fintype ι] [DecidableEq ι] in
/-- Масштаб строки не больше корня из плеча `ω_i = Σ_j B_ij²/d_i` (при `Σ_f = I`). -/
lemma krho_le_sqrt {d : ι → ℝ} (B : ι → Fin (K' + 1) → ℝ) (i : ι) (hd : 0 < d i) :
    krho d B i ≤ Real.sqrt (∑ j, B i j ^ 2 / d i) := by
  rw [krho]
  apply Real.abs_le_sqrt
  calc krow d B i (kl d B i) ^ 2 ≤ ∑ j, krow d B i j ^ 2 :=
        Finset.single_le_sum (f := fun j => krow d B i j ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ _)
    _ = ∑ j, B i j ^ 2 / d i := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [krow, div_pow, Real.sq_sqrt hd.le]

end KernelCells

end SparseSharpe.Factor
