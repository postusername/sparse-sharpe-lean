import SparseSharpe.Factor.KeyRounding
import SparseSharpe.Factor.NormalExists
import SparseSharpe.Factor.GridFilter
import SparseSharpe.Factor.Cover

set_option linter.style.header false

/-!
# Динамика как функция, а не как контракт

`DPInvariant.lean` описывал динамику **контрактом реализации** (гипотезы
`step_skip`, `step_take`, `tab_key`, …) и доказывал инвариант из них. Здесь
динамика определена **конкретно** — как функция `survivors`, — и все её
свойства доказаны о ней самой, без гипотез.

    survivors base [] = {base}
    survivors base (i :: rest) = prune (F ∪ F.image (insert i))   если `adm i`,
                                 prune F                           иначе,
    где F = survivors base rest,

а `prune` оставляет в каждой корзине ключа **один** набор — с наибольшим `Q_t`
(`repOf`, выбор максимума через `Finset.exists_max_image`).

Три свойства:

* `survivors_card_le` — размер таблицы не больше числа ключей в коробке
  `keyBox`, то есть ровно оценка `StateCount.lean`;
* `survivors_mem` — всякий выживший содержит `base` (якоря), лежит в
  обработанных строках и состоит из допущенных фильтром;
* `survivors_spec` — **инвариант**: для любого допустимого `U` (в приложении —
  носитель оптимума) найдётся выживший `R` **той же мощности** с
  `Q_t(R) ≥ Q_t(U)`, чей ключ отличается от ключа `U` не больше чем на `|L|`
  шагов округления.

Дрейф `|L|·η` неизбежен: округлённый ключ не аддитивен (`⌊(x+c)/η⌋` не
определяется через `⌊x/η⌋`), поэтому за каждый слой теряется одна ширина
корзины — ровно как в `minM_invariant`. Но Теорема Z (`Rounding.lean`)
принимает допуск в виде `∑_l(ΔM̃_l)² ≤ Δ²`, так что дрейф просто подставляется
как `Δ = √K·|L|·η`: требование к округлению первых моментов становится
`8√K·|L|·η ≤ θ₀`, и число корзин по `K` координатам `M̃` растёт в `|L|^K` раз.
Координат формы Грама `Κ̃` в ключе `K²`, и для них тот же дрейф требует
`|L|·ξ·K ≤ 1/8`, то есть по ним число корзин растёт в `|L|^{K²}` раз. Полная
граница на размер таблицы — `lo_fptas_cost` (`Factor/Cost.lean`). Оба условия
записаны произведениями, а не делением на `|L|`: при `L = []` они тривиальны, и
тогда `A = base`.

Итог файла — `lo_fptas_step`: динамика возвращает набор `R` с
`F_LO(R) ≥ (1−2ε)·F(Ā*)`, где `Ā*` — любой самосогласованный носитель,
допущенный фильтром в узле. Вместе с Теоремой X (`Reduction.lean`), которая
сводит long-only к таким носителям, и с `exists_node_closing_step_half`
(`GridFilter.lean`), дающей нужный узел, это гарантия приближения, на которой
держится FPTAS. О времени работы теоремы этого файла не говорят: `η`, `ξ` в них
любые положительные, удовлетворяющие условиям калибровки; при конкретном выборе
`η = θ₀/(8√K·M)`, `ξ = 1/(8MK)` число узлов и размер таблицы ограничены явно в
`Factor/Cost.lean` (`lo_fptas_cost`, `lo_fptas_cost_block`).
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {T : κ → ι} {t : κ → ℝ}

/-! ### Близость в координатах ключа -/

/-- `R` и `U` различаются не больше чем на `d` ширин корзины. -/
structure KeyClose (a : ι → κ → ℝ) (y : ι → ℝ) (T : κ → ι) (t : κ → ℝ) (η ξ d : ℝ)
    (R U : Finset ι) : Prop where
  mom : ∀ l, |momK a y T R t l - momK a y T U t l| ≤ d * η
  gram : ∀ l l', |gramK2 a T R l l' - gramK2 a T U l l'| ≤ d * ξ
  card : R.card = U.card

namespace KeyClose

variable {η ξ d d₁ d₂ : ℝ} {R R' U : Finset ι}

lemma rfl' (hη : 0 ≤ η) (hξ : 0 ≤ ξ) (R : Finset ι) :
    KeyClose a y T t η ξ 0 R R where
  mom := fun l => by simp
  gram := fun l l' => by simp
  card := rfl

lemma trans (h₁ : KeyClose a y T t η ξ d₁ R R') (h₂ : KeyClose a y T t η ξ d₂ R' U) :
    KeyClose a y T t η ξ (d₁ + d₂) R U where
  mom := fun l => by
    have := h₁.mom l
    have := h₂.mom l
    calc |momK a y T R t l - momK a y T U t l|
        ≤ |momK a y T R t l - momK a y T R' t l|
          + |momK a y T R' t l - momK a y T U t l| := abs_sub_le _ _ _
      _ ≤ d₁ * η + d₂ * η := by linarith [h₁.mom l, h₂.mom l]
      _ = (d₁ + d₂) * η := by ring
  gram := fun l l' => by
    calc |gramK2 a T R l l' - gramK2 a T U l l'|
        ≤ |gramK2 a T R l l' - gramK2 a T R' l l'|
          + |gramK2 a T R' l l' - gramK2 a T U l l'| := abs_sub_le _ _ _
      _ ≤ d₁ * ξ + d₂ * ξ := by linarith [h₁.gram l l', h₂.gram l l']
      _ = (d₁ + d₂) * ξ := by ring
  card := by rw [h₁.card, h₂.card]

lemma insert' {i : ι} (hiR : i ∉ R) (hiU : i ∉ U) (h : KeyClose a y T t η ξ d R U) :
    KeyClose a y T t η ξ d (insert i R) (insert i U) where
  mom := fun l => by
    rw [momK_insert hiR, momK_insert hiU]
    simpa using h.mom l
  gram := fun l l' => by
    rw [gramK2_insert hiR, gramK2_insert hiU]
    simpa using h.gram l l'
  card := by rw [Finset.card_insert_of_notMem hiR, Finset.card_insert_of_notMem hiU, h.card]

/-- Совпадение округлённых ключей — это близость на один шаг. -/
lemma of_key_eq {η ξ : ℝ} (hη : 0 < η) (hξ : 0 < ξ)
    (h : keyOf a y T t η ξ R = keyOf a y T t η ξ U) :
    KeyClose a y T t η ξ 1 R U where
  mom := fun l => by
    have hl : ⌊momK a y T R t l / η⌋ = ⌊momK a y T U t l / η⌋ :=
      congrFun (congrArg Prod.fst h) l
    simpa using abs_sub_le_of_floor_eq hη hl
  gram := fun l l' => by
    have hl : ⌊gramK2 a T R l l' / ξ⌋ = ⌊gramK2 a T U l l' / ξ⌋ :=
      congrFun (congrFun (congrArg (fun p => p.2.1) h) l) l'
    simpa using abs_sub_le_of_floor_eq hξ hl
  card := congrArg (fun p => p.2.2) h

/-- Близость влечёт гипотезы `ApproxBucket` с `Δ = √K·d·η`, `ζ = (d·ξ)·K`. -/
lemma toApproxBucket (hdet : (rowMat a T).det ≠ 0) {S : Finset ι} (hTS : ∀ l, T l ∈ S)
    (hQ : phi a y S t ≤ phi a y R t) {d : ℝ} (hd : 0 ≤ d) (hη : 0 ≤ η) (hξ : 0 ≤ ξ)
    (h : KeyClose a y T t η ξ d R S) :
    ApproxBucket a y S R t (Real.sqrt (Fintype.card κ : ℝ) * (d * η))
      ((d * ξ) * (Fintype.card κ : ℝ)) := by
  refine approxBucket_of_key hdet hTS hQ (by positivity) (by positivity) ?_
    (fun l l' => h.gram l l')
  have hterm : ∀ l ∈ (Finset.univ : Finset κ),
      (momK a y T R t l - momK a y T S t l) ^ 2 ≤ (d * η) ^ 2 := by
    intro l _
    have h1 := h.mom l
    have h2 := abs_nonneg (momK a y T R t l - momK a y T S t l)
    nlinarith [sq_abs (momK a y T R t l - momK a y T S t l)]
  have hsum : ∑ l, (momK a y T R t l - momK a y T S t l) ^ 2
      ≤ (Fintype.card κ : ℝ) * (d * η) ^ 2 := by
    calc ∑ l, (momK a y T R t l - momK a y T S t l) ^ 2
        ≤ ∑ _l : κ, (d * η) ^ 2 := Finset.sum_le_sum hterm
      _ = (Fintype.card κ : ℝ) * (d * η) ^ 2 := by simp [Finset.sum_const, mul_comm]
  have hsq : (Real.sqrt (Fintype.card κ : ℝ) * (d * η)) ^ 2
      = (Fintype.card κ : ℝ) * (d * η) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [hsq]; exact hsum

end KeyClose

/-! ### Усечение: один представитель на ключ -/

/-- Представитель ключа `k` в семействе `F` — набор с наибольшим значением `val`. -/
noncomputable def repOf (val : Finset ι → ℝ) (key : Finset ι → (κ → ℤ) × (κ → κ → ℤ) × ℕ)
    (F : Finset (Finset ι)) (k : (κ → ℤ) × (κ → κ → ℤ) × ℕ) : Finset ι :=
  if h : (F.filter (fun U => key U = k)).Nonempty then
    ((F.filter (fun U => key U = k)).exists_max_image val h).choose
  else ∅

variable {val : Finset ι → ℝ} {key : Finset ι → (κ → ℤ) × (κ → κ → ℤ) × ℕ}
variable {F : Finset (Finset ι)} {U : Finset ι}

lemma repOf_spec (hU : U ∈ F) :
    repOf val key F (key U) ∈ F ∧ key (repOf val key F (key U)) = key U
      ∧ val U ≤ val (repOf val key F (key U)) := by
  have hne : ((F.filter (fun V => key V = key U))).Nonempty :=
    ⟨U, Finset.mem_filter.mpr ⟨hU, rfl⟩⟩
  have hspec := ((F.filter (fun V => key V = key U)).exists_max_image val hne).choose_spec
  rw [repOf, dif_pos hne]
  obtain ⟨hmem, hmax⟩ := hspec
  have hmem' := Finset.mem_filter.mp hmem
  exact ⟨hmem'.1, hmem'.2, hmax U (Finset.mem_filter.mpr ⟨hU, rfl⟩)⟩

/-- Усечённое семейство: по одному представителю на встретившийся ключ. -/
noncomputable def prune (val : Finset ι → ℝ)
    (key : Finset ι → (κ → ℤ) × (κ → κ → ℤ) × ℕ) (F : Finset (Finset ι)) :
    Finset (Finset ι) :=
  F.image (fun U => repOf val key F (key U))

lemma prune_subset : prune val key F ⊆ F := by
  intro R hR
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hR
  exact (repOf_spec hU).1

lemma mem_prune (hU : U ∈ F) : repOf val key F (key U) ∈ prune val key F :=
  Finset.mem_image.mpr ⟨U, hU, rfl⟩

lemma card_prune_le : (prune val key F).card ≤ (F.image key).card := by
  have hsub : prune val key F ⊆ (F.image key).image (repOf val key F) := by
    intro R hR
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hR
    exact Finset.mem_image.mpr ⟨key U, Finset.mem_image.mpr ⟨U, hU, rfl⟩, rfl⟩
  exact le_trans (Finset.card_le_card hsub) (Finset.card_image_le)

/-! ### Сама динамика -/

/-- **Таблица динамики.** `base` — обязательные строки (якоря), список `L` —
строки-кандидаты. На каждом шаге берём «не брать» и «взять» (если строка
допущена фильтром `adm`) и усекаем до одного представителя на ключ. -/
noncomputable def survivors (val : Finset ι → ℝ)
    (key : Finset ι → (κ → ℤ) × (κ → κ → ℤ) × ℕ) (adm : ι → Bool) (base : Finset ι) :
    List ι → Finset (Finset ι)
  | [] => {base}
  | i :: rest =>
      prune val key
        (if adm i then
            survivors val key adm base rest
              ∪ (survivors val key adm base rest).image (insert i)
          else survivors val key adm base rest)

lemma survivors_cons (val : Finset ι → ℝ)
    (key : Finset ι → (κ → ℤ) × (κ → κ → ℤ) × ℕ) (adm : ι → Bool) (base : Finset ι)
    (i : ι) (rest : List ι) :
    survivors val key adm base (i :: rest)
      = prune val key
        (if adm i then
            survivors val key adm base rest
              ∪ (survivors val key adm base rest).image (insert i)
          else survivors val key adm base rest) := rfl

/-- **Что лежит в таблице.** Каждый выживший содержит `base`, лежит в
обработанных строках и состоит из допущенных фильтром. -/
theorem survivors_mem (val : Finset ι → ℝ)
    (key : Finset ι → (κ → ℤ) × (κ → κ → ℤ) × ℕ) (adm : ι → Bool) (base : Finset ι) :
    ∀ (L : List ι), ∀ R ∈ survivors val key adm base L,
      base ⊆ R ∧ R ⊆ base ∪ L.toFinset ∧ ∀ i ∈ R, i ∉ base → adm i := by
  intro L
  induction L with
  | nil =>
      intro R hR
      rw [survivors, Finset.mem_singleton] at hR
      subst hR
      refine ⟨Finset.Subset.refl _, ?_, fun i hi hni => absurd hi hni⟩
      simp
  | cons i rest ih =>
      intro R hR
      rw [survivors_cons] at hR
      have hRE := prune_subset hR
      have hgrow : ∀ V ∈ survivors val key adm base rest,
          base ⊆ V ∧ V ⊆ base ∪ (i :: rest).toFinset ∧ ∀ j ∈ V, j ∉ base → adm j := by
        intro V hV
        obtain ⟨h1, h2, h3⟩ := ih V hV
        refine ⟨h1, ?_, h3⟩
        refine le_trans h2 ?_
        simp only [List.toFinset_cons]
        exact Finset.union_subset_union_right (Finset.subset_insert _ _)
      by_cases hadm : adm i
      · rw [if_pos hadm] at hRE
        rcases Finset.mem_union.mp hRE with h | h
        · exact hgrow R h
        · obtain ⟨R', hR', rfl⟩ := Finset.mem_image.mp h
          obtain ⟨h1, h2, h3⟩ := ih R' hR'
          refine ⟨le_trans h1 (Finset.subset_insert _ _), ?_, ?_⟩
          · intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · simp [List.toFinset_cons]
            · have := h2 hx
              rcases Finset.mem_union.mp this with hb | hr
              · exact Finset.mem_union_left _ hb
              · exact Finset.mem_union_right _ (by simp [List.toFinset_cons, hr])
          · intro j hj hjb
            rcases Finset.mem_insert.mp hj with rfl | hj
            · exact hadm
            · exact h3 j hj hjb
      · rw [if_neg hadm] at hRE
        exact hgrow R hRE

/-- **Инвариант динамики.** Для любого допустимого `U` в таблице есть набор `R`
с не меньшим `Q_t` и ключом, отличающимся не более чем на `|L|` ширин корзины. -/
theorem survivors_spec {η ξ : ℝ} (hη : 0 < η) (hξ : 0 < ξ) (adm : ι → Bool)
    (base : Finset ι) :
    ∀ (L : List ι), L.Nodup → (∀ i ∈ L, i ∉ base) →
    ∀ U : Finset ι, base ⊆ U → U ⊆ base ∪ L.toFinset → (∀ i ∈ U, i ∉ base → adm i) →
    ∃ R ∈ survivors (fun V => phi a y V t) (keyOf a y T t η ξ) adm base L,
      KeyClose a y T t η ξ (L.length : ℝ) R U ∧ phi a y U t ≤ phi a y R t := by
  intro L
  induction L with
  | nil =>
      intro _ _ U hbU hU _
      have hUb : U = base := by
        refine Finset.Subset.antisymm ?_ hbU
        simpa using hU
      subst hUb
      refine ⟨U, by rw [survivors]; exact Finset.mem_singleton_self _, ?_, le_refl _⟩
      simpa using KeyClose.rfl' (a := a) (y := y) (T := T) (t := t) hη.le hξ.le U
  | cons i rest ih =>
      intro hnd hdisj U hbU hU hadmU
      have hndrest : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hirest : i ∉ rest := (List.nodup_cons.mp hnd).1
      have hib : i ∉ base := hdisj i (List.mem_cons_self ..)
      have hdisjrest : ∀ j ∈ rest, j ∉ base := fun j hj => hdisj j (List.mem_cons_of_mem _ hj)
      set F := survivors (fun V => phi a y V t) (keyOf a y T t η ξ) adm base rest with hF
      set E := (if adm i then F ∪ F.image (insert i) else F) with hE
      -- каждый элемент `F` не содержит `i`
      have hnotin : ∀ V ∈ F, i ∉ V := by
        intro V hV hiV
        obtain ⟨_, h2, _⟩ := survivors_mem _ _ adm base rest V hV
        rcases Finset.mem_union.mp (h2 hiV) with hb | hr
        · exact hib hb
        · exact hirest (List.mem_toFinset.mp hr)
      by_cases hiU : i ∈ U
      · -- шаг «взять»
        have hadmi : adm i := hadmU i hiU hib
        have hU0b : base ⊆ U.erase i := by
          intro x hx
          exact Finset.mem_erase.mpr ⟨fun hxi => hib (hxi ▸ hx), hbU hx⟩
        have hU0 : U.erase i ⊆ base ∪ rest.toFinset := by
          intro x hx
          have hx' := Finset.mem_of_mem_erase hx
          have hxi : x ≠ i := (Finset.mem_erase.mp hx).1
          rcases Finset.mem_union.mp (hU hx') with hb | hr
          · exact Finset.mem_union_left _ hb
          · refine Finset.mem_union_right _ ?_
            have := List.mem_toFinset.mp hr
            rcases List.mem_cons.mp this with rfl | h
            · exact absurd rfl hxi
            · exact List.mem_toFinset.mpr h
        obtain ⟨R₀, hR₀, hclose, hval⟩ := ih hndrest hdisjrest (U.erase i) hU0b hU0
          (fun j hj hjb => hadmU j (Finset.mem_of_mem_erase hj) hjb)
        have hiR₀ : i ∉ R₀ := hnotin R₀ hR₀
        have hmemE : insert i R₀ ∈ E := by
          rw [hE, if_pos hadmi]
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨R₀, hR₀, rfl⟩)
        obtain ⟨hmem, hkey, hge⟩ := repOf_spec (val := fun V => phi a y V t)
          (key := keyOf a y T t η ξ) (F := E) hmemE
        refine ⟨repOf (fun V => phi a y V t) (keyOf a y T t η ξ) E
          (keyOf a y T t η ξ (insert i R₀)), ?_, ?_, ?_⟩
        · rw [survivors_cons, ← hF, ← hE]
          exact mem_prune hmemE
        · have h1 : KeyClose a y T t η ξ 1
              (repOf (fun V => phi a y V t) (keyOf a y T t η ξ) E
                (keyOf a y T t η ξ (insert i R₀))) (insert i R₀) :=
            KeyClose.of_key_eq hη hξ hkey
          have h2 : KeyClose a y T t η ξ (rest.length : ℝ) (insert i R₀) U := by
            have := KeyClose.insert' (i := i) hiR₀ (Finset.notMem_erase i U) hclose
            rwa [Finset.insert_erase hiU] at this
          have := h1.trans h2
          have hlen : (1 : ℝ) + (rest.length : ℝ) = ((i :: rest).length : ℝ) := by
            simp [List.length_cons]; ring
          rwa [hlen] at this
        · have hins : phi a y (insert i R₀) t
              = (dotp (a i) t - y i) ^ 2 + phi a y R₀ t := phi_insert hiR₀
          have hinsU : phi a y U t
              = (dotp (a i) t - y i) ^ 2 + phi a y (U.erase i) t := by
            have := phi_insert (a := a) (y := y) (t := t) (Finset.notMem_erase i U)
            rwa [Finset.insert_erase hiU] at this
          linarith [hins, hinsU, hval, hge]
      · -- шаг «не брать»
        have hU' : U ⊆ base ∪ rest.toFinset := by
          intro x hx
          rcases Finset.mem_union.mp (hU hx) with hb | hr
          · exact Finset.mem_union_left _ hb
          · refine Finset.mem_union_right _ ?_
            have := List.mem_toFinset.mp hr
            rcases List.mem_cons.mp this with rfl | h
            · exact absurd hx hiU
            · exact List.mem_toFinset.mpr h
        obtain ⟨R₀, hR₀, hclose, hval⟩ := ih hndrest hdisjrest U hbU hU' hadmU
        have hmemE : R₀ ∈ E := by
          rw [hE]
          by_cases hadmi : adm i
          · rw [if_pos hadmi]; exact Finset.mem_union_left _ hR₀
          · rw [if_neg hadmi]; exact hR₀
        obtain ⟨hmem, hkey, hge⟩ := repOf_spec (val := fun V => phi a y V t)
          (key := keyOf a y T t η ξ) (F := E) hmemE
        refine ⟨repOf (fun V => phi a y V t) (keyOf a y T t η ξ) E
          (keyOf a y T t η ξ R₀), ?_, ?_, ?_⟩
        · rw [survivors_cons, ← hF, ← hE]
          exact mem_prune hmemE
        · have h1 := KeyClose.of_key_eq (a := a) (y := y) (T := T) (t := t) hη hξ hkey
          have := h1.trans hclose
          have hlen : (1 : ℝ) + (rest.length : ℝ) = ((i :: rest).length : ℝ) := by
            simp [List.length_cons]; ring
          rwa [hlen] at this
        · linarith [hval, hge]

/-! ### Размер таблицы -/

/-- Внутри усечённого семейства ключ инъективен — в этом и смысл усечения. -/
lemma key_injOn_prune (val : Finset ι → ℝ)
    (key : Finset ι → (κ → ℤ) × (κ → κ → ℤ) × ℕ) (F : Finset (Finset ι)) :
    Set.InjOn key ↑(prune val key F) := by
  intro R₁ h₁ R₂ h₂ heq
  obtain ⟨U₁, hU₁, rfl⟩ := Finset.mem_image.mp h₁
  obtain ⟨U₂, hU₂, rfl⟩ := Finset.mem_image.mp h₂
  have e₁ := (repOf_spec (val := val) (key := key) hU₁).2.1
  have e₂ := (repOf_spec (val := val) (key := key) hU₂).2.1
  have : key U₁ = key U₂ := by rw [← e₁, ← e₂]; exact heq
  rw [this]

lemma key_injOn_survivors (val : Finset ι → ℝ)
    (key : Finset ι → (κ → ℤ) × (κ → κ → ℤ) × ℕ) (adm : ι → Bool) (base : Finset ι) :
    ∀ L : List ι, Set.InjOn key ↑(survivors val key adm base L) := by
  intro L
  cases L with
  | nil =>
      intro R₁ h₁ R₂ h₂ _
      rw [survivors] at h₁ h₂
      have e₁ : R₁ = base := Finset.mem_singleton.mp (by simpa using h₁)
      have e₂ : R₂ = base := Finset.mem_singleton.mp (by simpa using h₂)
      rw [e₁, e₂]
  | cons i rest =>
      rw [survivors_cons]
      exact key_injOn_prune _ _ _

/-- **Размер таблицы не больше числа ключей в коробке.** Это ровно оценка
`StateCount.lean`, но теперь про конкретную динамику. -/
theorem survivors_card_le {S : Finset ι} (hmax : MaxVol a S T)
    (hdet : (rowMat a T).det ≠ 0) {η ξ : ℝ} (hη : 0 < η) (hξ : 0 < ξ)
    (adm : ι → Bool) (base : Finset ι) (L : List ι)
    (hbase : base ⊆ S) (hL : ∀ i ∈ L.toFinset, i ∈ S) :
    (survivors (fun V => phi a y V t) (keyOf a y T t η ξ) adm base L).card
      ≤ (keyBox (κ := κ) ⌈Real.sqrt ((S.card : ℝ) * phi a y S t) / η⌉
          ⌈(S.card : ℝ) / ξ⌉ S.card).card := by
  rw [← Finset.card_image_of_injOn
    (key_injOn_survivors (fun V => phi a y V t) (keyOf a y T t η ξ) adm base L)]
  refine Finset.card_le_card ?_
  intro k hk
  obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨_, hsub, _⟩ := survivors_mem _ _ adm base L R hR
  refine keyOf_mem_keyBox (y := y) (t := t) hmax hdet hη hξ ?_
  intro x hx
  rcases Finset.mem_union.mp (hsub hx) with hb | hl
  · exact hbase hb
  · exact hL x hl

/-! ### Условие обусловленности наследуется подмножествами с якорями -/

/-- Значение растёт с носителем: `F(base) ≤ F(V)` при `base ⊆ V`. -/
lemma phi_normal_mono {base V : Finset ι} {thb thv : κ → ℝ} (hsub : base ⊆ V)
    (hnb : IsNormal a y base thb) :
    phi a y base thb ≤ phi a y V thv :=
  le_trans (phi_min hnb thv) (phi_mono hsub thv)

lemma gram_cond_of_subset {S U : Finset ι} {cl : ι → Bool} {γ : ℝ} (hγ : 0 ≤ γ)
    (hUS : U ⊆ S) (hanchU : anchorSet cl S ⊆ U)
    (hcond : ∀ v, γ * gram a S v ≤ gram a (anchorSet cl S) v) :
    ∀ v : κ → ℝ, γ * gram a U v ≤ gram a (anchorSet cl U) v := by
  intro v
  have h1 : gram a U v ≤ gram a S v := gram_mono hUS v
  have h2 : anchorSet cl S ⊆ anchorSet cl U := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hanchU hi, hi'.2⟩
  have h3 : gram a (anchorSet cl S) v ≤ gram a (anchorSet cl U) v := gram_mono h2 v
  nlinarith [hcond v, h1, h3, hγ]

/-! ### Итог: шаг FPTAS целиком -/

/-- **Динамика возвращает `(1−2ε)`-приближение.**

Гипотезы — то, чем располагает алгоритм:

* `hdet`, `hTA` — `T` невырожденная `K`-ка строк носителя `A`
  (алгоритм перебирает `K`-ки, это уже оплаченный множитель `O(n^K)`);
* `hgap`, `hcal`, `hErr` — калибровка узла и округления (§11.8);
* `hfilter` — фильтр порога `−θ₀` допускает ровно те строки, которые
  разрешены (`node_filter_admits` гарантирует, что оптимум среди них);
* `hTb`, `hdetBase` — в `base` (якорях) есть невырожденная `K`-ка строк.
  Отсюда у каждого набора динамики есть неподвижная точка
  (`exists_isNormal_of_det`, `Factor/NormalExists.lean`): это свойство
  **входа**, а не предположение о промежуточных объектах алгоритма. Оттуда же
  следует существование `thA`, так что гипотеза `hnormA` лишь именует
  неподвижную точку `A`, а не постулирует её.

Вывод: среди выживших есть `R` с `F_LO(R) ≥ (1−2ε)·F(Ā)`. -/
theorem lo_fptas_step {S A base : Finset ι} {cl : ι → Bool} {thA : κ → ℝ}
    {η ξ γ ε θ₀ : ℝ} {L : List ι}
    (hdet : (rowMat a T).det ≠ 0) (hTA : ∀ l, T l ∈ A)
    (hη : 0 < η) (hξ : 0 < ξ) (hθ₀ : 0 ≤ θ₀)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (adm : ι → Bool)
    (hnd : L.Nodup) (hdisj : ∀ i ∈ L, i ∉ base)
    (hbA : base ⊆ A) (hAL : A ⊆ base ∪ L.toFinset)
    (hadmA : ∀ i ∈ A, i ∉ base → adm i)
    (hnormA : IsNormal a y A thA)
    (hAS : A ⊆ S) (hbaseS : base ⊆ S) (hLS : ∀ i ∈ L.toFinset, i ∈ S)
    (hanch : ∀ i, ¬ cl i → y i = 0)
    (hanchBase : anchorSet cl S ⊆ base) (hbaseAnch : ∀ i ∈ base, ¬ cl i)
    (hcondS : ∀ v : κ → ℝ, γ * gram a S v ≤ gram a (anchorSet cl S) v)
    (hadmFilter : ∀ i, adm i → -θ₀ ≤ y i - dotp (a i) t)
    {Tb : κ → ι} (hTb : ∀ l, Tb l ∈ base) (hdetBase : (rowMat a Tb).det ≠ 0)
    (hζ2 : 2 * (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ)) < 1)
    (hgap : (phi a y A t - phi a y A thA)
      + bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
        (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
        (phi a y A t - phi a y A thA) ≤ θ₀ ^ 2)
    (hErr : bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
      (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
      (phi a y A t - phi a y A thA) ≤ ε * phi a y A thA)
    (hcalA : 256 * (S.card : ℝ) * θ₀ ^ 2
      ≤ ε ^ 2 * γ * (phi a y A thA
        - bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
          (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
          (phi a y A t - phi a y A thA))) :
    ∃ R ∈ survivors (fun V => phi a y V t) (keyOf a y T t η ξ) adm base L,
      R.card = A.card ∧
      ∀ t' : κ → ℝ, (1 - 2 * ε) * phi a y A thA ≤ psiC a y cl R t' := by
  obtain ⟨R, hR, hclose, hQ⟩ :=
    survivors_spec (a := a) (y := y) (T := T) (t := t) hη hξ adm base L hnd hdisj A
      hbA hAL hadmA
  obtain ⟨hbaseR, hRsub, hRadm⟩ := survivors_mem _ _ adm base L R hR
  -- неподвижная точка `R` существует: в нём лежит невырожденная `K`-ка якорей
  obtain ⟨thR, hnormR⟩ :=
    exists_isNormal_of_det (a := a) (V := R) (fun l => hbaseR (hTb l)) hdetBase y
  have hRS : R ⊆ S := by
    intro x hx
    rcases Finset.mem_union.mp (hRsub hx) with hb | hl
    · exact hbaseS hb
    · exact hLS x hl
  have hb : ApproxBucket a y A R t
      (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
      (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ)) :=
    hclose.toApproxBucket hdet hTA hQ (by positivity) hη.le hξ.le
  have hanchR : ∀ i ∈ R, ¬ cl i → y i = 0 := fun i _ hc => hanch i hc
  have hcondR : ∀ v : κ → ℝ, γ * gram a R v ≤ gram a (anchorSet cl R) v :=
    gram_cond_of_subset hγ.le hRS (le_trans hanchBase hbaseR) hcondS
  have hfilterR : ∀ i ∈ R, cl i → -θ₀ ≤ y i - dotp (a i) t := by
    intro i hi hc
    by_cases hib : i ∈ base
    · exact absurd hc (by simpa using hbaseAnch i hib)
    · exact hadmFilter i (hRadm i hi hib)
  -- калибровка для `R`: `|R| ≤ |S|` и `F(R) ≥ F(Ā) − err` (`phi_normal_ge_of_approxBucket'`)
  have hcalR : 256 * (R.card : ℝ) * θ₀ ^ 2 ≤ ε ^ 2 * γ * phi a y R thR := by
    have hcard : (R.card : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hRS
    have hFR := phi_normal_ge_of_approxBucket' hb (by positivity) (by positivity)
      hζ2 hnormA hnormR
    have h1 : 256 * (R.card : ℝ) * θ₀ ^ 2 ≤ 256 * (S.card : ℝ) * θ₀ ^ 2 := by
      nlinarith [sq_nonneg θ₀, hcard]
    have h2 : ε ^ 2 * γ * (phi a y A thA
        - bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
          (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
          (phi a y A t - phi a y A thA))
        ≤ ε ^ 2 * γ * phi a y R thR := by
      have hnn : (0:ℝ) ≤ ε ^ 2 * γ := by positivity
      nlinarith [hFR, hnn]
    linarith
  refine ⟨R, hR, hclose.card, fun t' => ?_⟩
  exact psiC_ge_of_approxBucket_calibrated hb hnormA hnormR (by positivity) (by positivity)
    hζ2 hθ₀ hγ hγ1 hε hε1 hanchR hcondR hfilterR hgap hcalR hErr t'

/-! ### Сквозная теорема: сетка + фильтр + динамика -/

/-- **Гарантия приближения long-only при любом `K ≥ 1`, одним утверждением**
(содержательно новое — `K ≥ 2`; при `K = 1` работает и префиксное правило EGP).

Берём носитель `A` (в приложении — самосогласованный носитель оптимума,
который по Теореме X (`Reduction.lean`) реализует `OPT_LO`), его
максимально-объёмную `K`-ку `T` и сетку с шагом
`s = 2√(ε_g·V/(K·C))`, `ε_g = ε²γ/(1024n)`. Тогда **в сетке есть узел**, в
котором

* фильтр порога `−θ₀`, `θ₀ = ε√(γV)/(16√n)`, допускает все строки `A`;
* динамика `survivors` возвращает набор `R` **той же мощности**, что `A`
  (то есть допустимый по ограничению на число активов), с
  `F_LO(R) ≥ (1−2ε)·F(Ā)`.

Номера узлов ограничены величиной без данных входа, размер таблицы — числом
ключей коробки `keyBox` (`survivors_card_le`). Сама теорема о времени не
говорит: при выборе `η = θ₀/(8√K·M)`, `ξ = 1/(8MK)` обе величины выписаны явно в
`lo_fptas_cost` (`Factor/Cost.lean`) — это и даёт полиномиальность от `M`, `n`,
`1/ε` и `1/√γ` при фиксированном `K` (без модели вычислений, §16 заметки 7). -/
theorem lo_fptas {S A base : Finset ι} {cl : ι → Bool} {thA : κ → ℝ}
    {η ξ γ ε V C s : ℝ} {n : ℕ} {L : List ι}
    (hmax : MaxVol a A T) (hdet : (rowMat a T).det ≠ 0)
    (hnormA : IsNormal a y A thA)
    (hC : (A.card * Fintype.card κ : ℝ) ≤ C) (hCpos : 0 < C)
    (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hV : 0 < V)
    (hVF : V ≤ phi a y A thA) (hFV : phi a y A thA ≤ 2 * V)
    (hKc : 0 < (Fintype.card κ : ℝ)) (hn : 0 < n)
    (hnS : 2 * (S.card : ℝ) ≤ (n : ℝ))
    (hs : s = 2 * Real.sqrt ((ε ^ 2 * γ / (1024 * (n : ℝ))) * V
      / ((Fintype.card κ : ℝ) * C)))
    (hselfA : ∀ i ∈ A, cl i → 0 ≤ y i - dotp (a i) thA)
    (hη : 0 < η) (hξ : 0 < ξ)
    (hnd : L.Nodup) (hdisj : ∀ i ∈ L, i ∉ base)
    (hbA : base ⊆ A) (hAL : A ⊆ base ∪ L.toFinset)
    (hAS : A ⊆ S) (hbaseS : base ⊆ S) (hLS : ∀ i ∈ L.toFinset, i ∈ S)
    (hanch : ∀ i, ¬ cl i → y i = 0)
    (hanchBase : anchorSet cl S ⊆ base) (hbaseAnch : ∀ i ∈ base, ¬ cl i)
    (hcondS : ∀ v : κ → ℝ, γ * gram a S v ≤ gram a (anchorSet cl S) v)
    {Tb : κ → ι} (hTb : ∀ l, Tb l ∈ base) (hdetBase : (rowMat a Tb).det ≠ 0)
    (hηθ : 8 * (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
      ≤ theta0 ε γ V n)
    (hζ8 : ((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ) ≤ 1/8) :
    ∃ z : κ → ℤ,
      (∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C
        / (2 * (ε ^ 2 * γ / (1024 * (n : ℝ))))) + 1 / 2) ∧
      ∀ t : κ → ℝ, (∀ l, dotp (a (T l)) t = y (T l) + s * (z l : ℝ)) →
        ∃ adm : ι → Bool,
          (∀ i, adm i → -theta0 ε γ V n ≤ y i - dotp (a i) t) ∧
          (∀ i ∈ A, i ∉ base → adm i) ∧
          ∃ R ∈ survivors (fun W => phi a y W t) (keyOf a y T t η ξ) adm base L,
            R.card = A.card ∧
            ∀ t' : κ → ℝ, (1 - 2 * ε) * phi a y A thA ≤ psiC a y cl R t' := by
  classical
  obtain ⟨z, hz1, hz2⟩ := exists_node_closing_step_half (a := a) (y := y) (cl := cl)
    (S := A) (T := T) (th := thA) hmax hdet hnormA hC hCpos hε hγ hV hVF hFV hKc hn hs
    hselfA
  refine ⟨z, hz1, fun t ht => ?_⟩
  obtain ⟨hgapA, hadmitA⟩ := hz2 t ht
  refine ⟨fun i => decide (-theta0 ε γ V n ≤ y i - dotp (a i) t), ?_, ?_, ?_⟩
  · intro i hi
    exact of_decide_eq_true hi
  · intro i hiA hib
    refine decide_eq_true ?_
    by_cases hc : cl i
    · exact hadmitA i hiA hc
    · exact absurd (hanchBase (Finset.mem_filter.mpr ⟨hAS hiA, by simpa using hc⟩)) hib
  · have hgap0 : 0 ≤ phi a y A t - phi a y A thA := by
      have := phi_min hnormA t; linarith
    have hθ0 : 0 ≤ theta0 ε γ V n := theta0_nonneg hε.le
    -- цена округления не больше половины запаса `θ₀²`
    have hr1 : bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
        (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
        (phi a y A t - phi a y A thA) ≤ theta0 ε γ V n ^ 2 / 2 :=
      bucketErr_le_half (by positivity) (by positivity) hθ0 hηθ hζ8 hgap0 hgapA
    -- и не больше `ε·F(Ā)`: `θ₀²/2 = ε²γV/(512n) ≤ εF`
    have hr2 : bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
        (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
        (phi a y A t - phi a y A thA) ≤ ε * phi a y A thA := by
      refine le_trans hr1 ?_
      rw [theta0_sq (by positivity) hn]
      have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hF : 0 ≤ phi a y A thA := phi_nonneg a y A thA
      have key : ε ^ 2 * (γ * V) ≤ ε * phi a y A thA := by
        have hεγ : ε * γ ≤ 1 := by nlinarith [hε.le, hγ.le, hε1, hγ1]
        have h1 : ε ^ 2 * (γ * V) ≤ ε * V := by
          have hmul := mul_le_mul_of_nonneg_left hεγ (mul_nonneg hε.le hV.le)
          nlinarith [hmul]
        have h2 : ε * V ≤ ε * phi a y A thA := mul_le_mul_of_nonneg_left hVF hε.le
        linarith
      rw [div_div, div_le_iff₀ (by positivity)]
      nlinarith [key, mul_nonneg hε.le hF, hn1]
    -- калибровка: `256|S|θ₀² = |S|·ε²γV/n ≤ ε²γV/2 ≤ ε²γF(Ā)/2 ≤ ε²γ(F(Ā) − err)`
    have hcalA : 256 * (S.card : ℝ) * theta0 ε γ V n ^ 2
        ≤ ε ^ 2 * γ * (phi a y A thA
          - bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
            (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
            (phi a y A t - phi a y A thA)) := by
      have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hF : 0 ≤ phi a y A thA := phi_nonneg a y A thA
      have hlhs : 256 * (S.card : ℝ) * theta0 ε γ V n ^ 2
          = (S.card : ℝ) * (ε ^ 2 * (γ * V)) / (n : ℝ) := by
        rw [theta0_sq (by positivity) hn]; field_simp
      have hstep : (S.card : ℝ) * (ε ^ 2 * (γ * V)) / (n : ℝ)
          ≤ ε ^ 2 * (γ * V) / 2 := by
        rw [div_le_div_iff₀ hn0 (by norm_num)]
        nlinarith [hnS, mul_nonneg (mul_nonneg (sq_nonneg ε) hγ.le) hV.le, hn0]
      have hgoal : ε ^ 2 * (γ * V) / 2
          ≤ ε ^ 2 * γ * (phi a y A thA
            - bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
              (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
              (phi a y A t - phi a y A thA)) := by
        have hhalf : phi a y A thA / 2 ≤ phi a y A thA
            - bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
              (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
              (phi a y A t - phi a y A thA) := by
          nlinarith [hr2, hε1, hF]
        have hnn : (0:ℝ) ≤ ε ^ 2 * γ := by positivity
        nlinarith [hVF, hhalf, hnn, hF]
      linarith
    exact lo_fptas_step hdet (fun l => hmax.1 l) hη hξ (theta0_nonneg hε.le) hγ hγ1 hε
      (by linarith)
      _ hnd hdisj hbA hAL
      (fun i hiA hib => decide_eq_true (by
        by_cases hc : cl i
        · exact hadmitA i hiA hc
        · exact absurd (hanchBase (Finset.mem_filter.mpr ⟨hAS hiA, by simpa using hc⟩)) hib))
      hnormA hAS hbaseS hLS hanch hanchBase hbaseAnch hcondS
      (fun i hi => of_decide_eq_true hi) hTb hdetBase (by linarith) (by linarith) hr2 hcalA

/-! ### `δ`-цепочка: шаг и сквозная теорема без `γ`

То же самое, но калибровка идёт через покрытие нарушителей относительно
якорей (`AnchorCover`, `Factor/Cover.lean`) с константой `c`, а шаг — через
Теорему Z″ (`psiC_ge_of_approxBucket_calibrated_block`). Отличия от
`lo_fptas_step` / `lo_fptas`:

* гипотезы на `γ` (`hcondS`) нет — вместо неё `AnchorCover … k c` на
  вселенной `S` и `|A| ≤ |base| + k` (активов в оптимуме не больше `k`);
* гипотезы `y = 0` на якорях (`hanch`) нет — Теорема Z″ её не требует;
* порог `θ₀ = √(εV/(8c))`, сетка с `ε_g = ε/(32c)`; параметр `n` (граница на
  размер вселенной) больше не нужен вовсе.

Покрытие вселенной переносится на набор `R`, который вернула динамика,
леммой `coveredBy_of_anchorCover`: `R` содержит якоря, лежит во вселенной и
содержит не больше `k` зажатых строк, потому что `|R| = |A|`. -/

/-- **Шаг динамики в `δ`-цепочке.** Среди выживших есть `R` той же мощности,
что `A`, с `F_LO(R) ≥ (1−2ε)·F(Ā)`. -/
theorem lo_fptas_step_block {S A base : Finset ι} {cl : ι → Bool} {thA : κ → ℝ}
    {η ξ ε θ₀ c : ℝ} {k : ℕ} {L : List ι}
    (hdet : (rowMat a T).det ≠ 0) (hTA : ∀ l, T l ∈ A)
    (hη : 0 < η) (hξ : 0 < ξ) (hθ₀ : 0 ≤ θ₀) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (adm : ι → Bool)
    (hnd : L.Nodup) (hdisj : ∀ i ∈ L, i ∉ base)
    (hbA : base ⊆ A) (hAL : A ⊆ base ∪ L.toFinset)
    (hadmA : ∀ i ∈ A, i ∉ base → adm i)
    (hnormA : IsNormal a y A thA)
    (hbaseS : base ⊆ S) (hLS : ∀ i ∈ L.toFinset, i ∈ S)
    (hbaseAnch : ∀ i ∈ base, ¬ cl i)
    (hcov : AnchorCover a y cl S base k c) (hk : A.card ≤ base.card + k)
    (hadmFilter : ∀ i, adm i → -θ₀ ≤ y i - dotp (a i) t)
    {Tb : κ → ι} (hTb : ∀ l, Tb l ∈ base) (hdetBase : (rowMat a Tb).det ≠ 0)
    (hζ2 : 2 * (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ)) < 1)
    (hgap : (phi a y A t - phi a y A thA)
      + bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
        (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
        (phi a y A t - phi a y A thA) ≤ θ₀ ^ 2)
    (hErr : bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
      (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
      (phi a y A t - phi a y A thA) ≤ ε * phi a y A thA)
    (hcalA : c * (2 * θ₀) ^ 2
      ≤ ε * (phi a y A thA
        - bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
          (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
          (phi a y A t - phi a y A thA))) :
    ∃ R ∈ survivors (fun V => phi a y V t) (keyOf a y T t η ξ) adm base L,
      R.card = A.card ∧
      ∀ t' : κ → ℝ, (1 - 2 * ε) * phi a y A thA ≤ psiC a y cl R t' := by
  obtain ⟨R, hR, hclose, hQ⟩ :=
    survivors_spec (a := a) (y := y) (T := T) (t := t) hη hξ adm base L hnd hdisj A
      hbA hAL hadmA
  obtain ⟨hbaseR, hRsub, hRadm⟩ := survivors_mem _ _ adm base L R hR
  obtain ⟨thR, hnormR⟩ :=
    exists_isNormal_of_det (a := a) (V := R) (fun l => hbaseR (hTb l)) hdetBase y
  have hRS : R ⊆ S := by
    intro x hx
    rcases Finset.mem_union.mp (hRsub hx) with hb | hl
    · exact hbaseS hb
    · exact hLS x hl
  have hb : ApproxBucket a y A R t
      (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
      (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ)) :=
    hclose.toApproxBucket hdet hTA hQ (by positivity) hη.le hξ.le
  have hfilterR : ∀ i ∈ R, cl i → -θ₀ ≤ y i - dotp (a i) t := by
    intro i hi hc
    by_cases hib : i ∈ base
    · exact absurd hc (by simpa using hbaseAnch i hib)
    · exact hadmFilter i (hRadm i hi hib)
  -- зажатых строк в `R` не больше `k`: `|R| = |A| ≤ |base| + k`
  have hkR : (clipSet cl R).card ≤ k := by
    have h1 := card_clipSet_le_of_base (cl := cl) hbaseR hbaseAnch
    have h2 : R.card = A.card := hclose.card
    omega
  -- калибровка для `R`: `c(2θ₀)² ≤ ε(F(Ā) − err) ≤ ε·F(R)`
  have hFR := phi_normal_ge_of_approxBucket' hb (by positivity) (by positivity)
    hζ2 hnormA hnormR
  have hcalR : c * (2 * θ₀) ^ 2 ≤ ε * phi a y R thR := by
    have := mul_le_mul_of_nonneg_left hFR hε.le
    linarith
  have hcovR : CoveredBy a y cl R (2 * θ₀) (ε * phi a y R thR) :=
    coveredBy_of_anchorCover hcov hbaseR hRS hbaseAnch hkR hcalR
  refine ⟨R, hR, hclose.card, fun t' => ?_⟩
  exact psiC_ge_of_approxBucket_calibrated_block hb hnormA hnormR (by positivity)
    (by positivity) hζ2 hθ₀ hε hε1 hfilterR hgap hcovR hErr t'

/-- **Гарантия приближения long-only при любом `K ≥ 1` в `δ`-цепочке, одним утверждением.**

Как `lo_fptas`, но без `γ`: вместо якорной гипотезы — покрытие нарушителей
вселенной относительно якорей с константой `c ≥ 1` (`AnchorCover`), порог
`θ₀ = √(εV/(8c))`, шаг сетки `s = 2√(ε_g·V/(K·C))` с `ε_g = ε/(32c)`.
Гипотез `y = 0` на якорях и `n ≥ 2|S|` нет.

Вывод тот же: в сетке есть узел, в котором фильтр порога `−θ₀` допускает все
строки `A`, а динамика возвращает набор `R` той же мощности с
`F_LO(R) ≥ (1−2ε)·F(Ā)`. Номера узлов не больше `√(K·C·16c/ε) + ½`; явные
границы на число узлов и размер таблицы при `η = θ₀/(8√K·M)`, `ξ = 1/(8MK)` —
`lo_fptas_cost_block` (`Factor/Cost.lean`). -/
theorem lo_fptas_block {S A base : Finset ι} {cl : ι → Bool} {thA : κ → ℝ}
    {η ξ ε V C c s : ℝ} {k : ℕ} {L : List ι}
    (hmax : MaxVol a A T) (hdet : (rowMat a T).det ≠ 0)
    (hnormA : IsNormal a y A thA)
    (hC : (A.card * Fintype.card κ : ℝ) ≤ C) (hCpos : 0 < C)
    (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hc : 1 ≤ c) (hV : 0 < V)
    (hVF : V ≤ phi a y A thA) (hFV : phi a y A thA ≤ 2 * V)
    (hKc : 0 < (Fintype.card κ : ℝ))
    (hs : s = 2 * Real.sqrt ((ε / (32 * c)) * V / ((Fintype.card κ : ℝ) * C)))
    (hselfA : ∀ i ∈ A, cl i → 0 ≤ y i - dotp (a i) thA)
    (hη : 0 < η) (hξ : 0 < ξ)
    (hnd : L.Nodup) (hdisj : ∀ i ∈ L, i ∉ base)
    (hbA : base ⊆ A) (hAL : A ⊆ base ∪ L.toFinset)
    (hAS : A ⊆ S) (hbaseS : base ⊆ S) (hLS : ∀ i ∈ L.toFinset, i ∈ S)
    (hanchBase : anchorSet cl S ⊆ base) (hbaseAnch : ∀ i ∈ base, ¬ cl i)
    (hcov : AnchorCover a y cl S base k c) (hk : A.card ≤ base.card + k)
    {Tb : κ → ι} (hTb : ∀ l, Tb l ∈ base) (hdetBase : (rowMat a Tb).det ≠ 0)
    (hηθ : 8 * (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
      ≤ theta0B ε V c)
    (hζ8 : ((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ) ≤ 1/8) :
    ∃ z : κ → ℤ,
      (∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C
        / (2 * (ε / (32 * c)))) + 1 / 2) ∧
      ∀ t : κ → ℝ, (∀ l, dotp (a (T l)) t = y (T l) + s * (z l : ℝ)) →
        ∃ adm : ι → Bool,
          (∀ i, adm i → -theta0B ε V c ≤ y i - dotp (a i) t) ∧
          (∀ i ∈ A, i ∉ base → adm i) ∧
          ∃ R ∈ survivors (fun W => phi a y W t) (keyOf a y T t η ξ) adm base L,
            R.card = A.card ∧
            ∀ t' : κ → ℝ, (1 - 2 * ε) * phi a y A thA ≤ psiC a y cl R t' := by
  classical
  have hcpos : 0 < c := by linarith
  obtain ⟨z, hz1, hz2⟩ := exists_node_closing_step_block (a := a) (y := y) (cl := cl)
    (S := A) (T := T) (th := thA) hmax hdet hnormA hC hCpos hε hcpos hV hVF hFV hKc hs
    hselfA
  refine ⟨z, hz1, fun t ht => ?_⟩
  obtain ⟨hgapA, hadmitA⟩ := hz2 t ht
  have hadmA : ∀ i ∈ A, i ∉ base → decide (-theta0B ε V c ≤ y i - dotp (a i) t) = true := by
    intro i hiA hib
    refine decide_eq_true ?_
    by_cases hcl : cl i
    · exact hadmitA i hiA hcl
    · exact absurd (hanchBase (Finset.mem_filter.mpr ⟨hAS hiA, by simpa using hcl⟩)) hib
  refine ⟨fun i => decide (-theta0B ε V c ≤ y i - dotp (a i) t), ?_, hadmA, ?_⟩
  · intro i hi
    exact of_decide_eq_true hi
  · have hgap0 : 0 ≤ phi a y A t - phi a y A thA := by
      have := phi_min hnormA t; linarith
    have hθ0 : 0 ≤ theta0B ε V c := theta0B_nonneg
    have hθsq : theta0B ε V c ^ 2 = ε * V / (8 * c) := theta0B_sq hε.le hV.le hcpos.le
    have hF : 0 ≤ phi a y A thA := phi_nonneg a y A thA
    -- цена округления не больше половины запаса `θ₀²`
    have hr1 : bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
        (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
        (phi a y A t - phi a y A thA) ≤ theta0B ε V c ^ 2 / 2 :=
      bucketErr_le_half (by positivity) (by positivity) hθ0 hηθ hζ8 hgap0 hgapA
    -- и не больше `ε·F(Ā)`: `θ₀²/2 = εV/(16c) ≤ εV ≤ εF`
    have hr2 : bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
        (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
        (phi a y A t - phi a y A thA) ≤ ε * phi a y A thA := by
      refine le_trans hr1 ?_
      rw [hθsq]
      have h1 : ε * V / (8 * c) / 2 ≤ ε * V := by
        rw [div_div, div_le_iff₀ (by positivity)]
        nlinarith [mul_pos hε hV]
      have h2 : ε * V ≤ ε * phi a y A thA := mul_le_mul_of_nonneg_left hVF hε.le
      linarith
    -- калибровка: `c(2θ₀)² = εV/2 ≤ εF(Ā)/2 ≤ ε(F(Ā) − err)`
    have hcalA : c * (2 * theta0B ε V c) ^ 2
        ≤ ε * (phi a y A thA
          - bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
            (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
            (phi a y A t - phi a y A thA)) := by
      have hlhs : c * (2 * theta0B ε V c) ^ 2 = ε * V / 2 := by
        rw [mul_pow, hθsq]; field_simp; ring
      have hhalf : phi a y A thA / 2 ≤ phi a y A thA
          - bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
            (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
            (phi a y A t - phi a y A thA) := by
        nlinarith [hr2, hε1, hF]
      rw [hlhs]
      nlinarith [hVF, hhalf, hε.le]
    have hgapT : (phi a y A t - phi a y A thA)
        + bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
          (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
          (phi a y A t - phi a y A thA) ≤ theta0B ε V c ^ 2 := by linarith
    exact lo_fptas_step_block hdet (fun l => hmax.1 l) hη hξ hθ0 hε (by linarith)
      _ hnd hdisj hbA hAL hadmA hnormA hbaseS hLS hbaseAnch hcov hk
      (fun i hi => of_decide_eq_true hi) hTb hdetBase (by linarith) hgapT hr2 hcalA

end SparseSharpe.Factor
