import SparseSharpe.Factor.AnchorBasis

set_option linter.style.header false

/-!
# Динамика с отбрасыванием по коробке ключей: размер таблицы для настоящего прогона

**Зачем.** Оценки размера таблицы `lo_fptas_cost` и `lo_fptas_cost_block`
(`Factor/Cost.lean`) доказаны для набора строк `S`, содержащего **все** строки прохода
`L`, с гипотезами `|S| ≤ N` и `φ_S(τ) ≤ 4V`. В настоящем прогоне `L` — все допущенные
фильтром активы, и обе гипотезы в общем случае неверны: у допущенного актива вне
оптимума невязка в узле может быть сколь угодно большой, и тогда `φ_S(τ) ≫ V`. Сама
гарантия от этого не зависит (размер таблицы в ней не участвует), но утверждение о
полиномиальном размере таблицы для `survivors` в Lean не было доказано для реального
прогона. В спецификации long-short (`SPEC_FPTAS_K.md`, §4) это закрыто правилом
«состояния, чей ключ вышел за коробку, отбрасываются»; в `survivors` и в
`SPEC_LO_K3.md` этого правила не было.

**Что здесь.** `survivorsBox` — та же динамика, но после каждого шага остаются только
наборы, чей ключ лежит в заданной коробке `box`. Доказано:

* `survivorsBox_card_le` — таблица не больше `|box| + 1` **при любом прогоне**;
* `survivorsBox_spec` — инвариант `survivors_spec` сохраняется, если коробка содержит
  ключи всех наборов, близких по ключу (с дрейфом `|L|`) к подмножествам носителя
  оптимума;
* `keyOf_mem_boxOf` — канонической коробке `boxOf` (она вычисляется по `V`, `N`, `η`,
  `ξ`, `|L|` и `ρ`, без знания оптимума) это условие выполнено, если на носителе
  оптимума `|cf| ≤ ρ`, `|Ā| ≤ N` и `φ_Ā(τ) ≤ 4V`.

Сквозные теоремы с `survivorsBox` и явной стоимостью — в `Factor/Main.lean`.
-/

namespace SparseSharpe.Factor

open Finset

set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {T : κ → ι} {t : κ → ℝ}

/-- Близость по ключу монотонна по допуску. -/
lemma KeyClose.mono {η ξ d d' : ℝ} {R U : Finset ι} (h : KeyClose a y T t η ξ d R U)
    (hdd : d ≤ d') (hη : 0 ≤ η) (hξ : 0 ≤ ξ) : KeyClose a y T t η ξ d' R U where
  mom := fun l => le_trans (h.mom l) (mul_le_mul_of_nonneg_right hdd hη)
  gram := fun l l' => le_trans (h.gram l l') (mul_le_mul_of_nonneg_right hdd hξ)
  card := h.card

/-- **Динамика с коробкой.** Как `survivors`, но на каждом шаге до усечения остаются
только наборы с ключом в `box`. -/
noncomputable def survivorsBox (val : Finset ι → ℝ)
    (key : Finset ι → (κ → ℤ) × (κ → κ → ℤ) × ℕ) (adm : ι → Bool)
    (box : Finset ((κ → ℤ) × (κ → κ → ℤ) × ℕ)) (base : Finset ι) :
    List ι → Finset (Finset ι)
  | [] => {base}
  | i :: rest =>
      prune val key
        ((if adm i then
            survivorsBox val key adm box base rest
              ∪ (survivorsBox val key adm box base rest).image (insert i)
          else survivorsBox val key adm box base rest).filter (fun U => key U ∈ box))

variable {val : Finset ι → ℝ} {key : Finset ι → (κ → ℤ) × (κ → κ → ℤ) × ℕ}

lemma survivorsBox_cons (val : Finset ι → ℝ)
    (key : Finset ι → (κ → ℤ) × (κ → κ → ℤ) × ℕ) (adm : ι → Bool)
    (box : Finset ((κ → ℤ) × (κ → κ → ℤ) × ℕ)) (base : Finset ι) (i : ι) (rest : List ι) :
    survivorsBox val key adm box base (i :: rest)
      = prune val key
        ((if adm i then
            survivorsBox val key adm box base rest
              ∪ (survivorsBox val key adm box base rest).image (insert i)
          else survivorsBox val key adm box base rest).filter (fun U => key U ∈ box)) := rfl

/-- Что лежит в таблице: как `survivors_mem`. -/
theorem survivorsBox_mem (val : Finset ι → ℝ)
    (key : Finset ι → (κ → ℤ) × (κ → κ → ℤ) × ℕ) (adm : ι → Bool)
    (box : Finset ((κ → ℤ) × (κ → κ → ℤ) × ℕ)) (base : Finset ι) :
    ∀ (L : List ι), ∀ R ∈ survivorsBox val key adm box base L,
      base ⊆ R ∧ R ⊆ base ∪ L.toFinset ∧ ∀ i ∈ R, i ∉ base → adm i := by
  intro L
  induction L with
  | nil =>
      intro R hR
      rw [survivorsBox, Finset.mem_singleton] at hR
      subst hR
      refine ⟨Finset.Subset.refl _, ?_, fun i hi hni => absurd hi hni⟩
      simp
  | cons i rest ih =>
      intro R hR
      rw [survivorsBox_cons] at hR
      have hRE := Finset.mem_of_mem_filter _ (prune_subset hR)
      have hgrow : ∀ V ∈ survivorsBox val key adm box base rest,
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

/-- Ключи выживших лежат в коробке (кроме стартового набора `base`). -/
theorem survivorsBox_key_mem (val : Finset ι → ℝ)
    (key : Finset ι → (κ → ℤ) × (κ → κ → ℤ) × ℕ) (adm : ι → Bool)
    (box : Finset ((κ → ℤ) × (κ → κ → ℤ) × ℕ)) (base : Finset ι) (L : List ι) :
    ∀ R ∈ survivorsBox val key adm box base L, R = base ∨ key R ∈ box := by
  intro R hR
  cases L with
  | nil =>
      rw [survivorsBox, Finset.mem_singleton] at hR
      exact Or.inl hR
  | cons i rest =>
      rw [survivorsBox_cons] at hR
      exact Or.inr (Finset.mem_filter.mp (prune_subset hR)).2

lemma key_injOn_survivorsBox (val : Finset ι → ℝ)
    (key : Finset ι → (κ → ℤ) × (κ → κ → ℤ) × ℕ) (adm : ι → Bool)
    (box : Finset ((κ → ℤ) × (κ → κ → ℤ) × ℕ)) (base : Finset ι) :
    ∀ L : List ι, Set.InjOn key ↑(survivorsBox val key adm box base L) := by
  intro L
  cases L with
  | nil =>
      intro R₁ h₁ R₂ h₂ _
      rw [survivorsBox] at h₁ h₂
      have e₁ : R₁ = base := Finset.mem_singleton.mp (by simpa using h₁)
      have e₂ : R₂ = base := Finset.mem_singleton.mp (by simpa using h₂)
      rw [e₁, e₂]
  | cons i rest =>
      rw [survivorsBox_cons]
      exact key_injOn_prune _ _ _

/-- **Размер таблицы при любом прогоне:** не больше `|box| + 1`. -/
theorem survivorsBox_card_le (val : Finset ι → ℝ)
    (key : Finset ι → (κ → ℤ) × (κ → κ → ℤ) × ℕ) (adm : ι → Bool)
    (box : Finset ((κ → ℤ) × (κ → κ → ℤ) × ℕ)) (base : Finset ι) (L : List ι) :
    (survivorsBox val key adm box base L).card ≤ box.card + 1 := by
  rw [← Finset.card_image_of_injOn (key_injOn_survivorsBox val key adm box base L)]
  have hsub : (survivorsBox val key adm box base L).image key ⊆ insert (key base) box := by
    intro k hk
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hk
    rcases survivorsBox_key_mem val key adm box base L R hR with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem h
  refine le_trans (Finset.card_le_card hsub) ?_
  exact le_trans (Finset.card_insert_le _ _) (by omega)

/-- **Инвариант динамики с коробкой.** Как `survivors_spec`, если коробка содержит
ключи всех наборов, `|L|`-близких по ключу к подмножествам `U`. -/
theorem survivorsBox_spec {η ξ : ℝ} (hη : 0 < η) (hξ : 0 < ξ) (adm : ι → Bool)
    (box : Finset ((κ → ℤ) × (κ → κ → ℤ) × ℕ)) (base : Finset ι) :
    ∀ (L : List ι), L.Nodup → (∀ i ∈ L, i ∉ base) →
    ∀ U : Finset ι, base ⊆ U → U ⊆ base ∪ L.toFinset → (∀ i ∈ U, i ∉ base → adm i) →
    (∀ U' ⊆ U, ∀ V : Finset ι, KeyClose a y T t η ξ (L.length : ℝ) V U' →
      keyOf a y T t η ξ V ∈ box) →
    ∃ R ∈ survivorsBox (fun V => phi a y V t) (keyOf a y T t η ξ) adm box base L,
      KeyClose a y T t η ξ (L.length : ℝ) R U ∧ phi a y U t ≤ phi a y R t := by
  intro L
  induction L with
  | nil =>
      intro _ _ U hbU hU _ _
      have hUb : U = base := by
        refine Finset.Subset.antisymm ?_ hbU
        simpa using hU
      subst hUb
      refine ⟨U, by rw [survivorsBox]; exact Finset.mem_singleton_self _, ?_, le_refl _⟩
      simpa using KeyClose.rfl' (a := a) (y := y) (T := T) (t := t) hη.le hξ.le U
  | cons i rest ih =>
      intro hnd hdisj U hbU hU hadmU hbox
      have hndrest : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hirest : i ∉ rest := (List.nodup_cons.mp hnd).1
      have hib : i ∉ base := hdisj i (List.mem_cons_self ..)
      have hdisjrest : ∀ j ∈ rest, j ∉ base := fun j hj => hdisj j (List.mem_cons_of_mem _ hj)
      have hlenle : (rest.length : ℝ) ≤ ((i :: rest).length : ℝ) := by
        simp [List.length_cons]
      set F := survivorsBox (fun V => phi a y V t) (keyOf a y T t η ξ) adm box base rest
        with hF
      set E := (if adm i then F ∪ F.image (insert i) else F) with hE
      set Ef := E.filter (fun U => keyOf a y T t η ξ U ∈ box) with hEf
      have hnotin : ∀ V ∈ F, i ∉ V := by
        intro V hV hiV
        obtain ⟨_, h2, _⟩ := survivorsBox_mem _ _ adm box base rest V hV
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
        have hboxrest : ∀ U' ⊆ U.erase i, ∀ V : Finset ι,
            KeyClose a y T t η ξ (rest.length : ℝ) V U' → keyOf a y T t η ξ V ∈ box :=
          fun U' hU' V hV => hbox U' (le_trans hU' (Finset.erase_subset i U)) V
            (hV.mono hlenle hη.le hξ.le)
        obtain ⟨R₀, hR₀, hclose, hval⟩ := ih hndrest hdisjrest (U.erase i) hU0b hU0
          (fun j hj hjb => hadmU j (Finset.mem_of_mem_erase hj) hjb) hboxrest
        have hiR₀ : i ∉ R₀ := hnotin R₀ hR₀
        have h2 : KeyClose a y T t η ξ (rest.length : ℝ) (insert i R₀) U := by
          have := KeyClose.insert' (i := i) hiR₀ (Finset.notMem_erase i U) hclose
          rwa [Finset.insert_erase hiU] at this
        have hmemE : insert i R₀ ∈ E := by
          rw [hE, if_pos hadmi]
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨R₀, hR₀, rfl⟩)
        have hmemEf : insert i R₀ ∈ Ef :=
          Finset.mem_filter.mpr ⟨hmemE, hbox U (Finset.Subset.refl _) _
            (h2.mono hlenle hη.le hξ.le)⟩
        obtain ⟨hmem, hkey, hge⟩ := repOf_spec (val := fun V => phi a y V t)
          (key := keyOf a y T t η ξ) (F := Ef) hmemEf
        refine ⟨repOf (fun V => phi a y V t) (keyOf a y T t η ξ) Ef
          (keyOf a y T t η ξ (insert i R₀)), ?_, ?_, ?_⟩
        · rw [survivorsBox_cons, ← hF, ← hE, ← hEf]
          exact mem_prune hmemEf
        · have h1 : KeyClose a y T t η ξ 1
              (repOf (fun V => phi a y V t) (keyOf a y T t η ξ) Ef
                (keyOf a y T t η ξ (insert i R₀))) (insert i R₀) :=
            KeyClose.of_key_eq hη hξ hkey
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
        have hboxrest : ∀ U' ⊆ U, ∀ V : Finset ι,
            KeyClose a y T t η ξ (rest.length : ℝ) V U' → keyOf a y T t η ξ V ∈ box :=
          fun U' hU' V hV => hbox U' hU' V (hV.mono hlenle hη.le hξ.le)
        obtain ⟨R₀, hR₀, hclose, hval⟩ := ih hndrest hdisjrest U hbU hU' hadmU hboxrest
        have hmemE : R₀ ∈ E := by
          rw [hE]
          by_cases hadmi : adm i
          · rw [if_pos hadmi]; exact Finset.mem_union_left _ hR₀
          · rw [if_neg hadmi]; exact hR₀
        have hmemEf : R₀ ∈ Ef :=
          Finset.mem_filter.mpr ⟨hmemE, hbox U (Finset.Subset.refl _) _
            (hclose.mono hlenle hη.le hξ.le)⟩
        obtain ⟨hmem, hkey, hge⟩ := repOf_spec (val := fun V => phi a y V t)
          (key := keyOf a y T t η ξ) (F := Ef) hmemEf
        refine ⟨repOf (fun V => phi a y V t) (keyOf a y T t η ξ) Ef
          (keyOf a y T t η ξ R₀), ?_, ?_, ?_⟩
        · rw [survivorsBox_cons, ← hF, ← hE, ← hEf]
          exact mem_prune hmemEf
        · have h1 := KeyClose.of_key_eq (a := a) (y := y) (T := T) (t := t) hη hξ hkey
          have := h1.trans hclose
          have hlen : (1 : ℝ) + (rest.length : ℝ) = ((i :: rest).length : ℝ) := by
            simp [List.length_cons]; ring
          rwa [hlen] at this
        · linarith [hval, hge]

/-! ### Каноническая коробка -/

/-- **Каноническая коробка ключей.** Вычисляется без знания оптимума: по догадке `V`,
границе мощности `N`, ширинам корзин `η`, `ξ`, длине прохода `Lc` и границе
коэффициентов `ρ`. -/
noncomputable def boxOf (κ : Type*) [Fintype κ] [DecidableEq κ] (ρ V η ξ : ℝ) (N Lc : ℕ) :
    Finset ((κ → ℤ) × (κ → κ → ℤ) × ℕ) :=
  keyBox (κ := κ) ⌈(ρ * Real.sqrt ((N : ℝ) * (4 * V)) + (Lc : ℝ) * η) / η⌉
    ⌈((N : ℝ) * ρ ^ 2 + (Lc : ℝ) * ξ) / ξ⌉ N

/-- **Коробка содержит ключи всех нужных наборов.** Если на носителе `A` коэффициенты
Крамера по `T` не больше `ρ`, `|A| ≤ N` и `φ_A(τ) ≤ 4V`, то всякий набор, близкий по
ключу (с дрейфом `d ≤ Lc`) к подмножеству `A`, имеет ключ в `boxOf`. -/
theorem keyOf_mem_boxOf {A : Finset ι} {ρ V η ξ d : ℝ} {N Lc : ℕ} (hρ : 0 ≤ ρ)
    (hcf : ∀ i ∈ A, ∀ l, |cf a T i l| ≤ ρ) (hAN : A.card ≤ N)
    (hQ : phi a y A t ≤ 4 * V) (hη : 0 < η) (hξ : 0 < ξ) (hd : d ≤ (Lc : ℝ))
    {U' V' : Finset ι} (hU' : U' ⊆ A) (hclose : KeyClose a y T t η ξ d V' U') :
    keyOf a y T t η ξ V' ∈ boxOf κ ρ V η ξ N Lc := by
  have hU'N : (U'.card : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast le_trans (Finset.card_le_card hU') hAN
  have hphiU : phi a y U' t ≤ 4 * V := le_trans (phi_mono hU' t) hQ
  have h0 : (0:ℝ) ≤ phi a y U' t := phi_nonneg a y U' t
  rw [keyOf, boxOf, keyBox, Finset.mem_product, Finset.mem_product]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Fintype.mem_piFinset]
    intro l
    refine floor_div_mem_Icc ?_ hη
    have h1 := abs_momK_le_rho (y := y) (t := t) hρ hcf hU' l
    have h2 := hclose.mom l
    have h3 : ρ * Real.sqrt ((U'.card : ℝ) * phi a y U' t)
        ≤ ρ * Real.sqrt ((N : ℝ) * (4 * V)) := by
      refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hρ
      exact mul_le_mul hU'N hphiU h0 (by positivity)
    have h4 : d * η ≤ (Lc : ℝ) * η := mul_le_mul_of_nonneg_right hd hη.le
    calc |momK a y T V' t l|
        ≤ |momK a y T V' t l - momK a y T U' t l| + |momK a y T U' t l| := by
          have := abs_sub_abs_le_abs_sub (momK a y T V' t l) (momK a y T U' t l)
          linarith
      _ ≤ ρ * Real.sqrt ((N : ℝ) * (4 * V)) + (Lc : ℝ) * η := by linarith
  · simp only [Fintype.mem_piFinset]
    intro l l'
    refine floor_div_mem_Icc ?_ hξ
    have h1 := abs_gramK2_le_rho hcf hU' l l'
    have h2 := hclose.gram l l'
    have h3 : (U'.card : ℝ) * ρ ^ 2 ≤ (N : ℝ) * ρ ^ 2 :=
      mul_le_mul_of_nonneg_right hU'N (sq_nonneg _)
    have h4 : d * ξ ≤ (Lc : ℝ) * ξ := mul_le_mul_of_nonneg_right hd hξ.le
    calc |gramK2 a T V' l l'|
        ≤ |gramK2 a T V' l l' - gramK2 a T U' l l'| + |gramK2 a T U' l l'| := by
          have := abs_sub_abs_le_abs_sub (gramK2 a T V' l l') (gramK2 a T U' l l')
          linarith
      _ ≤ (N : ℝ) * ρ ^ 2 + (Lc : ℝ) * ξ := by linarith
  · simp only [Finset.mem_range]
    rw [hclose.card]
    exact Nat.lt_succ_iff.mpr (le_trans (Finset.card_le_card hU') hAN)

/-- Мощность канонической коробки. -/
theorem card_boxOf {ρ V η ξ : ℝ} {N Lc : ℕ} (hρ : 0 ≤ ρ) (hη : 0 < η) (hξ : 0 < ξ) :
    (boxOf κ ρ V η ξ N Lc).card
      = (2 * ⌈(ρ * Real.sqrt ((N : ℝ) * (4 * V)) + (Lc : ℝ) * η) / η⌉ + 1).toNat
          ^ Fintype.card κ
        * ((2 * ⌈((N : ℝ) * ρ ^ 2 + (Lc : ℝ) * ξ) / ξ⌉ + 1).toNat
            ^ (Fintype.card κ * Fintype.card κ) * (N + 1)) := by
  rw [boxOf]
  refine card_keyBox _ _ ?_ ?_ _
  · exact Int.ceil_nonneg (div_nonneg (by positivity) hη.le)
  · exact Int.ceil_nonneg (div_nonneg (by positivity) hξ.le)

end SparseSharpe.Factor
