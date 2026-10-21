import SparseSharpe.LOFptas
import SparseSharpe.Grid
import SparseSharpe.Factor.SchemeLS

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Теорема J из данных: long-only, один фактор (сессия 26, задача C0)

Long-only задача при `K = 1`, `β_i > 0`: `F_LO(S) = max_{w ≥ 0} (2m_S'w − w'V_Sw)`,
`V = diag(d) + σ²ββ'`. Схема (`code/SPEC_LO.md`, `theory_note_v4.md` §5):

* догадки `V = L·2^j`;
* узлы: сетка вокруг **каждого** центра `r_c` (`c` — актив, `r_c = m_c/β_c`, `u_c = β_c²/d_c`,
  или якорь `r = 0`, `u = 1/σ²`) с шагом `√(εV/(k+1))/(2√u_c)` и номерами `|z| ≤ Z`, плюс
  узлы `r_i` (Л1: `lo_node_exists_grid`);
* в узле `t` — динамика «минимум `M`» (`minMTable`): пул `{i : tβ_i ≤ m_i}`, ключ
  `(Q̃, корзина κ, корзина M, |U|)`, где `Q̃ = Σ⌊q_i/θ⌋` **точно аддитивно**, корзины `κ`
  геометрические с шагом `1 + ξ`, ширина корзины `M` пропорциональна `√κ` корзины;
  в каждой корзине хранится набор с **минимальным точным** `M`; ключи вне коробки
  отбрасываются (`findings_v16.md` §1: правило коробки записано явно).

Главные утверждения:

* `minMTable_spec` — инвариант динамики (как `minM_invariant`, но о конкретной функции);
* `lo1_one_guess` — при догадке `V ≤ OPT ≤ 2V` в таблице одного из узлов есть
  самосогласованный носитель `R` с `F(R) ≥ (1 − 33ε/8)·OPT` (шаг — `lo_step`);
* `card_lo1Candidates_poly` — размер семейства в полиномиальной форме
  `138744·(J+1)·M³·k²·√k·ε⁻²·(1 + ln(1 + σ²Σ_iβ_i²/d_i))`;
* `main_theorem_lo1` — **Теорема J из данных** в языке `main_theorem_clipped` при `K = 1`:
  размер семейства (без `ω`; величины входа — только в числе догадок и в числе
  геометрических корзин веса, оба — логарифмы отношений величин входа), `≤ k` имён,
  существование лучшей пары, гарантия `1 − 33ε/8` и `√(1 − 33ε/8)` для коэффициента
  Шарпа полностью инвестированного портфеля.
-/

namespace SparseSharpe

open Finset

/-! ### Динамика «минимум `M`» с коробкой ключей -/

section MinMTable

variable {ι : Type*} [DecidableEq ι]

/-- Ключ состояния схемы «минимум `M`»: `(Q̃, корзина веса, корзина момента, мощность)`. -/
abbrev LoKey : Type := ℤ × ℤ × ℤ × ℕ

/-- **Динамика «минимум `M`» с коробкой.** По списку `L`: «не брать» и «взять» (если актив
допущен `adm`); наборы с ключом вне `box` отбрасываются; из наборов с одним ключом остаётся
один — с наибольшим `val` (в приложении `val = −M`, то есть с **минимальным точным** `M`). -/
noncomputable def minMTable (val : Finset ι → ℝ) (key : Finset ι → LoKey) (adm : ι → Bool)
    (box : Finset LoKey) : List ι → Finset (Finset ι)
  | [] => {∅}
  | i :: rest =>
      Factor.kPrune val key
        ((if adm i then
            minMTable val key adm box rest ∪ (minMTable val key adm box rest).image (insert i)
          else minMTable val key adm box rest).filter (fun U => key U ∈ box))

lemma minMTable_cons (val : Finset ι → ℝ) (key : Finset ι → LoKey) (adm : ι → Bool)
    (box : Finset LoKey) (i : ι) (rest : List ι) :
    minMTable val key adm box (i :: rest)
      = Factor.kPrune val key
        ((if adm i then
            minMTable val key adm box rest ∪ (minMTable val key adm box rest).image (insert i)
          else minMTable val key adm box rest).filter (fun U => key U ∈ box)) := rfl

/-- Что лежит в таблице: подмножества `L` из допущенных активов. -/
theorem minMTable_mem (val : Finset ι → ℝ) (key : Finset ι → LoKey) (adm : ι → Bool)
    (box : Finset LoKey) :
    ∀ (L : List ι), ∀ R ∈ minMTable val key adm box L, R ⊆ L.toFinset ∧ ∀ i ∈ R, adm i := by
  intro L
  induction L with
  | nil =>
      intro R hR
      rw [minMTable, Finset.mem_singleton] at hR
      subst hR
      simp
  | cons i rest ih =>
      intro R hR
      rw [minMTable_cons] at hR
      have hRE := Finset.mem_of_mem_filter _ (Factor.kPrune_subset hR)
      have hgrow : ∀ V ∈ minMTable val key adm box rest,
          V ⊆ (i :: rest).toFinset ∧ ∀ j ∈ V, adm j := by
        intro V hV
        obtain ⟨h1, h2⟩ := ih V hV
        refine ⟨le_trans h1 ?_, h2⟩
        intro x hx
        simp only [List.mem_toFinset] at hx ⊢
        exact List.mem_cons_of_mem _ hx
      by_cases hadm : adm i
      · simp only [hadm, ↓reduceIte] at hRE
        rcases Finset.mem_union.mp hRE with h | h
        · exact hgrow R h
        · obtain ⟨R', hR', rfl⟩ := Finset.mem_image.mp h
          obtain ⟨h1, h2⟩ := ih R' hR'
          refine ⟨?_, ?_⟩
          · intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · simp
            · have := h1 hx
              simp only [List.mem_toFinset] at this ⊢
              exact List.mem_cons_of_mem _ this
          · intro j hj
            rcases Finset.mem_insert.mp hj with rfl | hj
            · exact hadm
            · exact h2 j hj
      · simp only [hadm, Bool.false_eq_true, ↓reduceIte] at hRE
        exact hgrow R hRE

/-- Ключи выживших лежат в коробке (кроме пустого набора пустого списка). -/
theorem minMTable_key_mem (val : Finset ι → ℝ) (key : Finset ι → LoKey) (adm : ι → Bool)
    (box : Finset LoKey) (L : List ι) :
    ∀ R ∈ minMTable val key adm box L, R = ∅ ∨ key R ∈ box := by
  intro R hR
  cases L with
  | nil =>
      rw [minMTable, Finset.mem_singleton] at hR
      exact Or.inl hR
  | cons i rest =>
      rw [minMTable_cons] at hR
      exact Or.inr (Finset.mem_filter.mp (Factor.kPrune_subset hR)).2

lemma key_injOn_minMTable (val : Finset ι → ℝ) (key : Finset ι → LoKey) (adm : ι → Bool)
    (box : Finset LoKey) :
    ∀ L : List ι, Set.InjOn key ↑(minMTable val key adm box L) := by
  intro L
  cases L with
  | nil =>
      intro R₁ h₁ R₂ h₂ _
      rw [minMTable] at h₁ h₂
      have e₁ : R₁ = ∅ := Finset.mem_singleton.mp (by simpa using h₁)
      have e₂ : R₂ = ∅ := Finset.mem_singleton.mp (by simpa using h₂)
      rw [e₁, e₂]
  | cons i rest =>
      rw [minMTable_cons]
      exact Factor.key_injOn_kPrune

/-- **Размер таблицы при любом прогоне:** не больше `|box| + 1`. -/
theorem minMTable_card_le (val : Finset ι → ℝ) (key : Finset ι → LoKey) (adm : ι → Bool)
    (box : Finset LoKey) (L : List ι) :
    (minMTable val key adm box L).card ≤ box.card + 1 := by
  rw [← Finset.card_image_of_injOn (key_injOn_minMTable val key adm box L)]
  have hsub : (minMTable val key adm box L).image key ⊆ insert (key ∅) box := by
    intro z hz
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hz
    rcases minMTable_key_mem val key adm box L R hR with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem h
  refine le_trans (Finset.card_le_card hsub) ?_
  exact le_trans (Finset.card_insert_le _ _) (by omega)

/-- **Инвариант динамики «минимум `M`»** (о конкретной функции `minMTable`). Пусть `QT`, `MM`,
`kap` аддитивны по активам (`kap` — с неотрицательными вкладами), а ключ определяет `QT` и
мощность точно, `kap` — с множителем `1 + ξ`, `MM` — с точностью `c₀√kap`. Тогда для любого
допущенного `U ⊆ L`, у которого коробка содержит ключи всех наборов с `QT` и мощностью
какого-нибудь `U' ⊆ U`, в таблице есть `R` с

    QT R = QT U,  |R| = |U|,  MM R ≤ MM U,  MM R ≥ MM U − |L|·c₀√((1+ξ)^|L|·kap U),
    kap R ≤ (1+ξ)^|L|·kap U,  kap U ≤ (1+ξ)^|L|·kap R. -/
theorem minMTable_spec (MM kap : Finset ι → ℝ) (QT : Finset ι → ℤ) (key : Finset ι → LoKey)
    (adm : ι → Bool) (box : Finset LoKey) (q : ι → ℤ) (δ u : ι → ℝ) {ξ c₀ : ℝ}
    (hξ : 0 ≤ ξ) (hc₀ : 0 ≤ c₀) (hu : ∀ i, 0 ≤ u i) (hkap0 : ∀ S, 0 ≤ kap S)
    (QT_ins : ∀ (S : Finset ι) (i : ι), i ∉ S → QT (insert i S) = QT S + q i)
    (MM_ins : ∀ (S : Finset ι) (i : ι), i ∉ S → MM (insert i S) = MM S + δ i)
    (kap_ins : ∀ (S : Finset ι) (i : ι), i ∉ S → kap (insert i S) = kap S + u i)
    (key_QT : ∀ S S' : Finset ι, key S = key S' → QT S = QT S')
    (key_card : ∀ S S' : Finset ι, key S = key S' → S.card = S'.card)
    (key_kap : ∀ S S' : Finset ι, key S = key S' → kap S ≤ (1 + ξ) * kap S')
    (key_MM : ∀ S S' : Finset ι, key S = key S' → |MM S - MM S'| ≤ c₀ * Real.sqrt (kap S)) :
    ∀ (L : List ι), L.Nodup → ∀ U : Finset ι, U ⊆ L.toFinset → (∀ i ∈ U, adm i) →
    (∀ X U' : Finset ι, U' ⊆ U → QT X = QT U' → X.card = U'.card → key X ∈ box) →
    ∃ R ∈ minMTable (fun V => -MM V) key adm box L,
      QT R = QT U ∧ R.card = U.card ∧ MM R ≤ MM U ∧
      MM U - (L.length : ℝ) * (c₀ * Real.sqrt ((1 + ξ) ^ L.length * kap U)) ≤ MM R ∧
      kap R ≤ (1 + ξ) ^ L.length * kap U ∧ kap U ≤ (1 + ξ) ^ L.length * kap R := by
  have hξ1 : (1:ℝ) ≤ 1 + ξ := by linarith
  intro L
  induction L with
  | nil =>
      intro _ U hU _ _
      have hU0 : U = ∅ := by simpa using hU
      subst hU0
      refine ⟨∅, by rw [minMTable]; exact Finset.mem_singleton_self _, rfl, rfl, le_rfl,
        ?_, ?_, ?_⟩ <;> simp
  | cons i rest ih =>
      intro hnd U hU hadmU hbox
      have hndrest : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hirest : i ∉ rest := (List.nodup_cons.mp hnd).1
      set r := rest.length with hr
      have hlen : (i :: rest).length = r + 1 := by simp [hr]
      set F := minMTable (fun V => -MM V) key adm box rest with hF
      set E := (if adm i then F ∪ F.image (insert i) else F) with hE
      set Ef := E.filter (fun V => key V ∈ box) with hEf
      have hpow1 : (1:ℝ) ≤ (1 + ξ) ^ r := one_le_pow₀ hξ1
      have hpow_succ : (1 + ξ) ^ (r + 1) = (1 + ξ) ^ r * (1 + ξ) := pow_succ _ _
      have hpowle : (1 + ξ) ^ r ≤ (1 + ξ) ^ (r + 1) := by
        rw [hpow_succ]; nlinarith
      -- общий шаг: из представителя `X` (до усечения) — представитель в таблице
      have finish : ∀ X : Finset ι, X ∈ E → key X ∈ box →
          ∃ R ∈ minMTable (fun V => -MM V) key adm box (i :: rest),
            key R = key X ∧ MM R ≤ MM X := by
        intro X hXE hXbox
        have hmemEf : X ∈ Ef := Finset.mem_filter.mpr ⟨hXE, hXbox⟩
        obtain ⟨_, hkey, hge⟩ := Factor.kRep_spec (val := fun V => -MM V) (key := key)
          (F := Ef) hmemEf
        refine ⟨Factor.kRep (fun V => -MM V) key Ef (key X), ?_, hkey, by linarith⟩
        rw [minMTable_cons, ← hF, ← hE, ← hEf]
        exact Factor.mem_kPrune hmemEf
      have hnotin : ∀ V ∈ F, i ∉ V := by
        intro V hV hiV
        have := (minMTable_mem _ _ adm box rest V hV).1 hiV
        exact hirest (List.mem_toFinset.mp this)
      by_cases hiU : i ∈ U
      · -- шаг «взять»
        set U₀ := U.erase i with hU₀
        have hiU₀ : i ∉ U₀ := Finset.notMem_erase i U
        have hUins : U = insert i U₀ := (Finset.insert_erase hiU).symm
        have hU0 : U₀ ⊆ rest.toFinset := by
          intro x hx
          have hx' := Finset.mem_of_mem_erase hx
          have hxi : x ≠ i := (Finset.mem_erase.mp hx).1
          have := hU hx'
          simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset] at this
          rcases this with rfl | h
          · exact absurd rfl hxi
          · exact List.mem_toFinset.mpr h
        obtain ⟨R₀, hR₀, hQT₀, hcard₀, hMle₀, hMge₀, hK₀, hK₀'⟩ := ih hndrest U₀ hU0
          (fun j hj => hadmU j (Finset.mem_of_mem_erase hj))
          (fun X U' hU' => hbox X U' (le_trans hU' (Finset.erase_subset _ _)))
        have hiR₀ : i ∉ R₀ := hnotin R₀ hR₀
        set X := insert i R₀ with hX
        have hXQT : QT X = QT U := by
          rw [hX, QT_ins _ _ hiR₀, hUins, QT_ins _ _ hiU₀, hQT₀]
        have hXcard : X.card = U.card := by
          rw [hX, Finset.card_insert_of_notMem hiR₀, hUins, Finset.card_insert_of_notMem hiU₀,
            hcard₀]
        have hXE : X ∈ E := by
          rw [hE]
          simp only [hadmU i hiU, ↓reduceIte]
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨R₀, hR₀, rfl⟩)
        obtain ⟨R, hR, hkey, hMR⟩ := finish X hXE (hbox X U le_rfl hXQT hXcard)
        have hMX : MM X = MM R₀ + δ i := by rw [hX, MM_ins _ _ hiR₀]
        have hMU : MM U = MM U₀ + δ i := by rw [hUins, MM_ins _ _ hiU₀]
        have hKX : kap X = kap R₀ + u i := by rw [hX, kap_ins _ _ hiR₀]
        have hKU : kap U = kap U₀ + u i := by rw [hUins, kap_ins _ _ hiU₀]
        have hui := hu i
        have hKXle : kap X ≤ (1 + ξ) ^ r * kap U := by
          rw [hKX, hKU]; nlinarith
        have hKUle : kap U ≤ (1 + ξ) ^ r * kap X := by
          rw [hKX, hKU]; nlinarith
        have hkU₀ : kap U₀ ≤ kap U := by rw [hKU]; linarith
        refine ⟨R, hR, by rw [key_QT R X hkey, hXQT], by rw [key_card R X hkey, hXcard],
          by linarith, ?_, ?_, ?_⟩
        · -- нижняя граница по `M`
          have hcl := key_MM X R hkey.symm
          have hcl' := (abs_le.mp hcl).2
          have hsq1 : Real.sqrt (kap X) ≤ Real.sqrt ((1 + ξ) ^ (r + 1) * kap U) := by
            apply Real.sqrt_le_sqrt
            nlinarith [hkap0 U]
          have hsq2 : Real.sqrt ((1 + ξ) ^ r * kap U₀)
              ≤ Real.sqrt ((1 + ξ) ^ (r + 1) * kap U) := by
            apply Real.sqrt_le_sqrt
            have h1 : (1 + ξ) ^ r * kap U₀ ≤ (1 + ξ) ^ r * kap U :=
              mul_le_mul_of_nonneg_left hkU₀ (by positivity)
            have h2 : (1 + ξ) ^ r * kap U ≤ (1 + ξ) ^ (r + 1) * kap U :=
              mul_le_mul_of_nonneg_right hpowle (hkap0 U)
            linarith
          have hr0 : (0:ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
          have e1 : (r : ℝ) * (c₀ * Real.sqrt ((1 + ξ) ^ r * kap U₀))
              ≤ (r : ℝ) * (c₀ * Real.sqrt ((1 + ξ) ^ (r + 1) * kap U)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq2 hc₀) hr0
          have e2 : c₀ * Real.sqrt (kap X) ≤ c₀ * Real.sqrt ((1 + ξ) ^ (r + 1) * kap U) :=
            mul_le_mul_of_nonneg_left hsq1 hc₀
          rw [hlen]
          push_cast
          have hfin : MM U - ((r : ℝ) + 1) * (c₀ * Real.sqrt ((1 + ξ) ^ (r + 1) * kap U))
              = MM U₀ + δ i - (r : ℝ) * (c₀ * Real.sqrt ((1 + ξ) ^ (r + 1) * kap U))
                - c₀ * Real.sqrt ((1 + ξ) ^ (r + 1) * kap U) := by rw [hMU]; ring
          rw [hfin]
          linarith
        · rw [hlen]
          have := key_kap R X hkey
          calc kap R ≤ (1 + ξ) * kap X := this
            _ ≤ (1 + ξ) * ((1 + ξ) ^ r * kap U) :=
                mul_le_mul_of_nonneg_left hKXle (by linarith)
            _ = (1 + ξ) ^ (r + 1) * kap U := by rw [hpow_succ]; ring
        · rw [hlen]
          have := key_kap X R hkey.symm
          calc kap U ≤ (1 + ξ) ^ r * kap X := hKUle
            _ ≤ (1 + ξ) ^ r * ((1 + ξ) * kap R) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = (1 + ξ) ^ (r + 1) * kap R := by rw [hpow_succ]; ring
      · -- шаг «не брать»
        have hU' : U ⊆ rest.toFinset := by
          intro x hx
          have := hU hx
          simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset] at this
          rcases this with rfl | h
          · exact absurd hx hiU
          · exact List.mem_toFinset.mpr h
        obtain ⟨R₀, hR₀, hQT₀, hcard₀, hMle₀, hMge₀, hK₀, hK₀'⟩ := ih hndrest U hU' hadmU hbox
        have hXE : R₀ ∈ E := by
          rw [hE]
          by_cases hadmi : adm i
          · simp only [hadmi, ↓reduceIte]; exact Finset.mem_union_left _ hR₀
          · simp only [hadmi, Bool.false_eq_true, ↓reduceIte]; exact hR₀
        obtain ⟨R, hR, hkey, hMR⟩ := finish R₀ hXE (hbox R₀ U le_rfl hQT₀ hcard₀)
        refine ⟨R, hR, by rw [key_QT R R₀ hkey, hQT₀], by rw [key_card R R₀ hkey, hcard₀],
          by linarith, ?_, ?_, ?_⟩
        · have hcl := key_MM R₀ R hkey.symm
          have hcl' := (abs_le.mp hcl).2
          have hsq1 : Real.sqrt (kap R₀) ≤ Real.sqrt ((1 + ξ) ^ (r + 1) * kap U) := by
            apply Real.sqrt_le_sqrt
            have h2 : (1 + ξ) ^ r * kap U ≤ (1 + ξ) ^ (r + 1) * kap U :=
              mul_le_mul_of_nonneg_right hpowle (hkap0 U)
            linarith
          have hsq2 : Real.sqrt ((1 + ξ) ^ r * kap U)
              ≤ Real.sqrt ((1 + ξ) ^ (r + 1) * kap U) := by
            apply Real.sqrt_le_sqrt
            exact mul_le_mul_of_nonneg_right hpowle (hkap0 U)
          have hr0 : (0:ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
          have e1 : (r : ℝ) * (c₀ * Real.sqrt ((1 + ξ) ^ r * kap U))
              ≤ (r : ℝ) * (c₀ * Real.sqrt ((1 + ξ) ^ (r + 1) * kap U)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq2 hc₀) hr0
          have e2 : c₀ * Real.sqrt (kap R₀) ≤ c₀ * Real.sqrt ((1 + ξ) ^ (r + 1) * kap U) :=
            mul_le_mul_of_nonneg_left hsq1 hc₀
          rw [hlen]
          push_cast
          have hfin : MM U - ((r : ℝ) + 1) * (c₀ * Real.sqrt ((1 + ξ) ^ (r + 1) * kap U))
              = MM U - (r : ℝ) * (c₀ * Real.sqrt ((1 + ξ) ^ (r + 1) * kap U))
                - c₀ * Real.sqrt ((1 + ξ) ^ (r + 1) * kap U) := by ring
          rw [hfin]
          linarith
        · rw [hlen]
          have := key_kap R R₀ hkey
          calc kap R ≤ (1 + ξ) * kap R₀ := this
            _ ≤ (1 + ξ) * ((1 + ξ) ^ r * kap U) :=
                mul_le_mul_of_nonneg_left hK₀ (by linarith)
            _ = (1 + ξ) ^ (r + 1) * kap U := by rw [hpow_succ]; ring
        · rw [hlen]
          have := key_kap R₀ R hkey.symm
          calc kap U ≤ (1 + ξ) ^ r * kap R₀ := hK₀'
            _ ≤ (1 + ξ) ^ r * ((1 + ξ) * kap R) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = (1 + ξ) ^ (r + 1) * kap R := by rw [hpow_succ]; ring

end MinMTable

/-! ### Ключ схемы при одном факторе (на данных `m, d, β, σ²`) -/

section OneFactorKey

variable {ι : Type*} [DecidableEq ι]

/-- Вес набора `κ(U) = 1/σ² + Σ_{i∈U} β_i²/d_i` (это `OneFactor.kappa` на данных). -/
noncomputable def kap1 (d β : ι → ℝ) (σ2 : ℝ) (U : Finset ι) : ℝ :=
  1 / σ2 + ∑ i ∈ U, β i ^ 2 / d i

/-- Первый момент `M_t(U) = −t/σ² + Σ_{i∈U} β_i(m_i − tβ_i)/d_i` (это `OneFactor.Mt`). -/
noncomputable def mt1 (m d β : ι → ℝ) (σ2 : ℝ) (U : Finset ι) (t : ℝ) : ℝ :=
  -(t / σ2) + ∑ i ∈ U, β i * (m i - t * β i) / d i

/-- Вклад актива во второй момент: `q_i(t) = (m_i − tβ_i)²/d_i`. -/
noncomputable def q1 (m d β : ι → ℝ) (t : ℝ) (i : ι) : ℝ := (m i - t * β i) ^ 2 / d i

/-- Поштучно округлённый вниз второй момент `Q̃(U) = Σ_{i∈U} ⌊q_i(t)/θ⌋` (в единицах `θ`);
**точно аддитивен**. -/
noncomputable def qt1 (m d β : ι → ℝ) (t θ : ℝ) (U : Finset ι) : ℤ :=
  ∑ i ∈ U, ⌊q1 m d β t i / θ⌋

/-- Геометрическая корзина веса: `⌊log_{1+ξ}(σ²·κ(U))⌋`. -/
noncomputable def kb1 (d β : ι → ℝ) (σ2 ξ : ℝ) (U : Finset ι) : ℤ :=
  ⌊Real.logb (1 + ξ) (kap1 d β σ2 U * σ2)⌋

/-- Ширина корзины момента в корзине веса `b`: `c₀·√((1+ξ)^b/σ²)` (пропорциональна `√κ`). -/
noncomputable def mw1 (σ2 ξ c₀ : ℝ) (b : ℤ) : ℝ := c₀ * Real.sqrt ((1 + ξ) ^ (b : ℝ) / σ2)

/-- Корзина момента: `⌊M_t(U)/(ширина корзины веса U)⌋`. -/
noncomputable def mb1 (m d β : ι → ℝ) (σ2 t ξ c₀ : ℝ) (U : Finset ι) : ℤ :=
  ⌊mt1 m d β σ2 U t / mw1 σ2 ξ c₀ (kb1 d β σ2 ξ U)⌋

/-- **Ключ схемы «минимум `M`»**: `(Q̃, корзина κ, корзина M, |U|)`. -/
noncomputable def loKey1 (m d β : ι → ℝ) (σ2 t θ ξ c₀ : ℝ) (U : Finset ι) : LoKey :=
  (qt1 m d β t θ U, kb1 d β σ2 ξ U, mb1 m d β σ2 t ξ c₀ U, U.card)

variable {m d β : ι → ℝ} {σ2 : ℝ}

lemma kap1_insert {U : Finset ι} {i : ι} (hi : i ∉ U) :
    kap1 d β σ2 (insert i U) = kap1 d β σ2 U + β i ^ 2 / d i := by
  simp only [kap1, Finset.sum_insert hi]; ring

lemma mt1_insert {U : Finset ι} {i : ι} {t : ℝ} (hi : i ∉ U) :
    mt1 m d β σ2 (insert i U) t = mt1 m d β σ2 U t + β i * (m i - t * β i) / d i := by
  simp only [mt1, Finset.sum_insert hi]; ring

lemma qt1_insert {U : Finset ι} {i : ι} {t θ : ℝ} (hi : i ∉ U) :
    qt1 m d β t θ (insert i U) = qt1 m d β t θ U + ⌊q1 m d β t i / θ⌋ := by
  simp only [qt1, Finset.sum_insert hi]; ring

lemma kap1_pos (hd : ∀ i, 0 < d i) (hσ : 0 < σ2) (U : Finset ι) : 0 < kap1 d β σ2 U := by
  have h1 : (0:ℝ) < 1 / σ2 := by positivity
  have h2 : (0:ℝ) ≤ ∑ i ∈ U, β i ^ 2 / d i :=
    Finset.sum_nonneg fun i _ => by have := hd i; positivity
  unfold kap1; linarith

lemma one_le_kap1_mul (hd : ∀ i, 0 < d i) (hσ : 0 < σ2) (U : Finset ι) :
    1 ≤ kap1 d β σ2 U * σ2 := by
  have h2 : (0:ℝ) ≤ ∑ i ∈ U, β i ^ 2 / d i :=
    Finset.sum_nonneg fun i _ => by have := hd i; positivity
  unfold kap1
  rw [add_mul, one_div, inv_mul_cancel₀ hσ.ne']
  nlinarith

/-- Целая часть логарифма: `b^⌊log_b x⌋ ≤ x < b^(⌊log_b x⌋+1)`. -/
lemma floor_logb_spec {b x : ℝ} (hb : 1 < b) (hx : 0 < x) :
    b ^ (⌊Real.logb b x⌋ : ℝ) ≤ x ∧ x < b ^ ((⌊Real.logb b x⌋ : ℝ) + 1) := by
  constructor
  · exact (Real.le_logb_iff_rpow_le hb hx).mp (Int.floor_le _)
  · exact (Real.logb_lt_iff_lt_rpow hb hx).mp (Int.lt_floor_add_one _)

/-- Нижний край корзины веса не больше `σ²κ(U)`, верхний — больше. -/
lemma kb1_spec (hd : ∀ i, 0 < d i) (hσ : 0 < σ2) {ξ : ℝ} (hξ : 0 < ξ) (U : Finset ι) :
    (1 + ξ) ^ (kb1 d β σ2 ξ U : ℝ) ≤ kap1 d β σ2 U * σ2
      ∧ kap1 d β σ2 U * σ2 < (1 + ξ) ^ (kb1 d β σ2 ξ U : ℝ) * (1 + ξ) := by
  have hx : 0 < kap1 d β σ2 U * σ2 := by
    have := kap1_pos (β := β) hd hσ U; positivity
  obtain ⟨h1, h2⟩ := floor_logb_spec (by linarith : (1:ℝ) < 1 + ξ) hx
  refine ⟨h1, ?_⟩
  rw [Real.rpow_add_one (by positivity)] at h2
  exact h2

lemma kb1_nonneg (hd : ∀ i, 0 < d i) (hσ : 0 < σ2) {ξ : ℝ} (hξ : 0 < ξ) (U : Finset ι) :
    0 ≤ kb1 d β σ2 ξ U := by
  unfold kb1
  refine Int.floor_nonneg.mpr (Real.logb_nonneg (by linarith) ?_)
  exact one_le_kap1_mul hd hσ U

/-- **Ключ определяет вес с множителем `1 + ξ`.** -/
lemma loKey1_kap (hd : ∀ i, 0 < d i) (hσ : 0 < σ2) {t θ ξ c₀ : ℝ} (hξ : 0 < ξ)
    {U U' : Finset ι} (h : loKey1 m d β σ2 t θ ξ c₀ U = loKey1 m d β σ2 t θ ξ c₀ U') :
    kap1 d β σ2 U ≤ (1 + ξ) * kap1 d β σ2 U' := by
  have hb : kb1 d β σ2 ξ U = kb1 d β σ2 ξ U' := congrArg (fun p => p.2.1) h
  obtain ⟨_, h2⟩ := kb1_spec (β := β) hd hσ hξ U
  obtain ⟨h1', _⟩ := kb1_spec (β := β) hd hσ hξ U'
  rw [hb] at h2
  have : kap1 d β σ2 U * σ2 ≤ (1 + ξ) * kap1 d β σ2 U' * σ2 := by nlinarith
  have hσ' : 0 < σ2 := hσ
  nlinarith

lemma mw1_pos (hσ : 0 < σ2) {ξ c₀ : ℝ} (hξ : 0 < ξ) (hc₀ : 0 < c₀) (b : ℤ) :
    0 < mw1 σ2 ξ c₀ b := by
  unfold mw1
  have : 0 < (1 + ξ) ^ (b : ℝ) / σ2 := by
    have := Real.rpow_pos_of_pos (by linarith : (0:ℝ) < 1 + ξ) (b : ℝ); positivity
  exact mul_pos hc₀ (Real.sqrt_pos.mpr this)

/-- Ширина корзины момента не больше `c₀√κ(U)`. -/
lemma mw1_le (hd : ∀ i, 0 < d i) (hσ : 0 < σ2) {ξ c₀ : ℝ} (hξ : 0 < ξ) (hc₀ : 0 ≤ c₀)
    (U : Finset ι) :
    mw1 σ2 ξ c₀ (kb1 d β σ2 ξ U) ≤ c₀ * Real.sqrt (kap1 d β σ2 U) := by
  obtain ⟨h1, _⟩ := kb1_spec (β := β) hd hσ hξ U
  unfold mw1
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hc₀
  rw [div_le_iff₀ hσ]
  exact h1

/-- Квадрат ширины корзины момента не меньше `c₀²κ(U)/(1+ξ)`. -/
lemma mw1_sq_ge (hd : ∀ i, 0 < d i) (hσ : 0 < σ2) {ξ c₀ : ℝ} (hξ : 0 < ξ)
    (U : Finset ι) :
    c₀ ^ 2 * kap1 d β σ2 U / (1 + ξ) ≤ mw1 σ2 ξ c₀ (kb1 d β σ2 ξ U) ^ 2 := by
  obtain ⟨_, h2⟩ := kb1_spec (β := β) hd hσ hξ U
  have hrp : 0 ≤ (1 + ξ) ^ (kb1 d β σ2 ξ U : ℝ) :=
    (Real.rpow_pos_of_pos (by linarith) _).le
  unfold mw1
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [div_le_iff₀ (by linarith), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg c₀)
  rw [div_mul_eq_mul_div, le_div_iff₀ hσ]
  nlinarith

/-- **Ключ определяет момент с точностью `c₀√κ`.** -/
lemma loKey1_mt (hd : ∀ i, 0 < d i) (hσ : 0 < σ2) {t θ ξ c₀ : ℝ} (hξ : 0 < ξ) (hc₀ : 0 < c₀)
    {U U' : Finset ι} (h : loKey1 m d β σ2 t θ ξ c₀ U = loKey1 m d β σ2 t θ ξ c₀ U') :
    |mt1 m d β σ2 U t - mt1 m d β σ2 U' t| ≤ c₀ * Real.sqrt (kap1 d β σ2 U) := by
  have hb : kb1 d β σ2 ξ U = kb1 d β σ2 ξ U' := congrArg (fun p => p.2.1) h
  have hm : mb1 m d β σ2 t ξ c₀ U = mb1 m d β σ2 t ξ c₀ U' := congrArg (fun p => p.2.2.1) h
  unfold mb1 at hm
  rw [← hb] at hm
  have hη := mw1_pos hσ hξ hc₀ (kb1 d β σ2 ξ U)
  exact le_trans (Factor.abs_sub_le_of_floor_eq hη hm) (mw1_le hd hσ hξ hc₀.le U)

/-- Корзина момента набора с `M² ≤ κ·Φ` лежит в `[−⌈B⌉, ⌈B⌉]`, если `(1+ξ)Φ/c₀² ≤ B²`. -/
lemma mb1_mem_Icc (hd : ∀ i, 0 < d i) (hσ : 0 < σ2) {t ξ c₀ Φ B : ℝ} (hξ : 0 < ξ)
    (hc₀ : 0 < c₀) {X : Finset ι}
    (hM : mt1 m d β σ2 X t ^ 2 ≤ kap1 d β σ2 X * Φ) (hB0 : 0 ≤ B)
    (hB : (1 + ξ) * Φ / c₀ ^ 2 ≤ B ^ 2) :
    mb1 m d β σ2 t ξ c₀ X ∈ Finset.Icc (-⌈B⌉) ⌈B⌉ := by
  set η := mw1 σ2 ξ c₀ (kb1 d β σ2 ξ X) with hηdef
  have hη : 0 < η := mw1_pos hσ hξ hc₀ _
  have hk := kap1_pos (β := β) hd hσ X
  have hη2 := mw1_sq_ge (β := β) (c₀ := c₀) hd hσ hξ X
  rw [← hηdef] at hη2
  set x := mt1 m d β σ2 X t / η with hx
  have hΦ0 : 0 ≤ Φ := by
    have := sq_nonneg (mt1 m d β σ2 X t)
    by_contra hneg
    rw [not_le] at hneg
    nlinarith
  have hx2 : x ^ 2 ≤ B ^ 2 := by
    rw [hx, div_pow, div_le_iff₀ (by positivity)]
    -- `M² ≤ κΦ ≤ B²·η²`
    have h1 : kap1 d β σ2 X * Φ ≤ B ^ 2 * η ^ 2 := by
      have hc2 : 0 < c₀ ^ 2 := by positivity
      have e : (1 + ξ) * Φ ≤ B ^ 2 * c₀ ^ 2 := by
        rw [div_le_iff₀ hc2] at hB; linarith
      have e2 : c₀ ^ 2 * kap1 d β σ2 X ≤ η ^ 2 * (1 + ξ) := by
        rw [div_le_iff₀ (by linarith)] at hη2; linarith
      nlinarith [mul_le_mul_of_nonneg_left e2 (sq_nonneg B), mul_le_mul_of_nonneg_left e hk.le]
    linarith
  have hxB : |x| ≤ B := abs_le_of_sq_le_sq' hx2 hB0 |> fun h => abs_le.mpr h
  unfold mb1
  rw [← hηdef, ← hx]
  rw [Finset.mem_Icc]
  have hxl := (abs_le.mp hxB).1
  have hxu := (abs_le.mp hxB).2
  constructor
  · rw [← Int.floor_neg]
    exact Int.floor_mono (by linarith)
  · calc ⌊x⌋ ≤ ⌈x⌉ := Int.floor_le_ceil _
      _ ≤ ⌈B⌉ := Int.ceil_mono hxu

end OneFactorKey

/-! ### Мост: данные `K = 1` ↔ однофакторная модель; оптимум long-only -/

section Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {m d : ι → ℝ} {B : ι → Unit → ℝ} {Sf P G : Unit → Unit → ℝ}

open Factor

/-- При `K = 1` из `G'G = Σ_f⁻¹` и `Σ_f⁻¹Σ_f = 1` следует `Σ_f > 0` и `Σ_f⁻¹ = 1/Σ_f`. -/
lemma sf_pos_of_root (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) :
    0 < Sf () () ∧ P () () * Sf () () = 1 := by
  have h1 := hPS () ()
  have h2 := hG () ()
  simp only [Finset.univ_unique, Finset.sum_singleton, PUnit.default_eq_unit, ite_true]
    at h1 h2
  have hP0 : 0 ≤ P () () := by rw [← h2]; exact mul_self_nonneg _
  refine ⟨?_, h1⟩
  by_contra h
  rw [not_lt] at h
  nlinarith

/-- **Однофакторная модель из данных `K = 1`**: `β_i = B_i`, `σ² = Σ_f`. -/
noncomputable def oneFactorOf (m d : ι → ℝ) (B : ι → Unit → ℝ) (Sf : Unit → Unit → ℝ)
    (hd : ∀ i, 0 < d i) (hσ : 0 < Sf () ()) : OneFactor ι :=
  ⟨m, fun i => B i (), d, Sf () (), hd, hσ⟩

/-- **Цель совпадает:** `objLO = 2m'w − (Σd_iw_i² + σ²(Σβ_iw_i)²)`. -/
lemma objLO_eq_obj (hd : ∀ i, 0 < d i) (hσ : 0 < Sf () ()) (S : Finset ι) (w : ι → ℝ) :
    objLO m d B Sf S w = (oneFactorOf m d B Sf hd hσ).obj S w := by
  rw [objLO_eq]
  simp only [quadf, Bw, OneFactor.obj, oneFactorOf, Finset.univ_unique, Finset.sum_singleton,
    PUnit.default_eq_unit]
  ring

/-- **Наименьшие квадраты на строках совпадают с `φ` однофакторной модели.** -/
lemma phi_rowsK_eq (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (S : Finset ι) (t : Unit → ℝ) :
    phi (rowsK d B G) (targetsK m d) (barK (κ := Unit) S) t
      = (oneFactorOf m d B Sf hd (sf_pos_of_root hG hPS).1).phi S (t ()) := by
  obtain ⟨hσ, hPSf⟩ := sf_pos_of_root hG hPS
  rw [phiK_eq (P := P) hd hG]
  simp only [OneFactor.phi, oneFactorOf, dotp, Finset.univ_unique, Finset.sum_singleton,
    PUnit.default_eq_unit]
  have hP : P () () = 1 / Sf () () := by
    field_simp; linarith
  rw [hP]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _ => by ring

/-- **Неподвижная точка набора `S̄` — это центроид `t̂(S)`.** -/
lemma normal_eq_that (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {S : Finset ι} {th : Unit → ℝ}
    (hnormal : IsNormal (rowsK d B G) (targetsK m d) (barK (κ := Unit) S) th) :
    th () = (oneFactorOf m d B Sf hd (sf_pos_of_root hG hPS).1).that S := by
  set Q := oneFactorOf m d B Sf hd (sf_pos_of_root hG hPS).1 with hQ
  have hmin := phi_min hnormal (fun _ => Q.that S)
  rw [phi_rowsK_eq (P := P) hd hG hPS, phi_rowsK_eq (P := P) hd hG hPS, ← hQ,
    OneFactor.phi_that, OneFactor.phi_eq_completed_square] at hmin
  have hκ : 0 < Q.kappa S := OneFactor.kappa_pos
  have hsq : (th () - Q.that S) ^ 2 = 0 := by
    have := sq_nonneg (th () - Q.that S)
    nlinarith
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  linarith

/-- **Строгая самосогласованность.** Выбросив из самосогласованного носителя активы с
нулевым весом (`m_i = t̂β_i`), получаем носитель с тем же центроидом и тем же значением,
у которого все веса строго положительны. -/
lemma strict_selfconsistent (Q : OneFactor ι) (A₀ : Finset ι)
    (hself : ∀ i ∈ A₀, 0 ≤ Q.m i - Q.that A₀ * Q.β i) :
    Q.that (A₀.filter (fun i => 0 < Q.m i - Q.that A₀ * Q.β i)) = Q.that A₀
      ∧ Q.Fval (A₀.filter (fun i => 0 < Q.m i - Q.that A₀ * Q.β i)) = Q.Fval A₀ := by
  set τ := Q.that A₀ with hτ
  set A := A₀.filter (fun i => 0 < Q.m i - τ * Q.β i) with hA
  have hzero : ∀ i ∈ A₀, ¬ (0 < Q.m i - τ * Q.β i) → Q.m i - τ * Q.β i = 0 := by
    intro i hi hn
    exact le_antisymm (not_lt.mp hn) (hself i hi)
  have hsumM : ∑ i ∈ A, Q.β i * (Q.m i - τ * Q.β i) / Q.d i
      = ∑ i ∈ A₀, Q.β i * (Q.m i - τ * Q.β i) / Q.d i := by
    rw [hA]
    refine Finset.sum_filter_of_ne fun i hi hne => ?_
    by_contra hn
    exact hne (by rw [hzero i hi hn]; ring)
  have hsumφ : ∑ i ∈ A, (Q.m i - τ * Q.β i) ^ 2 / Q.d i
      = ∑ i ∈ A₀, (Q.m i - τ * Q.β i) ^ 2 / Q.d i := by
    rw [hA]
    refine Finset.sum_filter_of_ne fun i hi hne => ?_
    by_contra hn
    exact hne (by rw [hzero i hi hn]; ring)
  have hMA₀ : Q.Mt A₀ τ = 0 := by rw [OneFactor.Mt_eq, hτ, sub_self, mul_zero]
  have hMA : Q.Mt A τ = 0 := by
    rw [← hMA₀]; simp only [OneFactor.Mt]; rw [hsumM]
  have hthat : Q.that A = τ := by
    rw [OneFactor.Mt_eq] at hMA
    have hκ : 0 < Q.kappa A := OneFactor.kappa_pos
    rcases mul_eq_zero.mp hMA with h | h
    · exact absurd h hκ.ne'
    · linarith
  refine ⟨hthat, ?_⟩
  rw [← OneFactor.phi_that, hthat, ← OneFactor.phi_that (S := A₀), ← hτ]
  simp only [OneFactor.phi]
  rw [hsumφ]

/-- **Оптимум long-only при `K = 1`, в однофакторных терминах.** Существует носитель `A`,
`|A| ≤ k`, **строго** самосогласованный (`m_i > t̂(A)β_i` на `A`), значение `F(A)` которого
не меньше значения любого long-only портфеля с не более чем `k` именами. -/
theorem exists_opt_lo1 (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) (k : ℕ) :
    ∃ A : Finset ι, A.card ≤ k
      ∧ (∀ i ∈ A, 0 < m i - (oneFactorOf m d B Sf hd (sf_pos_of_root hG hPS).1).that A * B i ())
      ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
          objLO m d B Sf S' u ≤ (oneFactorOf m d B Sf hd (sf_pos_of_root hG hPS).1).Fval A := by
  set Q := oneFactorOf m d B Sf hd (sf_pos_of_root hG hPS).1 with hQ
  obtain ⟨S, hkS, Fopt, hFopt, hSopt⟩ := exists_optimal_support (m := m) (d := d) (B := B)
    (Sf := Sf) (P := P) (G := G) hd hG hPS k
  obtain ⟨A₀, hA₀S, th, _, hnorm, hself, hgreat⟩ :=
    exists_optimal_selfconsistent (m := m) (B := B) (Sf := Sf) (P := P) (G := G) hd hG hPS S
  have hFeq : Fopt = phi (rowsK d B G) (targetsK m d) (barK (κ := Unit) A₀) th :=
    hFopt.unique hgreat
  have hth : th () = Q.that A₀ := normal_eq_that (P := P) hd hG hPS hnorm
  have hF : Fopt = Q.Fval A₀ := by
    rw [hFeq, phi_rowsK_eq (P := P) hd hG hPS, ← hQ, hth, OneFactor.phi_that]
  have hself' : ∀ i ∈ A₀, 0 ≤ Q.m i - Q.that A₀ * Q.β i := by
    intro i hi
    have h := hself (Sum.inl i) (inl_mem_barK hi) (by simp)
    have hdi := hd i
    have hs : 0 < Real.sqrt (d i) := Real.sqrt_pos.mpr hdi
    simp only [targetsK, rowsK, Sum.elim_inl, dotp, Finset.univ_unique, Finset.sum_singleton,
      PUnit.default_eq_unit] at h
    rw [hth] at h
    have h' : 0 ≤ (m i - B i () * Q.that A₀) / Real.sqrt (d i) := by
      rw [sub_div]; field_simp at h ⊢; linarith
    have h3 : 0 ≤ m i - B i () * Q.that A₀ := by
      rcases div_nonneg_iff.mp h' with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · linarith
    change 0 ≤ m i - Q.that A₀ * B i ()
    linarith
  obtain ⟨hthat, hFval⟩ := strict_selfconsistent Q A₀ hself'
  refine ⟨A₀.filter (fun i => 0 < Q.m i - Q.that A₀ * Q.β i), ?_, ?_, ?_⟩
  · exact le_trans (Finset.card_filter_le _ _) (le_trans (Finset.card_le_card hA₀S) hkS)
  · intro i hi
    have := (Finset.mem_filter.mp hi).2
    rw [hthat]
    simpa [hQ, oneFactorOf] using this
  · intro S' hS' u hu
    rw [hFval, ← hF]
    exact hSopt S' hS' u hu

end Bridge

/-! ### Параметры, узлы, таблица и семейство Теоремы J -/

section SchemeDefs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Точка центра сетки: якорь `r = 0` (`none`) или `r_j = m_j/β_j` (`some j`). -/
noncomputable def ctrR (m β : ι → ℝ) : Option ι → ℝ
  | none => 0
  | some j => m j / β j

/-- Вес центра: `1/σ²` у якоря, `u_j = β_j²/d_j` у актива. -/
noncomputable def ctrU (d β : ι → ℝ) (σ2 : ℝ) : Option ι → ℝ
  | none => 1 / σ2
  | some j => β j ^ 2 / d j

/-- Шаг сетки вокруг центра `c` при догадке `V`: `√(εV/(k+1))/(2√u_c)`. -/
noncomputable def loStep (d β : ι → ℝ) (σ2 : ℝ) (k : ℕ) (ε V : ℝ) (c : Option ι) : ℝ :=
  Real.sqrt (ε * V / ((k : ℝ) + 1)) / (2 * Real.sqrt (ctrU d β σ2 c))

/-- Радиус номеров узлов: `Z = ⌈4√(2(k+1)/ε) + 1/2⌉`; величин входа в нём нет. -/
noncomputable def loZ (k : ℕ) (ε : ℝ) : ℕ := ⌈4 * Real.sqrt (2 * ((k : ℝ) + 1) / ε) + 1 / 2⌉₊

/-- **Узлы схемы при догадке `V`**: сетка `r_c + z·s_c`, `|z| ≤ Z`, вокруг каждого из `M + 1`
центров (якорь и все активы) и точки `r_i` всех активов (Л1). -/
noncomputable def loNodes (m d β : ι → ℝ) (σ2 : ℝ) (k : ℕ) (ε V : ℝ) : Finset ℝ :=
  ((Finset.univ : Finset (Option ι)) ×ˢ Finset.Icc (-(loZ k ε : ℤ)) (loZ k ε : ℤ)).image
      (fun p => ctrR m β p.1 + (p.2 : ℝ) * loStep d β σ2 k ε V p.1)
    ∪ (Finset.univ : Finset ι).image (fun i => m i / β i)

/-- Единица округления цели: `θ = εV/k`. -/
noncomputable def loTheta (k : ℕ) (ε V : ℝ) : ℝ := ε * V / k

/-- Шаг геометрических корзин веса: `ξ = 1/(2M)`. -/
noncomputable def loXi (Mc : ℕ) : ℝ := 1 / (2 * (Mc : ℝ))

/-- Масштаб корзин момента: `c₀ = √(εV)/(4√2·M)`. -/
noncomputable def loC0 (Mc : ℕ) (ε V : ℝ) : ℝ := Real.sqrt (ε * V) / (4 * Real.sqrt 2 * (Mc : ℝ))

/-- Граница `Q̃`: `⌈2(1+ε)k/ε⌉`. -/
noncomputable def loQTm (k : ℕ) (ε : ℝ) : ℤ := ⌈2 * (1 + ε) * (k : ℝ) / ε⌉

/-- Граница корзины веса: `⌈log_{1+ξ}(σ²κ(все активы))⌉` — логарифм отношения величин входа
`1 + σ²Σ_iβ_i²/d_i`. -/
noncomputable def loKBm (d β : ι → ℝ) (σ2 : ℝ) : ℤ :=
  ⌈Real.logb (1 + loXi (Fintype.card ι)) (kap1 d β σ2 Finset.univ * σ2)⌉

/-- Вещественная граница корзины момента: `4√2·M·√((1+ξ)(2(1+ε) + ε(Q̃_max + k)/k)/ε)`. -/
noncomputable def loMBreal (Mc k : ℕ) (ε : ℝ) : ℝ :=
  4 * Real.sqrt 2 * (Mc : ℝ)
    * Real.sqrt ((1 + loXi Mc) * (2 * (1 + ε) + ε * ((loQTm k ε : ℝ) + k) / k) / ε)

/-- Граница корзины момента. -/
noncomputable def loMBm (Mc k : ℕ) (ε : ℝ) : ℤ := ⌈loMBreal Mc k ε⌉

/-- Коробка ключей `[0, Q̃_max] × [0, KB_max] × [−MB_max, MB_max] × [0, k]`. -/
def loBox (QTm KBm MBm : ℤ) (k : ℕ) : Finset LoKey :=
  Finset.Icc 0 QTm ×ˢ (Finset.Icc 0 KBm ×ˢ (Finset.Icc (-MBm) MBm ×ˢ Finset.range (k + 1)))

/-- Коробка ключей схемы. -/
noncomputable def lo1Box (d β : ι → ℝ) (σ2 : ℝ) (k : ℕ) (ε : ℝ) : Finset LoKey :=
  loBox (loQTm k ε) (loKBm d β σ2) (loMBm (Fintype.card ι) k ε) k

/-- **Таблица Теоремы J** в узле `t` при догадке `V`: пул `{i : tβ_i ≤ m_i}`, ключ
`loKey1`, в корзине — набор с минимальным точным `M_t`, ключи вне коробки отбрасываются. -/
noncomputable def lo1Table (m d β : ι → ℝ) (σ2 : ℝ) (k : ℕ) (ε V t : ℝ) (La : List ι) :
    Finset (Finset ι) :=
  minMTable (fun U => -mt1 m d β σ2 U t)
    (loKey1 m d β σ2 t (loTheta k ε V) (loXi (Fintype.card ι)) (loC0 (Fintype.card ι) ε V))
    (fun i => decide (t * β i ≤ m i)) (lo1Box d β σ2 k ε) La

/-- Семейство при одной догадке: все таблицы во всех узлах. -/
noncomputable def lo1Family (m d β : ι → ℝ) (σ2 : ℝ) (k : ℕ) (ε V : ℝ) (La : List ι) :
    Finset (Finset ι) :=
  (loNodes m d β σ2 k ε V).biUnion (fun t => lo1Table m d β σ2 k ε V t La)

/-- **Семейство кандидатов Теоремы J** по всем догадкам `V_j = L·2^j`, `j ≤ J`. -/
noncomputable def lo1Candidates (m d β : ι → ℝ) (σ2 : ℝ) (k : ℕ) (ε L : ℝ) (J : ℕ)
    (La : List ι) : Finset (Finset ι) :=
  (Finset.range (J + 1)).biUnion (fun j => lo1Family m d β σ2 k ε (L * 2 ^ j) La)

/-- Граница размера одной таблицы: мощность коробки
`(Q̃_max + 1)·(KB_max + 1)·(2MB_max + 1)·(k + 1)`. -/
noncomputable def lo1TableBound (d β : ι → ℝ) (σ2 : ℝ) (k : ℕ) (ε : ℝ) : ℕ :=
  (loQTm k ε + 1).toNat * ((loKBm d β σ2 + 1).toNat
    * ((2 * loMBm (Fintype.card ι) k ε + 1).toNat * (k + 1)))

lemma card_loBox (QTm KBm MBm : ℤ) (k : ℕ) :
    (loBox QTm KBm MBm k).card
      = (QTm + 1).toNat * ((KBm + 1).toNat * ((2 * MBm + 1).toNat * (k + 1))) := by
  simp only [loBox, Finset.card_product, Int.card_Icc, Finset.card_range]
  congr 3
  · omega
  · omega
  · omega

lemma card_loNodes_le (m d β : ι → ℝ) (σ2 : ℝ) (k : ℕ) (ε V : ℝ) :
    (loNodes m d β σ2 k ε V).card
      ≤ (Fintype.card ι + 1) * (2 * loZ k ε + 1) + Fintype.card ι := by
  unfold loNodes
  refine le_trans (Finset.card_union_le _ _) (add_le_add ?_ ?_)
  · refine le_trans Finset.card_image_le (le_of_eq ?_)
    rw [Finset.card_product, Finset.card_univ, Fintype.card_option, Int.card_Icc]
    congr 1
    omega
  · exact le_trans Finset.card_image_le (by simp)

lemma card_lo1Table_le (m d β : ι → ℝ) (σ2 : ℝ) (k : ℕ) (ε V t : ℝ) (La : List ι) :
    (lo1Table m d β σ2 k ε V t La).card ≤ lo1TableBound d β σ2 k ε + 1 := by
  unfold lo1Table
  refine le_trans (minMTable_card_le _ _ _ _ _) (le_of_eq ?_)
  rw [lo1Box, card_loBox, lo1TableBound]

lemma card_lo1Family_le (m d β : ι → ℝ) (σ2 : ℝ) (k : ℕ) (ε V : ℝ) (La : List ι) :
    (lo1Family m d β σ2 k ε V La).card
      ≤ ((Fintype.card ι + 1) * (2 * loZ k ε + 1) + Fintype.card ι)
        * (lo1TableBound d β σ2 k ε + 1) := by
  unfold lo1Family
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ _
    (fun t _ => card_lo1Table_le m d β σ2 k ε V t La)) ?_
  rw [smul_eq_mul]
  exact Nat.mul_le_mul_right _ (card_loNodes_le m d β σ2 k ε V)

/-- **Размер семейства Теоремы J**:
`(J+1)·((M+1)(2Z+1) + M)·(T_J + 1)`, `T_J = (Q̃_max+1)(KB_max+1)(2MB_max+1)(k+1)`. -/
theorem card_lo1Candidates_le (m d β : ι → ℝ) (σ2 : ℝ) (k : ℕ) (ε L : ℝ) (J : ℕ)
    (La : List ι) :
    (lo1Candidates m d β σ2 k ε L J La).card
      ≤ (J + 1) * (((Fintype.card ι + 1) * (2 * loZ k ε + 1) + Fintype.card ι)
        * (lo1TableBound d β σ2 k ε + 1)) := by
  unfold lo1Candidates
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ _
    (fun j _ => card_lo1Family_le m d β σ2 k ε (L * 2 ^ j) La)) ?_
  rw [Finset.card_range, smul_eq_mul]

/-- У каждого члена таблицы не больше `k` активов. -/
lemma card_le_of_mem_lo1Table {m d β : ι → ℝ} {σ2 : ℝ} {k : ℕ} {ε V t : ℝ} {La : List ι}
    {R : Finset ι} (hR : R ∈ lo1Table m d β σ2 k ε V t La) : R.card ≤ k := by
  unfold lo1Table at hR
  rcases minMTable_key_mem _ _ _ _ La R hR with h | h
  · rw [h]; simp
  · simp only [lo1Box, loBox, loKey1, Finset.mem_product, Finset.mem_range] at h
    omega

/-- У каждого кандидата не больше `k` активов. -/
theorem card_le_of_mem_lo1Candidates {m d β : ι → ℝ} {σ2 : ℝ} {k : ℕ} {ε L : ℝ} {J : ℕ}
    {La : List ι} {R : Finset ι} (hR : R ∈ lo1Candidates m d β σ2 k ε L J La) :
    R.card ≤ k := by
  unfold lo1Candidates lo1Family at hR
  simp only [Finset.mem_biUnion] at hR
  obtain ⟨j, _, t, _, hRt⟩ := hR
  exact card_le_of_mem_lo1Table hRt

end SchemeDefs

/-! ### Вспомогательные оценки для одной догадки -/

section GuessAux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {m d β : ι → ℝ}

lemma q1_nonneg (hd : ∀ i, 0 < d i) (t : ℝ) (i : ι) : 0 ≤ q1 m d β t i := by
  have := hd i; unfold q1; positivity

lemma floor_q1_nonneg (hd : ∀ i, 0 < d i) {t θ : ℝ} (hθ : 0 < θ) (i : ι) :
    0 ≤ ⌊q1 m d β t i / θ⌋ :=
  Int.floor_nonneg.mpr (div_nonneg (q1_nonneg hd t i) hθ.le)

lemma qt1_nonneg (hd : ∀ i, 0 < d i) {t θ : ℝ} (hθ : 0 < θ) (U : Finset ι) :
    0 ≤ qt1 m d β t θ U :=
  Finset.sum_nonneg fun i _ => floor_q1_nonneg hd hθ i

lemma qt1_mono (hd : ∀ i, 0 < d i) {t θ : ℝ} (hθ : 0 < θ) {U U' : Finset ι} (h : U' ⊆ U) :
    qt1 m d β t θ U' ≤ qt1 m d β t θ U :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun i _ _ => floor_q1_nonneg hd hθ i

/-- `θ·Q̃(U) ≤ Σ_{i∈U} q_i`. -/
lemma qt1_mul_le {t θ : ℝ} (hθ : 0 < θ) (U : Finset ι) :
    (qt1 m d β t θ U : ℝ) * θ ≤ ∑ i ∈ U, q1 m d β t i := by
  unfold qt1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have := Int.floor_le (q1 m d β t i / θ)
  rwa [le_div_iff₀ hθ] at this

/-- `Σ_{i∈U} q_i ≤ θ·(Q̃(U) + |U|)`. -/
lemma sum_q1_le {t θ : ℝ} (hθ : 0 < θ) (U : Finset ι) :
    ∑ i ∈ U, q1 m d β t i ≤ θ * ((qt1 m d β t θ U : ℝ) + U.card) := by
  unfold qt1
  push_cast
  rw [mul_add, Finset.mul_sum, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have := Int.lt_floor_add_one (q1 m d β t i / θ)
  rw [div_lt_iff₀ hθ] at this
  push_cast
  linarith

/-- `Σ_{i∈U} q_i − θ|U| ≤ θ·Q̃(U)`. -/
lemma sum_q1_sub_le {t θ : ℝ} (hθ : 0 < θ) (U : Finset ι) :
    ∑ i ∈ U, q1 m d β t i - θ * U.card ≤ (qt1 m d β t θ U : ℝ) * θ := by
  have := sum_q1_le (m := m) (d := d) (β := β) (t := t) hθ U
  linarith

variable (Q : OneFactor ι)

lemma phi_eq_q1 (U : Finset ι) (t : ℝ) :
    Q.phi U t = t ^ 2 / Q.σ2 + ∑ i ∈ U, q1 Q.m Q.d Q.β t i := rfl

lemma kappa_eq_kap1 (U : Finset ι) : Q.kappa U = kap1 Q.d Q.β Q.σ2 U := rfl

lemma Mt_eq_mt1 (U : Finset ι) (t : ℝ) : Q.Mt U t = mt1 Q.m Q.d Q.β Q.σ2 U t := rfl

/-- **Самый тяжёлый центр `Ā`.** Среди якоря и активов `A` есть центр `c` с весом
`u_c ≤ κ(A) ≤ (k+1)·u_c` и `u_c·(r_c − t̂(A))² ≤ F(A)`. -/
lemma exists_heavy_center (hβ : ∀ i, 0 < Q.β i) {A : Finset ι} (hA : A.Nonempty) {k : ℕ}
    (hAk : A.card ≤ k) :
    ∃ c : Option ι, (∀ j, c = some j → j ∈ A)
      ∧ 0 < ctrU Q.d Q.β Q.σ2 c ∧ ctrU Q.d Q.β Q.σ2 c ≤ Q.kappa A
      ∧ Q.kappa A ≤ ((k : ℝ) + 1) * ctrU Q.d Q.β Q.σ2 c
      ∧ ctrU Q.d Q.β Q.σ2 c * (ctrR Q.m Q.β c - Q.that A) ^ 2 ≤ Q.Fval A := by
  obtain ⟨j₀, hj₀, hmax⟩ := Finset.exists_max_image A (fun i => Q.β i ^ 2 / Q.d i) hA
  have hσ := Q.hσ2
  have hsum : ∑ i ∈ A, Q.β i ^ 2 / Q.d i ≤ (A.card : ℝ) * (Q.β j₀ ^ 2 / Q.d j₀) := by
    calc ∑ i ∈ A, Q.β i ^ 2 / Q.d i ≤ ∑ _i ∈ A, Q.β j₀ ^ 2 / Q.d j₀ := Finset.sum_le_sum hmax
      _ = (A.card : ℝ) * (Q.β j₀ ^ 2 / Q.d j₀) := by simp
  have hAk' : (A.card : ℝ) ≤ k := by exact_mod_cast hAk
  have hsum0 : 0 ≤ ∑ i ∈ A, Q.β i ^ 2 / Q.d i :=
    Finset.sum_nonneg fun i _ => by have := Q.hd i; positivity
  have hκ : Q.kappa A = 1 / Q.σ2 + ∑ i ∈ A, Q.β i ^ 2 / Q.d i := rfl
  have huj₀ : 0 < Q.β j₀ ^ 2 / Q.d j₀ := by have := Q.hd j₀; have := hβ j₀; positivity
  by_cases hcase : Q.β j₀ ^ 2 / Q.d j₀ ≤ 1 / Q.σ2
  · refine ⟨none, (fun j h => by cases h), (by simp only [ctrU]; positivity), ?_, ?_, ?_⟩
    · simp only [ctrU]; rw [hκ]; linarith
    · simp only [ctrU]
      rw [hκ]
      have h1 : (A.card : ℝ) * (Q.β j₀ ^ 2 / Q.d j₀) ≤ (k : ℝ) * (1 / Q.σ2) := by
        have : (0:ℝ) ≤ A.card := Nat.cast_nonneg _
        nlinarith
      nlinarith
    · simp only [ctrU, ctrR]
      have := OneFactor.anchor_le_Fval (P := Q) (S := A)
      have e : 1 / Q.σ2 * (0 - Q.that A) ^ 2 = Q.that A ^ 2 / Q.σ2 := by ring
      rw [e]; exact this
  · rw [not_le] at hcase
    refine ⟨some j₀, (fun j h => by cases h; exact hj₀), (by simp only [ctrU]; exact huj₀),
      ?_, ?_, ?_⟩
    · simp only [ctrU]
      rw [hκ]
      have := Finset.single_le_sum (f := fun i => Q.β i ^ 2 / Q.d i)
        (fun i _ => by have := Q.hd i; positivity) hj₀
      have : (0:ℝ) < 1 / Q.σ2 := by positivity
      linarith
    · simp only [ctrU]
      rw [hκ]
      have h1 : (A.card : ℝ) * (Q.β j₀ ^ 2 / Q.d j₀) ≤ (k : ℝ) * (Q.β j₀ ^ 2 / Q.d j₀) :=
        mul_le_mul_of_nonneg_right hAk' huj₀.le
      nlinarith
    · simp only [ctrU, ctrR]
      have := OneFactor.term_le_Fval (P := Q) hj₀
      have hb := (hβ j₀).ne'
      have hd0 := (Q.hd j₀).ne'
      have e : Q.β j₀ ^ 2 / Q.d j₀ * (Q.m j₀ / Q.β j₀ - Q.that A) ^ 2
          = (Q.m j₀ - Q.that A * Q.β j₀) ^ 2 / Q.d j₀ := by
        field_simp
      rw [e]; exact this

end GuessAux

/-! ### Одна догадка: шаг Теоремы J в конкретной схеме -/

section OneGuess

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Одна догадка (шаг Теоремы J).** Пусть `β > 0`, `A`, `0 < |A| ≤ k`, — строго
самосогласованный носитель (`m_i > t̂(A)β_i` на `A`), `V ≤ F(A) ≤ 2V`, `0 < ε ≤ 1`. Тогда в
семействе догадки `V` есть носитель `R`, самосогласованный (`m_i > t̂(R)β_i` на `R`, так что
`F_LO(R) = F(R)`), с `F(R) ≥ (1 − 33ε/8)·F(A)`.

Ход: самый тяжёлый центр `Ā` (`exists_heavy_center`) даёт шаг сетки `≤ W/2`,
`W = √(εF/κ)`; узел — Л1 (`lo_node_exists_grid`); пул `{tβ_i ≤ m_i}` содержит `A`
(`pool_contains`); инвариант `minMTable_spec` даёт представителя с `Q̃(R) = Q̃(A)`,
`M(A) − Δ ≤ M(R) ≤ M(A)`, `κ(A) ≤ 2κ(R)` (`(1 + 1/(2M))^M ≤ 2`); коробка содержит нужные
ключи (`Q̃ ≤ 2(1+ε)k/ε`, корзина веса — по `κ(все активы)`, корзина момента — `mb1_mem_Icc`);
шаг — `lo_step`, самосогласованность — `selfconsistent_of_Mt_neg`. -/
theorem lo1_one_guess [Nonempty ι] (Q : OneFactor ι) (hβ : ∀ i, 0 < Q.β i)
    {k : ℕ} {ε V : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {A : Finset ι} (hAk : A.card ≤ k) (hAne : A.Nonempty)
    (hself : ∀ i ∈ A, 0 < Q.m i - Q.that A * Q.β i)
    (hV : 0 < V) (hVF : V ≤ Q.Fval A) (hFV : Q.Fval A ≤ 2 * V)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La) :
    ∃ R ∈ lo1Family Q.m Q.d Q.β Q.σ2 k ε V La,
      (1 - 33 * ε / 8) * Q.Fval A ≤ Q.Fval R ∧ ∀ i ∈ R, 0 < Q.m i - Q.that R * Q.β i := by
  classical
  have hσ := Q.hσ2
  have hk1 : 1 ≤ k := le_trans (Finset.card_pos.mpr hAne) hAk
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk1
  have hF0 : 0 < Q.Fval A := lt_of_lt_of_le hV hVF
  have hκ : 0 < Q.kappa A := OneFactor.kappa_pos
  have hM0 : 0 < Fintype.card ι := Fintype.card_pos
  have hMr : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hM0
  -- 1. самый тяжёлый центр и шаг сетки
  obtain ⟨c, _, hu, huκ, hκu, hterm⟩ := exists_heavy_center Q hβ hAne hAk
  set u := ctrU Q.d Q.β Q.σ2 c with hudef
  set W := Real.sqrt (ε * Q.Fval A / Q.kappa A) with hW
  set s := loStep Q.d Q.β Q.σ2 k ε V c with hs
  set Rad := 2 * Real.sqrt (2 * V / u) with hRad
  have hWpos : 0 < W := Real.sqrt_pos.mpr (by positivity)
  have hW2 : W ^ 2 = ε * Q.Fval A / Q.kappa A := Real.sq_sqrt (by positivity)
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hspos : 0 < s := by
    rw [hs, loStep]
    have : 0 < Real.sqrt (ε * V / ((k : ℝ) + 1)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have hs2 : s ^ 2 = ε * V / (((k : ℝ) + 1) * (4 * u)) := by
    rw [hs, loStep, div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hu.le]
    field_simp
    ring
  have hstep : s ≤ W / 2 := by
    have key : ε * V / (((k : ℝ) + 1) * (4 * u)) ≤ ε * Q.Fval A / (4 * Q.kappa A) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : V * Q.kappa A ≤ Q.Fval A * (((k : ℝ) + 1) * u) := by
        have e1 := mul_le_mul_of_nonneg_right hVF hκ.le
        have e2 := mul_le_mul_of_nonneg_left hκu hF0.le
        linarith
      have e3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 4 * ε)
      linarith
    have h2 : s ^ 2 ≤ (W / 2) ^ 2 := by
      rw [hs2, div_pow, hW2]
      have e : ε * Q.Fval A / Q.kappa A / 2 ^ 2 = ε * Q.Fval A / (4 * Q.kappa A) := by ring
      rw [e]; exact key
    have h0 : 0 ≤ W / 2 := by positivity
    exact (abs_le_of_sq_le_sq' h2 h0).2
  -- 2. диапазон сетки
  have hrange : |Q.that A + 3 * W / 4 - ctrR Q.m Q.β c| ≤ Rad := by
    have h1 : |ctrR Q.m Q.β c - Q.that A| ≤ Real.sqrt (Q.Fval A / u) := by
      apply Real.abs_le_sqrt
      rw [le_div_iff₀ hu]; linarith
    have h2 : W ≤ Real.sqrt (Q.Fval A / u) := by
      apply Real.sqrt_le_sqrt
      have e1 : ε * Q.Fval A / Q.kappa A ≤ Q.Fval A / Q.kappa A := by
        apply div_le_div_of_nonneg_right _ hκ.le
        nlinarith
      have e2 : Q.Fval A / Q.kappa A ≤ Q.Fval A / u :=
        div_le_div_of_nonneg_left hF0.le hu huκ
      linarith
    have h3 : Real.sqrt (Q.Fval A / u) ≤ Real.sqrt (2 * V / u) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hFV hu.le)
    have h4 := abs_le.mp h1
    have hW0 : 0 ≤ W := hWpos.le
    rw [abs_le, hRad]
    constructor <;> linarith [Real.sqrt_nonneg (2 * V / u)]
  -- 3. Л1: узел
  set rs := A.image (fun i => Q.m i / Q.β i) with hrs
  have hrsne : rs.Nonempty := hAne.image _
  set rmin := rs.min' hrsne with hrmin
  have hμ : Q.that A < rmin := by
    obtain ⟨i, hi, hieq⟩ := Finset.mem_image.mp (Finset.min'_mem rs hrsne)
    rw [hrmin, ← hieq, lt_div_iff₀ (hβ i)]
    linarith [hself i hi]
  obtain ⟨t, htlo, hthi, htr, hcase⟩ :=
    OneFactor.lo_node_exists_grid hWpos hμ hspos hstep hrange
  -- узел лежит в перебираемом семействе
  have htnode : t ∈ loNodes Q.m Q.d Q.β Q.σ2 k ε V := by
    rcases hcase with ht | ⟨z, ht, hz⟩
    · refine Finset.mem_union_right _ ?_
      obtain ⟨i, _, hieq⟩ := Finset.mem_image.mp (Finset.min'_mem rs hrsne)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by rw [hieq, ht]⟩
    · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(c, z), ?_, ?_⟩)
      · refine Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩
        have hRs : Rad / s ≤ 4 * Real.sqrt (2 * ((k : ℝ) + 1) / ε) := by
          have hb : 0 ≤ 4 * Real.sqrt (2 * ((k : ℝ) + 1) / ε) := by positivity
          have hsq : (Rad / s) ^ 2 ≤ (4 * Real.sqrt (2 * ((k : ℝ) + 1) / ε)) ^ 2 := by
            rw [div_pow, hs2, hRad, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
              Real.sq_sqrt (by positivity)]
            apply le_of_eq
            field_simp
            ring
          exact (abs_le_of_sq_le_sq' hsq hb).2
        have hzZ : |(z : ℝ)| ≤ (loZ k ε : ℝ) :=
          le_trans hz (le_trans (by linarith) (Nat.le_ceil _))
        have hzZ' := abs_le.mp hzZ
        rw [Finset.mem_Icc]
        constructor
        · exact_mod_cast hzZ'.1
        · exact_mod_cast hzZ'.2
      · simp only
        rw [ht]
  -- свойства узла
  have hdev : 0 < t - Q.that A := by linarith
  have hnode : Q.kappa A * (t - Q.that A) ^ 2 ≤ ε * Q.Fval A := by
    have h1 : (t - Q.that A) ^ 2 ≤ W ^ 2 := pow_le_pow_left₀ hdev.le (by linarith) 2
    rw [hW2, le_div_iff₀ hκ] at h1
    linarith
  have hpool : ∀ i ∈ A, t * Q.β i ≤ Q.m i :=
    OneFactor.pool_contains (P := Q) (fun i _ => hβ i)
      (fun i hi => le_trans htr (Finset.min'_le rs _ (Finset.mem_image_of_mem _ hi)))
  have hφt : Q.phi A t ≤ (1 + ε) * Q.Fval A := OneFactor.phi_le_of_dev_sq hε.le hnode
  have hsumA0 : 0 ≤ ∑ i ∈ A, q1 Q.m Q.d Q.β t i :=
    Finset.sum_nonneg fun i _ => q1_nonneg Q.hd t i
  have ht2 : t ^ 2 / Q.σ2 ≤ 2 * (1 + ε) * V := by
    have e1 := phi_eq_q1 Q A t
    have e2 := mul_le_mul_of_nonneg_left hFV (by linarith : (0:ℝ) ≤ 1 + ε)
    linarith
  -- 4. динамика
  set θ := loTheta k ε V with hθdef
  set ξ := loXi (Fintype.card ι) with hξdef
  set c₀ := loC0 (Fintype.card ι) ε V with hc₀def
  have hθ : 0 < θ := by rw [hθdef, loTheta]; positivity
  have hξ : 0 < ξ := by rw [hξdef, loXi]; positivity
  have hc₀ : 0 < c₀ := by
    rw [hc₀def, loC0]
    have : 0 < Real.sqrt (ε * V) := Real.sqrt_pos.mpr (by positivity)
    have : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  have hθk : θ * k = ε * V := by rw [hθdef, loTheta]; field_simp
  -- `Q̃(A) ≤ Q̃_max`
  have hQTA : qt1 Q.m Q.d Q.β t θ A ≤ loQTm k ε := by
    have h1 : (qt1 Q.m Q.d Q.β t θ A : ℝ) * θ ≤ 2 * (1 + ε) * V := by
      have e1 := qt1_mul_le (m := Q.m) (d := Q.d) (β := Q.β) (t := t) hθ A
      have e2 := phi_eq_q1 Q A t
      have e3 : 0 ≤ t ^ 2 / Q.σ2 := by positivity
      have e4 := mul_le_mul_of_nonneg_left hFV (by linarith : (0:ℝ) ≤ 1 + ε)
      linarith
    have h2 : (qt1 Q.m Q.d Q.β t θ A : ℝ) ≤ 2 * (1 + ε) * (k : ℝ) / ε := by
      rw [le_div_iff₀ hε]
      have h3 : (qt1 Q.m Q.d Q.β t θ A : ℝ) * (ε * V) ≤ 2 * (1 + ε) * (k : ℝ) * V := by
        rw [← hθk]
        have := mul_le_mul_of_nonneg_right h1 hkpos.le
        linarith
      have h4 : ((qt1 Q.m Q.d Q.β t θ A : ℝ) * ε) * V ≤ (2 * (1 + ε) * (k : ℝ)) * V := by
        linarith
      exact le_of_mul_le_mul_right h4 hV
    have := le_trans h2 (Int.le_ceil _)
    unfold loQTm
    exact_mod_cast this
  -- коробка содержит ключи всех нужных наборов
  have hbox : ∀ X U' : Finset ι, U' ⊆ A → qt1 Q.m Q.d Q.β t θ X = qt1 Q.m Q.d Q.β t θ U' →
      X.card = U'.card → loKey1 Q.m Q.d Q.β Q.σ2 t θ ξ c₀ X ∈ lo1Box Q.d Q.β Q.σ2 k ε := by
    intro X U' hU' hXQ hXc
    have hQX : qt1 Q.m Q.d Q.β t θ X ≤ loQTm k ε :=
      hXQ ▸ le_trans (qt1_mono Q.hd hθ hU') hQTA
    have hcX : X.card ≤ k := hXc ▸ le_trans (Finset.card_le_card hU') hAk
    unfold lo1Box loBox loKey1
    simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
    refine ⟨⟨hXQ ▸ qt1_nonneg Q.hd hθ U', hQX⟩, ⟨kb1_nonneg Q.hd hσ hξ X, ?_⟩, ?_, by omega⟩
    · -- корзина веса
      unfold kb1 loKBm
      refine le_trans (Int.floor_le_ceil _) (Int.ceil_mono ?_)
      refine Real.logb_le_logb_of_le (by linarith) ?_ ?_
      · have := kap1_pos (β := Q.β) Q.hd hσ X; positivity
      · refine mul_le_mul_of_nonneg_right ?_ hσ.le
        unfold kap1
        have : ∑ i ∈ X, Q.β i ^ 2 / Q.d i ≤ ∑ i, Q.β i ^ 2 / Q.d i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ X)
            (fun i _ _ => by have := Q.hd i; positivity)
        linarith
    · -- корзина момента
      set Φ := 2 * (1 + ε) * V + θ * ((loQTm k ε : ℝ) + k) with hΦ
      have hQTm0 : (0:ℝ) ≤ (loQTm k ε : ℝ) := by
        have := qt1_nonneg (m := Q.m) (d := Q.d) (β := Q.β) (t := t) Q.hd hθ A
        exact_mod_cast le_trans this hQTA
      have hphiX : Q.phi X t ≤ Φ := by
        rw [phi_eq_q1]
        have h1 := sum_q1_le (m := Q.m) (d := Q.d) (β := Q.β) (t := t) hθ X
        have h2 : (qt1 Q.m Q.d Q.β t θ X : ℝ) ≤ (loQTm k ε : ℝ) := by exact_mod_cast hQX
        have h3 : (X.card : ℝ) ≤ k := by exact_mod_cast hcX
        have h4 : θ * ((qt1 Q.m Q.d Q.β t θ X : ℝ) + X.card) ≤ θ * ((loQTm k ε : ℝ) + k) :=
          mul_le_mul_of_nonneg_left (by linarith) hθ.le
        linarith
      have hMX : mt1 Q.m Q.d Q.β Q.σ2 X t ^ 2 ≤ kap1 Q.d Q.β Q.σ2 X * Φ := by
        have h1 := OneFactor.Mt_sq_le_kappa_mul_phi (P := Q) (S := X) (t := t)
        have hk0 : 0 ≤ Q.kappa X := OneFactor.kappa_pos.le
        rw [Mt_eq_mt1, kappa_eq_kap1] at h1
        rw [kappa_eq_kap1] at hk0
        have := mul_le_mul_of_nonneg_left hphiX hk0
        linarith
      have hB0 : 0 ≤ loMBreal (Fintype.card ι) k ε := by unfold loMBreal; positivity
      have hB : (1 + ξ) * Φ / c₀ ^ 2 ≤ loMBreal (Fintype.card ι) k ε ^ 2 := by
        apply le_of_eq
        have hin : 0 ≤ (1 + ξ) * (2 * (1 + ε) + ε * ((loQTm k ε : ℝ) + k) / k) / ε := by
          positivity
        have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have h3 : Real.sqrt (ε * V) ^ 2 = ε * V := Real.sq_sqrt (by positivity)
        have h4 := Real.sq_sqrt hin
        rw [hΦ, hc₀def, loC0, loMBreal, ← hξdef]
        simp only [div_pow, mul_pow, h2, h3, h4]
        rw [hθdef, loTheta]
        field_simp
      have := mb1_mem_Icc (m := Q.m) (d := Q.d) (β := Q.β) (σ2 := Q.σ2) (t := t) Q.hd hσ hξ hc₀
        hMX hB0 hB
      rw [Finset.mem_Icc] at this
      exact this
  obtain ⟨R, hR, hQTR, _, hMle, hMge, _, hKR'⟩ := minMTable_spec
    (fun U => mt1 Q.m Q.d Q.β Q.σ2 U t) (kap1 Q.d Q.β Q.σ2) (qt1 Q.m Q.d Q.β t θ)
    (loKey1 Q.m Q.d Q.β Q.σ2 t θ ξ c₀) (fun i => decide (t * Q.β i ≤ Q.m i))
    (lo1Box Q.d Q.β Q.σ2 k ε) (fun i => ⌊q1 Q.m Q.d Q.β t i / θ⌋)
    (fun i => Q.β i * (Q.m i - t * Q.β i) / Q.d i) (fun i => Q.β i ^ 2 / Q.d i)
    hξ.le hc₀.le (fun i => by have := Q.hd i; positivity)
    (fun S => (kap1_pos (β := Q.β) Q.hd hσ S).le)
    (fun S i hi => qt1_insert hi) (fun S i hi => mt1_insert hi) (fun S i hi => kap1_insert hi)
    (fun S S' h => congrArg Prod.fst h) (fun S S' h => congrArg (fun p => p.2.2.2) h)
    (fun S S' h => loKey1_kap Q.hd hσ hξ h) (fun S S' h => loKey1_mt Q.hd hσ hξ hc₀ h)
    La hnd A (fun i _ => List.mem_toFinset.mpr (hall i))
    (fun i hi => decide_eq_true (hpool i hi)) hbox
  have hLlen : La.length = Fintype.card ι := Factor.length_of_nodup_complete hnd hall
  rw [hLlen] at hMge hKR'
  have hpow : (1 + ξ) ^ Fintype.card ι ≤ 2 := by
    rw [hξdef, loXi]; exact one_add_half_inv_pow_le_two hM0
  -- 5. шаг `lo_step`
  set Δ := (Fintype.card ι : ℝ) * (c₀ * Real.sqrt ((1 + ξ) ^ Fintype.card ι
    * kap1 Q.d Q.β Q.σ2 A)) with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  have hpow0 : 0 ≤ (1 + ξ) ^ Fintype.card ι := by positivity
  have hQR : Q.phi A t - ε * Q.Fval A ≤ Q.phi R t := by
    rw [phi_eq_q1, phi_eq_q1]
    have h1 := qt1_mul_le (m := Q.m) (d := Q.d) (β := Q.β) (t := t) hθ R
    have h2 := sum_q1_sub_le (m := Q.m) (d := Q.d) (β := Q.β) (t := t) hθ A
    rw [hQTR] at h1
    have h3 : θ * (A.card : ℝ) ≤ ε * V := by
      rw [← hθk]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hAk) hθ.le
    have h4 : ε * V ≤ ε * Q.Fval A := mul_le_mul_of_nonneg_left hVF hε.le
    linarith
  have hΔsq : 16 * Δ ^ 2 ≤ ε * Q.Fval A * Q.kappa A := by
    have hc2 : c₀ ^ 2 = ε * V / (32 * (Fintype.card ι : ℝ) ^ 2) := by
      rw [hc₀def, loC0, div_pow, Real.sq_sqrt (by positivity), mul_pow, mul_pow,
        Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      ring
    have hk0 : 0 ≤ kap1 Q.d Q.β Q.σ2 A := (kap1_pos (β := Q.β) Q.hd hσ A).le
    have hD2 : Δ ^ 2 = (Fintype.card ι : ℝ) ^ 2 * c₀ ^ 2
        * ((1 + ξ) ^ Fintype.card ι * kap1 Q.d Q.β Q.σ2 A) := by
      rw [hΔ, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      ring
    rw [hD2, hc2, ← kappa_eq_kap1]
    have hMsq : (Fintype.card ι : ℝ) ^ 2 * (ε * V / (32 * (Fintype.card ι : ℝ) ^ 2))
        = ε * V / 32 := by field_simp
    have e : 16 * ((Fintype.card ι : ℝ) ^ 2 * (ε * V / (32 * (Fintype.card ι : ℝ) ^ 2))
        * ((1 + ξ) ^ Fintype.card ι * Q.kappa A))
        = ε * V / 2 * ((1 + ξ) ^ Fintype.card ι * Q.kappa A) := by
      rw [hMsq]; ring
    rw [e]
    have h1 : (1 + ξ) ^ Fintype.card ι * Q.kappa A ≤ 2 * Q.kappa A :=
      mul_le_mul_of_nonneg_right hpow hκ.le
    have h2 : ε * V ≤ ε * Q.Fval A := mul_le_mul_of_nonneg_left hVF hε.le
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ ε * V / 2)
    have h4 := mul_le_mul_of_nonneg_right h2 hκ.le
    linarith
  have hκR : Q.kappa A ≤ 2 * Q.kappa R := by
    rw [kappa_eq_kap1, kappa_eq_kap1]
    have hkR0 : 0 ≤ kap1 Q.d Q.β Q.σ2 R := (kap1_pos (β := Q.β) Q.hd hσ R).le
    have := mul_le_mul_of_nonneg_right hpow hkR0
    linarith
  have hFR := OneFactor.lo_step (P := Q) (A := A) (R := R) (t := t) hε.le hΔ0
    OneFactor.Fval_nonneg hnode htlo hQR (by rw [Mt_eq_mt1, Mt_eq_mt1]; exact hMle)
    (by rw [Mt_eq_mt1, Mt_eq_mt1]; exact hMge) hΔsq hκR
  -- 6. самосогласованность представителя
  have hmemR := minMTable_mem _ _ _ _ La R hR
  have hpoolR : ∀ i ∈ R, t * Q.β i ≤ Q.m i := fun i hi => of_decide_eq_true (hmemR.2 i hi)
  have hMRneg : Q.Mt R t < 0 := by
    have := OneFactor.Mt_neg_of_gt_that (P := Q) (A := A) htlo
    rw [Mt_eq_mt1] at this ⊢
    linarith
  refine ⟨R, Finset.mem_biUnion.mpr ⟨t, htnode, hR⟩, hFR, ?_⟩
  exact OneFactor.selfconsistent_of_Mt_neg (fun i _ => hβ i) hpoolR hMRneg

end OneGuess

/-! ### Полиномиальная форма границы размера (Теорема J)

При `k ≥ 1`, `0 < ε ≤ 1`: размер семейства Теоремы J не больше
`138744·(J+1)·M³·k²·√k·ε⁻²·(1 + ln(1 + σ²Σ_iβ_i²/d_i))` — произведение одночленов от `J + 1`,
`M`, `k`, `1/ε` и логарифма отношения величин входа. -/

section LongOnlyPoly

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `log_{1+1/(2M)} y ≤ (2M+1)·ln y` при `y ≥ 1`. -/
lemma logb_loXi_le {Mc : ℕ} (hM : 0 < Mc) {y : ℝ} (hy : 1 ≤ y) :
    Real.logb (1 + loXi Mc) y ≤ (2 * (Mc : ℝ) + 1) * Real.log y := by
  have hMr : (0:ℝ) < Mc := by exact_mod_cast hM
  have hξ : 0 < loXi Mc := by unfold loXi; positivity
  have hlog : 1 / (2 * (Mc : ℝ) + 1) ≤ Real.log (1 + loXi Mc) := by
    have h1 := Real.one_sub_inv_le_log_of_pos (by linarith : (0:ℝ) < 1 + loXi Mc)
    have e : 1 - (1 + loXi Mc)⁻¹ = 1 / (2 * (Mc : ℝ) + 1) := by
      unfold loXi; field_simp; ring
    linarith
  have hlogpos : 0 < Real.log (1 + loXi Mc) := lt_of_lt_of_le (by positivity) hlog
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy
  have h1 : 1 ≤ (2 * (Mc : ℝ) + 1) * Real.log (1 + loXi Mc) := by
    rw [div_le_iff₀ (by positivity)] at hlog; linarith
  rw [Real.logb, div_le_iff₀ hlogpos]
  have := mul_le_mul_of_nonneg_left h1 hly
  linarith

/-- **Полиномиальная оценка размера семейства Теоремы J.** При `k ≥ 1`, `0 < ε ≤ 1`:

    |lo1Candidates| ≤ 138744·(J+1)·M³·k²·√k·ε⁻²·(1 + ln(1 + σ²Σ_iβ_i²/d_i)).

Множители: узлы `(M+1)(2Z+1) + M ≤ 41M√k/√ε`; в таблице `Q̃_max + 1 ≤ 6k/ε`,
`KB_max + 1 ≤ 3M(1 + ln(1 + σ²Σβ²/d))` (через `1/ln(1+ξ) ≤ (1+ξ)/ξ = 2M+1`, `logb_loXi_le`),
`2MB_max + 1 ≤ 47M/√ε`, `k + 1 ≤ 2k`, а `T + 1 ≤ 2T`; `138744 = 41·2·6·3·47·2`. -/
theorem card_lo1Candidates_poly [Nonempty ι] (m d β : ι → ℝ) (σ2 : ℝ) (hd : ∀ i, 0 < d i)
    (hσ : 0 < σ2) {k : ℕ} (hk1 : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (L : ℝ) (J : ℕ)
    (La : List ι) :
    ((lo1Candidates m d β σ2 k ε L J La).card : ℝ)
      ≤ 138744 * ((J : ℝ) + 1) * (Fintype.card ι : ℝ) ^ 3 * (k : ℝ) ^ 2 * Real.sqrt (k : ℝ)
          / ε ^ 2 * (1 + Real.log (1 + σ2 * ∑ i, β i ^ 2 / d i)) := by
  have hcard := card_lo1Candidates_le m d β σ2 k ε L J La
  set M := Fintype.card ι with hMdef
  have hM0 : 0 < M := Fintype.card_pos
  have hM1 : (1:ℝ) ≤ (M : ℝ) := by exact_mod_cast hM0
  have hk : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  set sε := Real.sqrt ε with hsεdef
  have hs0 : 0 < sε := Real.sqrt_pos.mpr hε
  have hs2 : sε ^ 2 = ε := Real.sq_sqrt hε.le
  have hs1 : sε ≤ 1 := by
    have := Real.sqrt_le_sqrt hε1
    rwa [Real.sqrt_one] at this
  set q := Real.sqrt (k : ℝ) with hqdef
  have hq1 : 1 ≤ q := Real.one_le_sqrt.mpr hk
  have hq2 : q ^ 2 = (k : ℝ) := Real.sq_sqrt (by positivity)
  have hqs : 1 ≤ q / sε := by rw [le_div_iff₀ hs0]; linarith
  set y := kap1 d β σ2 Finset.univ * σ2 with hydef
  have hyeq : y = 1 + σ2 * ∑ i, β i ^ 2 / d i := by
    rw [hydef, kap1]; field_simp
  have hy : 1 ≤ y := one_le_kap1_mul hd hσ Finset.univ
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy
  -- (a) узлы: `(M+1)(2Z+1) + M ≤ 41M·√k/√ε`
  have hnodes : (((M + 1) * (2 * loZ k ε + 1) + M : ℕ) : ℝ) ≤ 41 * (M : ℝ) * (q / sε) := by
    have hroot : Real.sqrt (2 * ((k : ℝ) + 1) / ε) ≤ 2 * (q / sε) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, div_pow, hq2, hs2]
      have : 2 * ((k : ℝ) + 1) ≤ 2 ^ 2 * (k : ℝ) := by nlinarith
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right this hε.le
    have hZ : (loZ k ε : ℝ) < 4 * Real.sqrt (2 * ((k : ℝ) + 1) / ε) + 1 / 2 + 1 := by
      rw [loZ]; exact Nat.ceil_lt_add_one (by positivity)
    have h2Z : 2 * (loZ k ε : ℝ) + 1 ≤ 20 * (q / sε) := by linarith
    push_cast
    have h1 : ((M : ℝ) + 1) * (2 * (loZ k ε : ℝ) + 1) ≤ (2 * (M : ℝ)) * (20 * (q / sε)) :=
      mul_le_mul (by linarith) h2Z (by positivity) (by positivity)
    have h2 : (M : ℝ) ≤ (M : ℝ) * (q / sε) := by
      have := mul_le_mul_of_nonneg_left hqs (by positivity : (0:ℝ) ≤ (M : ℝ))
      linarith
    linarith
  -- (b) `Q̃_max + 1 ≤ 6k/ε`
  have hQT : (((loQTm k ε + 1).toNat : ℕ) : ℝ) ≤ 6 * (k : ℝ) / ε := by
    have hc0 : (0:ℤ) ≤ loQTm k ε := Int.ceil_nonneg (by positivity)
    have hcast : (((loQTm k ε + 1).toNat : ℕ) : ℝ) = (loQTm k ε : ℝ) + 1 := by
      have : (((loQTm k ε + 1).toNat : ℕ) : ℤ) = loQTm k ε + 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [hcast]
    have hc : (loQTm k ε : ℝ) < 2 * (1 + ε) * (k : ℝ) / ε + 1 := by
      unfold loQTm; exact Int.ceil_lt_add_one _
    have e : 2 * (1 + ε) * (k : ℝ) / ε = 2 * (k : ℝ) / ε + 2 * (k : ℝ) := by field_simp
    have h1 : 2 * (k : ℝ) ≤ 2 * (k : ℝ) / ε := by
      rw [le_div_iff₀ hε]; nlinarith
    have h2 : 2 ≤ 2 * (k : ℝ) / ε := by rw [le_div_iff₀ hε]; nlinarith
    have e2 : 6 * (k : ℝ) / ε = 3 * (2 * (k : ℝ) / ε) := by ring
    linarith
  -- (c) корзины веса: `KB_max + 1 ≤ 3M(1 + ln y)`
  have hb1 : 1 < 1 + loXi M := by
    have : 0 < loXi M := by unfold loXi; positivity
    linarith
  have hKB : (((loKBm d β σ2 + 1).toNat : ℕ) : ℝ) ≤ 3 * (M : ℝ) * (1 + Real.log y) := by
    have hlb : 0 ≤ Real.logb (1 + loXi M) y := Real.logb_nonneg hb1 hy
    have hc0 : (0:ℤ) ≤ loKBm d β σ2 := by unfold loKBm; exact Int.ceil_nonneg hlb
    have hcast : (((loKBm d β σ2 + 1).toNat : ℕ) : ℝ) = (loKBm d β σ2 : ℝ) + 1 := by
      have : (((loKBm d β σ2 + 1).toNat : ℕ) : ℤ) = loKBm d β σ2 + 1 :=
        Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [hcast]
    have hc : (loKBm d β σ2 : ℝ) < Real.logb (1 + loXi M) y + 1 := by
      unfold loKBm; rw [← hydef]; exact Int.ceil_lt_add_one _
    have h1 := logb_loXi_le hM0 hy
    have h2 : (2 * (M : ℝ) + 1) * Real.log y ≤ 3 * (M : ℝ) * Real.log y :=
      mul_le_mul_of_nonneg_right (by linarith) hly
    linarith
  -- (d) корзины момента: `2MB_max + 1 ≤ 47M/√ε`
  have hMB : (((2 * loMBm M k ε + 1).toNat : ℕ) : ℝ) ≤ 47 * (M : ℝ) / sε := by
    have hB0 : 0 ≤ loMBreal M k ε := by unfold loMBreal; positivity
    have h1 := Factor.cast_toNat_two_ceil_le hB0
    have hξ : loXi M ≤ 1 / 2 := by
      unfold loXi; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hξ0 : 0 ≤ loXi M := by unfold loXi; positivity
    have hQ : (loQTm k ε : ℝ) ≤ 2 * (1 + ε) * (k : ℝ) / ε + 1 := by
      unfold loQTm; exact (Int.ceil_lt_add_one _).le
    have hQ0 : (0:ℝ) ≤ (loQTm k ε : ℝ) := by
      have : (0:ℤ) ≤ loQTm k ε := Int.ceil_nonneg (by positivity)
      exact_mod_cast this
    have hin : (1 + loXi M) * (2 * (1 + ε) + ε * ((loQTm k ε : ℝ) + k) / k) ≤ 15 := by
      have e1 : ε * ((loQTm k ε : ℝ) + k) / k ≤ 6 := by
        rw [div_le_iff₀ (by linarith)]
        have : ε * (loQTm k ε : ℝ) ≤ 2 * (1 + ε) * (k : ℝ) + ε := by
          have := mul_le_mul_of_nonneg_left hQ hε.le
          have e : ε * (2 * (1 + ε) * (k : ℝ) / ε + 1) = 2 * (1 + ε) * (k : ℝ) + ε := by
            field_simp
          linarith
        nlinarith
      have e2 : 2 * (1 + ε) + ε * ((loQTm k ε : ℝ) + k) / k ≤ 10 := by linarith
      have e3 : 0 ≤ 2 * (1 + ε) + ε * ((loQTm k ε : ℝ) + k) / k := by positivity
      nlinarith
    have hsq : loMBreal M k ε ^ 2 ≤ (22 * (M : ℝ) / sε) ^ 2 := by
      have hin0 : 0 ≤ (1 + loXi M) * (2 * (1 + ε) + ε * ((loQTm k ε : ℝ) + k) / k) / ε := by
        positivity
      unfold loMBreal
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sq_sqrt hin0]
      have h15 : (1 + loXi M) * (2 * (1 + ε) + ε * ((loQTm k ε : ℝ) + k) / k) / ε ≤ 15 / ε :=
        div_le_div_of_nonneg_right hin hε.le
      have e : (22 * (M : ℝ) / sε) ^ 2 = 4 ^ 2 * 2 * (M : ℝ) ^ 2 * (484 / 32 / ε) := by
        rw [div_pow, hs2]; field_simp; ring
      rw [e]
      have h484 : 15 / ε ≤ 484 / 32 / ε := div_le_div_of_nonneg_right (by norm_num) hε.le
      have hM2 : 0 ≤ 4 ^ 2 * 2 * (M : ℝ) ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left (le_trans h15 h484) hM2
      linarith
    have hB : loMBreal M k ε ≤ 22 * (M : ℝ) / sε := (abs_le_of_sq_le_sq' hsq (by positivity)).2
    have h3 : (3:ℝ) ≤ 3 * (M : ℝ) / sε := by rw [le_div_iff₀ hs0]; linarith
    unfold loMBm
    have e : 47 * (M : ℝ) / sε = 2 * (22 * (M : ℝ) / sε) + 3 * (M : ℝ) / sε := by ring
    linarith
  -- (e) сборка
  have hTdef : (lo1TableBound d β σ2 k ε : ℝ)
      = (((loQTm k ε + 1).toNat : ℕ) : ℝ) * ((((loKBm d β σ2 + 1).toNat : ℕ) : ℝ)
        * ((((2 * loMBm M k ε + 1).toNat : ℕ) : ℝ) * ((k : ℝ) + 1))) := by
    rw [lo1TableBound]; push_cast; ring
  have hone : ∀ z : ℤ, 0 ≤ z → (1:ℝ) ≤ (((z + 1).toNat : ℕ) : ℝ) := by
    intro z hz
    have : 1 ≤ (z + 1).toNat := by omega
    exact_mod_cast this
  have hQ1 : (1:ℝ) ≤ (((loQTm k ε + 1).toNat : ℕ) : ℝ) :=
    hone _ (Int.ceil_nonneg (by positivity))
  have hK1' : (1:ℝ) ≤ (((loKBm d β σ2 + 1).toNat : ℕ) : ℝ) := by
    apply hone
    unfold loKBm
    exact Int.ceil_nonneg (Real.logb_nonneg hb1 hy)
  have hM1' : (1:ℝ) ≤ (((2 * loMBm M k ε + 1).toNat : ℕ) : ℝ) := by
    have hm0 : (0:ℤ) ≤ loMBm M k ε := by
      unfold loMBm; exact Int.ceil_nonneg (by unfold loMBreal; positivity)
    have : 1 ≤ (2 * loMBm M k ε + 1).toNat := by omega
    exact_mod_cast this
  have hT1 : (1:ℝ) ≤ (lo1TableBound d β σ2 k ε : ℝ) := by
    rw [hTdef]
    exact one_le_mul_of_one_le_of_one_le hQ1 (one_le_mul_of_one_le_of_one_le hK1'
      (one_le_mul_of_one_le_of_one_le hM1' (by linarith)))
  have hTle : (lo1TableBound d β σ2 k ε : ℝ)
      ≤ (6 * (k : ℝ) / ε) * ((3 * (M : ℝ) * (1 + Real.log y))
        * ((47 * (M : ℝ) / sε) * (2 * (k : ℝ)))) := by
    rw [hTdef]
    refine mul_le_mul hQT (mul_le_mul hKB (mul_le_mul hMB (by linarith) (by positivity)
      (by positivity)) (by positivity) (by positivity)) (by positivity) (by positivity)
  have hcast : ((lo1Candidates m d β σ2 k ε L J La).card : ℝ)
      ≤ ((J : ℝ) + 1) * ((((M + 1) * (2 * loZ k ε + 1) + M : ℕ) : ℝ)
        * ((lo1TableBound d β σ2 k ε : ℝ) + 1)) := by
    have := (Nat.cast_le (α := ℝ)).mpr hcard
    push_cast at this ⊢
    exact this
  refine le_trans hcast ?_
  have hT2 : (lo1TableBound d β σ2 k ε : ℝ) + 1
      ≤ 2 * ((6 * (k : ℝ) / ε) * ((3 * (M : ℝ) * (1 + Real.log y))
        * ((47 * (M : ℝ) / sε) * (2 * (k : ℝ))))) := by linarith
  have h1 := mul_le_mul hnodes hT2 (by positivity) (by positivity)
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ (J : ℝ) + 1)
  refine le_trans h2 (le_of_eq ?_)
  rw [← hyeq, ← hs2]
  field_simp
  ring

end LongOnlyPoly

/-! ### Теорема J из данных -/

section MainJ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {m d : ι → ℝ} {B : ι → Unit → ℝ} {Sf P G : Unit → Unit → ℝ}

open Factor

lemma OneFactor.Fval_empty_zero (Q : OneFactor ι) : Q.Fval ∅ = 0 := by
  simp [OneFactor.Fval, OneFactor.Ccoef, OneFactor.Acoef]

/-- **В семействе Теоремы J есть хороший кандидат** для любой вилки
`L ≤ F(A) ≤ 2^(J+1)·L`: носитель `R` с long-only портфелем `w ≥ 0` и
`2m'w − w'Vw ≥ (1 − 33ε/8)·F(A)`. -/
theorem exists_good_lo1Candidate [Nonempty ι] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hβ : ∀ i, 0 < B i ()) {k : ℕ} {ε L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hL0 : 0 < L)
    {J : ℕ} {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    {A : Finset ι} (hAk : A.card ≤ k)
    (hself : ∀ i ∈ A,
      0 < m i - (oneFactorOf m d B Sf hd (sf_pos_of_root hG hPS).1).that A * B i ())
    (hLF : L ≤ (oneFactorOf m d B Sf hd (sf_pos_of_root hG hPS).1).Fval A)
    (hFJ : (oneFactorOf m d B Sf hd (sf_pos_of_root hG hPS).1).Fval A ≤ 2 ^ (J + 1) * L) :
    ∃ R ∈ lo1Candidates m d (fun i => B i ()) (Sf () ()) k ε L J La, ∃ w : ι → ℝ,
      (∀ i ∈ R, 0 ≤ w i) ∧
      (1 - 33 * ε / 8) * (oneFactorOf m d B Sf hd (sf_pos_of_root hG hPS).1).Fval A
        ≤ objLO m d B Sf R w := by
  set Q := oneFactorOf m d B Sf hd (sf_pos_of_root hG hPS).1 with hQ
  have hAne : A.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, OneFactor.Fval_empty_zero] at hLF
    linarith
  obtain ⟨j, hjJ, hVF, hFV⟩ := exists_doubling_guess_succ J hL0 hLF hFJ
  have hV : 0 < L * 2 ^ j := by positivity
  obtain ⟨R, hR, hFR, hscR⟩ := lo1_one_guess Q (fun i => hβ i) hε hε1 hAk hAne hself hV
    hVF hFV hnd hall
  obtain ⟨⟨w, hw, hwv⟩, _⟩ := OneFactor.lo_value_of_selfconsistent (P := Q) (R := R)
    (fun i hi => (hscR i hi).le)
  refine ⟨R, ?_, w, hw, ?_⟩
  · unfold lo1Candidates
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (by omega), hR⟩
  · rw [objLO_eq_obj hd (sf_pos_of_root hG hPS).1, ← hQ, ← hwv]
    exact hFR

/-- **Теорема J из данных (long-only, один фактор).**

Пусть `K = 1`: `V = diag(d) + σ²ββ'` с `β_i = B_i > 0`, `d > 0`, `G'G = Σ_f⁻¹ = 1/σ²`, `k ≥ 1`,
`0 < ε < 8/33`, `L = (m_i)_+²/V_ii > 0` — значение одиночного актива (естественный выбор —
`L = max_i (m_i)_+²/V_ii`), `J = ⌈log₂((Σ_i (m_i)_+²/d_i)/L)⌉`, `La` — список всех активов без
повторов (любой порядок). Тогда семейство `lo1Candidates` обладает свойствами:
(1) размер не больше `(J+1)·((M+1)(2Z+1) + M)·(T_J + 1)`, `Z = ⌈4√(2(k+1)/ε) + 1/2⌉` (`loZ`),
`T_J = (Q̃_max+1)(KB_max+1)(2MB_max+1)(k+1)` (`lo1TableBound`) с
`Q̃_max = ⌈2(1+ε)k/ε⌉`, `MB_max = ⌈4√2·M·√((1+ξ)(2(1+ε) + ε(Q̃_max+k)/k)/ε)⌉`,
`KB_max = ⌈log_{1+ξ}(1 + σ²Σ_iβ_i²/d_i)⌉`, `ξ = 1/(2M)` — **нет `ω`**; величины входа входят
только логарифмически: в число догадок `J + 1` и в число корзин веса `KB_max + 1`;
(2) у каждого кандидата не больше `k` имён; (3) лучшая пара существует; (4) для любой лучшей
пары `(R₀, w₀)` значение не меньше `(1 − 33ε/8)` от значения **любого** long-only портфеля с
не более чем `k` именами, а полностью инвестированный портфель `x = w₀/Σw₀` имеет коэффициент
Шарпа не меньше `√(1 − 33ε/8)` от коэффициента Шарпа любого такого портфеля с положительной
ожидаемой доходностью. -/
theorem main_theorem_lo1 [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    (hβ : ∀ i, 0 < B i ())
    {k : ℕ} (hk1 : 1 ≤ k) {ε L : ℝ} (hε : 0 < ε) (hε1 : 33 * ε < 8)
    (hL0 : 0 < L) (hLatt : ∃ i, max (m i) 0 ^ 2 / Vmat d B Sf i i = L)
    {J : ℕ} (hJ : J = ⌈Real.logb 2 ((∑ i, max (m i) 0 ^ 2 / d i) / L)⌉₊)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La) :
    (lo1Candidates m d (fun i => B i ()) (Sf () ()) k ε L J La).card
        ≤ (J + 1) * (((Fintype.card ι + 1) * (2 * loZ k ε + 1) + Fintype.card ι)
          * (lo1TableBound d (fun i => B i ()) (Sf () ()) k ε + 1))
    ∧ (∀ R ∈ lo1Candidates m d (fun i => B i ()) (Sf () ()) k ε L J La, R.card ≤ k)
    ∧ (∃ R₀ ∈ lo1Candidates m d (fun i => B i ()) (Sf () ()) k ε L J La, ∃ w₀ : ι → ℝ,
        (∀ i ∈ R₀, 0 ≤ w₀ i) ∧
        ∀ R ∈ lo1Candidates m d (fun i => B i ()) (Sf () ()) k ε L J La, ∀ w : ι → ℝ,
          (∀ i ∈ R, 0 ≤ w i) → objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀)
    ∧ ∀ R₀ ∈ lo1Candidates m d (fun i => B i ()) (Sf () ()) k ε L J La, ∀ w₀ : ι → ℝ,
        (∀ i ∈ R₀, 0 ≤ w₀ i) →
        (∀ R ∈ lo1Candidates m d (fun i => B i ()) (Sf () ()) k ε L J La, ∀ w : ι → ℝ,
          (∀ i ∈ R, 0 ≤ w i) → objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀) →
        R₀.card ≤ k
        ∧ (∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
            (1 - 33 * ε / 8) * objLO m d B Sf S' u ≤ objLO m d B Sf R₀ w₀)
        ∧ (∀ i ∈ R₀, 0 ≤ (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i)
        ∧ ∑ i ∈ R₀, (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i = 1
        ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
            0 < pRet m S' u →
            Real.sqrt (1 - 33 * ε / 8) * sharpe m d B Sf S' u
              ≤ sharpe m d B Sf R₀ (fun i => (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i) := by
  have hε1' : ε ≤ 1 := by linarith
  set Q := oneFactorOf m d B Sf hd (sf_pos_of_root hG hPS).1 with hQ
  -- оптимум long-only, строго самосогласованный
  obtain ⟨A, hAk, hself, hSopt⟩ := exists_opt_lo1 (m := m) (d := d) (B := B) (Sf := Sf)
    (P := P) (G := G) hd hG hPS k
  rw [← hQ] at hself hSopt
  -- вилка `[L, 2^(J+1)L]` без `ω`
  obtain ⟨i₀, hi₀⟩ := hLatt
  have hLF : L ≤ Q.Fval A := hi₀ ▸ opt_ge_single_of_opt (B := B) hd hG hPS hk1 hSopt i₀
  have hFU : Q.Fval A ≤ ∑ i, max (m i) 0 ^ 2 / d i := by
    obtain ⟨⟨w, hw, hwv⟩, _⟩ := OneFactor.lo_value_of_selfconsistent (P := Q) (R := A)
      (fun i hi => (hself i hi).le)
    rw [hwv, hQ, ← objLO_eq_obj hd (sf_pos_of_root hG hPS).1]
    refine le_trans (objLO_le_sum_posPart (B := B) (P := P) (G := G) hd hG hPS hw) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) ?_
    intro i _ _
    have := hd i
    positivity
  have hq1 : (1:ℝ) ≤ (∑ i, max (m i) 0 ^ 2 / d i) / L := by
    rw [le_div_iff₀ hL0]; linarith
  obtain ⟨hJa, _⟩ := guess_count_spec hq1
  rw [← hJ] at hJa
  have hFJ : Q.Fval A ≤ 2 ^ (J + 1) * L := by
    have h1 : ∑ i, max (m i) 0 ^ 2 / d i ≤ 2 ^ J * L := by
      rwa [div_le_iff₀ hL0] at hJa
    have h2 : (2:ℝ) ^ J * L ≤ 2 ^ (J + 1) * L := by
      rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) J]
    linarith
  obtain ⟨R, hR, w, hw, hgood⟩ := exists_good_lo1Candidate (Sf := Sf) (P := P) hd hG hPS hβ
    hε hε1' hL0 hnd hall hAk hself hLF hFJ
  refine ⟨card_lo1Candidates_le m d (fun i => B i ()) (Sf () ()) k ε L J La,
    fun R hR => card_le_of_mem_lo1Candidates hR,
    exists_best_set_of_family (P := P) (G := G) hd hG hPS ⟨R, hR⟩, ?_⟩
  intro R₀ hR₀ w₀ hw₀ hbest
  have hval : (1 - 33 * ε / 8) * Q.Fval A ≤ objLO m d B Sf R₀ w₀ :=
    le_trans hgood (hbest R hR w hw)
  have hval' : (1 - 2 * (33 * ε / 16)) * Q.Fval A ≤ objLO m d B Sf R₀ w₀ := by
    rw [show 1 - 2 * (33 * ε / 16) = 1 - 33 * ε / 8 by ring]; exact hval
  obtain ⟨hx0, hx1, hxs⟩ := best_pair_sharpe_uniform (B := B) hd hG hPS
    (by linarith : 33 * ε / 16 < 1 / 2) (lt_of_lt_of_le hL0 hLF) hSopt hw₀ hval'
  refine ⟨card_le_of_mem_lo1Candidates hR₀, fun S' hS' u hu => ?_, hx0, hx1,
    fun S' hS' u hu hru => ?_⟩
  · have hub := hSopt S' hS' u hu
    have hcoef : (0:ℝ) ≤ 1 - 33 * ε / 8 := by linarith
    linarith [mul_le_mul_of_nonneg_left hub hcoef]
  · have := hxs S' hS' u hu hru
    rwa [show 1 - 2 * (33 * ε / 16) = 1 - 33 * ε / 8 by ring] at this

end MainJ

/-! ### Непустота

Одноактивный инстанс с `β = 1 > 0`: `m = d = 1`, `B = Σ_f = G = P = 1` (так что `V = 2`),
`k = 1`, `ε = 1/5`, `L = 1/2`, `J = ⌈log₂ 2⌉ = 1`, порядок `[0]`. Все гипотезы
`main_theorem_lo1` выполнены; заключение даёт полностью инвестированный long-only портфель с
коэффициентом Шарпа не меньше `√(1 − 33/40)·(1/√2) > 0`. -/

theorem lo1_instance :
    ∃ R₀ ∈ lo1Candidates (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1) (fun _ => 1) 1 1 (1/5) (1/2) 1
        [0],
      ∃ x : Fin 1 → ℝ, (∀ i ∈ R₀, 0 ≤ x i) ∧ ∑ i ∈ R₀, x i = 1
        ∧ Real.sqrt (1 - 33 * (1/5) / 8) * (1 / Real.sqrt 2)
          ≤ Factor.sharpe (fun _ : Fin 1 => (1:ℝ)) (fun _ => 1) (fun _ (_ : Unit) => 1)
            (fun _ _ => 1) R₀ x := by
  set m : Fin 1 → ℝ := fun _ => 1
  set d : Fin 1 → ℝ := fun _ => 1
  set B : Fin 1 → Unit → ℝ := fun _ _ => 1
  set Sf : Unit → Unit → ℝ := fun _ _ => 1
  set G : Unit → Unit → ℝ := fun _ _ => 1
  set P : Unit → Unit → ℝ := fun _ _ => 1
  have hd : ∀ i, 0 < d i := fun _ => one_pos
  have hG : ∀ j j' : Unit, ∑ l : Unit, G l j * G l j' = P j j' := by intro j j'; simp [G, P]
  have hPS : ∀ j j' : Unit, ∑ l : Unit, P j l * Sf l j' = if j = j' then 1 else 0 := by
    intro j j'; simp [P, Sf]
  have hβ : ∀ i, 0 < B i () := fun _ => one_pos
  have hVd : ∀ i, Factor.Vmat d B Sf i i = 2 := by
    intro i; simp [Factor.Vmat, d, B, Sf]; norm_num
  have hLatt : ∃ i, max (m i) 0 ^ 2 / Factor.Vmat d B Sf i i = 1 / 2 :=
    ⟨0, by rw [hVd]; simp [m]⟩
  have hJlog : (1:ℕ) = ⌈Real.logb 2 ((∑ i, max (m i) 0 ^ 2 / d i) / (1 / 2))⌉₊ := by
    have h2 : (∑ i, max (m i) 0 ^ 2 / d i) / (1 / 2) = 2 := by norm_num [m, d]
    rw [h2, Real.logb_self_eq_one (by norm_num)]
    simp
  have hnd : ([0] : List (Fin 1)).Nodup := List.nodup_singleton 0
  have hall : ∀ i : Fin 1, i ∈ ([0] : List (Fin 1)) := by
    intro i; rw [List.mem_singleton]; exact Subsingleton.elim _ _
  have hsu : Factor.sharpe m d B Sf Finset.univ (fun _ => 1) = 1 / Real.sqrt 2 := by
    simp only [Factor.sharpe, Factor.pRet, Factor.pVar]
    simp [Factor.Vmat, m, d, B, Sf]
    norm_num
  obtain ⟨_, _, ⟨R₀, hR₀, w₀, hw₀, hbest⟩, h4⟩ := main_theorem_lo1 (G := G) (P := P)
    (Sf := Sf) hd hG hPS hβ le_rfl (by norm_num : (0:ℝ) < 1/5) (by norm_num)
    (by norm_num : (0:ℝ) < 1/2) hLatt hJlog hnd hall
  obtain ⟨_, _, hx0, hx1, hxsh⟩ := h4 R₀ hR₀ w₀ hw₀ hbest
  have hsh := hxsh Finset.univ (by simp) (fun _ => 1) (fun _ _ => zero_le_one)
    (by simp [Factor.pRet, m])
  refine ⟨R₀, hR₀, _, hx0, hx1, ?_⟩
  rw [hsu] at hsh
  exact hsh

end SparseSharpe
