import Mathlib

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Динамика с аддитивным ключом (задача L1 ТЗ, сессия 23)

Обычный рюкзак: у каждого актива `i` есть вес `s i` (сколько он добавляет к значению) и
вклад в ключ `c i` из аддитивного моноида `Key`. Ключ и значение набора `U` — суммы по `U`:

    val U = Σ_{j∈U} s j,        key U = Σ_{j∈U} c j.

Таблица `knap s c box L` строится по списку `L`: на каждом шаге к таблице добавляются
наборы с новым активом, остаются только наборы с ключом в коробке `box`, и из наборов с
одним ключом выживает один — с наибольшим значением.

Так как ключ **точно** аддитивен (`Finset.sum_insert`), представитель корзины на каждом шаге
имеет в точности тот же ключ, что и соответствующий префикс оптимального набора: дрейфа,
накапливающегося с длиной списка, нет.

* `knap_card_le` — таблица не больше `|box| + 1` **при любых данных**;
* `knap_spec` — для любого набора `U ⊆ L`, все подмножества которого лежат в коробке, в
  таблице есть набор `R ⊆ L` с тем же ключом и не меньшим значением;
* `knap_mem` — всё, что лежит в таблице, лежит в `L`.

Матрица Грама, фильтр и константа покрытия здесь не участвуют: это общая рюкзачная
конструкция. Конкретные `s` и `c` для задачи — в `Factor/ClippedDP.lean`.
-/

namespace SparseSharpe.Factor

open Finset

section Knapsack

variable {ι Key : Type*} [DecidableEq ι] [AddCommMonoid Key] [DecidableEq Key]

/-- Представитель ключа `k` в семействе `F`: набор с ключом `k` и наибольшим значением. -/
noncomputable def kRep (val : Finset ι → ℝ) (key : Finset ι → Key) (F : Finset (Finset ι))
    (k : Key) : Finset ι :=
  if h : (F.filter (fun V => key V = k)).Nonempty then
    ((F.filter (fun V => key V = k)).exists_max_image val h).choose
  else ∅

/-- Усечение: по одному представителю на каждый встретившийся ключ. -/
noncomputable def kPrune (val : Finset ι → ℝ) (key : Finset ι → Key) (F : Finset (Finset ι)) :
    Finset (Finset ι) :=
  F.image (fun U => kRep val key F (key U))

variable {val : Finset ι → ℝ} {key : Finset ι → Key} {F : Finset (Finset ι)} {U : Finset ι}

lemma kRep_spec (hU : U ∈ F) :
    kRep val key F (key U) ∈ F ∧ key (kRep val key F (key U)) = key U
      ∧ val U ≤ val (kRep val key F (key U)) := by
  have hne : ((F.filter (fun V => key V = key U))).Nonempty :=
    ⟨U, Finset.mem_filter.mpr ⟨hU, rfl⟩⟩
  have hspec := ((F.filter (fun V => key V = key U)).exists_max_image val hne).choose_spec
  rw [kRep, dif_pos hne]
  obtain ⟨hmem, hmax⟩ := hspec
  have hmem' := Finset.mem_filter.mp hmem
  exact ⟨hmem'.1, hmem'.2, hmax U (Finset.mem_filter.mpr ⟨hU, rfl⟩)⟩

lemma kPrune_subset : kPrune val key F ⊆ F := by
  intro R hR
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hR
  exact (kRep_spec hU).1

lemma mem_kPrune (hU : U ∈ F) : kRep val key F (key U) ∈ kPrune val key F :=
  Finset.mem_image.mpr ⟨U, hU, rfl⟩

/-- В усечённом семействе ключи различны. -/
lemma key_injOn_kPrune : Set.InjOn key ↑(kPrune val key F) := by
  intro R₁ h₁ R₂ h₂ h
  obtain ⟨U₁, hU₁, rfl⟩ := Finset.mem_image.mp h₁
  obtain ⟨U₂, hU₂, rfl⟩ := Finset.mem_image.mp h₂
  have e₁ := (kRep_spec (val := val) (key := key) (F := F) hU₁).2.1
  have e₂ := (kRep_spec (val := val) (key := key) (F := F) hU₂).2.1
  rw [e₁, e₂] at h
  rw [h]

/-- **Таблица рюкзака.** -/
noncomputable def knap (s : ι → ℝ) (c : ι → Key) (box : Finset Key) :
    List ι → Finset (Finset ι)
  | [] => {∅}
  | i :: rest =>
      kPrune (fun U => ∑ j ∈ U, s j) (fun U => ∑ j ∈ U, c j)
        (((knap s c box rest) ∪ (knap s c box rest).image (insert i)).filter
          (fun U => ∑ j ∈ U, c j ∈ box))

lemma knap_cons (s : ι → ℝ) (c : ι → Key) (box : Finset Key) (i : ι) (rest : List ι) :
    knap s c box (i :: rest)
      = kPrune (fun U => ∑ j ∈ U, s j) (fun U => ∑ j ∈ U, c j)
        (((knap s c box rest) ∪ (knap s c box rest).image (insert i)).filter
          (fun U => ∑ j ∈ U, c j ∈ box)) := rfl

/-- Что лежит в таблице: подмножества `L`. -/
theorem knap_mem (s : ι → ℝ) (c : ι → Key) (box : Finset Key) :
    ∀ (L : List ι), ∀ R ∈ knap s c box L, R ⊆ L.toFinset := by
  intro L
  induction L with
  | nil =>
      intro R hR
      rw [knap, Finset.mem_singleton] at hR
      subst hR
      simp
  | cons i rest ih =>
      intro R hR
      rw [knap_cons] at hR
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

/-- Ключи выживших лежат в коробке (кроме пустого набора, который есть только у `[]`). -/
theorem knap_key_mem (s : ι → ℝ) (c : ι → Key) (box : Finset Key) (L : List ι) :
    ∀ R ∈ knap s c box L, R = ∅ ∨ ∑ j ∈ R, c j ∈ box := by
  intro R hR
  cases L with
  | nil =>
      rw [knap, Finset.mem_singleton] at hR
      exact Or.inl hR
  | cons i rest =>
      rw [knap_cons] at hR
      exact Or.inr (Finset.mem_filter.mp (kPrune_subset hR)).2

lemma key_injOn_knap (s : ι → ℝ) (c : ι → Key) (box : Finset Key) :
    ∀ L : List ι, Set.InjOn (fun U : Finset ι => ∑ j ∈ U, c j) ↑(knap s c box L) := by
  intro L
  cases L with
  | nil =>
      intro R₁ h₁ R₂ h₂ _
      rw [knap] at h₁ h₂
      have e₁ : R₁ = ∅ := Finset.mem_singleton.mp (by simpa using h₁)
      have e₂ : R₂ = ∅ := Finset.mem_singleton.mp (by simpa using h₂)
      rw [e₁, e₂]
  | cons i rest =>
      rw [knap_cons]
      exact key_injOn_kPrune

/-- **Размер таблицы при любых данных:** не больше `|box| + 1`. -/
theorem knap_card_le (s : ι → ℝ) (c : ι → Key) (box : Finset Key) (L : List ι) :
    (knap s c box L).card ≤ box.card + 1 := by
  rw [← Finset.card_image_of_injOn (key_injOn_knap s c box L)]
  have hsub : (knap s c box L).image (fun U : Finset ι => ∑ j ∈ U, c j)
      ⊆ insert (∑ j ∈ (∅ : Finset ι), c j) box := by
    intro k hk
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hk
    rcases knap_key_mem s c box L R hR with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem h
  refine le_trans (Finset.card_le_card hsub) ?_
  exact le_trans (Finset.card_insert_le _ _) (by omega)

/-- **Инвариант рюкзака с аддитивным ключом.** Пусть список `L` без повторов, `U ⊆ L`, и у
каждого подмножества `U` ключ лежит в коробке. Тогда в таблице есть `R` с **тем же ключом** и
не меньшим значением. -/
theorem knap_spec (s : ι → ℝ) (c : ι → Key) (box : Finset Key) :
    ∀ (L : List ι), L.Nodup → ∀ U : Finset ι, U ⊆ L.toFinset →
    (∀ U' ⊆ U, ∑ j ∈ U', c j ∈ box) →
    ∃ R ∈ knap s c box L, ∑ j ∈ R, c j = ∑ j ∈ U, c j ∧ ∑ j ∈ U, s j ≤ ∑ j ∈ R, s j := by
  intro L
  induction L with
  | nil =>
      intro _ U hU _
      have hUb : U = ∅ := by simpa using hU
      subst hUb
      exact ⟨∅, by rw [knap]; exact Finset.mem_singleton_self _, rfl, le_rfl⟩
  | cons i rest ih =>
      intro hnd U hU hbox
      have hndrest : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hirest : i ∉ rest := (List.nodup_cons.mp hnd).1
      set F := knap s c box rest with hF
      by_cases hiU : i ∈ U
      · -- шаг «взять»
        have hU0 : U.erase i ⊆ rest.toFinset := by
          intro x hx
          have hx' := Finset.mem_of_mem_erase hx
          have hxi : x ≠ i := (Finset.mem_erase.mp hx).1
          have := hU hx'
          simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset] at this
          rcases this with rfl | h
          · exact absurd rfl hxi
          · exact List.mem_toFinset.mpr h
        obtain ⟨R₀, hR₀, hkey, hval⟩ := ih hndrest (U.erase i) hU0
          (fun U' hU' => hbox U' (le_trans hU' (Finset.erase_subset _ _)))
        have hiR₀ : i ∉ R₀ := fun h => hirest (List.mem_toFinset.mp (knap_mem s c box rest R₀ hR₀ h))
        have hUins : U = insert i (U.erase i) := (Finset.insert_erase hiU).symm
        have hkeyU : ∑ j ∈ insert i R₀, c j = ∑ j ∈ U, c j := by
          conv_rhs => rw [hUins]
          rw [Finset.sum_insert hiR₀, Finset.sum_insert (Finset.notMem_erase i U), hkey]
        have hvalU : ∑ j ∈ U, s j ≤ ∑ j ∈ insert i R₀, s j := by
          conv_lhs => rw [hUins]
          rw [Finset.sum_insert hiR₀, Finset.sum_insert (Finset.notMem_erase i U)]
          linarith
        have hmemE : insert i R₀ ∈ (F ∪ F.image (insert i)).filter
            (fun V => ∑ j ∈ V, c j ∈ box) := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨R₀, hR₀, rfl⟩), ?_⟩
          rw [hkeyU]
          exact hbox U (Finset.Subset.refl _)
        obtain ⟨hmem, hk, hge⟩ := kRep_spec
          (val := fun V => ∑ j ∈ V, s j) (key := fun V => ∑ j ∈ V, c j) hmemE
        refine ⟨kRep (fun V => ∑ j ∈ V, s j) (fun V => ∑ j ∈ V, c j)
          ((F ∪ F.image (insert i)).filter (fun V => ∑ j ∈ V, c j ∈ box))
          (∑ j ∈ insert i R₀, c j), ?_, ?_, ?_⟩
        · rw [knap_cons, ← hF]
          exact mem_kPrune hmemE
        · rw [hk, hkeyU]
        · exact le_trans hvalU hge
      · -- шаг «не брать»
        have hU0 : U ⊆ rest.toFinset := by
          intro x hx
          have := hU hx
          simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset] at this
          rcases this with rfl | h
          · exact absurd hx hiU
          · exact List.mem_toFinset.mpr h
        obtain ⟨R₀, hR₀, hkey, hval⟩ := ih hndrest U hU0 hbox
        have hmemE : R₀ ∈ (F ∪ F.image (insert i)).filter
            (fun V => ∑ j ∈ V, c j ∈ box) := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hR₀, ?_⟩
          rw [hkey]
          exact hbox U (Finset.Subset.refl _)
        obtain ⟨hmem, hk, hge⟩ := kRep_spec
          (val := fun V => ∑ j ∈ V, s j) (key := fun V => ∑ j ∈ V, c j) hmemE
        refine ⟨kRep (fun V => ∑ j ∈ V, s j) (fun V => ∑ j ∈ V, c j)
          ((F ∪ F.image (insert i)).filter (fun V => ∑ j ∈ V, c j ∈ box))
          (∑ j ∈ R₀, c j), ?_, ?_, ?_⟩
        · rw [knap_cons, ← hF]
          exact mem_kPrune hmemE
        · rw [hk, hkey]
        · exact le_trans hval hge

end Knapsack

end SparseSharpe.Factor
