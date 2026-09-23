import SparseSharpe.Factor.State

set_option linter.style.header false

/-!
# Число округлённых состояний динамики

Этот модуль превращает уже доказанные оценки диапазонов координат состояния в
конечную коробку ключей и явную оценку числа различных ключей.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {S : Finset ι} {T : κ → ι} {t : κ → ℝ}

/-- Целочисленный ключ состояния: округлённые первый момент, форма Грама и размер носителя. -/
noncomputable def keyOf (a : ι → κ → ℝ) (y : ι → ℝ) (T : κ → ι) (t : κ → ℝ)
    (η ξ : ℝ) (U : Finset ι) : (κ → ℤ) × (κ → κ → ℤ) × ℕ :=
  (fun l => ⌊momK a y T U t l / η⌋, fun l l' => ⌊gramK2 a T U l l' / ξ⌋, U.card)

/-- Конечная коробка всех допустимых ключей с заданными границами координат. -/
def keyBox (cM cK : ℤ) (n : ℕ) : Finset ((κ → ℤ) × (κ → κ → ℤ) × ℕ) :=
  (Fintype.piFinset fun _ => Finset.Icc (-cM) cM) ×ˢ
    ((Fintype.piFinset fun _ => Fintype.piFinset fun _ => Finset.Icc (-cK) cK) ×ˢ
      Finset.range (n + 1))

/-- Округление числа из симметричного отрезка остаётся между противоположными потолками. -/
lemma floor_div_mem_Icc {x B η : ℝ} (hB : |x| ≤ B) (hη : 0 < η) :
    ⌊x / η⌋ ∈ Finset.Icc (-⌈B / η⌉) ⌈B / η⌉ := by
  rw [Finset.mem_Icc]
  have hdiv : |x / η| ≤ B / η := by
    rw [abs_div, abs_of_pos hη]
    exact div_le_div_of_nonneg_right hB (le_of_lt hη)
  constructor
  · rw [← Int.floor_neg]
    apply Int.floor_mono
    linarith [abs_le.mp hdiv |>.1]
  · calc
      ⌊x / η⌋ ≤ ⌈x / η⌉ := Int.floor_le_ceil _
      _ ≤ ⌈B / η⌉ := Int.ceil_mono (abs_le.mp hdiv |>.2)

/-- Ключ любого подмножества `S` принадлежит коробке, заданной оценками диапазонов. -/
theorem keyOf_mem_keyBox (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0)
    {η ξ : ℝ} (hη : 0 < η) (hξ : 0 < ξ) {U : Finset ι} (hU : U ⊆ S) :
    keyOf a y T t η ξ U ∈
      keyBox (κ := κ) ⌈Real.sqrt ((S.card : ℝ) * phi a y S t) / η⌉
             ⌈(S.card : ℝ) / ξ⌉ S.card := by
  rw [keyOf, keyBox, Finset.mem_product, Finset.mem_product]
  constructor
  · simp only [Fintype.mem_piFinset]
    intro l
    exact floor_div_mem_Icc (abs_momK_le_of_subset hmax hdet hU l) hη
  constructor
  · simp only [Fintype.mem_piFinset]
    intro l l'
    refine floor_div_mem_Icc ?_ hξ
    exact le_trans (abs_gramK2_le hmax hdet hU l l')
      (by exact_mod_cast Finset.card_le_card hU)
  · simp only [Finset.mem_range]
    exact Nat.lt_succ_iff.mpr (Finset.card_le_card hU)

/-- Мощность коробки ключей: произведение мощностей двух кубов и отрезка размеров. -/
theorem card_keyBox (cM cK : ℤ) (hcM : 0 ≤ cM) (hcK : 0 ≤ cK) (n : ℕ) :
    (keyBox (κ := κ) cM cK n).card
      = (2 * cM + 1).toNat ^ (Fintype.card κ)
        * ((2 * cK + 1).toNat ^ (Fintype.card κ * Fintype.card κ) * (n + 1)) := by
  have _hM : 0 ≤ cM := hcM
  have _hK : 0 ≤ cK := hcK
  simp only [keyBox, Finset.card_product, Fintype.card_piFinset, Int.card_Icc,
    Finset.card_range]
  simp_rw [show (cM + 1 - -cM) = 2 * cM + 1 by omega,
    show (cK + 1 - -cK) = 2 * cK + 1 by omega]
  simp [Finset.prod_const, Finset.card_univ, pow_mul]

/-- Число различных округлённых состояний всех подмножеств `S` не превосходит мощности коробки. -/
theorem card_states_le (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0)
    {η ξ : ℝ} (hη : 0 < η) (hξ : 0 < ξ) :
    ((S.powerset).image (keyOf a y T t η ξ)).card
      ≤ (2 * ⌈Real.sqrt ((S.card : ℝ) * phi a y S t) / η⌉ + 1).toNat ^ (Fintype.card κ)
        * ((2 * ⌈(S.card : ℝ) / ξ⌉ + 1).toNat ^ (Fintype.card κ * Fintype.card κ)
           * (S.card + 1)) := by
  have hsub : (S.powerset).image (keyOf a y T t η ξ) ⊆
      keyBox (κ := κ) ⌈Real.sqrt ((S.card : ℝ) * phi a y S t) / η⌉
        ⌈(S.card : ℝ) / ξ⌉ S.card := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨U, hU, rfl⟩
    exact keyOf_mem_keyBox hmax hdet hη hξ (Finset.mem_powerset.mp hU)
  calc
    ((S.powerset).image (keyOf a y T t η ξ)).card ≤
        (keyBox (κ := κ) ⌈Real.sqrt ((S.card : ℝ) * phi a y S t) / η⌉
          ⌈(S.card : ℝ) / ξ⌉ S.card).card := Finset.card_le_card hsub
    _ = _ := card_keyBox _ _
      (Int.ceil_nonneg_of_neg_one_lt (lt_of_lt_of_le (by norm_num)
        (div_nonneg (Real.sqrt_nonneg _) (le_of_lt hη))))
      (Int.ceil_nonneg_of_neg_one_lt (lt_of_lt_of_le (by norm_num)
        (div_nonneg (by positivity) (le_of_lt hξ)))) _

/-- **Число состояний через отношение «диапазон / ширина корзины».**

`card_states_le` оценивает число ключей через `⌈√(|S|·φ_S(t))/η⌉`. Это отношение
«диапазон корзин по `M̃` / ширина корзины `η`», и `momK_range_over_precision`
показывает, что при калибровке §4 (`η = √(εV)/(2·kk·√Kc)`, `φ_S(t) ≤ 2(1+ε)V`)
оно равно `2·kk·√Kc·√(2N(1+ε)/ε)` — величина входа `V` сокращается полностью.

Здесь обе части соединены: если отношение не больше `D`, а `|S| ≤ N`, то число
состояний не больше явной величины от `D`, `N`, `K` и **ширины корзины `ξ`**.

Оговорка о `ξ`, чтобы не переоценить утверждение: `ξ` в правой части остаётся,
и при сколь угодно малом `ξ` множитель `⌈N/ξ⌉` сколь угодно велик. Но `ξ` —
это параметр алгоритма, а не величина входа: по `abs_gramK2_le` диапазон `Κ̃`
равен `[−N, N]` **сам по себе**, без всяких `m`, `B`, `d`, `Σ_f` и масштаба `V`
(коэффициенты Крамера ограничены единицей). Спецификация берёт `ξ` равным
доле единицы, зависящей только от `k` и `K`, и тогда `⌈N/ξ⌉ = poly(k,K)`.
Утверждение теоремы: в оценке нет величин входа сверх тех, что спрятаны в `D`
и в выборе `ξ` — а оба этих выбора алгоритм делает сам. -/
theorem card_states_le_of_ratio (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0)
    {η ξ : ℝ} (hη : 0 < η) (hξ : 0 < ξ) {D : ℝ}
    (hratio : Real.sqrt ((S.card : ℝ) * phi a y S t) / η ≤ D)
    {N : ℕ} (hN : S.card ≤ N) :
    ((S.powerset).image (keyOf a y T t η ξ)).card
      ≤ (2 * ⌈D⌉ + 1).toNat ^ (Fintype.card κ)
        * ((2 * ⌈(N : ℝ) / ξ⌉ + 1).toNat ^ (Fintype.card κ * Fintype.card κ) * (N + 1)) := by
  have hbase := card_states_le (a := a) (y := y) (T := T) (t := t) hmax hdet hη hξ
  have hMle : ⌈Real.sqrt ((S.card : ℝ) * phi a y S t) / η⌉ ≤ ⌈D⌉ := Int.ceil_mono hratio
  have hKle : ⌈(S.card : ℝ) / ξ⌉ ≤ ⌈(N : ℝ) / ξ⌉ :=
    Int.ceil_mono (div_le_div_of_nonneg_right (by exact_mod_cast hN) hξ.le)
  have h1 : (2 * ⌈Real.sqrt ((S.card : ℝ) * phi a y S t) / η⌉ + 1).toNat
      ≤ (2 * ⌈D⌉ + 1).toNat := Int.toNat_le_toNat (by omega)
  have h2 : (2 * ⌈(S.card : ℝ) / ξ⌉ + 1).toNat ≤ (2 * ⌈(N : ℝ) / ξ⌉ + 1).toNat :=
    Int.toNat_le_toNat (by omega)
  have h3 : S.card + 1 ≤ N + 1 := by omega
  exact le_trans hbase
    (Nat.mul_le_mul (Nat.pow_le_pow_left h1 _)
      (Nat.mul_le_mul (Nat.pow_le_pow_left h2 _) h3))

/-- Одноэлементный пример показывает, что гипотезы максимального объёма и ненулевого
определителя совместимы, а главная оценка применяется к реальному состоянию. -/
example :
    (((Finset.univ : Finset (Fin 1)).powerset).image
        (keyOf (fun _ _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => 0)
          (fun _ => (0 : ℝ)) 1 1)).card
      ≤ (2 * ⌈Real.sqrt (((Finset.univ : Finset (Fin 1)).card : ℝ) *
          phi (fun _ _ : Fin 1 => (1 : ℝ)) (fun _ => (1 : ℝ)) Finset.univ (fun _ => (0 : ℝ))) / 1⌉
          + 1).toNat ^ (Fintype.card (Fin 1))
        * ((2 * ⌈((Finset.univ : Finset (Fin 1)).card : ℝ) / 1⌉ + 1).toNat ^
            (Fintype.card (Fin 1) * Fintype.card (Fin 1))
          * ((Finset.univ : Finset (Fin 1)).card + 1)) := by
  apply card_states_le (a := fun _ _ : Fin 1 => (1 : ℝ)) (y := fun _ => (1 : ℝ))
    (T := fun _ => 0) (t := fun _ => (0 : ℝ))
  · constructor
    · intro l
      simp
    · intro T' _
      simp [rowMat]
  · norm_num [rowMat]
  · norm_num
  · norm_num

end SparseSharpe.Factor
