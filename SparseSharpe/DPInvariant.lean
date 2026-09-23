import Mathlib

set_option linter.style.header false

/-!
# Инвариант динамики: единственное место, которое раньше проверялось только численно

И в Теореме F (`K = 1`), и в Теореме I (`K` факторов), и в Теореме J (long-only)
последний шаг один и тот же: **после усечения в каждой корзине выживает представитель,
отстоящий от истинного префикса оптимального носителя не больше чем на одну ширину
корзины**. Здесь это формализовано.

Модель честная: динамика описана своим **контрактом реализации**, а не конкретным кодом.
Контракт — ровно то, что делает любая реализация «храним по одному представителю на
ключ»:

* `tab j k` — что лежит в ключе `k` после слоя `j`;
* ключ определяет округлённую цель (`key_QT`) и задаёт ширину корзины по `M` (`key_MM`);
* из живого состояния слоя `j` шаги «не брать» и «взять» дают живое состояние слоя `j+1`
  с **не большим** `M` (`step_skip`, `step_take`) — это и есть правило «минимум `M`».

Вывод (`minM_invariant`): для любого пути `P` (в приложении — префиксов оптимального
носителя) на каждом слое есть живой представитель `R` с

    QT R = QT (P j)  (точно),   MM R ≤ MM (P j),   MM R ≥ MM (P j) − j·η.

Первое — потому что округлённая цель **поштучно аддитивна** и входит в ключ;
второе — потому что минимум сохраняется при взятии минимума; третье — потому что
за шаг теряется не больше одной ширины корзины.

Схема «максимум `Q`» (Теоремы F и I) получается заменой `MM` на `−Q` и симметричным
переписыванием `step_*`; содержательная часть индукции та же.
-/

namespace SparseSharpe

open Finset

variable {ι Key : Type*} [DecidableEq ι]

/-- Обработанные к слою `j` активы. -/
def processed (item : ℕ → ι) (j : ℕ) : Finset ι := (Finset.range j).image item

lemma processed_zero (item : ℕ → ι) : processed item 0 = ∅ := by simp [processed]

lemma processed_succ (item : ℕ → ι) (j : ℕ) :
    processed item (j + 1) = insert (item j) (processed item j) := by
  ext x
  simp only [processed, Finset.mem_image, Finset.mem_range, Finset.mem_insert]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hy with h | h
    · exact Or.inr ⟨y, h, rfl⟩
    · exact Or.inl (by rw [h])
  · rintro (rfl | ⟨y, hy, rfl⟩)
    · exact ⟨j, Nat.lt_succ_self j, rfl⟩
    · exact ⟨y, Nat.lt_succ_of_lt hy, rfl⟩

/-- Инъективность нужна только на индексах, реально встречающихся в динамике
(их `N` штук). Требовать её на всём `ℕ` нельзя: при конечном `ι` таких `item` нет
вовсе, и утверждение стало бы пустым. -/
lemma item_not_mem_processed {item : ℕ → ι} {N : ℕ}
    (hinj : ∀ p q, p < N → q < N → item p = item q → p = q) {j : ℕ} (hj : j < N) :
    item j ∉ processed item j := by
  simp only [processed, Finset.mem_image, Finset.mem_range, not_exists]
  rintro x ⟨hx, hxe⟩
  exact absurd (hinj x j (lt_trans hx hj) hj hxe) (Nat.ne_of_lt hx)

/-- Проверка непустоты гипотезы: для настоящего конечного перечисления активов
(`item j = j mod n`) инъективность на `[0, n)` выполняется. Требование
`Function.Injective item` на всём `ℕ` при конечном `ι` не выполнимо никогда,
поэтому такая формулировка сделала бы инвариант пустым. -/
example :
    ∀ p q : ℕ, p < 3 → q < 3 →
      (fun j : ℕ => (⟨j % 3, Nat.mod_lt j (by norm_num)⟩ : Fin 3)) p
        = (fun j : ℕ => (⟨j % 3, Nat.mod_lt j (by norm_num)⟩ : Fin 3)) q → p = q := by
  intro p q hp hq h
  have h2 := congrArg Fin.val h
  simp only [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq] at h2
  exact h2

/-- **Инвариант динамики «минимум `M`».** -/
theorem minM_invariant
    (QT MM kap : Finset ι → ℝ) (qq dM uu : ι → ℝ) (key : Finset ι → Key)
    (tab : ℕ → Key → Option (Finset ι)) (item : ℕ → ι) {η ξ : ℝ} {N : ℕ} (hη : 0 ≤ η)
    (hξ : 0 ≤ ξ) (huu : ∀ i, 0 ≤ uu i) (hkap0 : ∀ S, 0 ≤ kap S)
    (hinj : ∀ p q, p < N → q < N → item p = item q → p = q)
    (kap_insert : ∀ (S : Finset ι) (i : ι), i ∉ S → kap (insert i S) = kap S + uu i)
    (key_kap : ∀ S S' : Finset ι, key S = key S' → kap S ≤ (1 + ξ) * kap S')
    (MM_insert : ∀ (S : Finset ι) (i : ι), i ∉ S → MM (insert i S) = MM S + dM i)
    (QT_insert : ∀ (S : Finset ι) (i : ι), i ∉ S → QT (insert i S) = QT S + qq i)
    (key_QT : ∀ S S' : Finset ι, key S = key S' → QT S = QT S')
    (key_MM : ∀ S S' : Finset ι, key S = key S' → |MM S - MM S'| ≤ η)
    (tab_sub : ∀ j k (R : Finset ι), tab j k = some R → R ⊆ processed item j)
    (tab_key : ∀ j (k : Key) (R : Finset ι), tab j k = some R → key R = k)
    (tab_zero : tab 0 (key ∅) = some ∅)
    (step_skip : ∀ j (k : Key) (R : Finset ι), tab j k = some R →
        ∃ R', tab (j + 1) (key R) = some R' ∧ MM R' ≤ MM R)
    (step_take : ∀ j (k : Key) (R : Finset ι), tab j k = some R → item j ∉ R →
        ∃ R', tab (j + 1) (key (insert (item j) R)) = some R' ∧
          MM R' ≤ MM (insert (item j) R))
    (P : ℕ → Finset ι) (hP0 : P 0 = ∅) (hPsub : ∀ j, P j ⊆ processed item j)
    (hPstep : ∀ j, P (j + 1) = P j ∨ P (j + 1) = insert (item j) (P j)) :
    ∀ j : ℕ, j ≤ N → ∃ (k : Key) (R : Finset ι), tab j k = some R ∧
      QT R = QT (P j) ∧ MM R ≤ MM (P j) ∧ MM (P j) - j * η ≤ MM R ∧
      kap R ≤ (1 + ξ) ^ j * kap (P j) ∧ kap (P j) ≤ (1 + ξ) ^ j * kap R := by
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨key ∅, ∅, tab_zero, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hP0]
  | succ j ih =>
      intro hjN
      have hjlt : j < N := Nat.lt_of_succ_le hjN
      obtain ⟨k, R, htab, hQ, hMle, hMge, hK, hK2⟩ := ih (Nat.le_of_succ_le hjN)
      have hRsub : R ⊆ processed item j := tab_sub j k R htab
      have hnotR : item j ∉ R := fun h => item_not_mem_processed hinj hjlt (hRsub h)
      have hnotP : item j ∉ P j := fun h => item_not_mem_processed hinj hjlt (hPsub j h)
      rcases hPstep j with hstep | hstep
      · -- шаг «не брать»
        obtain ⟨R', htab', hM'⟩ := step_skip j k R htab
        have hkey' : key R' = key R := tab_key (j + 1) _ R' htab'
        refine ⟨key R, R', htab', ?_, ?_, ?_, ?_, ?_⟩
        · rw [hstep, ← hQ]; exact key_QT R' R hkey'
        · rw [hstep]; linarith
        · rw [hstep]
          have hclose : |MM R' - MM R| ≤ η := key_MM R' R hkey'
          have := abs_le.mp hclose
          push_cast
          linarith [this.1, hMge]
        · rw [hstep]
          have h1 : kap R' ≤ (1 + ξ) * kap R := key_kap R' R hkey'
          have h2 : (1 + ξ) * kap R ≤ (1 + ξ) * ((1 + ξ) ^ j * kap (P j)) := by
            have : (0:ℝ) ≤ 1 + ξ := by linarith
            exact mul_le_mul_of_nonneg_left hK this
          calc kap R' ≤ (1 + ξ) * ((1 + ξ) ^ j * kap (P j)) := le_trans h1 h2
            _ = (1 + ξ) ^ (j + 1) * kap (P j) := by ring
        · rw [hstep]
          have h1 : kap R ≤ (1 + ξ) * kap R' := key_kap R R' hkey'.symm
          have hpos : (0:ℝ) < 1 + ξ := by linarith
          have h2 : kap (P j) ≤ (1 + ξ) ^ j * ((1 + ξ) * kap R') := by
            calc kap (P j) ≤ (1 + ξ) ^ j * kap R := hK2
              _ ≤ (1 + ξ) ^ j * ((1 + ξ) * kap R') := by
                  exact mul_le_mul_of_nonneg_left h1 (by positivity)
          calc kap (P j) ≤ (1 + ξ) ^ j * ((1 + ξ) * kap R') := h2
            _ = (1 + ξ) ^ (j + 1) * kap R' := by ring
      · -- шаг «взять `item j`»
        obtain ⟨R', htab', hM'⟩ := step_take j k R htab hnotR
        have hkey' : key R' = key (insert (item j) R) :=
          tab_key (j + 1) _ R' htab'
        have hQins : QT (insert (item j) R) = QT R + qq (item j) := QT_insert R _ hnotR
        have hMins : MM (insert (item j) R) = MM R + dM (item j) := MM_insert R _ hnotR
        have hQP : QT (P (j + 1)) = QT (P j) + qq (item j) := by
          rw [hstep]; exact QT_insert _ _ hnotP
        have hMP : MM (P (j + 1)) = MM (P j) + dM (item j) := by
          rw [hstep]; exact MM_insert _ _ hnotP
        have hKins : kap (insert (item j) R) = kap R + uu (item j) := kap_insert R _ hnotR
        have hKP : kap (P (j + 1)) = kap (P j) + uu (item j) := by
          rw [hstep]; exact kap_insert _ _ hnotP
        refine ⟨key (insert (item j) R), R', htab', ?_, ?_, ?_, ?_, ?_⟩
        · rw [key_QT R' _ hkey', hQins, hQ, hQP]
        · rw [hMP]; linarith [hM', hMins, hMle]
        · have hclose : |MM R' - MM (insert (item j) R)| ≤ η := key_MM R' _ hkey'
          have := abs_le.mp hclose
          rw [hMP]
          push_cast
          linarith [this.1, hMge, hMins]
        · have h1 : kap R' ≤ (1 + ξ) * kap (insert (item j) R) := key_kap R' _ hkey'
          have hpow : (1:ℝ) ≤ (1 + ξ) ^ j := one_le_pow₀ (by linarith)
          have hu : 0 ≤ uu (item j) := huu (item j)
          rw [hKP]
          have h2 : kap R + uu (item j) ≤ (1 + ξ) ^ j * (kap (P j) + uu (item j)) := by
            nlinarith [hK, hpow, hu]
          calc kap R' ≤ (1 + ξ) * (kap R + uu (item j)) := by rw [hKins] at h1; exact h1
            _ ≤ (1 + ξ) * ((1 + ξ) ^ j * (kap (P j) + uu (item j))) := by
                exact mul_le_mul_of_nonneg_left h2 (by linarith)
            _ = (1 + ξ) ^ (j + 1) * (kap (P j) + uu (item j)) := by ring
        · -- обратная сторона: вес представителя не сильно меньше веса префикса
          have h1 : kap (insert (item j) R) ≤ (1 + ξ) * kap R' := key_kap _ R' hkey'.symm
          have hpow : (1:ℝ) ≤ (1 + ξ) ^ j := one_le_pow₀ (by linarith)
          have hu : 0 ≤ uu (item j) := huu (item j)
          rw [hKP]
          have h2 : kap (P j) + uu (item j) ≤ (1 + ξ) ^ j * (kap R + uu (item j)) := by
            nlinarith [hK2, hpow, hu]
          calc kap (P j) + uu (item j) ≤ (1 + ξ) ^ j * (kap R + uu (item j)) := h2
            _ = (1 + ξ) ^ j * kap (insert (item j) R) := by rw [hKins]
            _ ≤ (1 + ξ) ^ j * ((1 + ξ) * kap R') := by
                exact mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = (1 + ξ) ^ (j + 1) * kap R' := by ring

/-- **Инвариант динамики «максимум `Q`»** — та же индукция для схемы Теорем F и I.
Там ключ несёт *отслеживаемое округлённое* состояние `trM`, которое ключом
определяется точно, а от истинного отстоит не больше чем на `c·η` (накопление
погрешности за `c` шагов «взять», см. `Factor/Accumulate.lean`). Оптимизируется `Q`.

Состояние живёт в **произвольной полунормированной группе** `E`: для Теоремы I туда
кладётся пара «вектор `M̃`, матрица `Κ̃`» с нормой-максимумом, и тогда одно применение
теоремы даёт один представитель сразу с обеими оценками — евклидовой по `M̃` и
поэлементной по `Κ̃`. Мощность представителя равна мощности префикса (`key_card`),
что и даёт `|R| ≤ k`. -/
theorem maxQ_invariant {E : Type*} [SeminormedAddCommGroup E]
    (Q : Finset ι → ℝ) (M trM : Finset ι → E) (qq : ι → ℝ) (key : Finset ι → Key)
    (tab : ℕ → Key → Option (Finset ι)) (item : ℕ → ι) {η : ℝ} {N : ℕ} (hη : 0 ≤ η)
    (hinj : ∀ p q, p < N → q < N → item p = item q → p = q)
    (Q_insert : ∀ (S : Finset ι) (i : ι), i ∉ S → Q (insert i S) = Q S + qq i)
    (key_trM : ∀ S S' : Finset ι, key S = key S' → trM S = trM S')
    (key_card : ∀ S S' : Finset ι, key S = key S' → S.card = S'.card)
    (trM_step : ∀ (S S' : Finset ι) (i : ι), i ∉ S → i ∉ S' → trM S = trM S' →
        trM (insert i S) = trM (insert i S'))
    (track_close : ∀ S : Finset ι, ‖trM S - M S‖ ≤ (S.card : ℝ) * η)
    (tab_sub : ∀ j k (R : Finset ι), tab j k = some R → R ⊆ processed item j)
    (tab_key : ∀ j (k : Key) (R : Finset ι), tab j k = some R → key R = k)
    (tab_zero : tab 0 (key ∅) = some ∅)
    (step_skip : ∀ j (k : Key) (R : Finset ι), tab j k = some R →
        ∃ R', tab (j + 1) (key R) = some R' ∧ Q R ≤ Q R')
    (step_take : ∀ j (k : Key) (R : Finset ι), tab j k = some R → item j ∉ R →
        ∃ R', tab (j + 1) (key (insert (item j) R)) = some R' ∧
          Q (insert (item j) R) ≤ Q R')
    (P : ℕ → Finset ι) (hP0 : P 0 = ∅) (hPsub : ∀ j, P j ⊆ processed item j)
    (hPstep : ∀ j, P (j + 1) = P j ∨ P (j + 1) = insert (item j) (P j)) :
    ∀ j : ℕ, j ≤ N → ∃ (k : Key) (R : Finset ι), tab j k = some R ∧
      Q (P j) ≤ Q R ∧ trM R = trM (P j) ∧ R.card = (P j).card ∧
      ‖M R - M (P j)‖ ≤ ((R.card : ℝ) + (P j).card) * η := by
  have main : ∀ j : ℕ, j ≤ N → ∃ (k : Key) (R : Finset ι), tab j k = some R ∧
      Q (P j) ≤ Q R ∧ trM R = trM (P j) ∧ R.card = (P j).card := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨key ∅, ∅, tab_zero, by simp [hP0], by simp [hP0], by simp [hP0]⟩
    | succ j ih =>
        intro hjN
        have hjlt : j < N := Nat.lt_of_succ_le hjN
        obtain ⟨k, R, htab, hQ, htr, hcard⟩ := ih (Nat.le_of_succ_le hjN)
        have hRsub : R ⊆ processed item j := tab_sub j k R htab
        have hnotR : item j ∉ R := fun h => item_not_mem_processed hinj hjlt (hRsub h)
        have hnotP : item j ∉ P j := fun h => item_not_mem_processed hinj hjlt (hPsub j h)
        rcases hPstep j with hstep | hstep
        · obtain ⟨R', htab', hQ'⟩ := step_skip j k R htab
          have hkey' : key R' = key R := tab_key (j + 1) _ R' htab'
          exact ⟨key R, R', htab', by rw [hstep]; linarith,
            by rw [hstep, ← htr]; exact key_trM R' R hkey',
            by rw [hstep, ← hcard]; exact key_card R' R hkey'⟩
        · obtain ⟨R', htab', hQ'⟩ := step_take j k R htab hnotR
          have hkey' : key R' = key (insert (item j) R) := tab_key (j + 1) _ R' htab'
          refine ⟨key (insert (item j) R), R', htab', ?_, ?_, ?_⟩
          · rw [hstep, Q_insert _ _ hnotP, Q_insert _ _ hnotR] at *
            linarith
          · rw [hstep, key_trM R' _ hkey']
            exact trM_step R (P j) (item j) hnotR hnotP htr
          · rw [hstep, key_card R' _ hkey', Finset.card_insert_of_notMem hnotR,
              Finset.card_insert_of_notMem hnotP, hcard]
  intro j hjN
  obtain ⟨k, R, htab, hQ, htr, hcard⟩ := main j hjN
  refine ⟨k, R, htab, hQ, htr, hcard, ?_⟩
  have h1 := track_close R
  have h2 := track_close (P j)
  have hsplit : M R - M (P j) = (trM (P j) - M (P j)) - (trM R - M R) := by
    rw [htr]; abel
  calc ‖M R - M (P j)‖ = ‖(trM (P j) - M (P j)) - (trM R - M R)‖ := by rw [hsplit]
    _ ≤ ‖trM (P j) - M (P j)‖ + ‖trM R - M R‖ := norm_sub_le _ _
    _ ≤ ((P j).card : ℝ) * η + (R.card : ℝ) * η := add_le_add h2 h1
    _ = ((R.card : ℝ) + (P j).card) * η := by ring

/-- **Как применять `maxQ_invariant` при `K` факторах.** Состояние — пара «вектор `M̃`,
матрица `Κ̃`» (матрица — как функция `κ → κ → ℝ`, ровно в таком виде её и хранит
`Factor/State.lean`). Одна оценка в норме произведения даёт сразу обе нужные:
евклидову по `M̃` (гипотеза `mom_close`) и поэлементную по `Κ̃`
(гипотеза `gram_half_of_entrywise`). Пример показывает, что формулировка теоремы
**применима**, а не только верна. -/
example {κ : Type*} [Fintype κ] (v : EuclideanSpace ℝ κ) (m : κ → κ → ℝ) {η : ℝ}
    (h : ‖(v, m)‖ ≤ η) :
    (∑ l, (v l) ^ 2) ≤ η ^ 2 ∧ ∀ l l', |m l l'| ≤ η := by
  have hv : ‖v‖ ≤ η := le_trans (norm_fst_le (v, m)) h
  have hm : ‖m‖ ≤ η := le_trans (norm_snd_le (v, m)) h
  have hη : 0 ≤ η := le_trans (norm_nonneg _) h
  constructor
  · have hsq : ‖v‖ ^ 2 = ∑ l, (v l) ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
      exact Finset.sum_congr rfl fun l _ => by rw [Real.norm_eq_abs, sq_abs]
    calc ∑ l, (v l) ^ 2 = ‖v‖ ^ 2 := hsq.symm
      _ ≤ η ^ 2 := by nlinarith [norm_nonneg v]
  · intro l l'
    have h1 := (pi_norm_le_iff_of_nonneg hη).mp hm l
    have h2 := (pi_norm_le_iff_of_nonneg hη).mp h1 l'
    simpa [Real.norm_eq_abs] using h2

end SparseSharpe
