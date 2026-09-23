import SparseSharpe.Factor.LeastSquares

set_option linter.style.header false

/-!
# Зажатые наименьшие квадраты: `long-only` как задача о сумме квадратов

Безусловная задача даёт `φ_S(t) = Σ_{i∈S}(⟨a_i,t⟩ − y_i)²` (файл `LeastSquares.lean`).
Ограничение `w ≥ 0` заменяет квадрат невязки на квадрат **положительной части**:

    ψ_S(t) = Σ_{i∈S} c_i(t)²,   c_i(t) = (y_i − ⟨a_i,t⟩)_+   у «зажатых» строк,
                                c_i(t) =  y_i − ⟨a_i,t⟩      у остальных.

Зажимаются строки активов; якорные строки (вклад `Σ_f⁻¹`) не зажимаются — поэтому
предикат `cl : ι → Bool`.

Главное утверждение — **односторонний аналог `phi_shift`**:

    ψ_S(t+v) ≥ ψ_S(t) − 2·momC(t,v) + gramC(t,v),

где `gramC` — «зажатая форма Грама» `Σ_i min(⟨a_i,v⟩², c_i(t)²)` (у незажатых строк
просто `⟨a_i,v⟩²`). Скалярное ядро — `sq_posPart_shift_ge`; это ровно выпуклость
функции `g ↦ (x−g)_+²` вместе с явным остаточным членом.

Отсюда:

* `psiC_le_phi` — зажатие только уменьшает: `ψ_S ≤ φ_S`;
* `psiC_eq_phi_of_nonneg` — при неотрицательных невязках `ψ_S(t) = φ_S(t)`;
* `psiC_mono` — монотонность по набору строк.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype κ]

/-! ### Скалярное ядро -/

/-- **Зажатый сдвиг (скаляр).** Для любых `x, g`:

    (x)_+² − 2(x)_+·g + min(g², (x)_+²)  ≤  (x − g)_+².

Это выпуклость `g ↦ (x−g)_+²` в нуле (`f(g) ≥ f(0) + f'(0)g`) с явным остатком.
Остаток `min(g², (x)_+²)` нельзя заменить на `g²`: при `g > x > 0` левая часть
обращается в ноль, и `g²` был бы слишком велик. -/
lemma sq_posPart_shift_ge (x g : ℝ) :
    max x 0 ^ 2 - 2 * max x 0 * g + min (g ^ 2) (max x 0 ^ 2) ≤ max (x - g) 0 ^ 2 := by
  have hmin1 : min (g ^ 2) (max x 0 ^ 2) ≤ g ^ 2 := min_le_left _ _
  have hmin2 : min (g ^ 2) (max x 0 ^ 2) ≤ max x 0 ^ 2 := min_le_right _ _
  rcases le_or_gt x 0 with hx | hx
  · -- `(x)_+ = 0`: слева `min(g², 0) = 0`, справа квадрат.
    have hx0 : max x 0 = 0 := max_eq_right hx
    have h1 : min (g ^ 2) ((0 : ℝ) ^ 2) = 0 := by
      have hz : ((0 : ℝ) ^ 2) = 0 := by norm_num
      rw [hz]; exact min_eq_right (sq_nonneg g)
    rw [hx0, h1]
    nlinarith [sq_nonneg (max (x - g) 0)]
  · -- `(x)_+ = x > 0`
    have hx0 : max x 0 = x := max_eq_left hx.le
    rw [hx0]
    rcases le_or_gt g x with hg | hg
    · -- невязка остаётся неотрицательной: зажатие не срабатывает
      have : max (x - g) 0 = x - g := max_eq_left (by linarith)
      rw [this]
      nlinarith [hmin1, hx0 ▸ hmin1]
    · -- невязка уходит в минус: справа ноль, слева заведомо отрицательно
      have : max (x - g) 0 = 0 := max_eq_right (by linarith)
      rw [this]
      have h2 : min (g ^ 2) (x ^ 2) ≤ x ^ 2 := min_le_right _ _
      nlinarith

/-! ### Зажатые невязка, значение, момент и форма Грама -/

/-- Невязка строки `i`: положительная часть у зажатых строк, обычная у остальных. -/
noncomputable def resC (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (i : ι) (t : κ → ℝ) : ℝ :=
  if cl i then max (y i - dotp (a i) t) 0 else y i - dotp (a i) t

/-- `ψ_S(t) = Σ_{i∈S} c_i(t)²`. -/
noncomputable def psiC (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (S : Finset ι)
    (t : κ → ℝ) : ℝ :=
  ∑ i ∈ S, resC a y cl i t ^ 2

/-- `⟨M_t(S), v⟩ = Σ_{i∈S} c_i(t)·⟨a_i,v⟩` — первый момент зажатых невязок. -/
noncomputable def momC (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (S : Finset ι)
    (t v : κ → ℝ) : ℝ :=
  ∑ i ∈ S, resC a y cl i t * dotp (a i) v

/-- Зажатая форма Грама `Σ_{i∈S} min(⟨a_i,v⟩², c_i(t)²)` (у незажатых строк — `⟨a_i,v⟩²`). -/
noncomputable def gramC (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (S : Finset ι)
    (t v : κ → ℝ) : ℝ :=
  ∑ i ∈ S, if cl i then min (dotp (a i) v ^ 2) (resC a y cl i t ^ 2) else dotp (a i) v ^ 2

variable {a : ι → κ → ℝ} {y : ι → ℝ} {cl : ι → Bool} {S R : Finset ι} {t v th : κ → ℝ}

lemma resC_nonneg_of_clip {i : ι} (h : cl i) : 0 ≤ resC a y cl i t := by
  simp [resC, h]

lemma psiC_nonneg (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (S : Finset ι) (t : κ → ℝ) :
    0 ≤ psiC a y cl S t :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma gramC_nonneg (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (S : Finset ι) (t v : κ → ℝ) :
    0 ≤ gramC a y cl S t v := by
  refine Finset.sum_nonneg fun i _ => ?_
  by_cases h : cl i <;> simp only [h, ite_true, ite_false, Bool.false_eq_true]
  · exact le_min (sq_nonneg _) (sq_nonneg _)
  · exact sq_nonneg _

/-- **Зажатый сдвиг узла.** Односторонний аналог `phi_shift`. -/
theorem psiC_shift_ge (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (S : Finset ι)
    (t v : κ → ℝ) :
    psiC a y cl S t - 2 * momC a y cl S t v + gramC a y cl S t v ≤ psiC a y cl S (t + v) := by
  simp only [psiC, momC, gramC, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hdot : dotp (a i) (t + v) = dotp (a i) t + dotp (a i) v := dotp_add _ _ _
  by_cases h : cl i
  · simp only [resC, h, ite_true, hdot]
    have := sq_posPart_shift_ge (y i - dotp (a i) t) (dotp (a i) v)
    have hrw : y i - (dotp (a i) t + dotp (a i) v)
        = (y i - dotp (a i) t) - dotp (a i) v := by ring
    rw [hrw]
    linarith [this]
  · simp only [resC, h, ite_false, Bool.false_eq_true, hdot]
    have : y i - (dotp (a i) t + dotp (a i) v)
        = (y i - dotp (a i) t) - dotp (a i) v := by ring
    rw [this]
    nlinarith [sq_nonneg (y i - dotp (a i) t - dotp (a i) v)]

/-- Зажатие только уменьшает значение: `ψ_S ≤ φ_S`. -/
theorem psiC_le_phi (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (S : Finset ι) (t : κ → ℝ) :
    psiC a y cl S t ≤ phi a y S t := by
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : cl i
  · simp only [resC, h, ite_true]
    rcases le_or_gt (y i - dotp (a i) t) 0 with hx | hx
    · rw [max_eq_right hx]; simpa using sq_nonneg (dotp (a i) t - y i)
    · rw [max_eq_left hx.le]; nlinarith
  · simp only [resC, h, ite_false, Bool.false_eq_true]
    nlinarith

/-- **`F_LO(S) ≤ F(S̄)`.** Если `tψ` минимизирует `ψ_S`, а `t̂` удовлетворяет
нормальным уравнениям для `φ_S`, то значение зажатой задачи не превосходит
значения безусловной. Это `psiC_le_phi` плюс минимальность — отдельное
утверждение именно о **значениях**, а не поточечное неравенство. -/
theorem psiC_min_le_phi_min {tpsi : κ → ℝ}
    (hmin : ∀ t, psiC a y cl S tpsi ≤ psiC a y cl S t) (th : κ → ℝ) :
    psiC a y cl S tpsi ≤ phi a y S th :=
  le_trans (hmin th) (psiC_le_phi a y cl S th)

/-- Если у всех зажатых строк невязка неотрицательна, зажатие ничего не меняет. -/
theorem psiC_eq_phi_of_nonneg (h : ∀ i ∈ S, cl i → 0 ≤ y i - dotp (a i) t) :
    psiC a y cl S t = phi a y S t := by
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases hc : cl i
  · simp only [resC, hc, ite_true]
    rw [max_eq_left (h i hi hc)]; ring
  · simp only [resC, hc, ite_false, Bool.false_eq_true]
    ring

/-- Монотонность по набору строк. -/
theorem psiC_mono (h : R ⊆ S) (t : κ → ℝ) : psiC a y cl R t ≤ psiC a y cl S t :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => sq_nonneg _

/-- Вклад одного элемента. -/
lemma psiC_insert [DecidableEq ι] {i : ι} (hi : i ∉ S) (t : κ → ℝ) :
    psiC a y cl (insert i S) t = resC a y cl i t ^ 2 + psiC a y cl S t :=
  Finset.sum_insert hi

lemma momC_insert [DecidableEq ι] {i : ι} (hi : i ∉ S) (t v : κ → ℝ) :
    momC a y cl (insert i S) t v = resC a y cl i t * dotp (a i) v + momC a y cl S t v :=
  Finset.sum_insert hi

/-- **Потеря от зажатия в узле.** Если у каждой зажатой строки с отрицательной
невязкой эта невязка мала (`r_i(t)² ≤ β`), то `φ_S(t) − ψ_S(t) ≤ |S|·β`.

Для чего: в узле сетки максимально-объёмной `K`-ки строки `S̄*`, ставшие
неактивными, имеют `r_i(t)² ≤ K·gram_T(t−t̂)` (правило Крамера), то есть
`β = εF/(k+K)`; значит зажатое `Q` набора `A*` отличается от незажатого
не более чем на `εF` — это ровно тот запас, который шаг FPTAS умеет поглощать
(`theory_note_v5.md`, §7.2). -/
theorem phi_sub_psiC_le {β : ℝ} (hβ : 0 ≤ β)
    (h : ∀ i ∈ S, cl i → y i - dotp (a i) t < 0 → (y i - dotp (a i) t) ^ 2 ≤ β) :
    phi a y S t - psiC a y cl S t ≤ S.card * β := by
  have hitem : ∀ i ∈ S, (dotp (a i) t - y i) ^ 2 - resC a y cl i t ^ 2 ≤ β := by
    intro i hi
    by_cases hc : cl i
    · simp only [resC, hc, ite_true]
      rcases le_or_gt 0 (y i - dotp (a i) t) with hx | hx
      · rw [max_eq_left hx]; nlinarith
      · rw [max_eq_right hx.le]
        have := h i hi hc hx
        nlinarith
    · simp only [resC, hc, ite_false, Bool.false_eq_true]
      nlinarith
  have hsum : ∑ i ∈ S, ((dotp (a i) t - y i) ^ 2 - resC a y cl i t ^ 2) ≤ S.card * β := by
    calc ∑ i ∈ S, ((dotp (a i) t - y i) ^ 2 - resC a y cl i t ^ 2)
        ≤ ∑ _i ∈ S, β := Finset.sum_le_sum hitem
      _ = S.card * β := by rw [Finset.sum_const, nsmul_eq_mul]
  simpa only [phi, psiC, Finset.sum_sub_distrib] using hsum

/-! ### Самосогласованность: когда long-only совпадает с безусловной задачей -/

/-- При неотрицательных невязках зажатый момент совпадает с обычным. -/
lemma momC_eq_mom_of_nonneg (h : ∀ i ∈ S, cl i → 0 ≤ y i - dotp (a i) t) (v : κ → ℝ) :
    momC a y cl S t v = mom a y S t v := by
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases hc : cl i
  · rw [resC, if_pos (by simpa using hc), max_eq_left (h i hi hc)]
  · rw [resC, if_neg (by simpa using hc)]

/-- **Самосогласованное множество: `t̂` минимизирует и зажатую задачу.**

Если `t̂` удовлетворяет нормальным уравнениям для `φ_S` и все зажатые невязки в нём
неотрицательны, то `ψ_S(t̂) = φ_S(t̂)` и `t̂` — точка минимума `ψ_S`.
Это `K`-мерный аналог `SparseSharpe.OneFactor.lo_value_of_selfconsistent`. -/
theorem psiC_min_of_normal_of_nonneg (hnormal : IsNormal a y S th)
    (h : ∀ i ∈ S, cl i → 0 ≤ y i - dotp (a i) th) (t : κ → ℝ) :
    psiC a y cl S th ≤ psiC a y cl S t := by
  have hmom : ∀ v, momC a y cl S th v = 0 := fun v => by
    rw [momC_eq_mom_of_nonneg h v]; exact hnormal v
  have hsh := psiC_shift_ge a y cl S th (t - th)
  have hid : th + (t - th) = t := by abel
  rw [hid, hmom (t - th)] at hsh
  linarith [gramC_nonneg a y cl S th (t - th)]

/-- Значение зажатой задачи на самосогласованном множестве. -/
theorem isLeast_psiC_of_selfconsistent (hnormal : IsNormal a y S th)
    (h : ∀ i ∈ S, cl i → 0 ≤ y i - dotp (a i) th) :
    IsLeast {v : ℝ | ∃ t', v = psiC a y cl S t'} (phi a y S th) := by
  refine ⟨⟨th, (psiC_eq_phi_of_nonneg h).symm⟩, ?_⟩
  rintro v ⟨t', rfl⟩
  rw [← psiC_eq_phi_of_nonneg h]
  exact psiC_min_of_normal_of_nonneg hnormal h t'

/-- **Сертификат самосогласованности.**

Пусть в узле `t` все зажатые невязки не меньше `ρ ≥ 0`, а зазор `φ_S(t) − φ_S(t̂)`
не превосходит `ρ²`. Тогда `S` самосогласовано: невязки в `t̂` неотрицательны.

Зазор `φ_S(t) − φ_S(t̂)` — это в точности `M_t(S)'Κ(S)⁻¹M_t(S)`, то есть величина,
которую динамика §4 и так контролирует. Ключ — `⟨a_i,v⟩² ≤ gram(S,v)` при `i ∈ S`
(в матричной записи `a_i'Κ(S)⁻¹a_i ≤ 1`), проверено численно в
`code/check_lo_dropcost.py`. -/
theorem selfconsistent_of_phi_gap (hnormal : IsNormal a y S th) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hact : ∀ i ∈ S, cl i → ρ ≤ y i - dotp (a i) t)
    (hgap : phi a y S t - phi a y S th ≤ ρ ^ 2) :
    ∀ i ∈ S, cl i → 0 ≤ y i - dotp (a i) th := by
  intro i hi hc
  have hgram : gram a S (t - th) ≤ ρ ^ 2 := by
    rw [phi_eq_add hnormal t] at hgap; linarith
  have hsingle : (dotp (a i) (t - th)) ^ 2 ≤ gram a S (t - th) :=
    Finset.single_le_sum (f := fun j => (dotp (a j) (t - th)) ^ 2)
      (fun j _ => sq_nonneg _) hi
  have hle : (dotp (a i) (t - th)) ^ 2 ≤ ρ ^ 2 := le_trans hsingle hgram
  have habs : -ρ ≤ dotp (a i) (t - th) := by nlinarith
  have hsub : dotp (a i) (t - th) = dotp (a i) t - dotp (a i) th := dotp_sub _ _ _
  have := hact i hi hc
  rw [hsub] at habs
  linarith

/-- **Итог: сертифицированное совпадение long-only и безусловной задачи.** -/
theorem isLeast_psiC_of_certificate (hnormal : IsNormal a y S th) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hact : ∀ i ∈ S, cl i → ρ ≤ y i - dotp (a i) t)
    (hgap : phi a y S t - phi a y S th ≤ ρ ^ 2) :
    IsLeast {v : ℝ | ∃ t', v = psiC a y cl S t'} (phi a y S th) :=
  isLeast_psiC_of_selfconsistent hnormal (selfconsistent_of_phi_gap hnormal hρ hact hgap)

/-! ### Непустота гипотез сертификата

`lake build` и аудит аксиом не отличают верное утверждение от бессодержательного
(урок из `findings_v12.md`, §4a). Ниже: (а) гипотезы `selfconsistent_of_phi_gap`
выполнимы; (б) его заключение **не автоматично** — есть набор строк с нормальными
уравнениями, у которого невязка в `t̂` отрицательна. -/

/-- (а) Гипотезы выполнимы: строка `a = (1)`, `y = 1`, `t̂ = 1`, узел `t = 0`, `ρ = 1`. -/
example : ∀ i ∈ (Finset.univ : Finset (Fin 1)), (fun _ : Fin 1 => true) i →
    0 ≤ (fun _ : Fin 1 => (1 : ℝ)) i
      - dotp ((fun _ _ => (1 : ℝ)) i : Fin 1 → ℝ) (fun _ => (1 : ℝ)) := by
  refine selfconsistent_of_phi_gap (a := fun _ _ => (1 : ℝ)) (y := fun _ => (1 : ℝ))
    (cl := fun _ => true) (S := Finset.univ) (th := fun _ => (1 : ℝ))
    (t := fun _ => (0 : ℝ)) (ρ := 1) ?_ zero_le_one ?_ ?_
  · intro v; simp [mom, dotp]
  · intro i _ _; simp [dotp]
  · simp [phi, dotp]

/-- (б) Заключение не автоматично: строки `a₁ = a₂ = (1)`, `y = (0, 2)`, `t̂ = 1`
удовлетворяют нормальным уравнениям, но невязка первой строки в `t̂` равна `−1`. -/
example :
    IsNormal (ι := Fin 2) (κ := Fin 1) (fun _ _ => 1)
      (fun i => if i = 0 then 0 else 2) Finset.univ (fun _ => 1)
    ∧ ¬ (0 ≤ (fun i : Fin 2 => if i = 0 then (0 : ℝ) else 2) 0
          - dotp ((fun _ _ => (1 : ℝ)) 0 : Fin 1 → ℝ) (fun _ => (1 : ℝ))) := by
  constructor
  · intro v
    simp [mom, dotp, Fin.sum_univ_two]
    ring
  · simp [dotp]


/-! ### Сосед по корзине не хуже

Динамика хранит в корзине набор с наибольшим `Q`. Если у `R` в узле `t` значение
не меньше, чем у `S`, первые моменты совпадают, а форма Грама не меньше, то `R`
не хуже `S` **всюду**, а значит и по значению безусловной задачи. Это то звено,
из-за которого вытеснение `S` из корзины само по себе ничего не портит:
вытеснивший набор заведомо не хуже — остаётся лишь вопрос его самосогласованности
(Теорема L). -/

/-- Поточечно: `φ_S(t+v) ≤ φ_R(t+v)` при любом `v`. -/
theorem phi_le_of_bucket (hQ : phi a y S t ≤ phi a y R t)
    (hM : ∀ v, mom a y R t v = mom a y S t v)
    (hK : ∀ v, gram a S v ≤ gram a R v) (v : κ → ℝ) :
    phi a y S (t + v) ≤ phi a y R (t + v) := by
  rw [phi_shift, phi_shift]
  have h1 := hM v
  have h2 := hK v
  linarith

/-- По значениям: `F(S̄) ≤ F(R̄)`. -/
theorem phi_normal_le_of_bucket {thS thR : κ → ℝ}
    (hQ : phi a y S t ≤ phi a y R t)
    (hM : ∀ v, mom a y R t v = mom a y S t v)
    (hK : ∀ v, gram a S v ≤ gram a R v)
    (hnormS : IsNormal a y S thS) :
    phi a y S thS ≤ phi a y R thR := by
  have h := phi_le_of_bucket hQ hM hK (thR - t)
  have hid : t + (thR - t) = thR := by abel
  rw [hid] at h
  exact le_trans (phi_min hnormS thR) h

/-- **Наборы одной корзины отличаются на константу.** При совпадении первого
момента и формы Грама `φ_R − φ_S` не зависит от точки. -/
theorem phi_eq_add_const (hMom : ∀ v, mom a y R t v = mom a y S t v)
    (hK : ∀ v, gram a R v = gram a S v) (u : κ → ℝ) :
    phi a y R u = phi a y S u + (phi a y R t - phi a y S t) := by
  have hid : t + (u - t) = u := by abel
  have hR := phi_shift a y R t (u - t)
  have hS := phi_shift a y S t (u - t)
  rw [hid] at hR hS
  rw [hR, hS, hMom (u - t), hK (u - t)]
  ring

/-- **Зазор `Q − F` у соседей по корзине одинаков.**

Поэтому сертификат Теоремы L, проверенный для `S`, автоматически верен и для
любого набора `R` из той же корзины: зазор — это ровно `‖M_t‖²_{Κ⁻¹}`, и он
переносится без потерь. Это и закрывает случай вытеснения `S` из корзины
(`theory_note_v5.md`, §12). -/
theorem gap_eq_of_bucket {thS thR : κ → ℝ}
    (hMom : ∀ v, mom a y R t v = mom a y S t v)
    (hK : ∀ v, gram a R v = gram a S v)
    (hnormS : IsNormal a y S thS) (hnormR : IsNormal a y R thR) :
    phi a y R t - phi a y R thR = phi a y S t - phi a y S thS := by
  have hconst := phi_eq_add_const hMom hK
  -- `φ_S` принимает в `thR` тот же минимум, что и в `thS`
  have h1 : phi a y S thS ≤ phi a y S thR := phi_min hnormS thR
  have h2 : phi a y R thR ≤ phi a y R thS := phi_min hnormR thS
  have e1 := hconst thR
  have e2 := hconst thS
  have heq : phi a y S thR = phi a y S thS := by linarith
  rw [hconst t, hconst thR, heq]
  ring

/-- **Шаг LO-K′ целиком.** Пусть в узле `t`:

* `S` — носитель оптимума: `t̂_S` удовлетворяет нормальным уравнениям и все
  зажатые невязки в нём неотрицательны (самосогласованность);
* `R` — набор, вытеснивший `S` из корзины: `Q` не меньше, моменты совпадают,
  форма Грама не меньше;
* `R` проходит сертификат Теоремы L: невязки в узле не меньше `ρ`, а зазор
  `φ_R(t) − φ_R(t̂_R)` не больше `ρ²`.

Тогда значение long-only у `R` не меньше, чем у `S`:
`F_LO(S) = φ_S(t̂_S) ≤ φ_R(t̂_R) = F_LO(R)`. -/
theorem psiC_min_le_of_bucket_of_certificate {thS thR : κ → ℝ} {ρ : ℝ}
    (hQ : phi a y S t ≤ phi a y R t)
    (hMom : ∀ v, mom a y R t v = mom a y S t v)
    (hK : ∀ v, gram a S v ≤ gram a R v)
    (hnormS : IsNormal a y S thS)
    (hselfS : ∀ i ∈ S, cl i → 0 ≤ y i - dotp (a i) thS)
    (hnormR : IsNormal a y R thR) (hρ : 0 ≤ ρ)
    (hactR : ∀ i ∈ R, cl i → ρ ≤ y i - dotp (a i) t)
    (hgapR : phi a y R t - phi a y R thR ≤ ρ ^ 2) :
    psiC a y cl S thS ≤ psiC a y cl R thR := by
  have hselfR := selfconsistent_of_phi_gap hnormR hρ hactR hgapR
  rw [psiC_eq_phi_of_nonneg hselfS, psiC_eq_phi_of_nonneg hselfR]
  exact phi_normal_le_of_bucket hQ hMom hK hnormS

/-- **Вытеснение из корзины закрыто.** Сертификат проверяется для `S` (носителя
оптимума), а не для вытеснившего `R`: по `gap_eq_of_bucket` зазоры совпадают.

Гипотеза `hgapS` — это ровно вывод (b) Теоремы O
(`gram_le_of_nearest_node`, `theory_note_v5.md`, §10.5): в ближайшем к `t̂_S` узле
`φ_S(t) − φ_S(t̂_S) = gram_S(t − t̂_S) ≤ ρ²`. Гипотеза `hactR` — условие фильтра
динамики. -/
theorem psiC_min_le_of_bucket_gap {thS thR : κ → ℝ} {ρ : ℝ}
    (hQ : phi a y S t ≤ phi a y R t)
    (hMom : ∀ v, mom a y R t v = mom a y S t v)
    (hK : ∀ v, gram a R v = gram a S v)
    (hnormS : IsNormal a y S thS)
    (hselfS : ∀ i ∈ S, cl i → 0 ≤ y i - dotp (a i) thS)
    (hnormR : IsNormal a y R thR) (hρ : 0 ≤ ρ)
    (hactR : ∀ i ∈ R, cl i → ρ ≤ y i - dotp (a i) t)
    (hgapS : phi a y S t - phi a y S thS ≤ ρ ^ 2) :
    psiC a y cl S thS ≤ psiC a y cl R thR := by
  have hgapR : phi a y R t - phi a y R thR ≤ ρ ^ 2 := by
    rw [gap_eq_of_bucket hMom hK hnormS hnormR]; exact hgapS
  exact psiC_min_le_of_bucket_of_certificate hQ hMom (fun v => le_of_eq (hK v).symm)
    hnormS hselfS hnormR hρ hactR hgapR

/-! ### Непустота гипотез шага

Гипотезы `psiC_min_le_of_bucket_of_certificate` выполнимы одновременно:
берём `S = R` (набор сам себе сосед по корзине), одну строку `a = (1)`, `y = 1`,
`t̂ = 1`, узел `t = 0`, `ρ = 1`. -/
example :
    psiC (ι := Fin 1) (κ := Fin 1) (fun _ _ => 1) (fun _ => 1) (fun _ => true)
        Finset.univ (fun _ => 1)
      ≤ psiC (ι := Fin 1) (κ := Fin 1) (fun _ _ => 1) (fun _ => 1) (fun _ => true)
        Finset.univ (fun _ => 1) := by
  refine psiC_min_le_of_bucket_of_certificate (t := fun _ => (0 : ℝ)) (ρ := 1)
    (le_refl _) (fun v => rfl) (fun v => le_refl _) ?_ ?_ ?_ zero_le_one ?_ ?_
  · intro v; simp [mom, dotp]
  · intro i _ _; simp [dotp]
  · intro v; simp [mom, dotp]
  · intro i _ _; simp [dotp]
  · simp [phi, dotp]

/-! ### Разрыв между `F_LO(R)` и `F(R̄)` — настоящий

Три строки в `ℝ¹`: `a₁ = a₂ = a₃ = 1`, цели `y = (0, 2, 0)`, зажаты первые две
(третья — якорная, отвечает `Σ_f⁻¹ = 1`). Тогда

    F(R̄)   = min_t [t² + (t−2)² + t²] = 8/3   при `t̂ = 2/3`,  причём `r₁(t̂) = −2/3 < 0`,
    F_LO(R) ≤ ψ(1) = 0 + 1 + 1 = 2   <   8/3 .

Значит, никакая «зажатая» версия `fptasK_step_general` (оценка снизу на `ψ_R(t+v)`
сразу при всех `v`) не может давать `F(R̄)`: самосогласованность представителя
приходится устанавливать отдельно — Теоремой L или устройством ключа динамики. -/

example :
    IsNormal (ι := Fin 3) (κ := Fin 1) (fun _ _ => 1)
      (fun i => if i = 1 then 2 else 0) Finset.univ (fun _ => 2 / 3) := by
  intro v
  simp [mom, dotp, Fin.sum_univ_three]
  ring

example :
    psiC (ι := Fin 3) (κ := Fin 1) (fun _ _ => 1) (fun i => if i = 1 then 2 else 0)
        (fun i => i != 2) Finset.univ (fun _ => 1)
      < phi (ι := Fin 3) (κ := Fin 1) (fun _ _ => 1) (fun i => if i = 1 then 2 else 0)
        Finset.univ (fun _ => 2 / 3) := by
  norm_num [psiC, phi, resC, dotp, Fin.sum_univ_three]

/-! ### Количественная форма Теоремы L: сколько строк может нарушить самосогласованность

`theory_note_v5.md`, §13.5. Теорема L требует `зазор ≤ ρ²` и тогда нарушителей
НЕТ вовсе. Если зазор больше, вывод не пропадает, а ослабевает: нарушителей не
больше `зазор/ρ²`. Действительно, у нарушителя `i` невязка в узле не меньше `ρ`,
а в неподвижной точке отрицательна, значит `|⟨a_i, t − t̂⟩| > ρ`; но сумма таких
квадратов по всему набору и есть зазор.

Это и есть точная форма остатка: при вытеснении из корзины в узле, далёком от
`t̂`, у вытеснившего набора `R` может быть до `зазор/ρ²` строк с отрицательной
невязкой — и вопрос лишь в том, во сколько обходится их потеря. -/

/-- **Число нарушителей самосогласованности ограничено зазором.** -/
theorem card_violators_mul_sq_le {ρ γ : ℝ} (hρ : 0 < ρ)
    (hact : ∀ i ∈ S, cl i → ρ ≤ y i - dotp (a i) t)
    (hgap : gram a S (t - th) ≤ γ) :
    (((S.filter (fun i => cl i = true ∧ y i - dotp (a i) th < 0)).card : ℝ)) * ρ ^ 2 ≤ γ := by
  classical
  set D := S.filter (fun i => cl i = true ∧ y i - dotp (a i) th < 0) with hD
  have hsub : D ⊆ S := Finset.filter_subset _ _
  have hterm : ∀ i ∈ D, ρ ^ 2 ≤ (dotp (a i) (t - th)) ^ 2 := by
    intro i hi
    have hmem : i ∈ S := hsub hi
    obtain ⟨hc, hneg⟩ := (Finset.mem_filter.mp hi).2
    have h1 := hact i hmem (by simp [hc])
    have hsub' : dotp (a i) (t - th) = dotp (a i) t - dotp (a i) th := dotp_sub _ _ _
    have h2 : dotp (a i) (t - th) ≤ -ρ := by rw [hsub']; linarith
    nlinarith [hρ.le]
  have hcard : (D.card : ℝ) * ρ ^ 2 ≤ ∑ i ∈ D, (dotp (a i) (t - th)) ^ 2 := by
    calc (D.card : ℝ) * ρ ^ 2 = ∑ _i ∈ D, ρ ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ D, (dotp (a i) (t - th)) ^ 2 := Finset.sum_le_sum hterm
  have hrest : ∑ i ∈ D, (dotp (a i) (t - th)) ^ 2 ≤ gram a S (t - th) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
  linarith

/-- Форма через `φ`: зазор — это `φ_S(t) − φ_S(t̂)`. -/
theorem card_violators_le_gap (hnormal : IsNormal a y S th) {ρ : ℝ} (hρ : 0 < ρ)
    (hact : ∀ i ∈ S, cl i → ρ ≤ y i - dotp (a i) t) :
    (((S.filter (fun i => cl i = true ∧ y i - dotp (a i) th < 0)).card : ℝ)) * ρ ^ 2
      ≤ phi a y S t - phi a y S th := by
  refine card_violators_mul_sq_le hρ hact ?_
  rw [phi_eq_add hnormal t]
  linarith

end SparseSharpe.Factor
