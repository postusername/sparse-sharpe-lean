import Mathlib

set_option linter.style.header false

/-!
# Наименьшие квадраты в `ℝ^K`: сдвиг, нормальные уравнения, теорема Пифагора

Файл готовит язык для FPTAS при фиксированном числе факторов `K`.

Целевая функция однофакторной задачи `φ_S(t) = t²/σ² + Σ_{i∈S}(m_i − tβ_i)²/d_i`
при `K` факторах превращается в `t'Σ_f⁻¹t + Σ_{i∈S}(m_i − B_i't)²/d_i`, а это —
обычная сумма квадратов невязок по набору **строк**: активы дают строки
`a_i = B_i/√d_i` с правой частью `y_i = m_i/√d_i`, а матрица факторов — `K`
«якорных» строк `Σ_f^{-1/2}` с нулевой правой частью. Поэтому здесь всё
формулируется абстрактно: строки `a : ι → κ → ℝ`, правые части `y : ι → ℝ`,
носитель `S : Finset ι` (якорные строки — просто элементы `S`, лежащие в нём всегда).

Главные утверждения:

* `phi_shift` — разложение `φ(t+v) = φ(t) − 2·mom(t,v) + gram(v)`: чистая алгебра,
  никаких обращений матриц. Это K-мерный аналог `Fval_eq_phi_sub`;
* `phi_eq_add` — теорема Пифагора: при нормальных уравнениях в `t̂`
  `φ(t) = φ(t̂) + gram(t − t̂)`;
* `sqrt_gram_add_le` — неравенство треугольника для полунормы `√gram`.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype κ]

/-- Скалярное произведение строки `a` и вектора параметров `t`. -/
noncomputable def dotp (a t : κ → ℝ) : ℝ := ∑ j, a j * t j

/-- Сумма квадратов невязок по набору строк `S`: `φ_S(t) = Σ_{i∈S}(⟨a_i,t⟩ − y_i)²`. -/
noncomputable def phi (a : ι → κ → ℝ) (y : ι → ℝ) (S : Finset ι) (t : κ → ℝ) : ℝ :=
  ∑ i ∈ S, (dotp (a i) t - y i) ^ 2

/-- Квадратичная форма Грама `v ↦ Σ_{i∈S} ⟨a_i,v⟩²` (в матричной записи `v'Κ(S)v`). -/
noncomputable def gram (a : ι → κ → ℝ) (S : Finset ι) (v : κ → ℝ) : ℝ :=
  ∑ i ∈ S, (dotp (a i) v) ^ 2

/-- Линейный функционал «первый момент», спаренный с направлением `v`:
`mom(t,v) = Σ_{i∈S}(y_i − ⟨a_i,t⟩)⟨a_i,v⟩` (в матричной записи `⟨M_t(S), v⟩`). -/
noncomputable def mom (a : ι → κ → ℝ) (y : ι → ℝ) (S : Finset ι) (t v : κ → ℝ) : ℝ :=
  ∑ i ∈ S, (y i - dotp (a i) t) * dotp (a i) v

/-- Нормальные уравнения: `t̂` — точка минимума `φ_S`. -/
def IsNormal (a : ι → κ → ℝ) (y : ι → ℝ) (S : Finset ι) (th : κ → ℝ) : Prop :=
  ∀ v : κ → ℝ, mom a y S th v = 0

variable {a : ι → κ → ℝ} {y : ι → ℝ} {S R : Finset ι} {t v th : κ → ℝ}

/-! ### Линейность `dotp` по второму аргументу -/

lemma dotp_add (a u v : κ → ℝ) : dotp a (u + v) = dotp a u + dotp a v := by
  simp only [dotp, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma dotp_sub (a u v : κ → ℝ) : dotp a (u - v) = dotp a u - dotp a v := by
  simp only [dotp, ← Finset.sum_sub_distrib, Pi.sub_apply]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma dotp_zero (a : κ → ℝ) : dotp a (0 : κ → ℝ) = 0 := by simp [dotp]

lemma dotp_neg (a v : κ → ℝ) : dotp a (-v) = -dotp a v := by
  simp only [dotp, ← Finset.sum_neg_distrib, Pi.neg_apply]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma gram_neg (a : ι → κ → ℝ) (S : Finset ι) (v : κ → ℝ) : gram a S (-v) = gram a S v := by
  simp only [gram]
  exact Finset.sum_congr rfl fun i _ => by rw [dotp_neg]; ring

/-! ### Основное разложение -/

/-- **Сдвиг узла.** `φ_S(t+v) = φ_S(t) − 2·mom(t,v) + gram(v)`.
Это K-мерная форма (E′): никаких обращений матриц, чистая алгебра. -/
theorem phi_shift (a : ι → κ → ℝ) (y : ι → ℝ) (S : Finset ι) (t v : κ → ℝ) :
    phi a y S (t + v) = phi a y S t - 2 * mom a y S t v + gram a S v := by
  simp only [phi, mom, gram, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotp_add]
  ring

lemma gram_nonneg (a : ι → κ → ℝ) (S : Finset ι) (v : κ → ℝ) : 0 ≤ gram a S v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Плечо строки, лежащей в наборе, не больше `1`.** `⟨a_i,v⟩² ≤ gram(S,v)` при `i ∈ S`;
в матричной записи это `a_i'Κ(S)⁻¹a_i ≤ 1`. Вместе с
`sq_dotp_le_card_mul_gram_of_subset` (плечо `≤ K` для строк ВНЕ набора, если в нём
лежит максимально-объёмная `K`-ка) это два случая из `theory_note_v5.md`, §8.3. -/
theorem sq_dotp_le_gram {i : ι} (hi : i ∈ S) (v : κ → ℝ) :
    (dotp (a i) v) ^ 2 ≤ gram a S v :=
  Finset.single_le_sum (f := fun j => (dotp (a j) v) ^ 2) (fun _ _ => sq_nonneg _) hi

lemma phi_nonneg (a : ι → κ → ℝ) (y : ι → ℝ) (S : Finset ι) (t : κ → ℝ) :
    0 ≤ phi a y S t :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Теорема Пифагора.** В точке нормальных уравнений
`φ_S(t) = φ_S(t̂) + gram(t − t̂)` при любом `t`. -/
theorem phi_eq_add (h : IsNormal a y S th) (t : κ → ℝ) :
    phi a y S t = phi a y S th + gram a S (t - th) := by
  have hsh := phi_shift a y S th (t - th)
  rw [h (t - th)] at hsh
  have hid : th + (t - th) = t := by abel
  rw [hid] at hsh
  linarith

/-- Точка нормальных уравнений минимизирует `φ_S`. -/
theorem phi_min (h : IsNormal a y S th) (t : κ → ℝ) : phi a y S th ≤ phi a y S t := by
  rw [phi_eq_add h t]
  linarith [gram_nonneg a S (t - th)]

/-- Однородность: `dotp a (s•v) = s·dotp a v`. -/
lemma dotp_smul (a v : κ → ℝ) (s : ℝ) : dotp a (s • v) = s * dotp a v := by
  simp only [dotp, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma gram_smul (a : ι → κ → ℝ) (S : Finset ι) (v : κ → ℝ) (s : ℝ) :
    gram a S (s • v) = s ^ 2 * gram a S v := by
  simp only [gram, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [dotp_smul]; ring

lemma mom_smul (a : ι → κ → ℝ) (y : ι → ℝ) (S : Finset ι) (t v : κ → ℝ) (s : ℝ) :
    mom a y S t (s • v) = s * mom a y S t v := by
  simp only [mom, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [dotp_smul]; ring

/-- **Точка минимума удовлетворяет нормальным уравнениям.** Обратное к `phi_min`;
доказывается масштабированием направления, без всякого дифференцирования. -/
theorem isNormal_of_min (h : ∀ t, phi a y S th ≤ phi a y S t) : IsNormal a y S th := by
  intro v
  have key : ∀ s : ℝ, 2 * s * mom a y S th v ≤ s ^ 2 * gram a S v := by
    intro s
    have h1 := h (th + s • v)
    rw [phi_shift a y S th (s • v), mom_smul, gram_smul] at h1
    linarith
  rcases eq_or_lt_of_le (gram_nonneg a S v) with hg | hg
  · have h1 := key 1
    have h2 := key (-1)
    rw [← hg] at h1 h2
    linarith
  · by_contra hne
    have h1 := key (mom a y S th v / gram a S v)
    have hsq : (mom a y S th v / gram a S v) ^ 2 * gram a S v
        = (mom a y S th v) ^ 2 / gram a S v := by field_simp
    rw [hsq] at h1
    have h2 : 2 * (mom a y S th v / gram a S v) * mom a y S th v
        = 2 * ((mom a y S th v) ^ 2 / gram a S v) := by field_simp
    rw [h2] at h1
    have h3 : (0:ℝ) < (mom a y S th v) ^ 2 := by positivity
    have h4 : (0:ℝ) < (mom a y S th v) ^ 2 / gram a S v := by positivity
    linarith

/-! ### `√gram` — полунорма -/

/-- Коши–Буняковский для конечных сумм в форме с корнями. -/
lemma sum_mul_le_sqrt {μ : Type*} [Fintype μ] (u w : μ → ℝ) :
    ∑ l, u l * w l ≤ Real.sqrt (∑ l, (u l) ^ 2) * Real.sqrt (∑ l, (w l) ^ 2) := by
  have hu : (0:ℝ) ≤ ∑ l, (u l) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hw : (0:ℝ) ≤ ∑ l, (w l) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset μ) u w
  rw [← Real.sqrt_mul hu]
  calc ∑ l, u l * w l ≤ |∑ l, u l * w l| := le_abs_self _
    _ = Real.sqrt ((∑ l, u l * w l) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ l, (u l) ^ 2) * ∑ l, (w l) ^ 2) := Real.sqrt_le_sqrt hcs

/-- Коши–Буняковский для формы Грама: `|gram-скалярное произведение| ≤ √gram·√gram`. -/
lemma gram_inner_le (a : ι → κ → ℝ) (S : Finset ι) (u v : κ → ℝ) :
    ∑ i ∈ S, dotp (a i) u * dotp (a i) v
      ≤ Real.sqrt (gram a S u) * Real.sqrt (gram a S v) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => dotp (a i) u) (fun i => dotp (a i) v)
  have h1 : Real.sqrt (gram a S u) * Real.sqrt (gram a S v)
      = Real.sqrt (gram a S u * gram a S v) := (Real.sqrt_mul (gram_nonneg a S u) _).symm
  rw [h1]
  calc ∑ i ∈ S, dotp (a i) u * dotp (a i) v
      ≤ |∑ i ∈ S, dotp (a i) u * dotp (a i) v| := le_abs_self _
    _ = Real.sqrt ((∑ i ∈ S, dotp (a i) u * dotp (a i) v) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (gram a S u * gram a S v) := by
        apply Real.sqrt_le_sqrt
        simpa [gram] using hcs

/-- Неравенство треугольника для полунормы `√gram`. -/
theorem sqrt_gram_add_le (a : ι → κ → ℝ) (S : Finset ι) (u v : κ → ℝ) :
    Real.sqrt (gram a S (u + v)) ≤ Real.sqrt (gram a S u) + Real.sqrt (gram a S v) := by
  have hexp : gram a S (u + v)
      = gram a S u + 2 * (∑ i ∈ S, dotp (a i) u * dotp (a i) v) + gram a S v := by
    simp only [gram, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dotp_add]; ring
  have hle : gram a S (u + v)
      ≤ (Real.sqrt (gram a S u) + Real.sqrt (gram a S v)) ^ 2 := by
    have h := gram_inner_le a S u v
    have hu : Real.sqrt (gram a S u) ^ 2 = gram a S u := Real.sq_sqrt (gram_nonneg a S u)
    have hv : Real.sqrt (gram a S v) ^ 2 = gram a S v := Real.sq_sqrt (gram_nonneg a S v)
    nlinarith [h, hu, hv]
  have hnn : 0 ≤ Real.sqrt (gram a S u) + Real.sqrt (gram a S v) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc Real.sqrt (gram a S (u + v))
      ≤ Real.sqrt ((Real.sqrt (gram a S u) + Real.sqrt (gram a S v)) ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = Real.sqrt (gram a S u) + Real.sqrt (gram a S v) := Real.sqrt_sq hnn

/-- Та же полунорма в форме `√gram(u) ≤ √gram(u − v) + √gram(v)`. -/
theorem sqrt_gram_le_sub_add (a : ι → κ → ℝ) (S : Finset ι) (u v : κ → ℝ) :
    Real.sqrt (gram a S u) ≤ Real.sqrt (gram a S (u - v)) + Real.sqrt (gram a S v) := by
  have := sqrt_gram_add_le a S (u - v) v
  simpa using this

/-- Монотонность формы Грама по носителю. -/
lemma gram_mono (h : S ⊆ R) (v : κ → ℝ) : gram a S v ≤ gram a R v :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => sq_nonneg _

/-- Монотонность `φ` по носителю. -/
lemma phi_mono (h : S ⊆ R) (t : κ → ℝ) : phi a y S t ≤ phi a y R t :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => sq_nonneg _

/-! ### Точная цена выбрасывания строки

`theory_note_v5.md`, §13.2. Пусть `t̂_S` и `t̂_{S∖{i₀}}` — точки нормальных
уравнений полного и урезанного наборов. Тогда

    φ_S(t̂_S) − φ_{S∖{i₀}}(t̂_{S∖{i₀}})  =  r_{i₀}(t̂_S) · r_{i₀}(t̂_{S∖{i₀}}) ,

то есть цена выбрасывания строки равна **произведению её невязок в двух
неподвижных точках** — без всяких обращений матриц. В матричной записи это
`r_{i₀}(t̂_S)²/(1 − h_{i₀})`, где `h_{i₀} = a_{i₀}'Κ(S)⁻¹a_{i₀}` — плечо строки;
множитель §4.2 `(1 + ‖a_{i₀}‖²_{Σ_f})` заменяется на `1/(1 − h_{i₀})`, который
может быть много меньше. Численно: `code/check_lo_12_5.py`. -/

/-- Разложение `φ` по одной строке: `φ_S(t) = φ_{S∖{i₀}}(t) + r_{i₀}(t)²`. -/
lemma phi_erase_add [DecidableEq ι] {i₀ : ι} (hi : i₀ ∈ S) (t : κ → ℝ) :
    phi a y S t = phi a y (S.erase i₀) t + (dotp (a i₀) t - y i₀) ^ 2 := by
  simp only [phi]
  rw [← Finset.add_sum_erase _ _ hi]
  ring

/-- То же для формы Грама. -/
lemma gram_erase_add [DecidableEq ι] {i₀ : ι} (hi : i₀ ∈ S) (v : κ → ℝ) :
    gram a S v = gram a (S.erase i₀) v + (dotp (a i₀) v) ^ 2 := by
  simp only [gram]
  rw [← Finset.add_sum_erase _ _ hi]
  ring

/-- **Сдвиг неподвижной точки.** `gram_{S∖{i₀}}(t̂₀ − t̂₁) = −r_{i₀}(t̂₁)·⟨a_{i₀}, t̂₀ − t̂₁⟩`.
Отсюда `r_{i₀}(t̂₁)·⟨a_{i₀},t̂₀−t̂₁⟩ ≤ 0`: выбрасывание строки уводит узел в ту
сторону, где её невязка растёт по модулю. -/
theorem gram_erase_shift [DecidableEq ι] {i₀ : ι} (hi : i₀ ∈ S)
    {th1 th0 : κ → ℝ} (h1 : IsNormal a y S th1) (h0 : IsNormal a y (S.erase i₀) th0) :
    gram a (S.erase i₀) (th0 - th1)
      = -((y i₀ - dotp (a i₀) th1) * dotp (a i₀) (th0 - th1)) := by
  have e0 := phi_erase_add (a := a) (y := y) hi th0
  have e1 := phi_erase_add (a := a) (y := y) hi th1
  have hA : phi a y S th0 = phi a y S th1 + gram a S (th0 - th1) := phi_eq_add h1 th0
  have hB : phi a y (S.erase i₀) th1
      = phi a y (S.erase i₀) th0 + gram a (S.erase i₀) (th0 - th1) := by
    have hb := phi_eq_add h0 th1
    have hneg : th1 - th0 = -(th0 - th1) := by abel
    rw [hneg, gram_neg] at hb
    exact hb
  have hg := gram_erase_add (a := a) hi (th0 - th1)
  have hx : dotp (a i₀) (th0 - th1) = dotp (a i₀) th0 - dotp (a i₀) th1 := dotp_sub _ _ _
  rw [hx] at hg ⊢
  linear_combination (1/2) * e0 - (1/2) * e1 - (1/2) * hA - (1/2) * hB - (1/2) * hg

/-- **Цена выбрасывания строки — произведение невязок.** -/
theorem phi_erase_cost [DecidableEq ι] {i₀ : ι} (hi : i₀ ∈ S)
    {th1 th0 : κ → ℝ} (h1 : IsNormal a y S th1) (h0 : IsNormal a y (S.erase i₀) th0) :
    phi a y S th1 - phi a y (S.erase i₀) th0
      = (y i₀ - dotp (a i₀) th1) * (y i₀ - dotp (a i₀) th0) := by
  have e0 := phi_erase_add (a := a) (y := y) hi th0
  have e1 := phi_erase_add (a := a) (y := y) hi th1
  have hA : phi a y S th0 = phi a y S th1 + gram a S (th0 - th1) := phi_eq_add h1 th0
  have hB : phi a y (S.erase i₀) th1
      = phi a y (S.erase i₀) th0 + gram a (S.erase i₀) (th0 - th1) := by
    have hb := phi_eq_add h0 th1
    have hneg : th1 - th0 = -(th0 - th1) := by abel
    rw [hneg, gram_neg] at hb
    exact hb
  have hg := gram_erase_add (a := a) hi (th0 - th1)
  have hx : dotp (a i₀) (th0 - th1) = dotp (a i₀) th0 - dotp (a i₀) th1 := dotp_sub _ _ _
  rw [hx] at hg
  linear_combination (1/2) * e0 + (1/2) * e1 - (1/2) * hA + (1/2) * hB - (1/2) * hg

/-- **Цена не меньше квадрата веса.** Прямое следствие `gram_erase_shift`:
`r₁·r₀ = r₁² + gram_{S∖{i₀}}(t̂₀ − t̂₁) ≥ r₁²`. -/
theorem sq_res_le_phi_erase_cost [DecidableEq ι] {i₀ : ι} (hi : i₀ ∈ S)
    {th1 th0 : κ → ℝ} (h1 : IsNormal a y S th1) (h0 : IsNormal a y (S.erase i₀) th0) :
    (y i₀ - dotp (a i₀) th1) ^ 2 ≤ phi a y S th1 - phi a y (S.erase i₀) th0 := by
  have hc := phi_erase_cost hi h1 h0
  have hs := gram_erase_shift hi h1 h0
  have hx : dotp (a i₀) (th0 - th1) = dotp (a i₀) th0 - dotp (a i₀) th1 := dotp_sub _ _ _
  rw [hx] at hs
  have hnn := gram_nonneg a (S.erase i₀) (th0 - th1)
  rw [hs] at hnn
  nlinarith [hc, hnn]

/-! ### Непустота: цена выбрасывания строго больше квадрата невязки

Строки `a₀ = 1`, `a₁ = 2` (одна координата), цели `y = (1, 0)`. Тогда
`t̂_{ {0,1} } = 1/5`, `t̂_{ {1} } = 0`, невязка строки `0` равна `4/5` в первой
точке и `1` во второй, и

    F({0,1}) − F({1})  =  4/5 · 1  =  4/5  >  (4/5)²  =  16/25 .

То есть в `phi_erase_cost` второй множитель действительно другой (сдвиг
неподвижной точки не нулевой), а неравенство `sq_res_le_phi_erase_cost` строгое —
иначе оба утверждения были бы бессодержательны. -/

/-- Строки примера: `a₀ = 1`, `a₁ = 2`. -/
private def aex : Fin 2 → Fin 1 → ℝ := fun i _ => if i = 0 then 1 else 2

/-- Цели примера: `y₀ = 1`, `y₁ = 0`. -/
private def yex : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0

example :
    IsNormal aex yex Finset.univ (fun _ => (1:ℝ)/5)
    ∧ IsNormal aex yex (Finset.univ.erase 0) (fun _ => (0:ℝ))
    ∧ phi aex yex Finset.univ (fun _ => (1:ℝ)/5)
        - phi aex yex (Finset.univ.erase 0) (fun _ => (0:ℝ)) = 4/5
    ∧ (yex 0 - dotp (aex 0) (fun _ => (1:ℝ)/5)) ^ 2 < 4/5 := by
  refine ⟨fun v => ?_, fun v => ?_, ?_, ?_⟩
  · simp [mom, dotp, aex, yex, Fin.sum_univ_two, Fin.sum_univ_one]
    ring
  · rw [mom, Finset.sum_erase_eq_sub (Finset.mem_univ (0 : Fin 2))]
    simp [dotp, aex, yex, Fin.sum_univ_two, Fin.sum_univ_one]
  · rw [phi, phi, Finset.sum_erase_eq_sub (Finset.mem_univ (0 : Fin 2))]
    simp [dotp, aex, yex, Fin.sum_univ_two, Fin.sum_univ_one]
    ring
  · simp [dotp, aex, yex, Fin.sum_univ_one]
    norm_num

end SparseSharpe.Factor
