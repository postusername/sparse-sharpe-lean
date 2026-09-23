import SparseSharpe.Factor.Clipped

set_option linter.style.header false

/-!
# Теорема X: long-only — это безусловная задача на самосогласованных подмножествах

`F_LO(S) = min_t ψ_S(t)` (зажатая задача), `F(A) = min_t φ_A(t)` (безусловная).
Известное направление (`Clipped.lean`, `isLeast_psiC_of_selfconsistent`): если `A`
самосогласовано в своей неподвижной точке `t̂`, то `F_LO(A) = F(A)`.

Здесь доказано **обратное и точное** утверждение:

    F_LO(S)  =  max { F(A) : A ⊆ S, A самосогласовано }.                    (X)

Две половины:

* `phi_le_psiC_of_selfconsistent` — «≥»: любое самосогласованное `A ⊆ S` даёт
  нижнюю оценку `F(A) ≤ ψ_S(t)` сразу во **всех** точках `t`;
* `isNormal_activeSet_of_min` — «≤»: в точке минимума `t₀` зажатой задачи
  активное множество `A(t₀) = {i ∈ S : строка не зажата или r_i(t₀) > 0}`
  удовлетворяет нормальным уравнениям для `φ_{A(t₀)}` в той же точке `t₀`
  (вариационный аргумент без дифференцирования, как в `isNormal_of_min`),
  а `ψ_S(t₀) = φ_{A(t₀)}(t₀)` (`psiC_eq_phi_activeSet`). Значит максимум
  в (X) достигается и равен `F_LO(S)`.

Итог для алгоритма (`lo_values_eq_sc_values`): перебор по **всем** носителям
размера `≤ k` с зажатой целью можно заменить перебором по носителям размера
`≤ k`, самосогласованным в собственной неподвижной точке, с **незажатой**
целью — той самой, которую вычисляет ключ `(Q, M, Κ)` динамики §4.
Это снимает вопрос «что делать с зажатием» на уровне постановки: вся
трудность сосредоточена в том, что самосогласованность не наследуется
префиксами набора при построении, и потому её проверяют в узле сетки
(Теорема U, `ActiveFilter.lean`) с потерей, оценённой в `Stability.lean`.

Незажатые строки (якоря `Σ_f^{-1/2}`) всегда остаются в `A(t₀)`
(`not_clip_mem_activeSet`), поэтому `A(t₀)` — это по-прежнему «носитель плюс
якоря», и `F(A(t₀))` — регуляризованное значение, а не вырожденное.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype κ]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {cl : ι → Bool} {S A : Finset ι} {t th t₀ : κ → ℝ}

/-! ### Вспомогательное: неотрицательный квадратный трёхчлен без линейного члена -/

/-- Если `−2sL + s²C ≥ 0` при всех `s` и `C ≥ 0`, то `L = 0`. -/
lemma eq_zero_of_quad_nonneg {L C : ℝ} (hC : 0 ≤ C)
    (h : ∀ s : ℝ, 0 ≤ -(2 * s * L) + s ^ 2 * C) : L = 0 := by
  by_contra hL
  have hpos : (0:ℝ) < C + 1 := by linarith
  have hsq : (0:ℝ) < (C + 1) ^ 2 := by positivity
  have h1 := h (L / (C + 1))
  have hid : -(2 * (L / (C + 1)) * L) + (L / (C + 1)) ^ 2 * C
      = -(L ^ 2 * (C + 2)) / (C + 1) ^ 2 := by
    field_simp; ring
  rw [hid] at h1
  have h2 : (0:ℝ) ≤ -(L ^ 2 * (C + 2)) := by
    have hmul := mul_nonneg h1 hsq.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hsq)] at hmul
  have h3 : (0:ℝ) < L ^ 2 * (C + 2) := by
    have : (0:ℝ) < L ^ 2 := by positivity
    nlinarith
  linarith

/-! ### Активное множество -/

/-- **Активное множество** набора `S` в точке `t`: зажатые строки с
строго положительной невязкой плюс все незажатые строки. -/
noncomputable def activeSet (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (S : Finset ι)
    (t : κ → ℝ) : Finset ι :=
  S.filter (fun i => cl i → 0 < y i - dotp (a i) t)

lemma mem_activeSet {i : ι} :
    i ∈ activeSet a y cl S t ↔ i ∈ S ∧ (cl i → 0 < y i - dotp (a i) t) := by
  simp [activeSet]

lemma activeSet_subset : activeSet a y cl S t ⊆ S := Finset.filter_subset _ _

/-- Незажатые строки (якоря) всегда активны. -/
lemma not_clip_mem_activeSet {i : ι} (hi : i ∈ S) (h : ¬ cl i) :
    i ∈ activeSet a y cl S t :=
  mem_activeSet.mpr ⟨hi, fun hc => absurd hc h⟩

/-- Активное множество самосогласовано в той точке, где оно взято. -/
lemma selfcons_activeSet :
    ∀ i ∈ activeSet a y cl S t, cl i → 0 ≤ y i - dotp (a i) t := by
  intro i hi hc
  exact le_of_lt ((mem_activeSet.mp hi).2 hc)

/-- Вне активного множества зажатая невязка равна нулю. -/
lemma resC_eq_zero_of_not_mem {i : ι} (hi : i ∈ S) (hni : i ∉ activeSet a y cl S t) :
    resC a y cl i t = 0 := by
  have h := mem_activeSet (a := a) (y := y) (cl := cl) (S := S) (t := t) (i := i)
  have hnot : ¬ (cl i → 0 < y i - dotp (a i) t) := by
    intro hcon; exact hni (h.mpr ⟨hi, hcon⟩)
  have hc : cl i := by by_contra hc; exact hnot (fun hc' => absurd hc' hc)
  have hle : y i - dotp (a i) t ≤ 0 := by
    by_contra hlt
    exact hnot (fun _ => lt_of_not_ge hlt)
  simp [resC, hc, max_eq_right hle]

/-- Поточечно: зажатая невязка не превосходит обычной по модулю. -/
lemma sq_resC_le (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (i : ι) (t : κ → ℝ) :
    resC a y cl i t ^ 2 ≤ (dotp (a i) t - y i) ^ 2 := by
  by_cases h : cl i
  · simp only [resC, h, ite_true]
    rcases le_or_gt (y i - dotp (a i) t) 0 with hx | hx
    · rw [max_eq_right hx]; simpa using sq_nonneg (dotp (a i) t - y i)
    · rw [max_eq_left hx.le]; nlinarith
  · simp only [resC, h, ite_false, Bool.false_eq_true]
    nlinarith

/-- **Значение зажатой задачи — это значение безусловной на активном множестве.** -/
theorem psiC_eq_phi_activeSet (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (S : Finset ι)
    (t : κ → ℝ) : psiC a y cl S t = phi a y (activeSet a y cl S t) t := by
  have hz : ∀ i ∈ S, i ∉ activeSet a y cl S t → resC a y cl i t ^ 2 = 0 := by
    intro i hi hni
    rw [resC_eq_zero_of_not_mem hi hni]; ring
  have h1 : psiC a y cl S t = ∑ i ∈ activeSet a y cl S t, resC a y cl i t ^ 2 :=
    (Finset.sum_subset activeSet_subset hz).symm
  rw [h1, phi]
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases hc : cl i
  · have hpos : 0 < y i - dotp (a i) t := (mem_activeSet.mp hi).2 hc
    simp only [resC, hc, ite_true, max_eq_left hpos.le]
    ring
  · simp only [resC, hc, ite_false, Bool.false_eq_true]
    ring

/-! ### Половина «≥»: самосогласованное подмножество даёт нижнюю оценку -/

/-- **Любое самосогласованное `A ⊆ S` оценивает long-only снизу во всех точках.**
Поэтому `F(A) ≤ F_LO(S)` для каждого такого `A`. -/
theorem phi_le_psiC_of_selfconsistent (hAS : A ⊆ S) (hnormal : IsNormal a y A th)
    (hself : ∀ i ∈ A, cl i → 0 ≤ y i - dotp (a i) th) (t : κ → ℝ) :
    phi a y A th ≤ psiC a y cl S t :=
  calc phi a y A th = psiC a y cl A th := (psiC_eq_phi_of_nonneg hself).symm
    _ ≤ psiC a y cl A t := psiC_min_of_normal_of_nonneg hnormal hself t
    _ ≤ psiC a y cl S t := psiC_mono hAS t

/-! ### Половина «≤»: в точке минимума активное множество нормально -/

/-- Оценка сверху вдоль направления: вне активного множества вклад строки
не больше `s²⟨a_i,v⟩²`, внутри — не больше незажатого квадрата невязки. -/
lemma psiC_shift_le_active [DecidableEq ι] (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool)
    (S : Finset ι) (t v : κ → ℝ) (s : ℝ) :
    psiC a y cl S (t + s • v)
      ≤ phi a y (activeSet a y cl S t) (t + s • v)
        + s ^ 2 * gram a (S \ activeSet a y cl S t) v := by
  have hsplit : ∑ i ∈ S \ activeSet a y cl S t, resC a y cl i (t + s • v) ^ 2
      + ∑ i ∈ activeSet a y cl S t, resC a y cl i (t + s • v) ^ 2
      = psiC a y cl S (t + s • v) :=
    Finset.sum_sdiff activeSet_subset
  have hout : ∑ i ∈ S \ activeSet a y cl S t, resC a y cl i (t + s • v) ^ 2
      ≤ s ^ 2 * gram a (S \ activeSet a y cl S t) v := by
    rw [gram, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hiS : i ∈ S := (Finset.mem_sdiff.mp hi).1
    have hni : i ∉ activeSet a y cl S t := (Finset.mem_sdiff.mp hi).2
    have hzero : resC a y cl i t = 0 := resC_eq_zero_of_not_mem hiS hni
    have hc : cl i := by
      by_cases hc : cl i
      · exact hc
      · exact absurd (not_clip_mem_activeSet hiS hc) hni
    have hle : y i - dotp (a i) t ≤ 0 := by
      by_contra hlt
      exact hni (mem_activeSet.mpr ⟨hiS, fun _ => lt_of_not_ge hlt⟩)
    have hdot : dotp (a i) (t + s • v) = dotp (a i) t + s * dotp (a i) v := by
      rw [dotp_add, dotp_smul]
    simp only [resC, hc, ite_true, hdot]
    have hstep : max (y i - (dotp (a i) t + s * dotp (a i) v)) 0
        ≤ max (-(s * dotp (a i) v)) 0 := by
      apply max_le_max _ (le_refl 0)
      linarith
    have hnn : (0:ℝ) ≤ max (y i - (dotp (a i) t + s * dotp (a i) v)) 0 := le_max_right _ _
    have hsq : max (y i - (dotp (a i) t + s * dotp (a i) v)) 0 ^ 2
        ≤ max (-(s * dotp (a i) v)) 0 ^ 2 := by
      have hnn2 : (0:ℝ) ≤ max (-(s * dotp (a i) v)) 0 := le_max_right _ _
      nlinarith
    have hfin : max (-(s * dotp (a i) v)) 0 ^ 2 ≤ s ^ 2 * dotp (a i) v ^ 2 := by
      rcases le_or_gt (-(s * dotp (a i) v)) 0 with hx | hx
      · rw [max_eq_right hx]
        have hz0 : (0:ℝ) ^ 2 = 0 := by norm_num
        rw [hz0]; positivity
      · rw [max_eq_left hx.le]; nlinarith
    linarith
  have hin : ∑ i ∈ activeSet a y cl S t, resC a y cl i (t + s • v) ^ 2
      ≤ phi a y (activeSet a y cl S t) (t + s • v) :=
    Finset.sum_le_sum fun i _ => sq_resC_le a y cl i (t + s • v)
  linarith [hsplit, hout, hin]

/-- **Теорема X, половина «≤».** В точке минимума зажатой задачи активное множество
удовлетворяет нормальным уравнениям безусловной задачи в той же точке. -/
theorem isNormal_activeSet_of_min
    (hmin : ∀ t, psiC a y cl S t₀ ≤ psiC a y cl S t) :
    IsNormal a y (activeSet a y cl S t₀) t₀ := by
  classical
  intro v
  set A := activeSet a y cl S t₀ with hA
  set C : ℝ := gram a A v + gram a (S \ A) v with hC
  have hCnn : 0 ≤ C := add_nonneg (gram_nonneg a A v) (gram_nonneg a (S \ A) v)
  have key : ∀ s : ℝ, 0 ≤ -(2 * s * mom a y A t₀ v) + s ^ 2 * C := by
    intro s
    have h1 := hmin (t₀ + s • v)
    have h2 := psiC_shift_le_active a y cl S t₀ v s
    have h3 : phi a y A (t₀ + s • v)
        = phi a y A t₀ - 2 * (s * mom a y A t₀ v) + s ^ 2 * gram a A v := by
      rw [phi_shift a y A t₀ (s • v), mom_smul, gram_smul]
    have h4 : psiC a y cl S t₀ = phi a y A t₀ := psiC_eq_phi_activeSet a y cl S t₀
    rw [h4] at h1
    rw [h3] at h2
    have := le_trans h1 h2
    rw [hC]
    linarith
  exact eq_zero_of_quad_nonneg hCnn key

/-! ### Теорема X целиком -/

/-- **Теорема X.** Если `t₀` доставляет минимум зажатой задаче на `S`, то

* активное множество `A = A(t₀) ⊆ S` самосогласовано в `t₀`;
* `t₀` — его неподвижная точка (нормальные уравнения);
* `F_LO(A) = F(A) = φ_A(t₀) = ψ_S(t₀) = F_LO(S)`;
* все незажатые строки (якоря) остались в `A`.

Иначе говоря, значение long-only на `S` достигается на подмножестве, для которого
зажатие неактивно, а значит его считает обычный ключ `(Q, M, Κ)`. -/
theorem exists_selfconsistent_subset
    (hmin : ∀ t, psiC a y cl S t₀ ≤ psiC a y cl S t) :
    ∃ A ⊆ S, A.card ≤ S.card
      ∧ (∀ i ∈ S, ¬ cl i → i ∈ A)
      ∧ IsNormal a y A t₀
      ∧ (∀ i ∈ A, cl i → 0 ≤ y i - dotp (a i) t₀)
      ∧ IsLeast {z : ℝ | ∃ t, z = psiC a y cl A t} (phi a y A t₀)
      ∧ phi a y A t₀ = psiC a y cl S t₀ := by
  refine ⟨activeSet a y cl S t₀, activeSet_subset, Finset.card_le_card activeSet_subset,
    fun i hi hc => not_clip_mem_activeSet hi hc, isNormal_activeSet_of_min hmin,
    selfcons_activeSet, ?_, (psiC_eq_phi_activeSet a y cl S t₀).symm⟩
  exact isLeast_psiC_of_selfconsistent (isNormal_activeSet_of_min hmin) selfcons_activeSet

/-- **Теорема X в форме «максимум».** Значение long-only на `S` — это в точности
наибольшее значение **безусловной** задачи по самосогласованным подмножествам `S`. -/
theorem isGreatest_phi_selfconsistent
    (hmin : ∀ t, psiC a y cl S t₀ ≤ psiC a y cl S t) :
    IsGreatest {z : ℝ | ∃ A, A ⊆ S ∧ ∃ th, IsNormal a y A th
        ∧ (∀ i ∈ A, cl i → 0 ≤ y i - dotp (a i) th) ∧ z = phi a y A th}
      (psiC a y cl S t₀) := by
  constructor
  · exact ⟨activeSet a y cl S t₀, activeSet_subset, t₀, isNormal_activeSet_of_min hmin,
      selfcons_activeSet, psiC_eq_phi_activeSet a y cl S t₀⟩
  · rintro z ⟨A, hAS, th, hnormal, hself, rfl⟩
    exact phi_le_psiC_of_selfconsistent hAS hnormal hself t₀

/-- **Следствие для динамики: множества достижимых значений совпадают.**

Слева — значения long-only по носителям размера `≤ k`; справа — значения
**безусловной** задачи по самосогласованным носителям размера `≤ k`.
Включение «⊆» — это Теорема X, «⊇» — `isLeast_psiC_of_selfconsistent`.
Следовательно совпадают и максимумы: FPTAS для long-only достаточно строить
как перебор самосогласованных носителей с незажатой целью. -/
theorem lo_values_eq_sc_values (k : ℕ)
    (hattain : ∀ S : Finset ι, ∃ t₀ : κ → ℝ, ∀ t, psiC a y cl S t₀ ≤ psiC a y cl S t) :
    {z : ℝ | ∃ S : Finset ι, S.card ≤ k ∧ IsLeast {u : ℝ | ∃ t, u = psiC a y cl S t} z}
      = {z : ℝ | ∃ A : Finset ι, A.card ≤ k ∧ ∃ th, IsNormal a y A th
          ∧ (∀ i ∈ A, cl i → 0 ≤ y i - dotp (a i) th) ∧ z = phi a y A th} := by
  ext z
  constructor
  · rintro ⟨S, hcard, hleast⟩
    obtain ⟨t₀, hmin⟩ := hattain S
    have hz : z = psiC a y cl S t₀ := by
      refine le_antisymm ?_ ?_
      · exact hleast.2 ⟨t₀, rfl⟩
      · obtain ⟨t₁, ht₁⟩ := hleast.1
        rw [ht₁]; exact hmin t₁
    obtain ⟨A, hAS, hcardA, _, hnormal, hself, _, hval⟩ := exists_selfconsistent_subset hmin
    exact ⟨A, le_trans hcardA hcard, t₀, hnormal, hself, by rw [hval, hz]⟩
  · rintro ⟨A, hcard, th, hnormal, hself, rfl⟩
    exact ⟨A, hcard, isLeast_psiC_of_selfconsistent hnormal hself⟩

/-! ### Непустота: активное множество бывает собственным подмножеством

`lake build` не отличает верное утверждение от бессодержательного. Ниже инстанс,
в котором редукция Теоремы X **реально выбрасывает строку**: актив с `y = −1`
и нулевой факторной нагрузкой (`a = 0`) при якоре `a = 1, y = 0`.
Минимум зажатой задачи достигается в `t₀ = 0` со значением `0`, активное
множество — это один якорь, и `φ_{A}(t₀) = 0 = ψ_S(t₀)`. -/

private def aEx : Fin 2 → Fin 1 → ℝ := fun i _ => if i = 0 then 0 else 1

private def yEx : Fin 2 → ℝ := fun i => if i = 0 then -1 else 0

private def clEx : Fin 2 → Bool := fun i => i = 0

example : ∀ t : Fin 1 → ℝ,
    psiC aEx yEx clEx Finset.univ (fun _ => 0) ≤ psiC aEx yEx clEx Finset.univ t := by
  intro t
  simp [psiC, resC, aEx, yEx, clEx, dotp, Fin.sum_univ_two, Fin.sum_univ_one]
  positivity

/-- Активное множество в точке минимума — строго меньше `S`: зажатая строка выброшена. -/
example : activeSet aEx yEx clEx Finset.univ (fun _ => (0 : ℝ)) ⊂ Finset.univ := by
  refine Finset.ssubset_univ_iff.mpr ?_
  intro hcon
  have h0 : (0 : Fin 2) ∈ activeSet aEx yEx clEx Finset.univ (fun _ => (0 : ℝ)) := by
    rw [hcon]; exact Finset.mem_univ _
  have := (mem_activeSet.mp h0).2 (by simp [clEx])
  simp [yEx, aEx, dotp] at this
  linarith

end SparseSharpe.Factor
