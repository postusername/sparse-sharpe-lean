import SparseSharpe.Factor.Reduction
import SparseSharpe.Factor.NormalExists
import SparseSharpe.Factor.Stability

set_option linter.style.header false

/-!
# Достижимость минимума зажатой задачи

Теорема X (`Factor/Reduction.lean`) формулируется «в точке минимума `t₀`
зажатой задачи», а `lo_values_eq_sc_values` принимает существование такой точки
гипотезой `hattain`. Здесь гипотеза снята.

Причина, по которой минимум достигается, — та же самая, из-за которой в
Теореме W появляется `γ`: **якорные строки**. На них `y = 0` и зажатия нет,
поэтому

    ψ_S(t)  ≥  Σ_{i ∈ base} ⟨a_i,t⟩²  =  gram_base(t),

а если внутри `base` есть невырожденная `K`-ка (в приложении — сами якоря
`Σ_f^{-1/2}`, `det_anchor_ne_zero`), то `gram_base` положительно определена
(`gram_pos_of_det`) и потому мажорирует `c‖t‖²` с `c > 0`
(`exists_gram_lower_bound`: минимум непрерывной положительной функции на
компактной сфере). Значит `ψ_S` коэрцитивна, и непрерывная коэрцитивная
функция на `ℝ^K` достигает минимума (`Continuous.exists_forall_le`).

Итог — `exists_min_psiC`, а через него `lo_values_eq_sc_values_of_det`:
Теорема X без гипотез существования, только со свойством входа
«в наборе есть невырожденная `K`-ка незажатых строк с нулевой целью».
-/

namespace SparseSharpe.Factor

open Finset Filter Topology Metric

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {cl : ι → Bool} {S base : Finset ι}

/-! ### Непрерывность -/

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma continuous_dotp (ai : κ → ℝ) : Continuous fun t : κ → ℝ => dotp ai t := by
  simp only [dotp]
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma continuous_resC (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (i : ι) :
    Continuous fun t : κ → ℝ => resC a y cl i t := by
  simp only [resC]
  by_cases h : cl i
  · simp only [h, ite_true]
    exact (continuous_const.sub (continuous_dotp (a i))).max continuous_const
  · simp only [h, ite_false, Bool.false_eq_true]
    exact continuous_const.sub (continuous_dotp (a i))

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma continuous_psiC (a : ι → κ → ℝ) (y : ι → ℝ) (cl : ι → Bool) (S : Finset ι) :
    Continuous fun t : κ → ℝ => psiC a y cl S t := by
  simp only [psiC]
  exact continuous_finsetSum _ fun i _ => (continuous_resC a y cl i).pow 2

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma continuous_gram (a : ι → κ → ℝ) (V : Finset ι) :
    Continuous fun v : κ → ℝ => gram a V v := by
  simp only [gram]
  exact continuous_finsetSum _ fun i _ => (continuous_dotp (a i)).pow 2

/-! ### Форма Грама невырожденного набора мажорирует `c‖v‖²` -/

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
/-- Положительно определённая форма Грама отделена от нуля на сфере, а значит
мажорирует `c‖v‖²` с `c > 0`. Это количественная форма `gram_pos_of_det`. -/
theorem exists_gram_lower_bound [Nonempty κ] {V : Finset ι}
    (hpos : ∀ v : κ → ℝ, v ≠ 0 → 0 < gram a V v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : κ → ℝ, c * ‖v‖ ^ 2 ≤ gram a V v := by
  obtain ⟨u, hu, hmin⟩ :=
    (isCompact_sphere (0 : κ → ℝ) 1).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr zero_le_one)
      (continuous_gram a V).continuousOn
  have hu1 : ‖u‖ = 1 := by simpa using mem_sphere_zero_iff_norm.mp hu
  have hune : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu1; exact zero_ne_one hu1
  refine ⟨gram a V u, hpos u hune, fun v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simpa using gram_nonneg a V (0 : κ → ℝ)
  · have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
    set w : κ → ℝ := ‖v‖⁻¹ • v with hw
    have hwmem : w ∈ sphere (0 : κ → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, hw, norm_smul]
      simp [inv_mul_cancel₀ (ne_of_gt hnv)]
    have hle : gram a V u ≤ gram a V w := hmin hwmem
    have hsm : gram a V v = ‖v‖ ^ 2 * gram a V w := by
      have : v = ‖v‖ • w := by
        rw [hw, smul_smul, mul_inv_cancel₀ (ne_of_gt hnv), one_smul]
      calc gram a V v = gram a V (‖v‖ • w) := by rw [← this]
        _ = ‖v‖ ^ 2 * gram a V w := gram_smul a V w ‖v‖
    rw [hsm]
    have := mul_le_mul_of_nonneg_left hle (sq_nonneg ‖v‖)
    linarith [this]

/-! ### Коэрцитивность зажатой задачи -/

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
/-- Вклад незажатых строк с нулевой целью в `ψ_S` — это в точности `gram_base(t)`. -/
lemma gram_base_le_psiC (hbase : base ⊆ S) (hcl : ∀ i ∈ base, ¬ cl i)
    (hy : ∀ i ∈ base, y i = 0) (t : κ → ℝ) :
    gram a base t ≤ psiC a y cl S t := by
  have heq : gram a base t = ∑ i ∈ base, resC a y cl i t ^ 2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [resC, hcl i hi, ite_false, Bool.false_eq_true, hy i hi]
    ring
  rw [heq, psiC]
  exact Finset.sum_le_sum_of_subset_of_nonneg hbase fun _ _ _ => sq_nonneg _

omit [Fintype ι] [DecidableEq ι] in
/-- **Минимум зажатой задачи достигается.** Достаточно, чтобы в наборе была
невырожденная `K`-ка незажатых строк с нулевой целью — в приложении это
якорные строки `Σ_f^{-1/2}`, входящие в каждый набор динамики. -/
theorem exists_min_psiC [Nonempty κ] {Ta : κ → ι}
    (hbase : base ⊆ S) (hcl : ∀ i ∈ base, ¬ cl i) (hy : ∀ i ∈ base, y i = 0)
    (hTa : ∀ l, Ta l ∈ base) (hdet : (rowMat a Ta).det ≠ 0) :
    ∃ t₀ : κ → ℝ, ∀ t, psiC a y cl S t₀ ≤ psiC a y cl S t := by
  obtain ⟨c, hc, hlow⟩ :=
    exists_gram_lower_bound (a := a) (V := base) fun v hv => gram_pos_of_det hTa hdet hv
  refine (continuous_psiC a y cl S).exists_forall_le ?_
  have hsq : Tendsto (fun t : κ → ℝ => c * ‖t‖ ^ 2) (cocompact (κ → ℝ)) atTop := by
    have hn : Tendsto (fun t : κ → ℝ => ‖t‖) (cocompact (κ → ℝ)) atTop :=
      tendsto_norm_cocompact_atTop
    have h2 : Tendsto (fun t : κ → ℝ => ‖t‖ ^ 2) (cocompact (κ → ℝ)) atTop := by
      simpa [sq] using hn.atTop_mul_atTop₀ hn
    exact h2.const_mul_atTop hc
  refine tendsto_atTop_mono (fun t => ?_) hsq
  exact le_trans (hlow t) (gram_base_le_psiC hbase hcl hy t)

/-! ### Теорема X без гипотез существования -/

omit [Fintype ι] [DecidableEq ι] in
/-- **Значение long-only определено.** Множество значений `ψ_S` имеет наименьший
элемент, то есть `F_LO(S) = min_t ψ_S(t)` — законное определение, а не `inf`. -/
theorem exists_isLeast_psiC [Nonempty κ] {Ta : κ → ι}
    (hbase : base ⊆ S) (hcl : ∀ i ∈ base, ¬ cl i) (hy : ∀ i ∈ base, y i = 0)
    (hTa : ∀ l, Ta l ∈ base) (hdet : (rowMat a Ta).det ≠ 0) :
    ∃ z : ℝ, IsLeast {u : ℝ | ∃ t, u = psiC a y cl S t} z := by
  obtain ⟨t₀, hmin⟩ := exists_min_psiC hbase hcl hy hTa hdet
  exact ⟨psiC a y cl S t₀, ⟨t₀, rfl⟩, by rintro u ⟨t, rfl⟩; exact hmin t⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **Теорема X, безусловная форма.** Гипотеза «минимум достигается» снята:
достаточно, чтобы набор содержал невырожденную `K`-ку незажатых строк
с нулевой целью (в приложении — якоря `Σ_f^{-1/2}`).

Вывод: значение long-only на `S` достигается на **самосогласованном**
подмножестве `A ⊆ S`, причём с незажатой целью `φ_A`, которую и считает
ключ динамики `(Q, M, Κ)`. -/
theorem exists_selfconsistent_subset_of_det [Nonempty κ] {Ta : κ → ι}
    (hbase : base ⊆ S) (hcl : ∀ i ∈ base, ¬ cl i) (hy : ∀ i ∈ base, y i = 0)
    (hTa : ∀ l, Ta l ∈ base) (hdet : (rowMat a Ta).det ≠ 0) :
    ∃ A ⊆ S, A.card ≤ S.card
      ∧ (∀ i ∈ S, ¬ cl i → i ∈ A)
      ∧ ∃ th : κ → ℝ, IsNormal a y A th
        ∧ (∀ i ∈ A, cl i → 0 ≤ y i - dotp (a i) th)
        ∧ IsLeast {z : ℝ | ∃ t, z = psiC a y cl A t} (phi a y A th)
        ∧ IsLeast {z : ℝ | ∃ t, z = psiC a y cl S t} (phi a y A th) := by
  obtain ⟨t₀, hmin⟩ := exists_min_psiC hbase hcl hy hTa hdet
  obtain ⟨A, hAS, hcard, hanch, hnormal, hself, hleastA, hval⟩ :=
    exists_selfconsistent_subset hmin
  refine ⟨A, hAS, hcard, hanch, t₀, hnormal, hself, hleastA, ?_, ?_⟩
  · rw [hval]; exact ⟨t₀, rfl⟩
  · rintro u ⟨t, rfl⟩; rw [hval]; exact hmin t

/-! ### Непустота гипотез

`lake build` не отличает верное утверждение от бессодержательного. Инстанс:
один актив (`y = 1`, нагрузка `1`) и один якорь (`a = 1`, `y = 0`).
Якорь образует невырожденную `1`-ку, все гипотезы выполнены, и минимум
действительно существует. -/

private def aAt : Fin 2 → Fin 1 → ℝ := fun _ _ => 1

private def yAt : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0

private def clAt : Fin 2 → Bool := fun i => i = 0

private def TaAt : Fin 1 → Fin 2 := fun _ => 1

example : (rowMat aAt TaAt).det ≠ 0 := by
  simp [rowMat, aAt, Matrix.det_unique]

/-- Все гипотезы `exists_min_psiC` выполнимы одновременно. -/
example : ∃ t₀ : Fin 1 → ℝ, ∀ t, psiC aAt yAt clAt Finset.univ t₀
    ≤ psiC aAt yAt clAt Finset.univ t :=
  exists_min_psiC (base := {1}) (S := Finset.univ) (Ta := TaAt)
    (Finset.subset_univ _) (by decide)
    (by intro i hi; simp only [Finset.mem_singleton] at hi; subst hi; norm_num [yAt])
    (by decide)
    (by simp [rowMat, aAt, Matrix.det_unique])

end SparseSharpe.Factor
