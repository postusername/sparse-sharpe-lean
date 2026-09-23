import SparseSharpe.Factor.KBridge
import SparseSharpe.Factor.Clipped

set_option linter.style.header false

/-!
# Контрпример к остатку §13.5: вытеснение из корзины в далёком узле вредно

`theory_note_v5.md`, §13.5 спрашивал: пусть `A` самосогласовано и допущено в узле `t`
(`r_i(t) ≥ ρ` при всех `i ∈ A`), но зазор `γ² = Q_t(Ā) − F(Ā)` больше `ρ²`;
пусть `R` — сосед `A` по корзине (те же `mom` и `gram` в узле) с `Q_t(R̄) ≥ Q_t(Ā)`,
тоже допущенный в узле. Верно ли `F_LO(R) ≥ F_LO(A) − poly(k,K)·ρ²`?

**Ответ — нет.** Инстанс: `K = 1` фактор, четыре актива, `k = 2`,
`Σ_f = 1`, `d ≡ 1`, узел `t = 0` и параметр `0 < δ ≤ 1`:

    нагрузки  B = (0, 5, 3, 4),    альфы  m = (2, 4 + 3δ/5, δ, 5),
    A = {0,1},   R = {2,3}.

Оба набора дают в узле **одну и ту же** форму Грама (`26 v²`) и **один и тот же**
первый момент (`(20+3δ)v`), у обоих одна и та же неподвижная точка
`t̂ = (20+3δ)/26`, и `Q_0(R̄) > Q_0(Ā)` при `δ ≤ 1` — то есть `R` законно вытесняет
`A` из корзины. При этом

* `A` самосогласовано: невязки в `t̂` равны `2` и `(20+3δ)/130`, обе положительны,
  поэтому `F_LO(A) = F(Ā) = 4 + (20+3δ)²/650 ≥ 60/13`;
* `R` самосогласованным **не** является: невязка актива `2` в `t̂` равна
  `(17δ−60)/26 < 0`, и `F_LO(R) = 25/17` ровно (достигается на `t = 20/17`);
* оба набора допущены в узле с запасом `ρ = δ`, а зазор `γ² = (20+3δ)²/26 > 1 ≥ ρ²`.

Потеря `F_LO(A) − F_LO(R) ≥ 695/221 > 3` **не зависит от `δ`**, а `ρ² = δ²`
можно сделать сколь угодно малым. Значит никакой `poly(k,K)·ρ²` её не покрывает:
кванторы берутся в том же порядке, что и в `Ex125` — сначала произвольный
множитель `p`, потом инстанс (теорема `eviction_far_node`).

Ломается, как и в §13.3, **маршрут доказательства**, а не алгоритм: на этом
инстансе у LO-K′ есть другие наборы (в частности `{1}` даёт `4 + 25/26`),
но доказательство полноты через «вытеснение безвредно» невозможно.
-/

namespace SparseSharpe.Factor
namespace Ex135

open Finset

/-- Единичная матрица `1×1`: одновременно `Σ_f`, `Σ_f⁻¹` и якорная строка `G`. -/
def Id1 : Fin 1 → Fin 1 → ℝ := fun _ _ => 1

/-- Нагрузки четырёх активов: `A = {0,1}` несёт `(0,5)`, `R = {2,3}` несёт `(3,4)`.
Суммы квадратов совпадают: `0² + 5² = 3² + 4² = 25`. -/
def bco : Fin 4 → ℝ :=
  fun i => if i = 0 then 0 else if i = 1 then 5 else if i = 2 then 3 else 4

/-- Нагрузка как `K`-вектор (`K = 1`). -/
def Bex : Fin 4 → Fin 1 → ℝ := fun i _ => bco i

/-- Идиосинкразия `d ≡ 1`. -/
def dex : Fin 4 → ℝ := fun _ => 1

/-- Альфы. Подобраны так, чтобы первый момент обоих наборов в узле `t = 0`
был равен `20 + 3δ`. -/
noncomputable def mex (δ : ℝ) : Fin 4 → ℝ :=
  fun i => if i = 0 then 2 else if i = 1 then 4 + 3 * δ / 5 else if i = 2 then δ else 5

/-- Самосогласованный набор — носитель, который динамика должна была бы сохранить. -/
def Aset : Finset (Fin 4) := {0, 1}

/-- Вытесняющий сосед по корзине. -/
def Rset : Finset (Fin 4) := {2, 3}

/-- Строки задачи наименьших квадратов (активы плюс якорная строка). -/
noncomputable def rowsE : (Fin 4 ⊕ Fin 1) → Fin 1 → ℝ := rowsK dex Bex Id1

/-- Правые части. -/
noncomputable def tgtsE (δ : ℝ) : (Fin 4 ⊕ Fin 1) → ℝ := targetsK (mex δ) dex

/-- Зажимаются строки активов, якорная — нет. -/
def clipE : (Fin 4 ⊕ Fin 1) → Bool := fun r => r.isLeft

/-- Узел сетки, в котором происходит вытеснение. -/
def node : Fin 1 → ℝ := fun _ => 0

/-- Общая неподвижная точка обоих наборов. -/
noncomputable def tfix (δ : ℝ) : Fin 1 → ℝ := fun _ => (20 + 3 * δ) / 26

/-! ### Развёртка определений -/

lemma bco0 : bco 0 = 0 := by norm_num [bco]
lemma bco1 : bco 1 = 5 := by norm_num [bco]
lemma bco2 : bco 2 = 3 := by norm_num [bco]
lemma bco3 : bco 3 = 4 := by norm_num [bco]

lemma mex0 (δ : ℝ) : mex δ 0 = 2 := by norm_num [mex]
lemma mex1 (δ : ℝ) : mex δ 1 = 4 + 3 * δ / 5 := by norm_num [mex]
lemma mex2 (δ : ℝ) : mex δ 2 = δ := by norm_num [mex]
lemma mex3 (δ : ℝ) : mex δ 3 = 5 := by norm_num [mex]

lemma dotp1 (a t : Fin 1 → ℝ) : dotp a t = a 0 * t 0 := by
  simp [dotp]

lemma dotp_inl (i : Fin 4) (t : Fin 1 → ℝ) :
    dotp (rowsE (Sum.inl i)) t = bco i * t 0 := by
  rw [dotp1]
  simp [rowsE, rowsK, Bex, dex]

lemma dotp_inr (l : Fin 1) (t : Fin 1 → ℝ) :
    dotp (rowsE (Sum.inr l)) t = t 0 := by
  rw [dotp1]
  simp [rowsE, rowsK, Id1]

lemma tgt_inl (δ : ℝ) (i : Fin 4) : tgtsE δ (Sum.inl i) = mex δ i := by
  simp [tgtsE, targetsK, dex]

lemma tgt_inr (δ : ℝ) (l : Fin 1) : tgtsE δ (Sum.inr l) = 0 := by
  simp [tgtsE, targetsK]

/-- Сумма по `Ā = A ∪ {якорь}`. -/
lemma sum_barA (f : (Fin 4 ⊕ Fin 1) → ℝ) :
    ∑ r ∈ barK (κ := Fin 1) Aset, f r
      = f (Sum.inl 0) + f (Sum.inl 1) + f (Sum.inr 0) := by
  rw [barK, Finset.sum_disjSum]
  have h1 : ∑ i ∈ Aset, f (Sum.inl i) = f (Sum.inl 0) + f (Sum.inl 1) := by
    rw [Aset]; exact Finset.sum_pair (by decide)
  rw [h1, Fin.sum_univ_one]

/-- Сумма по `R̄ = R ∪ {якорь}`. -/
lemma sum_barR (f : (Fin 4 ⊕ Fin 1) → ℝ) :
    ∑ r ∈ barK (κ := Fin 1) Rset, f r
      = f (Sum.inl 2) + f (Sum.inl 3) + f (Sum.inr 0) := by
  rw [barK, Finset.sum_disjSum]
  have h1 : ∑ i ∈ Rset, f (Sum.inl i) = f (Sum.inl 2) + f (Sum.inl 3) := by
    rw [Rset]; exact Finset.sum_pair (by decide)
  rw [h1, Fin.sum_univ_one]

/-! ### Оба набора лежат в одной корзине -/

/-- Форма Грама набора `A`: `26 v²`. -/
lemma gram_A (v : Fin 1 → ℝ) : gram rowsE (barK (κ := Fin 1) Aset) v = 26 * (v 0) ^ 2 := by
  rw [gram, sum_barA]
  rw [dotp_inl, dotp_inl, dotp_inr, bco0, bco1]
  ring

/-- Форма Грама набора `R`: та же `26 v²`. -/
lemma gram_R (v : Fin 1 → ℝ) : gram rowsE (barK (κ := Fin 1) Rset) v = 26 * (v 0) ^ 2 := by
  rw [gram, sum_barR]
  rw [dotp_inl, dotp_inl, dotp_inr, bco2, bco3]
  ring

/-- **Формы Грама совпадают** — первая половина условия «сосед по корзине». -/
theorem gram_eq (v : Fin 1 → ℝ) :
    gram rowsE (barK (κ := Fin 1) Aset) v = gram rowsE (barK (κ := Fin 1) Rset) v := by
  rw [gram_A, gram_R]

/-- Первый момент `A` в узле: `(20+3δ)·v`. -/
lemma mom_A (δ : ℝ) (v : Fin 1 → ℝ) :
    mom rowsE (tgtsE δ) (barK (κ := Fin 1) Aset) node v = (20 + 3 * δ) * v 0 := by
  rw [mom, sum_barA]
  rw [dotp_inl, dotp_inl, dotp_inr, dotp_inl, dotp_inl, dotp_inr,
    tgt_inl, tgt_inl, tgt_inr, bco0, bco1, mex0, mex1]
  simp [node]
  ring

/-- Первый момент `R` в узле: тот же `(20+3δ)·v`. -/
lemma mom_R (δ : ℝ) (v : Fin 1 → ℝ) :
    mom rowsE (tgtsE δ) (barK (κ := Fin 1) Rset) node v = (20 + 3 * δ) * v 0 := by
  rw [mom, sum_barR]
  rw [dotp_inl, dotp_inl, dotp_inr, dotp_inl, dotp_inl, dotp_inr,
    tgt_inl, tgt_inl, tgt_inr, bco2, bco3, mex2, mex3]
  simp [node]
  ring

/-- **Первые моменты в узле совпадают** — вторая половина условия «сосед по корзине». -/
theorem mom_eq (δ : ℝ) (v : Fin 1 → ℝ) :
    mom rowsE (tgtsE δ) (barK (κ := Fin 1) Aset) node v
      = mom rowsE (tgtsE δ) (barK (κ := Fin 1) Rset) node v := by
  rw [mom_A, mom_R]

/-! ### Общая неподвижная точка -/

/-- `t̂ = (20+3δ)/26` — точка нормальных уравнений для `Ā`. -/
theorem normal_A (δ : ℝ) : IsNormal rowsE (tgtsE δ) (barK (κ := Fin 1) Aset) (tfix δ) := by
  intro v
  rw [mom, sum_barA]
  rw [dotp_inl, dotp_inl, dotp_inr, dotp_inl, dotp_inl, dotp_inr,
    tgt_inl, tgt_inl, tgt_inr, bco0, bco1, mex0, mex1]
  simp only [tfix]
  ring

/-- Та же `t̂` — точка нормальных уравнений и для `R̄` (следствие совпадения
моментов и форм Грама, но здесь проверено прямым счётом). -/
theorem normal_R (δ : ℝ) : IsNormal rowsE (tgtsE δ) (barK (κ := Fin 1) Rset) (tfix δ) := by
  intro v
  rw [mom, sum_barR]
  rw [dotp_inl, dotp_inl, dotp_inr, dotp_inl, dotp_inl, dotp_inr,
    tgt_inl, tgt_inl, tgt_inr, bco2, bco3, mex2, mex3]
  simp only [tfix]
  ring

/-! ### Значения в узле и в неподвижной точке -/

lemma phi_A_node (δ : ℝ) :
    phi rowsE (tgtsE δ) (barK (κ := Fin 1) Aset) node = 4 + (20 + 3 * δ) ^ 2 / 25 := by
  rw [phi, sum_barA]
  rw [dotp_inl, dotp_inl, dotp_inr, tgt_inl, tgt_inl, tgt_inr, bco0, bco1, mex0, mex1]
  simp only [node]
  ring

lemma phi_R_node (δ : ℝ) :
    phi rowsE (tgtsE δ) (barK (κ := Fin 1) Rset) node = δ ^ 2 + 25 := by
  rw [phi, sum_barR]
  rw [dotp_inl, dotp_inl, dotp_inr, tgt_inl, tgt_inl, tgt_inr, bco2, bco3, mex2, mex3]
  simp only [node]
  ring

lemma phi_A_fix (δ : ℝ) :
    phi rowsE (tgtsE δ) (barK (κ := Fin 1) Aset) (tfix δ) = 4 + (20 + 3 * δ) ^ 2 / 650 := by
  rw [phi, sum_barA]
  rw [dotp_inl, dotp_inl, dotp_inr, tgt_inl, tgt_inl, tgt_inr, bco0, bco1, mex0, mex1]
  simp only [tfix]
  ring

/-- **`R` законно вытесняет `A`**: в узле у него не меньшее (при `δ < 5/4` — строго
большее) значение `Q`. -/
theorem Q_lt (δ : ℝ) (hδ1 : δ ≤ 1) :
    phi rowsE (tgtsE δ) (barK (κ := Fin 1) Aset) node
      < phi rowsE (tgtsE δ) (barK (κ := Fin 1) Rset) node := by
  rw [phi_A_node, phi_R_node]
  nlinarith [hδ1, sq_nonneg (δ - 1), sq_nonneg δ]

/-! ### Невязки -/

/-- Невязка актива `1` набора `A` в неподвижной точке: `(20+3δ)/130 > 0`. -/
lemma res_A1 (δ : ℝ) :
    tgtsE δ (Sum.inl 1) - dotp (rowsE (Sum.inl 1)) (tfix δ) = (20 + 3 * δ) / 130 := by
  rw [tgt_inl, dotp_inl, bco1, mex1]
  simp only [tfix]
  ring

/-- Невязка актива `0` набора `A` в неподвижной точке: `2`. -/
lemma res_A0 (δ : ℝ) :
    tgtsE δ (Sum.inl 0) - dotp (rowsE (Sum.inl 0)) (tfix δ) = 2 := by
  rw [tgt_inl, dotp_inl, bco0, mex0]
  ring

/-- Невязка актива `2` набора `R` в неподвижной точке: `(17δ−60)/26 < 0` при `δ ≤ 1`. -/
lemma res_R2 (δ : ℝ) :
    tgtsE δ (Sum.inl 2) - dotp (rowsE (Sum.inl 2)) (tfix δ) = (17 * δ - 60) / 26 := by
  rw [tgt_inl, dotp_inl, bco2, mex2]
  simp only [tfix]
  ring

/-- **`A` самосогласовано**: обе невязки в `t̂` неотрицательны. -/
theorem selfcons_A (δ : ℝ) (hδ0 : 0 ≤ δ) :
    ∀ r ∈ barK (κ := Fin 1) Aset, clipE r →
      0 ≤ tgtsE δ r - dotp (rowsE r) (tfix δ) := by
  rintro (i | l) hr hc
  · have hi : i ∈ Aset := by simpa [barK, Finset.inl_mem_disjSum] using hr
    have : i = 0 ∨ i = 1 := by
      rw [Aset] at hi; simpa using hi
    rcases this with rfl | rfl
    · rw [res_A0]; norm_num
    · rw [res_A1]; linarith
  · simp [clipE] at hc

/-- **`R` самосогласованным не является**: актив `2` имеет отрицательную невязку. -/
theorem not_selfcons_R (δ : ℝ) (hδ1 : δ ≤ 1) :
    tgtsE δ (Sum.inl 2) - dotp (rowsE (Sum.inl 2)) (tfix δ) < 0 := by
  rw [res_R2]; linarith

/-- **Оба набора допущены в узле с запасом `ρ = δ`.** -/
theorem admitted (δ : ℝ) (hδ1 : δ ≤ 1) :
    (∀ r ∈ barK (κ := Fin 1) Aset, clipE r → δ ≤ tgtsE δ r - dotp (rowsE r) node)
    ∧ (∀ r ∈ barK (κ := Fin 1) Rset, clipE r → δ ≤ tgtsE δ r - dotp (rowsE r) node) := by
  constructor
  · rintro (i | l) hr hc
    · have hi : i ∈ Aset := by simpa [barK, Finset.inl_mem_disjSum] using hr
      have : i = 0 ∨ i = 1 := by rw [Aset] at hi; simpa using hi
      rcases this with rfl | rfl
      · rw [tgt_inl, dotp_inl, mex0]; simp [node]; linarith
      · rw [tgt_inl, dotp_inl, mex1]; simp [node]; linarith
    · simp [clipE] at hc
  · rintro (i | l) hr hc
    · have hi : i ∈ Rset := by simpa [barK, Finset.inl_mem_disjSum] using hr
      have : i = 2 ∨ i = 3 := by rw [Rset] at hi; simpa using hi
      rcases this with rfl | rfl
      · rw [tgt_inl, dotp_inl, mex2]; simp [node]
      · rw [tgt_inl, dotp_inl, mex3]; simp [node]; linarith
    · simp [clipE] at hc

/-- **Зазор больше `ρ²`** — узел далёк от неподвижной точки. -/
theorem gap_gt (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    δ ^ 2 < phi rowsE (tgtsE δ) (barK (κ := Fin 1) Aset) node
              - phi rowsE (tgtsE δ) (barK (κ := Fin 1) Aset) (tfix δ) := by
  rw [phi_A_node, phi_A_fix]
  nlinarith [hδ0, hδ1]

/-! ### Значения long-only -/

/-- **`F_LO(A) = 4 + (20+3δ)²/650`** — минимум зажатой `psiC` на `Ā`. -/
theorem isLeast_LO_A (δ : ℝ) (hδ0 : 0 ≤ δ) :
    IsLeast {v : ℝ | ∃ t, v = psiC rowsE (tgtsE δ) clipE (barK (κ := Fin 1) Aset) t}
      (4 + (20 + 3 * δ) ^ 2 / 650) := by
  have h := isLeast_psiC_of_selfconsistent (cl := clipE) (normal_A δ) (selfcons_A δ hδ0)
  rwa [phi_A_fix] at h

/-- Значение зажатой функции на `R̄` в явном виде. -/
lemma psiC_R (δ : ℝ) (t : Fin 1 → ℝ) :
    psiC rowsE (tgtsE δ) clipE (barK (κ := Fin 1) Rset) t
      = max (δ - 3 * t 0) 0 ^ 2 + max (5 - 4 * t 0) 0 ^ 2 + (t 0) ^ 2 := by
  rw [psiC, sum_barR]
  have h2 : resC rowsE (tgtsE δ) clipE (Sum.inl 2) t = max (δ - 3 * t 0) 0 := by
    simp only [resC, clipE, Sum.isLeft_inl, ite_true]
    rw [tgt_inl, dotp_inl, bco2, mex2]
  have h3 : resC rowsE (tgtsE δ) clipE (Sum.inl 3) t = max (5 - 4 * t 0) 0 := by
    simp only [resC, clipE, Sum.isLeft_inl, ite_true]
    rw [tgt_inl, dotp_inl, bco3, mex3]
  have h4 : resC rowsE (tgtsE δ) clipE (Sum.inr 0) t = - t 0 := by
    simp only [resC, clipE, Sum.isLeft_inr, ite_false, Bool.false_eq_true]
    rw [tgt_inr, dotp_inr]; ring
  rw [h2, h3, h4]
  ring

/-- **`F_LO(R) = 25/17` ровно**: минимум достигается на `t = 20/17`, где актив `2`
выпадает из портфеля целиком. -/
theorem isLeast_LO_R (δ : ℝ) (hδ1 : δ ≤ 1) :
    IsLeast {v : ℝ | ∃ t, v = psiC rowsE (tgtsE δ) clipE (barK (κ := Fin 1) Rset) t}
      (25 / 17) := by
  constructor
  · refine ⟨fun _ => 20 / 17, ?_⟩
    rw [psiC_R]
    have h1 : max (δ - 3 * (20 / 17 : ℝ)) 0 = 0 := max_eq_right (by linarith)
    have h2 : max (5 - 4 * (20 / 17 : ℝ)) 0 = 5 - 4 * (20 / 17 : ℝ) :=
      max_eq_left (by norm_num)
    rw [h1, h2]
    norm_num
  · rintro v ⟨t, rfl⟩
    rw [psiC_R]
    have hpos : (0:ℝ) ≤ max (δ - 3 * t 0) 0 ^ 2 := sq_nonneg _
    rcases le_or_gt (5 - 4 * t 0) 0 with h | h
    · have hz : max (5 - 4 * t 0) 0 = 0 := max_eq_right h
      have ht : (5:ℝ) / 4 ≤ t 0 := by linarith
      rw [hz]
      nlinarith
    · have hz : max (5 - 4 * t 0) 0 = 5 - 4 * t 0 := max_eq_left h.le
      rw [hz]
      nlinarith [sq_nonneg (17 * t 0 - 20)]

/-! ### Итог -/

/-- **Потеря от вытеснения не меньше `695/221 > 3` при любом `δ ∈ (0,1]`.** -/
theorem loss_ge (δ : ℝ) (hδ0 : 0 ≤ δ) :
    (695 : ℝ) / 221 ≤ (4 + (20 + 3 * δ) ^ 2 / 650) - 25 / 17 := by
  nlinarith [hδ0]

/-- **Ответ на вопрос §13.5 — отрицательный, с правильными кванторами.**

Для **любого** множителя `p` (роль `poly(k,K)`) найдётся инстанс с `K = 1`, `k = 2`
и параметром `δ`, в котором выполнены все гипотезы вопроса:

* `A` самосогласовано (`selfcons_A`) и допущено в узле с запасом `ρ = δ`;
* `R` допущен в том же узле, имеет тот же `gram`, тот же `mom` и большее `Q`;
* зазор `γ²` больше `ρ²`;

и при этом `F_LO(A) − F_LO(R) > p·ρ²`. -/
theorem eviction_far_node (p : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1
      ∧ (∀ v, gram rowsE (barK (κ := Fin 1) Aset) v
                = gram rowsE (barK (κ := Fin 1) Rset) v)
      ∧ (∀ v, mom rowsE (tgtsE δ) (barK (κ := Fin 1) Aset) node v
                = mom rowsE (tgtsE δ) (barK (κ := Fin 1) Rset) node v)
      ∧ phi rowsE (tgtsE δ) (barK (κ := Fin 1) Aset) node
          < phi rowsE (tgtsE δ) (barK (κ := Fin 1) Rset) node
      ∧ IsNormal rowsE (tgtsE δ) (barK (κ := Fin 1) Aset) (tfix δ)
      ∧ IsNormal rowsE (tgtsE δ) (barK (κ := Fin 1) Rset) (tfix δ)
      ∧ (∀ r ∈ barK (κ := Fin 1) Aset, clipE r →
            0 ≤ tgtsE δ r - dotp (rowsE r) (tfix δ))
      ∧ (∀ r ∈ barK (κ := Fin 1) Aset, clipE r → δ ≤ tgtsE δ r - dotp (rowsE r) node)
      ∧ (∀ r ∈ barK (κ := Fin 1) Rset, clipE r → δ ≤ tgtsE δ r - dotp (rowsE r) node)
      ∧ δ ^ 2 < phi rowsE (tgtsE δ) (barK (κ := Fin 1) Aset) node
                  - phi rowsE (tgtsE δ) (barK (κ := Fin 1) Aset) (tfix δ)
      ∧ IsLeast {v : ℝ | ∃ t, v = psiC rowsE (tgtsE δ) clipE (barK (κ := Fin 1) Aset) t}
            (4 + (20 + 3 * δ) ^ 2 / 650)
      ∧ IsLeast {v : ℝ | ∃ t, v = psiC rowsE (tgtsE δ) clipE (barK (κ := Fin 1) Rset) t}
            (25 / 17)
      ∧ p * δ ^ 2 < (4 + (20 + 3 * δ) ^ 2 / 650) - 25 / 17 := by
  have hden : (0:ℝ) < |p| + 1 := by positivity
  refine ⟨min 1 (1 / (|p| + 1)), ?_, min_le_left _ _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min one_pos (by positivity)
  all_goals set δ : ℝ := min 1 (1 / (|p| + 1)) with hδdef
  all_goals have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  all_goals have hδ1 : δ ≤ 1 := min_le_left _ _
  · exact gram_eq
  · exact mom_eq δ
  · exact Q_lt δ hδ1
  · exact normal_A δ
  · exact normal_R δ
  · exact selfcons_A δ hδ0.le
  · exact (admitted δ hδ1).1
  · exact (admitted δ hδ1).2
  · exact gap_gt δ hδ0 hδ1
  · exact isLeast_LO_A δ hδ0.le
  · exact isLeast_LO_R δ hδ1
  · -- `p·δ² ≤ |p|/(|p|+1) < 1 < 695/221 ≤ потеря`
    have hδle : δ ≤ 1 / (|p| + 1) := min_le_right _ _
    have hple : p ≤ |p| := le_abs_self p
    have hkey : p * δ ^ 2 ≤ |p| / (|p| + 1) := by
      have hsqle : δ ^ 2 ≤ δ := by nlinarith [hδ0, hδ1]
      have h1 : δ ^ 2 ≤ 1 / (|p| + 1) := le_trans hsqle hδle
      have hstep1 : p * δ ^ 2 ≤ |p| * δ ^ 2 :=
        mul_le_mul_of_nonneg_right hple (sq_nonneg δ)
      have hstep2 : |p| * δ ^ 2 ≤ |p| * (1 / (|p| + 1)) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg p)
      have hid : |p| * (1 / (|p| + 1)) = |p| / (|p| + 1) := by ring
      linarith [hstep1, hstep2, hid.le, hid.ge]
    have hlt1 : |p| / (|p| + 1) < 1 := by
      rw [div_lt_one hden]; linarith
    have := loss_ge δ hδ0.le
    linarith

end Ex135
end SparseSharpe.Factor
