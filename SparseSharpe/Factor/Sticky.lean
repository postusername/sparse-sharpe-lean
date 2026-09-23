import SparseSharpe.Factor.KBridge
import SparseSharpe.Factor.ActiveFilter

set_option linter.style.header false

/-!
# Одной Теоремы U мало: остаток §4.3 существен

Теорема U (`Factor/ActiveFilter.lean`) говорит: если динамика допускает актив
**по знаку невязки в неподвижной точке** `t̂`, то всякий **точный** сосед по
корзине самосогласован по построению, и вытеснение из корзины безвредно.

Алгоритм, однако, точку `t̂` не знает и ставит фильтр в узле сетки `τ ≈ t̂`.
Этот файл показывает, что разницы между `t̂` и `τ` уже достаточно, чтобы
вытеснение стоило почти всего значения.

Инстанс (`theory_note_v6.md`, §4.4): `K = 1`, `k = 2`, четыре актива,
`d ≡ 1`, `Σ_f = N⁴` (якорная строка `1/N²`), параметр `N ≥ 3`,
`C = (N²−1)/(N²+1)`, `S = 2N/(N²+1)` (так что `C² + S² = 1`):

    нагрузки  B = (1, 0, C, S),   альфы  m = (1, 1, C−S, S+C),
    A* = {0, 1},    R = {2, 3},    t̂ = N⁴/(N⁴+1),    τ = (C−S)/C.

Доказано:

* `gram_eq`, `mom_eq`, `Q_eq` — `R` лежит в одной корзине с `A*` (формы Грама
  равны, первые моменты в узле `0` равны, значения `Q` равны). Заметим, что
  `Q` равны **точно**: ключ `(Q̃, M̃, Κ̃)` эти два набора не различает, и
  динамика, хранящая набор с максимальным `Q`, вправе оставить любой из них;
* `normal_A`, `normal_R` — у обоих одна и та же неподвижная точка `t̂`;
* `selfcons_A` — `A*` самосогласован; `not_selfcons_R` — `R` нет
  (невязка актива `2` в `t̂` отрицательна);
* `admitted_sign` — **оба набора проходят фильтр по знаку в `τ`**
  (у актива `2` невязка в `τ` равна ровно нулю, у остальных положительна);
* `isLeast_LO_A`, `isLeast_LO_R` — значения long-only (минимумы зажатой `psiC`):
  `F_LO(A*) = 1 + 1/(N⁴+1) ≥ 1`, а `F_LO(R) = (S+C)²/(N⁴S²+1) = O(1/N²)`;
* `gap_eq` — точный зазор узла;
* **`sticky_row_essential`** — итог с правильными кванторами: для любого `ε > 0`
  найдётся такой инстанс, в котором зазор узла не больше `ε·F_LO(A*)`, и
  всё-таки `F_LO(R) ≤ ε·F_LO(A*)`.

**Чего здесь нет.** Не формализовано (проверено только счётом, см. заметку,
§4.4): что плечо нарушающей строки равно `C²/(1+1/N⁴)`, то есть стремится к
единице при `N → ∞`. Именно это объясняет, *почему* общей оценки цены
выбрасывания `r²/(1−h)` не хватает, но само по себе для опровержения не нужно.
Также не утверждается, что инстанс ломает алгоритм: при **ближайшем** к `t̂`
узле (`τ = 1`) нарушающая строка не допущена, и алгоритм точен (заметка, §4.4).
-/

namespace SparseSharpe.Factor
namespace Sticky

open Finset

/-- Обратная факторная ковариация. -/
noncomputable def Pex (N : ℝ) : Fin 1 → Fin 1 → ℝ := fun _ _ => 1 / N^4
/-- Корень обратной ковариации, используемый как якорная строка. -/
noncomputable def Gex (N : ℝ) : Fin 1 → Fin 1 → ℝ := fun _ _ => 1 / N^2
/-- Косинусная координата. -/
noncomputable def C (N : ℝ) : ℝ := (N^2 - 1) / (N^2 + 1)
/-- Синусная координата. -/
noncomputable def S (N : ℝ) : ℝ := 2*N / (N^2 + 1)

/-- Нагрузки четырёх активов: `(1,0,C,S)`. -/
noncomputable def bco (N : ℝ) : Fin 4 → ℝ :=
  fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then C N else S N
/-- Нагрузка как `K`-вектор. -/
noncomputable def Bex (N : ℝ) : Fin 4 → Fin 1 → ℝ := fun i _ => bco N i
/-- Идиосинкразия `d ≡ 1`. -/
def dex : Fin 4 → ℝ := fun _ => 1
/-- Альфы `(1,1,C-S,S+C)`. -/
noncomputable def mex (N : ℝ) : Fin 4 → ℝ :=
  fun i => if i = 0 then 1 else if i = 1 then 1 else if i = 2 then C N - S N else S N + C N

/-- Носитель нормального решения. -/
def Aset : Finset (Fin 4) := {0, 1}
/-- Его сосед по корзине. -/
def Rset : Finset (Fin 4) := {2, 3}
/-- Строки least-squares задачи. -/
noncomputable def rowsE (N : ℝ) : (Fin 4 ⊕ Fin 1) → Fin 1 → ℝ := rowsK dex (Bex N) (Gex N)
/-- Правые части. -/
noncomputable def tgtsE (N : ℝ) : (Fin 4 ⊕ Fin 1) → ℝ := targetsK (mex N) dex
/-- Зажимаются только активные строки. -/
def clipE : (Fin 4 ⊕ Fin 1) → Bool := fun r => r.isLeft
/-- Узел корзины. -/
def node : Fin 1 → ℝ := fun _ => 0
/-- Общая неподвижная точка. -/
noncomputable def tfix (N : ℝ) : Fin 1 → ℝ := fun _ => N^4 / (N^4 + 1)
/-- Точка фильтра по знаку. -/
noncomputable def tau (N : ℝ) : Fin 1 → ℝ := fun _ => (C N - S N) / C N

lemma hNpos {N : ℝ} (hN : 3 ≤ N) : 0 < N := by linarith
lemma hN2p {N : ℝ} (hN : 3 ≤ N) : 0 < N^2 + 1 := by positivity
lemma hN4p {N : ℝ} (hN : 3 ≤ N) : 0 < N^4 + 1 := by positivity
lemma C_pos {N : ℝ} (hN : 3 ≤ N) : 0 < C N := by
  rw [C]; apply div_pos <;> nlinarith [sq_nonneg (N-1)]
lemma S_pos {N : ℝ} (hN : 3 ≤ N) : 0 < S N := by
  rw [S]; apply div_pos <;> nlinarith
lemma CS_sq {N : ℝ} (hN : 3 ≤ N) : C N ^ 2 + S N ^ 2 = 1 := by
  rw [C, S]
  have hp : N^2 + 1 ≠ 0 := ne_of_gt (hN2p hN)
  field_simp
  ring

lemma bco0 (N) : bco N 0 = 1 := by simp [bco]
lemma bco1 (N) : bco N 1 = 0 := by simp [bco]
lemma bco2 (N) : bco N 2 = C N := by simp [bco]
lemma bco3 (N) : bco N 3 = S N := by simp [bco]
lemma mex0 (N) : mex N 0 = 1 := by simp [mex]
lemma mex1 (N) : mex N 1 = 1 := by simp [mex]
lemma mex2 (N) : mex N 2 = C N - S N := by simp [mex]
lemma mex3 (N) : mex N 3 = S N + C N := by simp [mex]
lemma dotp1 (a t : Fin 1 → ℝ) : dotp a t = a 0 * t 0 := by simp [dotp]
lemma dotp_inl (N : ℝ) (i : Fin 4) (t : Fin 1 → ℝ) :
    dotp (rowsE N (Sum.inl i)) t = bco N i * t 0 := by
  rw [dotp1]; simp [rowsE, rowsK, Bex, dex]
lemma dotp_inr (N : ℝ) (l : Fin 1) (t : Fin 1 → ℝ) :
    dotp (rowsE N (Sum.inr l)) t = (1/N^2) * t 0 := by
  rw [dotp1]; simp [rowsE, rowsK, Gex]
lemma tgt_inl (N : ℝ) (i : Fin 4) : tgtsE N (Sum.inl i) = mex N i := by simp [tgtsE, targetsK, dex]
lemma tgt_inr (N : ℝ) (l : Fin 1) : tgtsE N (Sum.inr l) = 0 := by simp [tgtsE, targetsK]

lemma sum_barA (f : (Fin 4 ⊕ Fin 1) → ℝ) :
    ∑ r ∈ barK (κ := Fin 1) Aset, f r = f (Sum.inl 0) + f (Sum.inl 1) + f (Sum.inr 0) := by
  rw [barK, Finset.sum_disjSum]
  have h : ∑ i ∈ Aset, f (Sum.inl i) = f (Sum.inl 0) + f (Sum.inl 1) := by rw [Aset]; exact Finset.sum_pair (by decide)
  rw [h, Fin.sum_univ_one]
lemma sum_barR (f : (Fin 4 ⊕ Fin 1) → ℝ) :
    ∑ r ∈ barK (κ := Fin 1) Rset, f r = f (Sum.inl 2) + f (Sum.inl 3) + f (Sum.inr 0) := by
  rw [barK, Finset.sum_disjSum]
  have h : ∑ i ∈ Rset, f (Sum.inl i) = f (Sum.inl 2) + f (Sum.inl 3) := by rw [Rset]; exact Finset.sum_pair (by decide)
  rw [h, Fin.sum_univ_one]

lemma gram_A (N : ℝ) (v : Fin 1 → ℝ) : gram (rowsE N) (barK Aset) v = (1+1/N^4) * (v 0)^2 := by
  rw [gram, sum_barA, dotp_inl, dotp_inl, dotp_inr, bco0, bco1]; ring
lemma gram_R (N : ℝ) (hN : 3 ≤ N) (v : Fin 1 → ℝ) : gram (rowsE N) (barK Rset) v = (1+1/N^4) * (v 0)^2 := by
  rw [gram, sum_barR, dotp_inl, dotp_inl, dotp_inr, bco2, bco3]
  calc
    (C N * v 0)^2 + (S N * v 0)^2 + ((1 / N^2) * v 0)^2 =
        (C N^2 + S N^2 + 1/N^4) * (v 0)^2 := by ring
    _ = (1+1/N^4) * (v 0)^2 := by rw [CS_sq hN]

/-- Формы Грама двух корзин совпадают. -/
theorem gram_eq (N : ℝ) (hN : 3 ≤ N) (v : Fin 1 → ℝ) :
    gram (rowsE N) (barK Aset) v = gram (rowsE N) (barK Rset) v := by rw [gram_A, gram_R N hN]

lemma mom_A (N : ℝ) (v : Fin 1 → ℝ) : mom (rowsE N) (tgtsE N) (barK Aset) node v = v 0 := by
  rw [mom, sum_barA]
  rw [dotp_inl, dotp_inl, dotp_inr, dotp_inl, dotp_inl, dotp_inr, tgt_inl, tgt_inl, tgt_inr, bco0, bco1, mex0, mex1]
  simp [node]
lemma mom_R (N : ℝ) (hN : 3 ≤ N) (v : Fin 1 → ℝ) : mom (rowsE N) (tgtsE N) (barK Rset) node v = v 0 := by
  rw [mom, sum_barR]
  rw [dotp_inl, dotp_inl, dotp_inr, dotp_inl, dotp_inl, dotp_inr, tgt_inl, tgt_inl, tgt_inr, bco2, bco3, mex2, mex3]
  simp [node]
  calc
    (C N - S N) * (C N * v 0) + (S N + C N) * (S N * v 0) =
        (C N^2 + S N^2) * v 0 := by ring
    _ = v 0 := by rw [CS_sq hN]; ring
/-- Первые моменты в нулевом узле совпадают. -/
theorem mom_eq (N : ℝ) (hN : 3 ≤ N) (v : Fin 1 → ℝ) :
    mom (rowsE N) (tgtsE N) (barK Aset) node v = mom (rowsE N) (tgtsE N) (barK Rset) node v := by rw [mom_A, mom_R N hN]

lemma phi_A_node (N : ℝ) : phi (rowsE N) (tgtsE N) (barK Aset) node = 2 := by
  rw [phi, sum_barA]; rw [dotp_inl, dotp_inl, dotp_inr, tgt_inl, tgt_inl, tgt_inr, bco0, bco1, mex0, mex1]; norm_num [node]
lemma phi_R_node (N : ℝ) (hN : 3 ≤ N) : phi (rowsE N) (tgtsE N) (barK Rset) node = 2 := by
  rw [phi, sum_barR]; rw [dotp_inl, dotp_inl, dotp_inr, tgt_inl, tgt_inl, tgt_inr, bco2, bco3, mex2, mex3]; simp [node]
  calc
    (S N - C N)^2 + (-C N-S N)^2 = 2 * (C N^2 + S N^2) := by ring
    _ = 2 := by rw [CS_sq hN]; ring
/-- Значения `Q_0` равны. -/
theorem Q_eq (N : ℝ) (hN : 3 ≤ N) : phi (rowsE N) (tgtsE N) (barK Aset) node = phi (rowsE N) (tgtsE N) (barK Rset) node := by rw [phi_A_node, phi_R_node N hN]

/-- Нормальные уравнения для `A`. -/
theorem normal_A (N : ℝ) (hN : 3 ≤ N) : IsNormal (rowsE N) (tgtsE N) (barK Aset) (tfix N) := by
  intro v
  rw [mom, sum_barA]
  rw [dotp_inl, dotp_inl, dotp_inr, dotp_inl, dotp_inl, dotp_inr, tgt_inl, tgt_inl, tgt_inr, bco0, bco1, mex0, mex1]
  simp [tfix]
  have hn : N^4 + 1 ≠ 0 := ne_of_gt (hN4p hN)
  field_simp; ring
/-- Нормальные уравнения для `R`. -/
theorem normal_R (N : ℝ) (hN : 3 ≤ N) : IsNormal (rowsE N) (tgtsE N) (barK Rset) (tfix N) := by
  exact isNormal_of_bucket (S := barK Aset) (R := barK Rset)
    (fun v => (mom_eq N hN v).symm) (fun v => (gram_eq N hN v).symm) (normal_A N hN)

lemma res_A0 (N : ℝ) : tgtsE N (Sum.inl 0) - dotp (rowsE N (Sum.inl 0)) (tfix N) = 1/(N^4+1) := by
  rw [tgt_inl, dotp_inl, bco0, mex0]; simp [tfix]
  have hp : N^4+1 ≠ 0 := by positivity
  field_simp; ring
lemma res_A1 (N : ℝ) : tgtsE N (Sum.inl 1) - dotp (rowsE N (Sum.inl 1)) (tfix N) = 1 := by rw [tgt_inl, dotp_inl, bco1, mex1]; ring
lemma res_R2 (N : ℝ) : tgtsE N (Sum.inl 2) - dotp (rowsE N (Sum.inl 2)) (tfix N) = C N/(N^4+1)-S N := by
  rw [tgt_inl, dotp_inl, bco2, mex2]; simp [tfix]
  have hp : N^4+1 ≠ 0 := by positivity
  field_simp; ring

/-- `A` самосогласован в неподвижной точке. -/
theorem selfcons_A (N : ℝ) (hN : 3 ≤ N) : ∀ r ∈ barK (κ := Fin 1) Aset, clipE r → 0 ≤ tgtsE N r - dotp (rowsE N r) (tfix N) := by
  rintro (i|l) hr hc
  · have hi : i ∈ Aset := by simpa [barK, Finset.inl_mem_disjSum] using hr
    have h : i=0 ∨ i=1 := by rw [Aset] at hi; simpa using hi
    rcases h with rfl|rfl
    · rw [res_A0]; exact (one_div_nonneg.mpr (hN4p hN).le)
    · rw [res_A1]; norm_num
  · simp [clipE] at hc
/-- У `R` актив `2` имеет отрицательную невязку. -/
theorem not_selfcons_R (N : ℝ) (hN : 3 ≤ N) : tgtsE N (Sum.inl 2) - dotp (rowsE N (Sum.inl 2)) (tfix N) < 0 := by
  rw [res_R2]
  have hp := hN4p hN
  have hc := C_pos hN
  have hs := S_pos hN
  apply sub_neg.mpr
  rw [div_lt_iff₀ hp]
  rw [C, S]
  apply (div_lt_iff₀ (hN2p hN)).mpr
  have hid : (2*N/(N^2+1)) * (N^4+1) * (N^2+1) = 2*N*(N^4+1) := by
    field_simp
  rw [hid]
  have hbig : N^2 ≤ N^4 := by nlinarith [sq_nonneg (N^2-1)]
  nlinarith

lemma res_tau_A0 (N : ℝ) (hN : 3 ≤ N) :
    tgtsE N (Sum.inl 0) - dotp (rowsE N (Sum.inl 0)) (tau N) = S N / C N := by
  rw [tgt_inl, dotp_inl, bco0, mex0]
  simp [tau]
  field_simp [ne_of_gt (C_pos hN)]
  ring
lemma res_tau_A1 (N : ℝ) :
    tgtsE N (Sum.inl 1) - dotp (rowsE N (Sum.inl 1)) (tau N) = 1 := by
  rw [tgt_inl, dotp_inl, bco1, mex1]; ring
lemma res_tau_R2 (N : ℝ) (hN : 3 ≤ N) :
    tgtsE N (Sum.inl 2) - dotp (rowsE N (Sum.inl 2)) (tau N) = 0 := by
  rw [tgt_inl, dotp_inl, bco2, mex2]
  simp [tau]
  field_simp [ne_of_gt (C_pos hN)]
  ring
lemma res_tau_R3 (N : ℝ) (hN : 3 ≤ N) :
    tgtsE N (Sum.inl 3) - dotp (rowsE N (Sum.inl 3)) (tau N) = 1 / C N := by
  rw [tgt_inl, dotp_inl, bco3, mex3]
  simp [tau]
  have hc := CS_sq hN
  field_simp [ne_of_gt (C_pos hN)]
  nlinarith

/-- Оба набора проходят фильтр по знаку в точке `τ`. -/
theorem admitted_sign (N : ℝ) (hN : 3 ≤ N) :
    (∀ r ∈ barK (κ := Fin 1) Aset, clipE r → 0 ≤ tgtsE N r - dotp (rowsE N r) (tau N))
    ∧ (∀ r ∈ barK (κ := Fin 1) Rset, clipE r → 0 ≤ tgtsE N r - dotp (rowsE N r) (tau N)) := by
  constructor
  · rintro (i|l) hr hc
    · have hi : i ∈ Aset := by simpa [barK, Finset.inl_mem_disjSum] using hr
      have h : i=0 ∨ i=1 := by rw [Aset] at hi; simpa using hi
      rcases h with rfl|rfl
      · rw [res_tau_A0 N hN]; exact div_nonneg (S_pos hN).le (C_pos hN).le
      · rw [res_tau_A1]; norm_num
    · simp [clipE] at hc
  · rintro (i|l) hr hc
    · have hi : i ∈ Rset := by simpa [barK, Finset.inl_mem_disjSum] using hr
      have h : i=2 ∨ i=3 := by rw [Rset] at hi; simpa using hi
      rcases h with rfl|rfl
      · rw [res_tau_R2 N hN]
      · rw [res_tau_R3 N hN]; exact one_div_nonneg.mpr (C_pos hN).le
    · simp [clipE] at hc

lemma phi_A_fix (N : ℝ) (hN : 3 ≤ N) :
    phi (rowsE N) (tgtsE N) (barK Aset) (tfix N) = 1 + 1/(N^4+1) := by
  rw [phi, sum_barA]
  rw [dotp_inl, dotp_inl, dotp_inr, tgt_inl, tgt_inl, tgt_inr, bco0, bco1, mex0, mex1]
  simp [tfix]
  have hn : N^4+1 ≠ 0 := ne_of_gt (hN4p hN)
  field_simp
  ring

/-- Минимум `psiC` на самосогласованном наборе `A`. -/
theorem isLeast_LO_A (N : ℝ) (hN : 3 ≤ N) :
    IsLeast {v : ℝ | ∃ t, v = psiC (rowsE N) (tgtsE N) clipE (barK Aset) t}
      (1 + 1/(N^4+1)) := by
  have h := isLeast_psiC_of_selfconsistent (cl := clipE) (normal_A N hN) (selfcons_A N hN)
  rwa [phi_A_fix N hN] at h

/-- Точный зазор между фильтрующей точкой и неподвижной точкой. -/
theorem gap_eq (N : ℝ) (hN : 3 ≤ N) :
    phi (rowsE N) (tgtsE N) (barK Aset) (tau N) -
      phi (rowsE N) (tgtsE N) (barK Aset) (tfix N) =
    (1 + 1/N^4) * (S N / C N - 1/(N^4+1))^2 := by
  rw [phi, phi, sum_barA, sum_barA]
  rw [dotp_inl, dotp_inl, dotp_inr, tgt_inl, tgt_inl, tgt_inr, bco0, bco1, mex0, mex1]
  rw [dotp_inl, dotp_inl, dotp_inr, bco0, bco1]
  simp [tau, tfix]
  have hc : C N ≠ 0 := ne_of_gt (C_pos hN)
  have hn : N^4+1 ≠ 0 := ne_of_gt (hN4p hN)
  field_simp
  ring

/-! ### Значение long-only у вытеснившего набора -/

/-- Скалярное ядро: минимум `(a − b·x)_+² + (g·x)²` равен `g²a²/(b²+g²)`. -/
lemma min_quad_posPart {a b g : ℝ} (ha : 0 < a) (hb : 0 < b) (hg : 0 < g) (x : ℝ) :
    g^2*a^2/(b^2+g^2) ≤ max (a - b*x) 0 ^2 + (g*x)^2 := by
  have hD : (0:ℝ) < b^2 + g^2 := by positivity
  rcases le_or_gt 0 (a - b*x) with h | h
  · rw [max_eq_left h]
    have hid : (a - b*x)^2 + (g*x)^2
        = g^2*a^2/(b^2+g^2) + (b^2+g^2)*(x - a*b/(b^2+g^2))^2 := by
      field_simp
      ring
    rw [hid]
    nlinarith [sq_nonneg (x - a*b/(b^2+g^2)), hD]
  · rw [max_eq_right h.le]
    have hx : a/b < x := by rw [div_lt_iff₀ hb]; linarith
    have hxpos : (0:ℝ) < a/b := by positivity
    have hx2 : (a/b)^2 < x^2 := by nlinarith
    have he : (a/b)^2 * b^2 = a^2 := by field_simp
    have h1 : g^2*a^2/(b^2+g^2) ≤ g^2*(a/b)^2 := by
      rw [div_le_iff₀ hD]
      have hexp : g^2*(a/b)^2*(b^2+g^2) = g^2*((a/b)^2*b^2) + g^2*(a/b)^2*g^2 := by ring
      rw [hexp, he]
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg g) (sq_nonneg (a/b))) (sq_nonneg g)]
    nlinarith [h1, hx2, hg, sq_nonneg g]

/-- В точке `x₀ = ab/(b²+g²)` этот минимум достигается. -/
lemma attain_quad_posPart {a b g : ℝ} (ha : 0 < a) (hb : 0 < b) (hg : 0 < g) :
    max (a - b*(a*b/(b^2+g^2))) 0 ^2 + (g*(a*b/(b^2+g^2)))^2 = g^2*a^2/(b^2+g^2) := by
  have hD : (0:ℝ) < b^2 + g^2 := by positivity
  have hval : a - b*(a*b/(b^2+g^2)) = a*g^2/(b^2+g^2) := by
    field_simp
    ring
  rw [hval, max_eq_left (by positivity)]
  field_simp
  ring

/-- Зажатое значение на `R̄` в явном виде. -/
lemma psiC_R (N : ℝ) (t : Fin 1 → ℝ) :
    psiC (rowsE N) (tgtsE N) clipE (barK (κ := Fin 1) Rset) t
      = max (C N - S N - C N * t 0) 0 ^ 2
        + (max (S N + C N - S N * t 0) 0 ^ 2 + (1/N^2 * t 0) ^ 2) := by
  rw [psiC, sum_barR]
  have h2 : resC (rowsE N) (tgtsE N) clipE (Sum.inl 2) t
      = max (C N - S N - C N * t 0) 0 := by
    simp only [resC, clipE, Sum.isLeft_inl, ite_true]
    rw [tgt_inl, dotp_inl, bco2, mex2]
  have h3 : resC (rowsE N) (tgtsE N) clipE (Sum.inl 3) t
      = max (S N + C N - S N * t 0) 0 := by
    simp only [resC, clipE, Sum.isLeft_inl, ite_true]
    rw [tgt_inl, dotp_inl, bco3, mex3]
  have h4 : resC (rowsE N) (tgtsE N) clipE (Sum.inr 0) t = -(1/N^2 * t 0) := by
    simp only [resC, clipE, Sum.isLeft_inr, ite_false, Bool.false_eq_true]
    rw [tgt_inr, dotp_inr]; ring
  rw [h2, h3, h4]; ring

/-- Произведение координат не меньше якорного веса: `1/N⁴ ≤ S·C`. Отсюда точка
минимума `t₀` не меньше единицы, а значит и не меньше `τ`. -/
lemma SC_ge (N : ℝ) (hN : 3 ≤ N) : 1/N^4 ≤ S N * C N := by
  have hN0 : (0:ℝ) < N := by linarith
  have h1 : (0:ℝ) < (N^2 + 1)^2 := by positivity
  have h2 : (0:ℝ) < N^4 := by positivity
  have hne : (N^2 + 1) ≠ 0 := by positivity
  have hSC : S N * C N = 2*N*(N^2-1)/(N^2+1)^2 := by
    simp only [S, C]
    field_simp
  rw [hSC, div_le_div_iff₀ h2 h1]
  have hN2 : (9:ℝ) ≤ N^2 := by nlinarith [hN, hN0]
  have ha : (N^2+1)^2 ≤ 4*N^4 := by nlinarith [hN2, sq_nonneg (N^2 - 1)]
  have hc4 : (4:ℝ) ≤ 2*N*(N^2-1) := by nlinarith [hN, hN0]
  have hb : 4*N^4 ≤ 2*N*(N^2-1)*N^4 :=
    mul_le_mul_of_nonneg_right hc4 (le_of_lt (pow_pos hN0 4))
  linarith

/-- Целевое значение в форме «ядра». -/
lemma flor_eq (N : ℝ) (hN : 3 ≤ N) :
    (S N + C N)^2 / (N^4 * S N^2 + 1)
      = (1/N^2)^2*(S N + C N)^2/(S N^2 + (1/N^2)^2) := by
  have hN0 : (0:ℝ) < N := by linarith
  have hne : (N:ℝ) ≠ 0 := ne_of_gt hN0
  have hden : (0:ℝ) < N^4 * S N^2 + 1 := by positivity
  have hden2 : (0:ℝ) < S N^2 + (1/N^2)^2 := by positivity
  rw [div_eq_div_iff (ne_of_gt hden) (ne_of_gt hden2)]
  field_simp
  try ring

/-- **Минимум `psiC` на `R̄`.** Он равен `(S+C)²/(N⁴S²+1)` и достигается в точке
`t₀ = S(S+C)/(S² + 1/N⁴)`, где нарушающая строка обрезается в ноль — то есть
вытеснивший набор теряет её вклад целиком. -/
theorem isLeast_LO_R (N : ℝ) (hN : 3 ≤ N) :
    IsLeast {v : ℝ | ∃ t, v = psiC (rowsE N) (tgtsE N) clipE (barK (κ := Fin 1) Rset) t}
      ((S N + C N)^2 / (N^4 * S N^2 + 1)) := by
  have hN0 : (0:ℝ) < N := by linarith
  have hs := S_pos hN
  have hc := C_pos hN
  have hg0 : (0:ℝ) < 1/N^2 := by positivity
  have hsum : (0:ℝ) < S N + C N := by linarith
  have hD : (0:ℝ) < S N^2 + (1/N^2)^2 := by positivity
  have hgsq : (1/N^2)^2 = 1/N^4 := by field_simp
  -- точка минимума
  have ht01 : (1:ℝ) ≤ (S N + C N) * S N / (S N^2 + (1/N^2)^2) := by
    rw [le_div_iff₀ hD, hgsq]
    nlinarith [SC_ge N hN, hs, hc]
  have e1 : max (C N - S N - C N * ((S N + C N) * S N / (S N^2 + (1/N^2)^2))) 0 = 0 := by
    refine max_eq_right ?_
    nlinarith [hc, hs, ht01]
  have e2 := attain_quad_posPart (a := S N + C N) (b := S N) (g := 1/N^2) hsum hs hg0
  constructor
  · refine ⟨fun _ => (S N + C N) * S N / (S N^2 + (1/N^2)^2), ?_⟩
    have hp := psiC_R N (fun _ : Fin 1 => (S N + C N) * S N / (S N^2 + (1/N^2)^2))
    rw [hp, flor_eq N hN, e1, e2]
    ring
  · rintro v ⟨t, rfl⟩
    rw [psiC_R, flor_eq N hN]
    have hkey := min_quad_posPart (a := S N + C N) (b := S N) (g := 1/N^2) hsum hs hg0 (t 0)
    linarith [hkey, sq_nonneg (max (C N - S N - C N * t 0) 0)]

/-! ### Оценки и итог -/

lemma S_div_C_le (N : ℝ) (hN : 3 ≤ N) : S N / C N ≤ 9/(4*N) := by
  have hN0 : (0:ℝ) < N := by linarith
  have hc := C_pos hN
  have h2 : (0:ℝ) < N^2 - 1 := by nlinarith
  have hne : (N^2 + 1) ≠ 0 := by positivity
  have hSC : S N / C N = 2*N/(N^2-1) := by
    simp only [S, C]
    field_simp
  rw [hSC, div_le_div_iff₀ h2 (by positivity)]
  nlinarith [hN, hN0]

lemma gap_le (N : ℝ) (hN : 3 ≤ N) :
    phi (rowsE N) (tgtsE N) (barK Aset) (tau N)
      - phi (rowsE N) (tgtsE N) (barK Aset) (tfix N) ≤ 11/N^2 := by
  have hN0 : (0:ℝ) < N := by linarith
  have hc := C_pos hN
  have hs := S_pos hN
  have hsc0 : (0:ℝ) ≤ S N / C N := div_nonneg hs.le hc.le
  have hN3 : (27:ℝ) ≤ N^3 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ N - 3)
      (by positivity : (0:ℝ) ≤ N^2 + 3*N + 9)]
  have hN4 : (81:ℝ) ≤ N^4 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ N - 3) (by linarith : (0:ℝ) ≤ N^3),
      hN3, hN, hN0]
  have hinv : 1/(N^4+1) ≤ 9/(4*N) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hN4, hN, hN0]
  have hinv0 : (0:ℝ) ≤ 1/(N^4+1) := by positivity
  have hup : S N / C N - 1/(N^4+1) ≤ 9/(4*N) := by linarith [S_div_C_le N hN]
  have hlo : -(9/(4*N)) ≤ S N / C N - 1/(N^4+1) := by linarith
  have hsq : (S N / C N - 1/(N^4+1))^2 ≤ (9/(4*N))^2 := sq_le_sq' hlo hup
  have hfac : 1 + 1/N^4 ≤ 2 := by
    have h : 1/N^4 ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [hN4]
    linarith
  rw [gap_eq N hN]
  have hnn : (0:ℝ) ≤ (S N / C N - 1/(N^4+1))^2 := sq_nonneg _
  have hpos : (0:ℝ) < 1 + 1/N^4 := by positivity
  have h1 : (1 + 1/N^4) * (S N / C N - 1/(N^4+1))^2 ≤ 2 * (9/(4*N))^2 := by
    nlinarith [hsq, hfac, hnn, hpos]
  have h2 : 2 * (9/(4*N))^2 ≤ 11/N^2 := by
    have hpos : (0:ℝ) < N^2 := by positivity
    have hexp : 2 * (9/(4*N))^2 = (81/8)/N^2 := by field_simp; ring
    rw [hexp, div_le_div_iff₀ hpos hpos]
    nlinarith [hpos]
  linarith

lemma FLOR_le (N : ℝ) (hN : 3 ≤ N) :
    (S N + C N)^2 / (N^4 * S N^2 + 1) ≤ 1/N^2 := by
  have hN0 : (0:ℝ) < N := by linarith
  have hne : (N^2 + 1) ≠ 0 := by positivity
  have hden : (0:ℝ) < N^4 * S N^2 + 1 := by positivity
  have hSC : (S N + C N)^2 = (N^2 + 2*N - 1)^2/(N^2+1)^2 := by
    simp only [S, C]
    field_simp
    ring
  have hD : N^4 * S N^2 + 1 = (4*N^6 + (N^2+1)^2)/(N^2+1)^2 := by
    simp only [S]
    field_simp
    ring
  have hkey : (N^2 + 2*N - 1)^2 * N^2 ≤ 4*N^6 + (N^2+1)^2 := by
    have e1 : (0:ℝ) ≤ (N - 3) * N^5 := mul_nonneg (by linarith) (le_of_lt (pow_pos hN0 5))
    have e2 : (0:ℝ) ≤ (5*N - 1) * N^4 := mul_nonneg (by linarith) (le_of_lt (pow_pos hN0 4))
    nlinarith [e1, e2, pow_pos hN0 3, pow_pos hN0 2, hN0]
  rw [div_le_div_iff₀ hden (by positivity : (0:ℝ) < N^2), hSC, hD, one_mul,
    div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < (N^2+1)^2)]
  exact hkey

/-- **Остаток §4.3 существен.** Для любого `ε > 0` найдётся инстанс, в котором
выполнены все гипотезы Теоремы U, кроме одной — точности узла: набор `R` —
точный сосед `A*` по корзине, оба **проходят фильтр по знаку** в точке `τ`,
зазор узла не больше `ε·F_LO(A*)`, и тем не менее `F_LO(R) ≤ ε·F_LO(A*)`.

Замечание (в Lean **не** доказано, посчитано в заметке, §4.4): нарушающая
строка `R` липкая — её плечо равно `C²/(1+1/N⁴)` и стремится к единице.
Это объясняет, почему общей оценки цены выбрасывания `r²/(1−h)` не хватает. -/
theorem sticky_row_essential (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℝ, 3 ≤ N
      ∧ (∀ v, gram (rowsE N) (barK Aset) v = gram (rowsE N) (barK Rset) v)
      ∧ (∀ v, mom (rowsE N) (tgtsE N) (barK Aset) node v
                = mom (rowsE N) (tgtsE N) (barK Rset) node v)
      ∧ phi (rowsE N) (tgtsE N) (barK Aset) node
          = phi (rowsE N) (tgtsE N) (barK Rset) node
      ∧ IsNormal (rowsE N) (tgtsE N) (barK Aset) (tfix N)
      ∧ IsNormal (rowsE N) (tgtsE N) (barK Rset) (tfix N)
      ∧ (∀ r ∈ barK (κ := Fin 1) Aset, clipE r →
            0 ≤ tgtsE N r - dotp (rowsE N r) (tfix N))
      ∧ tgtsE N (Sum.inl 2) - dotp (rowsE N (Sum.inl 2)) (tfix N) < 0
      ∧ (∀ r ∈ barK (κ := Fin 1) Aset, clipE r →
            0 ≤ tgtsE N r - dotp (rowsE N r) (tau N))
      ∧ (∀ r ∈ barK (κ := Fin 1) Rset, clipE r →
            0 ≤ tgtsE N r - dotp (rowsE N r) (tau N))
      ∧ IsLeast {v : ℝ | ∃ t, v = psiC (rowsE N) (tgtsE N) clipE (barK Aset) t}
            (1 + 1/(N^4+1))
      ∧ IsLeast {v : ℝ | ∃ t, v = psiC (rowsE N) (tgtsE N) clipE (barK Rset) t}
            ((S N + C N)^2 / (N^4 * S N^2 + 1))
      ∧ phi (rowsE N) (tgtsE N) (barK Aset) (tau N)
          - phi (rowsE N) (tgtsE N) (barK Aset) (tfix N) ≤ ε * (1 + 1/(N^4+1))
      ∧ (S N + C N)^2 / (N^4 * S N^2 + 1) ≤ ε * (1 + 1/(N^4+1)) := by
  have hr0 : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hrsq : (Real.sqrt ε)^2 = ε := Real.sq_sqrt hε.le
  refine ⟨max 3 (6/Real.sqrt ε), le_max_left _ _, ?_⟩
  set N : ℝ := max 3 (6/Real.sqrt ε) with hNdef
  have hN : 3 ≤ N := le_max_left _ _
  have hN0 : (0:ℝ) < N := by linarith
  have hNr : 6/Real.sqrt ε ≤ N := le_max_right _ _
  have h1 : 6 ≤ N * Real.sqrt ε := (div_le_iff₀ hr0).mp hNr
  have hNbig : 36 ≤ N^2 * ε := by nlinarith [h1, hrsq, hr0, hN0]
  have hfac : (1:ℝ) ≤ 1 + 1/(N^4+1) := by
    have h : (0:ℝ) ≤ 1/(N^4+1) := by positivity
    linarith
  have hgap : 11/N^2 ≤ ε * (1 + 1/(N^4+1)) := by
    have h : 11/N^2 ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hNbig, hε.le]
    nlinarith [h, hfac, hε.le]
  have hflo : 1/N^2 ≤ ε * (1 + 1/(N^4+1)) := by
    have h : 1/N^2 ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hNbig, hε.le]
    nlinarith [h, hfac, hε.le]
  exact ⟨gram_eq N hN, mom_eq N hN, Q_eq N hN, normal_A N hN, normal_R N hN,
    selfcons_A N hN, not_selfcons_R N hN, (admitted_sign N hN).1, (admitted_sign N hN).2,
    isLeast_LO_A N hN, isLeast_LO_R N hN,
    le_trans (gap_le N hN) hgap, le_trans (FLOR_le N hN) hflo⟩

end Sticky
end SparseSharpe.Factor
