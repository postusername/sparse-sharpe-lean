import SparseSharpe.Factor.ScaleFreeStep
import SparseSharpe.Factor.ClippedTrading

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Схема без ω на классе «не больше одной тугой строки»: сквозная теорема (C1 ТЗ v26)

Схема (`code/SPEC_C1.md`, п. 7), строки `rowsK d B G`, цели `targetsK m d`, обрезаются строки
активов:

* догадки `V = L·2^j`, `j ≤ J`;
* перебор всех `K`-ок строк `T : κ → ι ⊕ κ` (`(M+K)^K` штук), активы `T` входят в каждый
  кандидат принудительно (`assetsT`);
* узлы `x(T, z)` с `ρ(x) = s·z`, `z ∈ [−Z, Z]^K`, шаг `s = √(εV)/(C√K)`, `C = (k+K)K`,
  `Z = ⌈C√(2K/ε)⌉ + 1` (`sfNode`, `sfStep`, `sfZ`) — без величин входа;
* в узле и для каждой строки `l ∈ κ` — рюкзак `knap` по допущенным активам (`|c_i|_∞ ≤ 1`,
  не из `T`) с аддитивным ключом `(⌊resC_i c_i/η⌋, ⌊resC_i²/ζ⌋, 1)` (ключ Крамера, округлённый
  счёт, счётчик), `η = √(εV)/(k√K)`, `ζ = εV/k`; в корзине хранится набор с **наименьшим
  точным** `κ_l = Σ resC_i c_{il}`; ключи вне коробки `sfBox` (границы `sfZk`, `sfZq` —
  без `ω`) отбрасываются;
* кандидаты — `assetsT T ∪ R` с не более чем `k` активами (`sfCandidates`).

Главные утверждения:

* `card_sfCandidates_le` — размер семейства `(J+1)·(M+K)^K·(2Z+1)^K·K·(|box|+1)`,
  `|box| = (2Z_κ+1)^K(Z_q+1)(k+1)`, `Z = ⌈(k+K)K√(2K/ε)⌉ + 1`, `Z_κ = ⌈k√K√(k(2+ε)/ε)⌉ + k`,
  `Z_q = ⌈(2+ε)k/ε⌉`: от данных зависит только число догадок `J + 1`;
* `sf_one_guess` — при `V ≤ F ≤ 2V` для любого набора `A₀` (`|A₀| ≤ k`, все активы активны
  в двойственной точке `x₀`, `F = F_LO(A₀)`) из класса «не больше одного актива с весом
  `r_i(x₀) < 2√(εV/K)`» в семействе есть кандидат с `F_LO ≥ (1 − 5ε)·F` (Леммы 1–5, 7 из
  `Factor/ScaleFreeStep.lean`); `exists_good_sfCandidate` — то же по всем догадкам;
* `main_theorem_sf` — сквозная теорема: `L` — значение одиночного актива `(m_i)_+²/V_ii`
  (естественный выбор — максимум), `J = ⌈log₂(Σ_i(m_i)_+²/d_i / L)⌉`; класс — у задачи есть
  оптимальный набор `A₀` (все активы активны в `x₀`) с не более чем одним активом веса
  `r_i(x₀) = √d_i·w*_i < 2√(ε·OPT/K)`. Гарантия `1 − 5ε` по значению и `√(1 − 5ε)` по Шарпу.
  `ω` нет ни в гипотезах, ни в схеме; величины входа — только в `J`: при `L = max_i(m_i)_+²/V_ii`
  `J ≤ ⌈log₂(M(1 + ω_max))⌉`, то есть плечо входит лишь логарифмически, через число догадок.
* `sf_instance` (один актив; класс выполнен тривиально), `sf_instance_two` (два актива, ровно
  один тугой: веса `22/15` и `1/15` при пороге `≈ 0.42`), `sf_instance_K2` (один актив, `K = 2`
  фактора) — гипотезы выполнимы.

Класс — уточнённый (точка остановки Леммы 7, `spec7_counterexample`, `spec7_fails`): «тугой»
может быть не более одной строки **среди всех активов оптимума**, а не только среди строк `T`.
-/

namespace SparseSharpe.Factor

open Finset

/-! ### Определения схемы -/

section SchemeDefs

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Константа зажима `C = (k+K)K`. -/
noncomputable def sfC (κ : Type*) [Fintype κ] (k : ℕ) : ℝ :=
  ((k + Fintype.card κ : ℕ) : ℝ) * Fintype.card κ

/-- Шаг ключа Крамера `η = √(εV)/(k√K)`. -/
noncomputable def sfEta (κ : Type*) [Fintype κ] (k : ℕ) (ε V : ℝ) : ℝ :=
  Real.sqrt (ε * V) / (k * Real.sqrt (Fintype.card κ))

/-- Шаг округления счёта `ζ = εV/k`. -/
noncomputable def sfZeta (k : ℕ) (ε V : ℝ) : ℝ := ε * V / k

/-- Шаг решётки по `ρ`: `s = √(εV)/(C√K)`. -/
noncomputable def sfStep (κ : Type*) [Fintype κ] (k : ℕ) (ε V : ℝ) : ℝ :=
  Real.sqrt (ε * V) / (sfC κ k * Real.sqrt (Fintype.card κ))

/-- Радиус номеров узлов `Z = ⌈C√(2K/ε)⌉ + 1` — без величин входа. -/
noncomputable def sfZ (κ : Type*) [Fintype κ] (k : ℕ) (ε : ℝ) : ℕ :=
  ⌈sfC κ k * Real.sqrt (2 * Fintype.card κ / ε)⌉₊ + 1

/-- Граница ключа Крамера `Z_κ = ⌈k√K·√(k(2+ε)/ε)⌉ + k`. -/
noncomputable def sfZk (κ : Type*) [Fintype κ] (k : ℕ) (ε : ℝ) : ℤ :=
  ⌈(k : ℝ) * Real.sqrt (Fintype.card κ) * Real.sqrt (k * (2 + ε) / ε)⌉ + k

/-- Граница округлённого счёта `Z_q = ⌈(2+ε)k/ε⌉`. -/
noncomputable def sfZq (k : ℕ) (ε : ℝ) : ℤ := ⌈(2 + ε) * k / ε⌉

/-- Коробка ключей `[−Z_κ, Z_κ]^K × [0, Z_q] × [0, k]`. -/
def sfBox (κ : Type*) [Fintype κ] [DecidableEq κ] (Zk Zq : ℤ) (k : ℕ) :
    Finset ((κ → ℤ) × ℤ × ℕ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-Zk) Zk) ×ˢ (Finset.Icc 0 Zq ×ˢ Finset.range (k + 1))

/-- Узел `x(T, z)`: точка с `ρ(x) = s·z` (при `det A_T ≠ 0`, `sfNode_rho`). -/
noncomputable def sfNode {ρ : Type*} (a : ρ → κ → ℝ) (y : ρ → ℝ) (T : κ → ρ) (s : ℝ)
    (z : κ → ℤ) : κ → ℝ :=
  (rowMat a T)⁻¹.mulVec (fun m => y (T m) - s * z m)

/-- Активы, вошедшие в `K`-ку. -/
def assetsT (T : κ → ι ⊕ κ) : Finset ι :=
  Finset.univ.filter (fun i => (Sum.inl i : ι ⊕ κ) ∈ rowsT T)

/-- Допуск актива в рюкзак: не из `T` и `|c_i|_∞ ≤ 1`. -/
noncomputable def sfAdm (a : ι ⊕ κ → κ → ℝ) (T : κ → ι ⊕ κ) (i : ι) : Bool :=
  decide ((Sum.inl i : ι ⊕ κ) ∉ rowsT T ∧ ∀ m, |cf a T (Sum.inl i) m| ≤ 1)

/-- Аддитивный ключ актива: ключ Крамера, округлённый счёт, счётчик. -/
noncomputable def sfKey (a : ι ⊕ κ → κ → ℝ) (y : ι ⊕ κ → ℝ) (cl : ι ⊕ κ → Bool)
    (T : κ → ι ⊕ κ) (η ζ : ℝ) (x : κ → ℝ) (i : ι) : (κ → ℤ) × ℤ × ℕ :=
  (keyC a y cl T η x (Sum.inl i), ⌊resC a y cl (Sum.inl i) x ^ 2 / ζ⌋, 1)

/-- Значение для отбора в корзине: `−resC_i c_{il}` (максимум суммы — минимум точного `κ_l`). -/
noncomputable def sfVal (a : ι ⊕ κ → κ → ℝ) (y : ι ⊕ κ → ℝ) (cl : ι ⊕ κ → Bool)
    (T : κ → ι ⊕ κ) (x : κ → ℝ) (l : κ) (i : ι) : ℝ :=
  -(resC a y cl (Sum.inl i) x * cf a T (Sum.inl i) l)

/-- **Таблица схемы** в узле `z` `K`-ки `T` для строки `l` при догадке `V`. -/
noncomputable def sfTable (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ) (ε V : ℝ)
    (T : κ → ι ⊕ κ) (z : κ → ℤ) (l : κ) (La : List ι) : Finset (Finset ι) :=
  knap (sfVal (rowsK d B G) (targetsK m d) (fun r => r.isLeft) T
      (sfNode (rowsK d B G) (targetsK m d) T (sfStep κ k ε V) z) l)
    (sfKey (rowsK d B G) (targetsK m d) (fun r => r.isLeft) T (sfEta κ k ε V) (sfZeta k ε V)
      (sfNode (rowsK d B G) (targetsK m d) T (sfStep κ k ε V) z))
    (sfBox κ (sfZk κ k ε) (sfZq k ε) k)
    (La.filter (sfAdm (rowsK d B G) T))

/-- **Семейство при одной догадке:** все `K`-ки, узлы и строки `l`; кандидаты `assetsT T ∪ R`
с не более чем `k` активами. -/
noncomputable def sfFamily (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ) (ε V : ℝ)
    (La : List ι) : Finset (Finset ι) :=
  (Finset.univ : Finset (κ → ι ⊕ κ)).biUnion fun T =>
    (nodeBox (κ := κ) (sfZ κ k ε)).biUnion fun z =>
      (Finset.univ : Finset κ).biUnion fun l =>
        ((sfTable m d B G k ε V T z l La).image (fun R => assetsT T ∪ R)).filter
          (fun W => W.card ≤ k)

/-- **Семейство кандидатов** по всем догадкам `V_j = L·2^j`, `j ≤ J`. -/
noncomputable def sfCandidates (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ)
    (ε L : ℝ) (J : ℕ) (La : List ι) : Finset (Finset ι) :=
  (Finset.range (J + 1)).biUnion fun j => sfFamily m d B G k ε (L * 2 ^ j) La

/-- Граница размера коробки ключей. -/
noncomputable def sfBoxBound (κ : Type*) [Fintype κ] (k : ℕ) (ε : ℝ) : ℕ :=
  (2 * sfZk κ k ε + 1).toNat ^ Fintype.card κ * ((sfZq k ε + 1).toNat * (k + 1))

lemma card_sfBox (Zk Zq : ℤ) (k : ℕ) :
    (sfBox κ Zk Zq k).card = (2 * Zk + 1).toNat ^ Fintype.card κ * ((Zq + 1).toNat * (k + 1)) := by
  simp only [sfBox, Finset.card_product, Fintype.card_piFinset, Int.card_Icc,
    Finset.card_range, Finset.prod_const, Finset.card_univ]
  congr 2
  · congr 1; omega
  · congr 1; omega

lemma card_sfTable_le (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ) (ε V : ℝ)
    (T : κ → ι ⊕ κ) (z : κ → ℤ) (l : κ) (La : List ι) :
    (sfTable m d B G k ε V T z l La).card ≤ sfBoxBound κ k ε + 1 := by
  unfold sfTable
  refine le_trans (knap_card_le _ _ _ _) (le_of_eq ?_)
  rw [card_sfBox, sfBoxBound]

lemma card_sfFamily_le (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ) (ε V : ℝ)
    (La : List ι) :
    (sfFamily m d B G k ε V La).card
      ≤ (Fintype.card ι + Fintype.card κ) ^ Fintype.card κ
        * ((2 * sfZ κ k ε + 1) ^ Fintype.card κ
          * (Fintype.card κ * (sfBoxBound κ k ε + 1))) := by
  unfold sfFamily
  refine le_trans Finset.card_biUnion_le ?_
  have hT : (Finset.univ : Finset (κ → ι ⊕ κ)).card
      = (Fintype.card ι + Fintype.card κ) ^ Fintype.card κ := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_sum]
  rw [← hT]
  refine Finset.sum_le_card_nsmul _ _ _ fun T _ => ?_
  refine le_trans Finset.card_biUnion_le ?_
  rw [← card_nodeBox (κ := κ) (sfZ κ k ε)]
  refine Finset.sum_le_card_nsmul _ _ _ fun z _ => ?_
  refine le_trans Finset.card_biUnion_le ?_
  have hl : (Finset.univ : Finset κ).card = Fintype.card κ := Finset.card_univ
  rw [← hl]
  refine Finset.sum_le_card_nsmul _ _ _ fun l _ => ?_
  refine le_trans (Finset.card_filter_le _ _) (le_trans Finset.card_image_le ?_)
  exact card_sfTable_le m d B G k ε V T z l La

/-- **Размер семейства схемы:** `(J+1)·(M+K)^K·(2Z+1)^K·K·(|box|+1)`. Здесь
`Z = ⌈(k+K)K√(2K/ε)⌉ + 1`, `|box| = (2Z_κ+1)^K(Z_q+1)(k+1)`, `Z_κ = ⌈k√K√(k(2+ε)/ε)⌉ + k`,
`Z_q = ⌈(2+ε)k/ε⌉` — в границе нет ни `ω`, ни величин входа; они входят только через число
догадок `J + 1`. -/
theorem card_sfCandidates_le (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ)
    (ε L : ℝ) (J : ℕ) (La : List ι) :
    (sfCandidates m d B G k ε L J La).card
      ≤ (J + 1) * ((Fintype.card ι + Fintype.card κ) ^ Fintype.card κ
        * ((2 * sfZ κ k ε + 1) ^ Fintype.card κ
          * (Fintype.card κ * (sfBoxBound κ k ε + 1)))) := by
  unfold sfCandidates
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ _
    (fun j _ => card_sfFamily_le m d B G k ε (L * 2 ^ j) La)) ?_
  rw [Finset.card_range, smul_eq_mul]

/-- У каждого кандидата не больше `k` активов. -/
theorem card_le_of_mem_sfCandidates {m d : ι → ℝ} {B : ι → κ → ℝ} {G : κ → κ → ℝ} {k : ℕ}
    {ε L : ℝ} {J : ℕ} {La : List ι} {W : Finset ι}
    (hW : W ∈ sfCandidates m d B G k ε L J La) : W.card ≤ k := by
  unfold sfCandidates sfFamily at hW
  simp only [Finset.mem_biUnion, Finset.mem_filter] at hW
  obtain ⟨_, _, _, _, _, _, _, _, hW⟩ := hW
  exact hW.2

end SchemeDefs

/-! ### Вспомогательные утверждения -/

section Aux

variable {ι κ : Type*} [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Вложение активов в строки. -/
def inlE (ι κ : Type*) : ι ↪ ι ⊕ κ := ⟨Sum.inl, Sum.inl_injective⟩

lemma barK_union_map (A U : Finset ι) :
    barK (κ := κ) (A ∪ U) = barK (κ := κ) A ∪ U.map (inlE ι κ) := by
  ext r
  rcases r with i | l
  · simp [barK, Finset.inl_mem_disjSum, inlE]
  · simp [barK, Finset.inr_mem_disjSum]

lemma disjoint_barK_map {A U : Finset ι} (h : Disjoint A U) :
    Disjoint (barK (κ := κ) A) (U.map (inlE ι κ)) := by
  rw [Finset.disjoint_left]
  intro r hr hU
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hU
  have : i ∈ A := by simpa [barK, Finset.inl_mem_disjSum, inlE] using hr
  exact Finset.disjoint_left.mp h this hi

lemma rowsT_subset_barK_assetsT [Fintype ι] (T : κ → ι ⊕ κ) :
    rowsT T ⊆ barK (κ := κ) (assetsT T) := by
  intro r hr
  rcases r with i | l
  · simp [barK, Finset.inl_mem_disjSum, assetsT, hr]
  · simp [barK, Finset.inr_mem_disjSum]

lemma assetsT_subset [Fintype ι] {A : Finset ι} {T : κ → ι ⊕ κ} (h : rowsT T ⊆ barK (κ := κ) A) :
    assetsT T ⊆ A := by
  intro i hi
  simp only [assetsT, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simpa [barK, Finset.inl_mem_disjSum] using h hi

lemma mem_assetsT [Fintype ι] {T : κ → ι ⊕ κ} {i : ι} :
    i ∈ assetsT T ↔ (Sum.inl i : ι ⊕ κ) ∈ rowsT T := by
  simp [assetsT]

/-- Точка узла: `ρ(x(T, z)) = s·z` при `det A_T ≠ 0`. -/
lemma sfNode_rho {ρ : Type*} {a : ρ → κ → ℝ} {y : ρ → ℝ} {T : κ → ρ}
    (hdet : (rowMat a T).det ≠ 0) (s : ℝ) (z : κ → ℤ) (m : κ) :
    rhoT a y T (sfNode a y T s z) m = s * z m := by
  have hinv : (rowMat a T).mulVec ((rowMat a T)⁻¹.mulVec (fun m => y (T m) - s * z m))
      = fun m => y (T m) - s * z m := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have h2 := congrFun hinv m
  have h3 : dotp (a (T m)) (sfNode a y T s z) = y (T m) - s * z m := by
    simpa [Matrix.mulVec, dotProduct, rowMat, dotp, sfNode] using h2
  rw [rhoT, h3]; ring

/-- **Ключ любого подмножества `U` лежит в коробке**, если `|c_i|_∞ ≤ 1` на `U`, `|U| ≤ k` и
границы `Z_κ`, `Z_q` покрывают `√(|U|·Σ_U resC²)/η + k` и `Σ_U resC²/ζ`. -/
lemma sfKey_sum_mem_box {a : ι ⊕ κ → κ → ℝ} {y : ι ⊕ κ → ℝ} {cl : ι ⊕ κ → Bool}
    {T : κ → ι ⊕ κ} {η ζ : ℝ} {x : κ → ℝ} {k : ℕ} {Zk Zq : ℤ} {U : Finset ι}
    (hη : 0 < η) (hζ : 0 < ζ) (hcl : ∀ i ∈ U, cl (Sum.inl i))
    (hcf : ∀ i ∈ U, ∀ m, |cf a T (Sum.inl i) m| ≤ 1) (hUk : U.card ≤ k)
    (hZk : Real.sqrt (U.card * ∑ i ∈ U, resC a y cl (Sum.inl i) x ^ 2) / η + k ≤ Zk)
    (hZq : (∑ i ∈ U, resC a y cl (Sum.inl i) x ^ 2) / ζ ≤ Zq) :
    ∀ U' ⊆ U, ∑ i ∈ U', sfKey a y cl T η ζ x i ∈ sfBox κ Zk Zq k := by
  intro U' hU'
  have hr0 : ∀ i ∈ U, 0 ≤ resC a y cl (Sum.inl i) x := fun i hi => resC_nonneg_of_clip (hcl i hi)
  -- `Σ_U resC ≤ √(|U|·Σ_U resC²)`
  have hsumU : ∑ i ∈ U, resC a y cl (Sum.inl i) x
      ≤ Real.sqrt (U.card * ∑ i ∈ U, resC a y cl (Sum.inl i) x ^ 2) := by
    have h0 : 0 ≤ ∑ i ∈ U, resC a y cl (Sum.inl i) x := Finset.sum_nonneg hr0
    rw [← Real.sqrt_sq h0]
    exact Real.sqrt_le_sqrt sq_sum_le_card_mul_sum_sq
  have hU'k : U'.card ≤ k := le_trans (Finset.card_le_card hU') hUk
  simp only [sfBox, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc, Finset.mem_range]
  refine ⟨fun m => ?_, ⟨?_, ?_⟩, ?_⟩
  · -- ключ Крамера
    have hval : ((∑ i ∈ U', sfKey a y cl T η ζ x i).1 m : ℝ)
        = ∑ i ∈ U', ((⌊resC a y cl (Sum.inl i) x * cf a T (Sum.inl i) m / η⌋ : ℤ) : ℝ) := by
      simp [sfKey, keyC, Prod.fst_sum, Finset.sum_apply]
    have hb : |((∑ i ∈ U', sfKey a y cl T η ζ x i).1 m : ℝ)|
        ≤ Real.sqrt (U.card * ∑ i ∈ U, resC a y cl (Sum.inl i) x ^ 2) / η + k := by
      rw [hval]
      calc |∑ i ∈ U', ((⌊resC a y cl (Sum.inl i) x * cf a T (Sum.inl i) m / η⌋ : ℤ) : ℝ)|
          ≤ ∑ i ∈ U', |((⌊resC a y cl (Sum.inl i) x * cf a T (Sum.inl i) m / η⌋ : ℤ) : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ U', (resC a y cl (Sum.inl i) x / η + 1) := by
            refine Finset.sum_le_sum fun i hi => ?_
            refine le_trans (abs_floor_le _) ?_
            have hri := hr0 i (hU' hi)
            have hc := hcf i (hU' hi) m
            rw [abs_div, abs_of_pos hη, abs_mul, abs_of_nonneg hri]
            have : resC a y cl (Sum.inl i) x * |cf a T (Sum.inl i) m|
                ≤ resC a y cl (Sum.inl i) x := mul_le_of_le_one_right hri hc
            have := div_le_div_of_nonneg_right this hη.le
            linarith
        _ = (∑ i ∈ U', resC a y cl (Sum.inl i) x) / η + U'.card := by
            rw [Finset.sum_add_distrib, Finset.sum_div]; simp
        _ ≤ (∑ i ∈ U, resC a y cl (Sum.inl i) x) / η + k := by
            have h1 : ∑ i ∈ U', resC a y cl (Sum.inl i) x ≤ ∑ i ∈ U, resC a y cl (Sum.inl i) x :=
              Finset.sum_le_sum_of_subset_of_nonneg hU' fun i hi _ => hr0 i hi
            have h2 : (U'.card : ℝ) ≤ k := by exact_mod_cast hU'k
            have h3 := div_le_div_of_nonneg_right h1 hη.le
            linarith
        _ ≤ Real.sqrt (U.card * ∑ i ∈ U, resC a y cl (Sum.inl i) x ^ 2) / η + k := by
            have := div_le_div_of_nonneg_right hsumU hη.le
            linarith
    have hb' := le_trans hb hZk
    rw [abs_le] at hb'
    constructor
    · have : ((-Zk : ℤ) : ℝ) ≤ ((∑ i ∈ U', sfKey a y cl T η ζ x i).1 m : ℝ) := by
        push_cast; linarith [hb'.1]
      exact_mod_cast this
    · exact_mod_cast hb'.2
  · -- счёт `≥ 0`
    have : ∀ i ∈ U', 0 ≤ ⌊resC a y cl (Sum.inl i) x ^ 2 / ζ⌋ := fun i _ =>
      Int.floor_nonneg.mpr (div_nonneg (sq_nonneg _) hζ.le)
    simpa [sfKey, Prod.snd_sum, Prod.fst_sum] using Finset.sum_nonneg this
  · -- счёт `≤ Z_q`
    have hle : ((∑ i ∈ U', ⌊resC a y cl (Sum.inl i) x ^ 2 / ζ⌋ : ℤ) : ℝ)
        ≤ (∑ i ∈ U, resC a y cl (Sum.inl i) x ^ 2) / ζ := by
      push_cast
      calc ∑ i ∈ U', ((⌊resC a y cl (Sum.inl i) x ^ 2 / ζ⌋ : ℤ) : ℝ)
          ≤ ∑ i ∈ U', resC a y cl (Sum.inl i) x ^ 2 / ζ :=
            Finset.sum_le_sum fun i _ => Int.floor_le _
        _ ≤ ∑ i ∈ U, resC a y cl (Sum.inl i) x ^ 2 / ζ :=
            Finset.sum_le_sum_of_subset_of_nonneg hU' fun i _ _ =>
              div_nonneg (sq_nonneg _) hζ.le
        _ = (∑ i ∈ U, resC a y cl (Sum.inl i) x ^ 2) / ζ := by rw [Finset.sum_div]
    have h2 := le_trans hle hZq
    have h3 : (∑ i ∈ U', ⌊resC a y cl (Sum.inl i) x ^ 2 / ζ⌋ : ℤ) ≤ Zq := by exact_mod_cast h2
    simpa [sfKey, Prod.snd_sum, Prod.fst_sum] using h3
  · -- счётчик
    have : (∑ i ∈ U', sfKey a y cl T η ζ x i).2.2 = U'.card := by
      simp [sfKey, Prod.snd_sum]
    rw [this]; omega

end Aux


/-! ### Параметры схемы: тождества и оценки -/

section Params

variable {κ : Type*} [Fintype κ] [Nonempty κ]

lemma sfC_eq (k : ℕ) : sfC κ k = ((k : ℝ) + Fintype.card κ) * Fintype.card κ := by
  rw [sfC]; push_cast; ring

lemma card_pos_real : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos

lemma one_le_sfC {k : ℕ} (hk : 1 ≤ k) : 1 ≤ sfC κ k := by
  rw [sfC_eq]
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : (1 : ℝ) ≤ Fintype.card κ := by exact_mod_cast Fintype.card_pos
  nlinarith

lemma sfEta_pos {k : ℕ} (hk : 1 ≤ k) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V) :
    0 < sfEta κ k ε V := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast hk
  have h2 := card_pos_real (κ := κ)
  rw [sfEta]; positivity

lemma sfZeta_pos {k : ℕ} (hk : 1 ≤ k) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V) :
    0 < sfZeta k ε V := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [sfZeta]; positivity

lemma sfStep_pos {k : ℕ} (hk : 1 ≤ k) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V) :
    0 < sfStep κ k ε V := by
  have h1 := lt_of_lt_of_le one_pos (one_le_sfC (κ := κ) hk)
  have h2 := card_pos_real (κ := κ)
  rw [sfStep]; positivity

/-- `kη√K = √(εV)`. -/
lemma k_sfEta {k : ℕ} (hk : 1 ≤ k) (ε V : ℝ) :
    (k : ℝ) * sfEta κ k ε V * Real.sqrt (Fintype.card κ) = Real.sqrt (ε * V) := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast hk
  have h2 : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr card_pos_real
  rw [sfEta]; field_simp

/-- `kζ = εV`. -/
lemma k_sfZeta {k : ℕ} (hk : 1 ≤ k) (ε V : ℝ) : (k : ℝ) * sfZeta k ε V = ε * V := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [sfZeta]; field_simp

/-- `C·√K·s = √(εV)`. -/
lemma sfC_sfStep {k : ℕ} (hk : 1 ≤ k) (ε V : ℝ) :
    sfC κ k * (Real.sqrt (Fintype.card κ) * sfStep κ k ε V) = Real.sqrt (ε * V) := by
  have h1 := lt_of_lt_of_le one_pos (one_le_sfC (κ := κ) hk)
  have h2 : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr card_pos_real
  rw [sfStep]; field_simp

/-- **Порог тугой строки:** `kη + k·K·s ≤ 2√(εV/K)`. -/
lemma sf_threshold {k : ℕ} (hk : 1 ≤ k) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V) :
    (k : ℝ) * sfEta κ k ε V + k * (Fintype.card κ * sfStep κ k ε V)
      ≤ 2 * Real.sqrt (ε * V / Fintype.card κ) := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast hk
  have hK := card_pos_real (κ := κ)
  have hsK : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr hK
  have hsK2 : Real.sqrt (Fintype.card κ : ℝ) ^ 2 = Fintype.card κ := Real.sq_sqrt hK.le
  have e1 : Real.sqrt (ε * V / Fintype.card κ)
      = Real.sqrt (ε * V) / Real.sqrt (Fintype.card κ) := Real.sqrt_div' _ hK.le
  have e2 : (k : ℝ) * sfEta κ k ε V = Real.sqrt (ε * V) / Real.sqrt (Fintype.card κ) := by
    rw [sfEta]; field_simp
  have e3 : (k : ℝ) * (Fintype.card κ * sfStep κ k ε V)
      = (k / (k + Fintype.card κ)) * (Real.sqrt (ε * V) / Real.sqrt (Fintype.card κ)) := by
    rw [sfStep, sfC_eq]; field_simp
  have hfr : (k : ℝ) / (k + Fintype.card κ) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hpos : 0 ≤ Real.sqrt (ε * V) / Real.sqrt (Fintype.card κ) := by positivity
  rw [e1, e2, e3]
  nlinarith [mul_le_mul_of_nonneg_right hfr hpos]

/-- **Запас активности:** `K·s ≤ 2√(εV/K)`. -/
lemma sf_margin {k : ℕ} (hk : 1 ≤ k) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V) :
    (Fintype.card κ : ℝ) * sfStep κ k ε V ≤ 2 * Real.sqrt (ε * V / Fintype.card κ) := by
  have h := sf_threshold (κ := κ) hk hε hV
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h0 : 0 ≤ (k : ℝ) * sfEta κ k ε V :=
    mul_nonneg (by positivity) (sfEta_pos (κ := κ) hk hε hV).le
  have hs : 0 ≤ (Fintype.card κ : ℝ) * sfStep κ k ε V :=
    mul_nonneg card_pos_real.le (sfStep_pos (κ := κ) hk hε hV).le
  have : (Fintype.card κ : ℝ) * sfStep κ k ε V ≤ k * (Fintype.card κ * sfStep κ k ε V) :=
    le_mul_of_one_le_left hs h1
  linarith

/-- `C·K·s² ≤ εV`. -/
lemma sfC_K_step_sq {k : ℕ} (hk : 1 ≤ k) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V) :
    sfC κ k * (Fintype.card κ * sfStep κ k ε V ^ 2) ≤ ε * V := by
  have hC1 := one_le_sfC (κ := κ) hk
  have hK := card_pos_real (κ := κ)
  have hsK2 : Real.sqrt (Fintype.card κ : ℝ) ^ 2 = Fintype.card κ := Real.sq_sqrt hK.le
  have e : sfC κ k * (Fintype.card κ * sfStep κ k ε V ^ 2) * sfC κ k = ε * V := by
    calc sfC κ k * (Fintype.card κ * sfStep κ k ε V ^ 2) * sfC κ k
        = (sfC κ k * (Real.sqrt (Fintype.card κ) * sfStep κ k ε V)) ^ 2 := by
          rw [mul_pow, mul_pow, hsK2]; ring
      _ = ε * V := by rw [sfC_sfStep hk, Real.sq_sqrt (mul_pos hε hV).le]
  have h0 : 0 ≤ sfC κ k * (Fintype.card κ * sfStep κ k ε V ^ 2) := by
    have := (sfStep_pos (κ := κ) hk hε hV)
    have : (0 : ℝ) ≤ sfC κ k := by linarith
    positivity
  calc sfC κ k * (Fintype.card κ * sfStep κ k ε V ^ 2)
      ≤ sfC κ k * (Fintype.card κ * sfStep κ k ε V ^ 2) * sfC κ k :=
        le_mul_of_one_le_right h0 hC1
    _ = ε * V := e

/-- Радиус решётки в шагах: `C√(2K/ε)·s = √(2V)`. -/
lemma sf_node_radius {k : ℕ} (hk : 1 ≤ k) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V) :
    sfC κ k * Real.sqrt (2 * Fintype.card κ / ε) * sfStep κ k ε V = Real.sqrt (2 * V) := by
  have hC := lt_of_lt_of_le one_pos (one_le_sfC (κ := κ) hk)
  have hK := card_pos_real (κ := κ)
  have hsK : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr hK
  have h1 : Real.sqrt (2 * Fintype.card κ / ε) * Real.sqrt (ε * V)
      = Real.sqrt (2 * V) * Real.sqrt (Fintype.card κ) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1; field_simp
  rw [sfStep]
  field_simp
  linarith [h1, mul_comm (Real.sqrt (2 * V)) (Real.sqrt (Fintype.card κ : ℝ))]

/-- Радиус ключа в шагах `η`: `√(k(2+ε)V)/η = k√K·√(k(2+ε)/ε)`. -/
lemma sf_key_radius {k : ℕ} (hk : 1 ≤ k) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V) :
    Real.sqrt ((k : ℝ) * ((2 + ε) * V)) / sfEta κ k ε V
      = (k : ℝ) * Real.sqrt (Fintype.card κ) * Real.sqrt (k * (2 + ε) / ε) := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast hk
  have hK := card_pos_real (κ := κ)
  have hsK : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr hK
  have hsq : 0 < Real.sqrt (ε * V) := Real.sqrt_pos.mpr (mul_pos hε hV)
  have e1 : Real.sqrt ((k : ℝ) * ((2 + ε) * V))
      = Real.sqrt (k * (2 + ε) / ε) * Real.sqrt (ε * V) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1; field_simp
  rw [e1, sfEta]
  field_simp

/-- Радиус счёта в шагах `ζ`: `(2+ε)V/ζ = (2+ε)k/ε`. -/
lemma sf_score_radius {k : ℕ} (hk : 1 ≤ k) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V) :
    (2 + ε) * V / sfZeta k ε V = (2 + ε) * k / ε := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [sfZeta]; field_simp

end Params

/-! ### Представитель корзины и его значение -/

section Core

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {a : ι ⊕ κ → κ → ℝ} {y : ι ⊕ κ → ℝ} {T : κ → ι ⊕ κ}

/-- Точная сумма Крамера набора активов `U` в узле `x`: `κ_U(x)_l = Σ_{i∈U} resC_i(x)c_{il}`. -/
noncomputable def kapA (a : ι ⊕ κ → κ → ℝ) (y : ι ⊕ κ → ℝ) (T : κ → ι ⊕ κ) (U : Finset ι)
    (x : κ → ℝ) (l : κ) : ℝ :=
  kapC a y (fun r => r.isLeft) T (U.map (inlE ι κ)) x l

/-- Счёт набора активов `U` в узле `x`: `Σ_{i∈U} resC_i(x)²`. -/
noncomputable def scoreA (a : ι ⊕ κ → κ → ℝ) (y : ι ⊕ κ → ℝ) (U : Finset ι) (x : κ → ℝ) : ℝ :=
  ∑ i ∈ U, resC a y (fun r => r.isLeft) (Sum.inl i) x ^ 2

/-- **Представитель корзины оптимума.** В таблице `knap` (ключ `sfKey`, отбор — минимум
точного `κ_l`) есть набор `R` той же мощности, что `U_S = A₀ ∖ T`, из допущенных активов, с
`|κ_R − κ_{U_S}|_∞ ≤ kη` (Лемма 4), `κ_{R,l} ≤ κ_{U_S,l}` и счётом не меньше счёта `U_S`
минус `kζ`. -/
theorem sf_rep_exists {A₀ : Finset ι} {x : κ → ℝ} {k : ℕ} {η ζ : ℝ} {l : κ} {Zk Zq : ℤ}
    {La : List ι} (hk1 : 1 ≤ k) (hη : 0 < η) (hζ : 0 < ζ) (hnd : La.Nodup)
    (hall : ∀ i, i ∈ La) (hcfS : ∀ j ∈ barK (κ := κ) A₀, ∀ m, |cf a T j m| ≤ 1)
    (hA₀k : A₀.card ≤ k)
    (hZk : Real.sqrt ((A₀ \ assetsT T).card * scoreA a y (A₀ \ assetsT T) x) / η + k ≤ Zk)
    (hZq : scoreA a y (A₀ \ assetsT T) x / ζ ≤ Zq) :
    ∃ R ∈ knap (sfVal a y (fun r => r.isLeft) T x l) (sfKey a y (fun r => r.isLeft) T η ζ x)
        (sfBox κ Zk Zq k) (La.filter (sfAdm a T)),
      R.card = (A₀ \ assetsT T).card
      ∧ (∀ i ∈ R, (Sum.inl i : ι ⊕ κ) ∉ rowsT T)
      ∧ (∀ m, |kapA a y T R x m - kapA a y T (A₀ \ assetsT T) x m| ≤ k * η)
      ∧ kapA a y T R x l ≤ kapA a y T (A₀ \ assetsT T) x l
      ∧ scoreA a y (A₀ \ assetsT T) x ≤ scoreA a y R x + k * ζ := by
  classical
  set US := A₀ \ assetsT T with hUS
  have hnotT : ∀ i ∈ US, (Sum.inl i : ι ⊕ κ) ∉ rowsT T := fun i hi hT =>
    (Finset.mem_sdiff.mp hi).2 (mem_assetsT.mpr hT)
  have hUSA : ∀ i ∈ US, (Sum.inl i : ι ⊕ κ) ∈ barK (κ := κ) A₀ := fun i hi =>
    inl_mem_barK (Finset.mem_sdiff.mp hi).1
  have hUSk : US.card ≤ k := le_trans (Finset.card_le_card Finset.sdiff_subset) hA₀k
  have hbox := sfKey_sum_mem_box (a := a) (y := y) (cl := fun r => r.isLeft) (T := T) (x := x)
    hη hζ (fun i _ => rfl) (fun i hi m => hcfS _ (hUSA i hi) m) hUSk hZk hZq
  have hUSL : US ⊆ (La.filter (sfAdm a T)).toFinset := by
    intro i hi
    rw [List.mem_toFinset, List.mem_filter]
    refine ⟨hall i, ?_⟩
    simp only [sfAdm, decide_eq_true_eq]
    exact ⟨hnotT i hi, fun m => hcfS _ (hUSA i hi) m⟩
  obtain ⟨R, hRmem, hRkey, hRval⟩ := knap_spec (sfVal a y (fun r => r.isLeft) T x l)
    (sfKey a y (fun r => r.isLeft) T η ζ x) (sfBox κ Zk Zq k) (La.filter (sfAdm a T))
    (hnd.filter _) US hUSL hbox
  have hRL := knap_mem (sfVal a y (fun r => r.isLeft) T x l)
    (sfKey a y (fun r => r.isLeft) T η ζ x) (sfBox κ Zk Zq k) (La.filter (sfAdm a T)) R hRmem
  have hkey1 : ∑ i ∈ R, keyC a y (fun r => r.isLeft) T η x (Sum.inl i)
      = ∑ i ∈ US, keyC a y (fun r => r.isLeft) T η x (Sum.inl i) := by
    have h := congrArg Prod.fst hRkey
    simpa [sfKey, Prod.fst_sum] using h
  have hkey2 : ∑ i ∈ R, ⌊resC a y (fun r => r.isLeft) (Sum.inl i) x ^ 2 / ζ⌋
      = ∑ i ∈ US, ⌊resC a y (fun r => r.isLeft) (Sum.inl i) x ^ 2 / ζ⌋ := by
    have h := congrArg (fun p => p.2.1) hRkey
    simpa [sfKey, Prod.snd_sum, Prod.fst_sum] using h
  have hcardR : R.card = US.card := by
    have h := congrArg (fun p => p.2.2) hRkey
    simpa [sfKey, Prod.snd_sum] using h
  refine ⟨R, hRmem, hcardR, fun i hi => ?_, fun m => ?_, ?_, ?_⟩
  · have h := hRL hi
    rw [List.mem_toFinset, List.mem_filter] at h
    simp only [sfAdm, decide_eq_true_eq] at h
    exact h.2.1
  · refine (abs_kap_sub_lt_of_key_eq hη (by omega) ?_ ?_ ?_ m).le
    · rw [Finset.card_map, hcardR]; exact hUSk
    · rw [Finset.card_map, Finset.card_map, hcardR]
    · rw [Finset.sum_map, Finset.sum_map]; exact hkey1
  · simp only [kapA, kapC, Finset.sum_map]
    simp only [sfVal, Finset.sum_neg_distrib] at hRval
    have : ∑ i ∈ R, resC a y (fun r => r.isLeft) (Sum.inl i) x * cf a T (Sum.inl i) l
        ≤ ∑ i ∈ US, resC a y (fun r => r.isLeft) (Sum.inl i) x * cf a T (Sum.inl i) l := by
      linarith
    simpa [inlE] using this
  · have hlt := abs_sum_sub_lt_of_floor_eq
      (f := fun i => resC a y (fun r => r.isLeft) (Sum.inl i) x ^ 2) hζ (by omega) hUSk
      hcardR.symm hkey2.symm
    rw [abs_lt] at hlt
    simp only [scoreA]
    linarith [hlt.2]

/-- **Значение представителя (Леммы 5 и 7 в схеме).** `T` — `K`-ка внутри `barK A₀` с
`|c|_∞ ≤ 1` и зажимом `C`; узел `x` — угол ячейки (`|Δρ|_∞ ≤ s`, знаки `H_{l·}`); класс:
все активы `A₀`, кроме `i₀`, имеют вес `≥ τ ≥ kη + kKs`, `τ ≥ Ks`, и `l` — индекс строки `i₀`
в `T`, если она там есть. Тогда для представителя `R` (свойства `sf_rep_exists`)
`ψ_{barK(T_A ∪ R)}(x') ≥ (1 − 5ε)·F` при всех `x'`. -/
theorem sf_value_of_rep (hdet : (rowMat a T).det ≠ 0) {A₀ R : Finset ι} {x₀ x : κ → ℝ}
    {k : ℕ} {ε V C η ζ s τ : ℝ} {l : κ} {i₀ : ι}
    (hA₀k : A₀.card ≤ k) (hTS : rowsT T ⊆ barK (κ := κ) A₀)
    (hcfS : ∀ j ∈ barK (κ := κ) A₀, ∀ m, |cf a T j m| ≤ 1)
    (hclamp : ∀ v, gram a (barK (κ := κ) A₀) v ≤ C * gramK a T v) (hC : 0 < C)
    (hnorm : IsNormal a y (barK (κ := κ) A₀) x₀)
    (hself : ∀ r ∈ barK (κ := κ) A₀, r.isLeft → 0 ≤ y r - dotp (a r) x₀)
    (hD : ∀ m, |rhoT a y T x m - rhoT a y T x₀ m| ≤ s)
    (hcorner : ∀ m, Hmat a T (barK (κ := κ) A₀) l m * (rhoT a y T x m - rhoT a y T x₀ m) ≤ 0)
    (hl : ∀ m, T m = Sum.inl i₀ → m = l)
    (hclass : ∀ i ∈ A₀, i ≠ i₀ → τ ≤ y (Sum.inl i) - dotp (a (Sum.inl i)) x₀)
    (hthr : (k : ℝ) * η + k * (Fintype.card κ * s) ≤ τ) (hmarg : (Fintype.card κ : ℝ) * s ≤ τ)
    (hη : 0 ≤ η) (hRadm : ∀ i ∈ R, (Sum.inl i : ι ⊕ κ) ∉ rowsT T)
    (hkeyc : ∀ m, |kapA a y T R x m - kapA a y T (A₀ \ assetsT T) x m| ≤ k * η)
    (hmin : kapA a y T R x l ≤ kapA a y T (A₀ \ assetsT T) x l)
    (hscore : scoreA a y (A₀ \ assetsT T) x ≤ scoreA a y R x + k * ζ)
    (hε : 0 ≤ ε) (hV : 0 ≤ V) (hVF : V ≤ phi a y (barK (κ := κ) A₀) x₀)
    (hnode : C * Real.sqrt (∑ m, (rhoT a y T x m - rhoT a y T x₀ m) ^ 2)
      ≤ Real.sqrt (ε * V))
    (hΔε : (k : ℝ) * η * Real.sqrt (Fintype.card κ) ≤ Real.sqrt (ε * V))
    (hδ : (k : ℝ) * ζ ≤ ε * V) (x' : κ → ℝ) :
    (1 - 5 * ε) * phi a y (barK (κ := κ) A₀) x₀
      ≤ psiC a y (fun r => r.isLeft) (barK (κ := κ) (assetsT T ∪ R)) x' := by
  classical
  set cl : ι ⊕ κ → Bool := fun r => r.isLeft with hcl
  set TA := assetsT (κ := κ) T with hTA
  set US := A₀ \ TA with hUS
  have hTAA : TA ⊆ A₀ := assetsT_subset hTS
  have hdTU : Disjoint TA US := Finset.disjoint_sdiff
  have hA₀eq : TA ∪ US = A₀ := Finset.union_sdiff_of_subset hTAA
  set base := barK (κ := κ) TA with hbase
  have hTb : rowsT T ⊆ base := rowsT_subset_barK_assetsT T
  have hSeq : barK (κ := κ) A₀ = base ∪ US.map (inlE ι κ) := by
    rw [hbase, ← barK_union_map, hA₀eq]
  have hdS : Disjoint base (US.map (inlE ι κ)) := disjoint_barK_map hdTU
  have hdTR : Disjoint TA R := by
    rw [Finset.disjoint_left]
    intro i hiT hiR
    exact hRadm i hiR (mem_assetsT.mp hiT)
  have hdR : Disjoint base (R.map (inlE ι κ)) := disjoint_barK_map hdTR
  have hXeq : barK (κ := κ) (TA ∪ R) = base ∪ R.map (inlE ι κ) := by
    rw [hbase, barK_union_map]
  have hnotT : ∀ i ∈ US, (Sum.inl i : ι ⊕ κ) ∉ rowsT T := fun i hi hT =>
    (Finset.mem_sdiff.mp hi).2 (mem_assetsT.mpr hT)
  -- `|S̄∖T| = |A₀| ≤ k`
  have hcardSm : ((base ∪ US.map (inlE ι κ)) \ rowsT T).card ≤ k := by
    rw [← hSeq, Finset.card_sdiff_of_subset hTS, card_barK, card_rowsT hdet]
    omega
  -- обрезаемая строка `T` — актив `A₀`; если это не `i₀`, у неё запас
  have hTrow : ∀ m, cl (T m) → T m ≠ Sum.inl i₀ →
      (k : ℝ) * η + k * (Fintype.card κ * s) ≤ rhoT a y T x₀ m := by
    intro m hc hne
    obtain ⟨i, hi⟩ : ∃ i, T m = Sum.inl i := by
      rcases h : T m with i | j
      · exact ⟨i, rfl⟩
      · rw [h] at hc; simp [hcl] at hc
    have hiA : i ∈ A₀ := by
      have := hTS (mem_rowsT T m)
      rw [hi] at this
      simpa [barK, Finset.inl_mem_disjSum] using this
    have hne' : i ≠ i₀ := fun h => hne (by rw [hi, h])
    have := hclass i hiA hne'
    rw [rhoT, hi]; linarith
  have hkeyc' : ∀ m, |kapC a y cl T (R.map (inlE ι κ)) x m
      - kapC a y cl T (US.map (inlE ι κ)) x m| ≤ k * η := hkeyc
  have hnorm' : IsNormal a y (base ∪ US.map (inlE ι κ)) x₀ := hSeq ▸ hnorm
  have hself' : ∀ j ∈ base ∪ US.map (inlE ι κ), cl j → 0 ≤ y j - dotp (a j) x₀ := hSeq ▸ hself
  have hcf' : ∀ j ∈ base ∪ US.map (inlE ι κ), ∀ m, |cf a T j m| ≤ 1 := hSeq ▸ hcfS
  -- знаки весов строк `T` у представителя (Лемма 7)
  have hsign : ∀ m, cl (T m) → 0 ≤ omegaT a y cl T (base ∪ R.map (inlE ι κ)) x m := by
    by_cases hA : (Sum.inl i₀ : ι ⊕ κ) ∈ rowsT T
    · have hcorner' : ∀ m, Hmat a T (base ∪ US.map (inlE ι κ)) l m
          * (rhoT a y T x m - rhoT a y T x₀ m) ≤ 0 := hSeq ▸ hcorner
      refine sf_signs_one_tight hdet hTb hdS hdR hcf' hcardSm hnorm' hself' hD hkeyc' ?_
        hcorner' ?_ hmin
      · intro m hne hc
        exact hTrow m hc (fun h => hne (hl m h))
      · intro j hj hc
        rw [← hSeq] at hj
        obtain ⟨hjS, hjT⟩ := Finset.mem_sdiff.mp hj
        obtain ⟨i, rfl⟩ : ∃ i, j = Sum.inl i := by
          rcases j with i | j
          · exact ⟨i, rfl⟩
          · simp [hcl] at hc
        have hiA : i ∈ A₀ := by simpa [barK, Finset.inl_mem_disjSum] using hjS
        have hne : i ≠ i₀ := fun h => hjT (h ▸ hA)
        refine active_of_margin hdet (hcfS _ hjS) hD ?_
        have := hclass i hiA hne
        linarith
    · refine sf_signs_no_tight hdet hTb hdS hdR hcf' hcardSm hnorm' hself' hD hkeyc' ?_
      intro m hc
      exact hTrow m hc (fun h => hA (h ▸ mem_rowsT T m))
  -- счёт: `ψ̃_S(x) ≤ ψ̃_X(x) + kζ`
  have hψ : ∀ U : Finset ι, (∀ i ∈ U, (Sum.inl i : ι ⊕ κ) ∉ rowsT T) →
      Disjoint base (U.map (inlE ι κ)) →
      psiC a y (clOff cl T) (base ∪ U.map (inlE ι κ)) x
        = psiC a y (clOff cl T) base x + scoreA a y U x := by
    intro U hU hd'
    rw [psiC, Finset.sum_union hd', Finset.sum_map, scoreA]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [show (inlE ι κ) i = Sum.inl i from rfl, resC_clOff_of_not_mem (hU i hi)]
  have hscoreX : psiC a y (clOff cl T) (barK (κ := κ) A₀) x
      ≤ psiC a y (clOff cl T) (base ∪ R.map (inlE ι κ)) x + k * ζ := by
    rw [hSeq, hψ US hnotT hdS, hψ R hRadm hdR]
    linarith
  -- ключ: `‖ω_T(X) − ω_T(S)‖² ≤ (kη√K)²`
  have hkey5 : ∑ m, (omegaT a y cl T (base ∪ R.map (inlE ι κ)) x m
      - omegaT a y cl T (barK (κ := κ) A₀) x m) ^ 2
      ≤ ((k : ℝ) * η * Real.sqrt (Fintype.card κ)) ^ 2 := by
    rw [hSeq]
    have e : ∀ m, omegaT a y cl T (base ∪ R.map (inlE ι κ)) x m
        - omegaT a y cl T (base ∪ US.map (inlE ι κ)) x m
        = -(kapC a y cl T (R.map (inlE ι κ)) x m - kapC a y cl T (US.map (inlE ι κ)) x m) := by
      intro m
      rw [omegaT_union hdR hTb, omegaT_union hdS hTb]; ring
    have hb : ∀ m, (omegaT a y cl T (base ∪ R.map (inlE ι κ)) x m
        - omegaT a y cl T (base ∪ US.map (inlE ι κ)) x m) ^ 2 ≤ ((k : ℝ) * η) ^ 2 := by
      intro m
      rw [e m, neg_sq]
      have h := hkeyc' m
      have h0 : 0 ≤ (k : ℝ) * η := le_trans (abs_nonneg _) h
      have := pow_le_pow_left₀ (abs_nonneg _) h 2
      rwa [sq_abs] at this
    calc ∑ m, (omegaT a y cl T (base ∪ R.map (inlE ι κ)) x m
          - omegaT a y cl T (base ∪ US.map (inlE ι κ)) x m) ^ 2
        ≤ ∑ _m : κ, ((k : ℝ) * η) ^ 2 := Finset.sum_le_sum fun m _ => hb m
      _ = ((k : ℝ) * η * Real.sqrt (Fintype.card κ)) ^ 2 := by
          have hK2 : Real.sqrt (Fintype.card κ : ℝ) ^ 2 = Fintype.card κ :=
            Real.sq_sqrt (Nat.cast_nonneg _)
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            show ((k : ℝ) * η * Real.sqrt (Fintype.card κ)) ^ 2
              = ((k : ℝ) * η) ^ 2 * Real.sqrt (Fintype.card κ : ℝ) ^ 2 by ring, hK2]
          ring
  have hTX : rowsT T ⊆ base ∪ R.map (inlE ι κ) := le_trans hTb Finset.subset_union_left
  have hFeq : psiC a y cl (barK (κ := κ) A₀) x₀ = phi a y (barK (κ := κ) A₀) x₀ :=
    psiC_eq_phi_of_nonneg hself
  have hstep := sf_step_eps (Δ := (k : ℝ) * η * Real.sqrt (Fintype.card κ)) (δ := k * ζ)
    (Fh := V) hdet hTS hTX hclamp hC hnorm hself hscoreX (by positivity) hkey5 hsign hε hV
    (by rw [hFeq]; exact hVF) hnode hΔε hδ x'
  rw [hFeq] at hstep
  rw [hXeq]
  exact hstep

end Core

/-! ### Одна догадка -/

section OneGuess

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- **Шаг схемы при одной догадке (Леммы 1–5, 7).** `A₀` — набор активов, `|A₀| ≤ k`, `x₀` —
двойственная точка: нормальные уравнения `barK A₀`, все активы активны,
`F = φ(barK A₀, x₀) = F_LO(A₀)`; догадка `V ≤ F ≤ 2V`; **класс:** все активы `A₀`, кроме,
быть может, одного (`i₀`), имеют вес `r_i(x₀) ≥ 2√(εV/K)`. Тогда в `sfFamily` есть кандидат
`W` с `ψ_{W̄}(x') ≥ (1 − 5ε)·F` при всех `x'`, то есть `F_LO(W) ≥ (1 − 5ε)·F_LO(A₀)`. Ни в
гипотезах, ни в схеме нет `ω`. -/
theorem sf_one_guess [Nonempty κ] (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    {A₀ : Finset ι} {x₀ : κ → ℝ} (hA₀k : A₀.card ≤ k)
    (hnorm : IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀)
    (hself : ∀ r ∈ barK (κ := κ) A₀, r.isLeft →
      0 ≤ targetsK m d r - dotp (rowsK d B G r) x₀)
    (hVF : V ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀)
    (hFV : phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀ ≤ 2 * V)
    {i₀ : ι} (hclass : ∀ i ∈ A₀, i ≠ i₀ →
      2 * Real.sqrt (ε * V / Fintype.card κ)
        ≤ targetsK m d (Sum.inl i : ι ⊕ κ) - dotp (rowsK d B G (Sum.inl i)) x₀) :
    ∃ W ∈ sfFamily m d B G k ε V La, ∀ x' : κ → ℝ,
      (1 - 5 * ε) * phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀
        ≤ psiC (rowsK d B G) (targetsK m d) (fun r => r.isLeft) (barK (κ := κ) W) x' := by
  classical
  -- максимально-объёмная `K`-ка строк `barK A₀`
  obtain ⟨T, hmax⟩ := exists_maxvol_barK (d := d) (B := B) (G := G) (S := A₀)
  have hdet : (rowMat (rowsK d B G) T).det ≠ 0 := maxvol_det_ne_zero (P := P) (Sf := Sf) hmax hG hPS
  have hinj := injective_of_det_ne_zero hdet
  have hTS : rowsT T ⊆ barK (κ := κ) A₀ := by
    intro r hr
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hr
    exact hmax.1 l
  have hcfS : ∀ j ∈ barK (κ := κ) A₀, ∀ mm, |cf (rowsK d B G) T j mm| ≤ 1 :=
    fun j hj mm => abs_cf_le_one hmax hdet hj mm
  have hC1 := one_le_sfC (κ := κ) hk1
  have hK0 := card_pos_real (κ := κ)
  have hclamp : ∀ v, gram (rowsK d B G) (barK (κ := κ) A₀) v
      ≤ sfC κ k * gramK (rowsK d B G) T v := by
    intro v
    refine le_trans (gram_le_card_mul_gramK hmax hdet v) ?_
    refine mul_le_mul_of_nonneg_right ?_ (gramK_nonneg _ _ _)
    rw [sfC_eq, card_barK]; push_cast
    have : (A₀.card : ℝ) ≤ k := by exact_mod_cast hA₀k
    nlinarith
  -- индекс `l` строки `i₀` в `T` (если она там есть)
  obtain ⟨l, hl⟩ : ∃ l : κ, ∀ mm, T mm = Sum.inl i₀ → mm = l := by
    by_cases h : ∃ l, T l = Sum.inl i₀
    · obtain ⟨l, hl⟩ := h
      exact ⟨l, fun mm hm => hinj (hm.trans hl.symm)⟩
    · exact ⟨Classical.arbitrary κ, fun mm hm => absurd ⟨mm, hm⟩ h⟩
  have hs0 := sfStep_pos (κ := κ) hk1 hε hV
  have hη0 := sfEta_pos (κ := κ) hk1 hε hV
  have hζ0 := sfZeta_pos hk1 hε hV
  -- угловой узел ячейки решётки
  obtain ⟨z, hzc, hzs, hzb⟩ := exists_corner hs0 (rhoT (rowsK d B G) (targetsK m d) T x₀)
    (Hmat (rowsK d B G) T (barK (κ := κ) A₀) l)
  obtain ⟨x, hx⟩ : ∃ x, x = sfNode (rowsK d B G) (targetsK m d) T (sfStep κ k ε V) z :=
    ⟨_, rfl⟩
  have hrho : ∀ mm, rhoT (rowsK d B G) (targetsK m d) T x mm = sfStep κ k ε V * z mm := by
    rw [hx]; exact sfNode_rho hdet _ z
  have hD : ∀ mm, |rhoT (rowsK d B G) (targetsK m d) T x mm
      - rhoT (rowsK d B G) (targetsK m d) T x₀ mm| ≤ sfStep κ k ε V := by
    intro mm; rw [hrho]; exact hzs mm
  have hcorner : ∀ mm, Hmat (rowsK d B G) T (barK (κ := κ) A₀) l mm
      * (rhoT (rowsK d B G) (targetsK m d) T x mm - rhoT (rowsK d B G) (targetsK m d) T x₀ mm)
      ≤ 0 := by
    intro mm; rw [hrho]; exact hzc mm
  have hΔρ2 : ∑ mm, (rhoT (rowsK d B G) (targetsK m d) T x mm
      - rhoT (rowsK d B G) (targetsK m d) T x₀ mm) ^ 2
      ≤ Fintype.card κ * sfStep κ k ε V ^ 2 := by
    calc ∑ mm, (rhoT (rowsK d B G) (targetsK m d) T x mm
          - rhoT (rowsK d B G) (targetsK m d) T x₀ mm) ^ 2
        ≤ ∑ _mm : κ, sfStep κ k ε V ^ 2 := by
          refine Finset.sum_le_sum fun mm _ => ?_
          have h := pow_le_pow_left₀ (abs_nonneg _) (hD mm) 2
          rwa [sq_abs] at h
      _ = Fintype.card κ * sfStep κ k ε V ^ 2 := by simp
  -- номер узла в коробке `[−Z, Z]^K`
  have hzZ : z ∈ nodeBox (κ := κ) (sfZ κ k ε) := by
    refine mem_nodeBox_of_abs_le fun mm => ?_
    have hρ0 : |rhoT (rowsK d B G) (targetsK m d) T x₀ mm| ≤ Real.sqrt (2 * V) := by
      have hsq1 : (rhoT (rowsK d B G) (targetsK m d) T x₀ mm) ^ 2
          ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀ := by
        have h1 := Finset.single_le_sum
          (f := fun r => (dotp (rowsK d B G r) x₀ - targetsK m d r) ^ 2)
          (fun _ _ => sq_nonneg _) (hmax.1 mm)
        have h2 : (rhoT (rowsK d B G) (targetsK m d) T x₀ mm) ^ 2
            = (dotp (rowsK d B G (T mm)) x₀ - targetsK m d (T mm)) ^ 2 := by
          simp only [rhoT]; ring
        rw [h2, phi]; exact h1
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
    have hb : |rhoT (rowsK d B G) (targetsK m d) T x₀ mm| / sfStep κ k ε V
        ≤ sfC κ k * Real.sqrt (2 * Fintype.card κ / ε) := by
      rw [div_le_iff₀ hs0, sf_node_radius hk1 hε hV]; exact hρ0
    have hceil : sfC κ k * Real.sqrt (2 * Fintype.card κ / ε)
        ≤ (⌈sfC κ k * Real.sqrt (2 * Fintype.card κ / ε)⌉₊ : ℝ) := Nat.le_ceil _
    have hz := hzb mm
    rw [sfZ]; push_cast
    linarith
  -- счёт `U_S = A₀ ∖ T` в узле: `≤ (2+ε)V`
  have hscoreUS : scoreA (rowsK d B G) (targetsK m d) (A₀ \ assetsT T) x ≤ (2 + ε) * V := by
    have h1 : scoreA (rowsK d B G) (targetsK m d) (A₀ \ assetsT T) x
        ≤ psiC (rowsK d B G) (targetsK m d) (fun r => r.isLeft) (barK (κ := κ) A₀) x := by
      have hsub : (A₀ \ assetsT T).map (inlE ι κ) ⊆ barK (κ := κ) A₀ := by
        intro r hr
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hr
        exact inl_mem_barK (Finset.mem_sdiff.mp hi).1
      have := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (f := fun r => resC (rowsK d B G) (targetsK m d) (fun r => r.isLeft) r x ^ 2)
        (fun _ _ _ => sq_nonneg _)
      rw [Finset.sum_map] at this
      exact this
    have h2 := sf_node hclamp hnorm hself x
    have h3 : psiC (rowsK d B G) (targetsK m d) (fun r => r.isLeft) (barK (κ := κ) A₀) x₀
        = phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀ := psiC_eq_phi_of_nonneg hself
    have h4 := mul_le_mul_of_nonneg_left hΔρ2 (by linarith : (0:ℝ) ≤ sfC κ k)
    have h5 := sfC_K_step_sq (κ := κ) hk1 hε hV
    linarith
  -- представитель корзины
  have hUSk : (A₀ \ assetsT T).card ≤ k :=
    le_trans (Finset.card_le_card Finset.sdiff_subset) hA₀k
  have hZk : Real.sqrt ((A₀ \ assetsT T).card
        * scoreA (rowsK d B G) (targetsK m d) (A₀ \ assetsT T) x) / sfEta κ k ε V + k
      ≤ sfZk κ k ε := by
    have h1 : Real.sqrt ((A₀ \ assetsT T).card
          * scoreA (rowsK d B G) (targetsK m d) (A₀ \ assetsT T) x)
        ≤ Real.sqrt ((k : ℝ) * ((2 + ε) * V)) := by
      refine Real.sqrt_le_sqrt ?_
      have hc : ((A₀ \ assetsT T).card : ℝ) ≤ k := by exact_mod_cast hUSk
      have hs0' : 0 ≤ scoreA (rowsK d B G) (targetsK m d) (A₀ \ assetsT T) x :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      exact mul_le_mul hc hscoreUS hs0' (by positivity)
    have h2 := sf_key_radius (κ := κ) hk1 hε hV
    have h3 : (k : ℝ) * Real.sqrt (Fintype.card κ) * Real.sqrt (k * (2 + ε) / ε)
        ≤ (⌈(k : ℝ) * Real.sqrt (Fintype.card κ) * Real.sqrt (k * (2 + ε) / ε)⌉ : ℝ) :=
      Int.le_ceil _
    have h4 := div_le_div_of_nonneg_right h1 hη0.le
    rw [sfZk]; push_cast
    linarith
  have hZq : scoreA (rowsK d B G) (targetsK m d) (A₀ \ assetsT T) x / sfZeta k ε V
      ≤ sfZq k ε := by
    have h1 := div_le_div_of_nonneg_right hscoreUS hζ0.le
    rw [sf_score_radius hk1 hε hV] at h1
    have h2 : (2 + ε) * (k : ℝ) / ε ≤ (⌈(2 + ε) * (k : ℝ) / ε⌉ : ℝ) := Int.le_ceil _
    rw [sfZq]
    linarith
  obtain ⟨R, hRmem, hcardR, hRadm, hkeyc, hmin, hscore⟩ :=
    sf_rep_exists (a := rowsK d B G) (y := targetsK m d) (T := T) (x := x) (l := l)
      (La := La) hk1 hη0 hζ0 hnd hall hcfS hA₀k hZk hZq
  -- значение представителя
  have hnode : sfC κ k * Real.sqrt (∑ mm, (rhoT (rowsK d B G) (targetsK m d) T x mm
      - rhoT (rowsK d B G) (targetsK m d) T x₀ mm) ^ 2) ≤ Real.sqrt (ε * V) := by
    have h1 : Real.sqrt (∑ mm, (rhoT (rowsK d B G) (targetsK m d) T x mm
        - rhoT (rowsK d B G) (targetsK m d) T x₀ mm) ^ 2)
        ≤ Real.sqrt (Fintype.card κ) * sfStep κ k ε V := by
      calc _ ≤ Real.sqrt (Fintype.card κ * sfStep κ k ε V ^ 2) := Real.sqrt_le_sqrt hΔρ2
        _ = Real.sqrt (Fintype.card κ) * sfStep κ k ε V := by
            rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hs0.le]
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ sfC κ k)
    rw [sfC_sfStep hk1] at h2
    exact h2
  have hval := sf_value_of_rep hdet hA₀k hTS hcfS hclamp (by linarith) hnorm hself hD hcorner hl
    hclass (sf_threshold hk1 hε hV) (sf_margin hk1 hε hV) hη0.le hRadm hkeyc hmin hscore
    hε.le hV.le hVF hnode (k_sfEta hk1 ε V).le (k_sfZeta hk1 ε V).le
  refine ⟨assetsT T ∪ R, ?_, hval⟩
  -- кандидат лежит в семействе
  have hRT : R ∈ sfTable m d B G k ε V T z l La := by
    unfold sfTable; rw [← hx]; exact hRmem
  have hcardW : (assetsT T ∪ R).card ≤ k := by
    have hTA : assetsT T ⊆ A₀ := assetsT_subset hTS
    calc (assetsT T ∪ R).card ≤ (assetsT T).card + R.card := Finset.card_union_le _ _
      _ = (assetsT T).card + (A₀ \ assetsT T).card := by rw [hcardR]
      _ = A₀.card := by rw [add_comm, Finset.card_sdiff_add_card_eq_card hTA]
      _ ≤ k := hA₀k
  unfold sfFamily
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter,
    Finset.mem_image]
  exact ⟨T, z, hzZ, l, ⟨R, hRT, rfl⟩, hcardW⟩

end OneGuess

/-! ### Сквозная теорема из данных -/

section MainSF

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- `F_LO(W) ≥ c` в форме портфеля: если `ψ_{W̄} ≥ c` всюду, то есть `w ≥ 0` на `W` с
`objLO(W, w) ≥ c`. -/
lemma exists_portfolio_of_psiC_ge [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {W : Finset ι} {c : ℝ}
    (h : ∀ x' : κ → ℝ, c ≤ psiC (rowsK d B G) (targetsK m d) (fun r => r.isLeft)
      (barK (κ := κ) W) x') :
    ∃ w : ι → ℝ, (∀ i ∈ W, 0 ≤ w i) ∧ c ≤ objLO m d B Sf W w := by
  obtain ⟨t₀, _, hgreat⟩ := isGreatest_objLO_psiC (m := m) (B := B) (Sf := Sf) (P := P)
    (G := G) hd hG hPS W
  obtain ⟨w, hw, hwv⟩ := hgreat.1
  exact ⟨w, hw, by rw [← hwv]; exact h t₀⟩

/-- **В семействе схемы есть хороший кандидат** при любой вилке `L ≤ F ≤ 2^(J+1)L`, если
набор `A₀` (все активы активны в `x₀`, `|A₀| ≤ k`) лежит в классе «не больше одного актива с
весом `r_i(x₀) < 2√(ε·F/K)`», `F = F_LO(A₀)`. -/
theorem exists_good_sfCandidate [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε L : ℝ} (hε : 0 < ε) (hL0 : 0 < L) {J : ℕ}
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    {A₀ : Finset ι} {x₀ : κ → ℝ} (hA₀k : A₀.card ≤ k)
    (hnorm : IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀)
    (hself : ∀ r ∈ barK (κ := κ) A₀, r.isLeft →
      0 ≤ targetsK m d r - dotp (rowsK d B G r) x₀)
    (hLF : L ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀)
    (hFJ : phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀ ≤ 2 ^ (J + 1) * L)
    {i₀ : ι} (hclass : ∀ i ∈ A₀, i ≠ i₀ →
      2 * Real.sqrt (ε * phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀
          / Fintype.card κ)
        ≤ targetsK m d (Sum.inl i : ι ⊕ κ) - dotp (rowsK d B G (Sum.inl i)) x₀) :
    ∃ W ∈ sfCandidates m d B G k ε L J La, ∃ w : ι → ℝ, (∀ i ∈ W, 0 ≤ w i) ∧
      (1 - 5 * ε) * phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀
        ≤ objLO m d B Sf W w := by
  obtain ⟨j, hjJ, hVF, hFV⟩ := exists_doubling_guess_succ J hL0 hLF hFJ
  have hV : 0 < L * 2 ^ j := by positivity
  have hclassV : ∀ i ∈ A₀, i ≠ i₀ →
      2 * Real.sqrt (ε * (L * 2 ^ j) / Fintype.card κ)
        ≤ targetsK m d (Sum.inl i : ι ⊕ κ) - dotp (rowsK d B G (Sum.inl i)) x₀ := by
    intro i hi hne
    refine le_trans ?_ (hclass i hi hne)
    have hK := card_pos_real (κ := κ)
    have : ε * (L * 2 ^ j) / Fintype.card κ
        ≤ ε * phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀ / Fintype.card κ := by
      gcongr
    have := Real.sqrt_le_sqrt this
    linarith
  obtain ⟨W, hW, hval⟩ := sf_one_guess (Sf := Sf) (P := P) hG hPS hk1 hε hV hnd hall hA₀k
    hnorm hself hVF hFV hclassV
  obtain ⟨w, hw, hwv⟩ := exists_portfolio_of_psiC_ge (Sf := Sf) (P := P) hd hG hPS hval
  refine ⟨W, ?_, w, hw, hwv⟩
  unfold sfCandidates
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (by omega), hW⟩

/-- **Схема без `ω` на классе «у оптимума не больше одной тугой строки» — из данных.**

`V = diag(d) + BΣ_fB'`, `d > 0`, `G'G = Σ_f⁻¹`, `K ≥ 1`, `k ≥ 1`, `0 < ε < 1/5`,
`L = (m_i)_+²/V_ii > 0` — значение одиночного актива (естественный выбор — максимум по `i`),
`J = ⌈log₂((Σ_i(m_i)_+²/d_i)/L)⌉`, `La` — все активы без повторов. **Класс:** у задачи есть
оптимальный набор `A₀` (`|A₀| ≤ k`, все активы активны в двойственной точке `x₀`) с не более
чем одним активом веса `r_i(x₀) < 2√(ε·OPT/K)` (`r_i(x₀) = √d_i·w*_i`, `w*` — оптимальный
портфель). Тогда семейство `sfCandidates` обладает свойствами:
(1) размер не больше `(J+1)·(M+K)^K·(2Z+1)^K·K·(|box|+1)` (`card_sfCandidates_le`) — ни `ω`,
ни величин входа, кроме числа догадок `J + 1` (логарифм отношения величин входа);
(2) у каждого кандидата не больше `k` активов; (3) лучшая пара существует; (4) для любой лучшей
пары `(R₀, w₀)` значение не меньше `(1 − 5ε)` от значения **любого** long-only портфеля с не
более чем `k` именами, а полностью инвестированный портфель `w₀/Σw₀` имеет коэффициент Шарпа
не меньше `√(1 − 5ε)` от коэффициента Шарпа любого такого портфеля с положительной доходностью. -/
theorem main_theorem_sf [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε L : ℝ} (hε : 0 < ε) (hε1 : 5 * ε < 1)
    (hL0 : 0 < L) (hLatt : ∃ i, max (m i) 0 ^ 2 / Vmat d B Sf i i = L)
    {J : ℕ} (hJ : J = ⌈Real.logb 2 ((∑ i, max (m i) 0 ^ 2 / d i) / L)⌉₊)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    (hclass : ∃ (A₀ : Finset ι) (x₀ : κ → ℝ), A₀.card ≤ k
      ∧ IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀
      ∧ (∀ r ∈ barK (κ := κ) A₀, r.isLeft → 0 ≤ targetsK m d r - dotp (rowsK d B G r) x₀)
      ∧ (∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
          objLO m d B Sf S' u ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀)
      ∧ ∃ i₀ : ι, ∀ i ∈ A₀, i ≠ i₀ →
          2 * Real.sqrt (ε * phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀
              / Fintype.card κ)
            ≤ targetsK m d (Sum.inl i : ι ⊕ κ) - dotp (rowsK d B G (Sum.inl i)) x₀) :
    (sfCandidates m d B G k ε L J La).card
        ≤ (J + 1) * ((Fintype.card ι + Fintype.card κ) ^ Fintype.card κ
          * ((2 * sfZ κ k ε + 1) ^ Fintype.card κ
            * (Fintype.card κ * (sfBoxBound κ k ε + 1))))
    ∧ (∀ W ∈ sfCandidates m d B G k ε L J La, W.card ≤ k)
    ∧ (∃ R₀ ∈ sfCandidates m d B G k ε L J La, ∃ w₀ : ι → ℝ,
        (∀ i ∈ R₀, 0 ≤ w₀ i) ∧
        ∀ R ∈ sfCandidates m d B G k ε L J La, ∀ w : ι → ℝ,
          (∀ i ∈ R, 0 ≤ w i) → objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀)
    ∧ ∀ R₀ ∈ sfCandidates m d B G k ε L J La, ∀ w₀ : ι → ℝ,
        (∀ i ∈ R₀, 0 ≤ w₀ i) →
        (∀ R ∈ sfCandidates m d B G k ε L J La, ∀ w : ι → ℝ,
          (∀ i ∈ R, 0 ≤ w i) → objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀) →
        R₀.card ≤ k
        ∧ (∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
            (1 - 5 * ε) * objLO m d B Sf S' u ≤ objLO m d B Sf R₀ w₀)
        ∧ (∀ i ∈ R₀, 0 ≤ (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i)
        ∧ ∑ i ∈ R₀, (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i = 1
        ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
            0 < pRet m S' u →
            Real.sqrt (1 - 5 * ε) * sharpe m d B Sf S' u
              ≤ sharpe m d B Sf R₀ (fun i => (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i) := by
  obtain ⟨A₀, x₀, hA₀k, hnorm, hself, hopt, i₀, hcl⟩ := hclass
  set F := phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀ with hF
  -- вилка `[L, 2^(J+1)L]` без `ω`
  obtain ⟨ia, hia⟩ := hLatt
  have hLF : L ≤ F := hia ▸ opt_ge_single_of_opt (B := B) hd hG hPS hk1 hopt ia
  have hFU : F ≤ ∑ i, max (m i) 0 ^ 2 / d i := by
    -- `F = F_LO(A₀)` достигается портфелем `w ≥ 0`
    have hmin : ∀ t, psiC (rowsK d B G) (targetsK m d) (fun r => r.isLeft) (barK (κ := κ) A₀) x₀
        ≤ psiC (rowsK d B G) (targetsK m d) (fun r => r.isLeft) (barK (κ := κ) A₀) t :=
      psiC_min_of_normal_of_nonneg hnorm hself
    obtain ⟨w, hw, hwv⟩ := exists_portfolio_of_psiC_ge (Sf := Sf) (P := P) (W := A₀) hd hG hPS hmin
    rw [psiC_eq_phi_of_nonneg hself] at hwv
    refine le_trans hwv (le_trans (objLO_le_sum_posPart (B := B) hd hG hPS hw) ?_)
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A₀) ?_
    intro i _ _
    have := hd i
    positivity
  have hq1 : (1:ℝ) ≤ (∑ i, max (m i) 0 ^ 2 / d i) / L := by
    rw [le_div_iff₀ hL0]; linarith
  obtain ⟨hJa, _⟩ := guess_count_spec hq1
  rw [← hJ] at hJa
  have hFJ : F ≤ 2 ^ (J + 1) * L := by
    have h1 : ∑ i, max (m i) 0 ^ 2 / d i ≤ 2 ^ J * L := by
      rwa [div_le_iff₀ hL0] at hJa
    have h2 : (2:ℝ) ^ J * L ≤ 2 ^ (J + 1) * L := by
      rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) J]
    linarith
  obtain ⟨W, hW, w, hw, hgood⟩ := exists_good_sfCandidate (Sf := Sf) (P := P) hd hG hPS hk1
    hε hL0 hnd hall hA₀k hnorm hself hLF hFJ hcl
  refine ⟨card_sfCandidates_le m d B G k ε L J La,
    fun R hR => card_le_of_mem_sfCandidates hR,
    exists_best_set_of_family (P := P) (G := G) hd hG hPS ⟨W, hW⟩, ?_⟩
  intro R₀ hR₀ w₀ hw₀ hbest
  have hval : (1 - 5 * ε) * F ≤ objLO m d B Sf R₀ w₀ := le_trans hgood (hbest W hW w hw)
  have hval' : (1 - 2 * (5 * ε / 2)) * F ≤ objLO m d B Sf R₀ w₀ := by
    rw [show 1 - 2 * (5 * ε / 2) = 1 - 5 * ε by ring]; exact hval
  obtain ⟨hx0, hx1, hxs⟩ := best_pair_sharpe_uniform (B := B) hd hG hPS
    (by linarith : 5 * ε / 2 < 1 / 2) (lt_of_lt_of_le hL0 hLF) hopt hw₀ hval'
  refine ⟨card_le_of_mem_sfCandidates hR₀, fun S' hS' u hu => ?_, hx0, hx1,
    fun S' hS' u hu hru => ?_⟩
  · have hub := hopt S' hS' u hu
    have hcoef : (0:ℝ) ≤ 1 - 5 * ε := by linarith
    linarith [mul_le_mul_of_nonneg_left hub hcoef]
  · have := hxs S' hS' u hu hru
    rwa [show 1 - 2 * (5 * ε / 2) = 1 - 5 * ε by ring] at this

end MainSF

/-! ### Непустота гипотез сквозной теоремы

Один актив, один фактор: `m = d = 1`, `B = Σ_f = G = P = 1` (так что `V = 2`), `k = 1`,
`ε = 1/10`, `L = 1/2` (значение одиночного актива), `J = ⌈log₂ 2⌉ = 1`, порядок `[0]`.
Оптимум `A₀ = {0}`, двойственная точка `x₀ = 1/2`, `OPT = 1/2`; класс выполнен (единственный
актив — сам `i₀`). Все гипотезы `main_theorem_sf` выполнены; заключение даёт лучшую пару
со значением `≥ (1 − 5ε)·OPT = 1/4`. -/
/-- Единичный вектор и единичная матрица `1 × 1` для примера. -/
noncomputable def oneV : Fin 1 → ℝ := fun _ => 1

/-- Матрица `1 × 1` из единицы. -/
noncomputable def oneM : Fin 1 → Fin 1 → ℝ := fun _ _ => 1

theorem sf_instance :
    ∃ R₀ ∈ sfCandidates oneV oneV oneM oneM 1 (1 / 10) (1 / 2) 1 [0],
      ∃ w₀ : Fin 1 → ℝ, (∀ i ∈ R₀, 0 ≤ w₀ i) ∧
        (1 / 4 : ℝ) ≤ objLO oneV oneV oneM oneM R₀ w₀ := by
  have hd : ∀ i, 0 < oneV i := fun _ => one_pos
  have hG : ∀ j j' : Fin 1, ∑ l : Fin 1, oneM l j * oneM l j' = oneM j j' := by
    intro j j'; simp [oneM]
  have hPS : ∀ j j' : Fin 1, ∑ l : Fin 1, oneM j l * oneM l j' = if j = j' then 1 else 0 := by
    intro j j'; simp [oneM, Subsingleton.elim j j']
  have hVd : ∀ i, Vmat oneV oneM oneM i i = 2 := by
    intro i; simp [Vmat, oneV, oneM]; norm_num
  have hLatt : ∃ i, max (oneV i) 0 ^ 2 / Vmat oneV oneM oneM i i = 1 / 2 :=
    ⟨0, by rw [hVd]; simp [oneV]⟩
  have hJlog : (1:ℕ) = ⌈Real.logb 2 ((∑ i, max (oneV i) 0 ^ 2 / oneV i) / (1 / 2))⌉₊ := by
    have h2 : (∑ i, max (oneV i) 0 ^ 2 / oneV i) / (1 / 2) = 2 := by norm_num [oneV]
    rw [h2, Real.logb_self_eq_one (by norm_num)]
    simp
  have hnd : ([0] : List (Fin 1)).Nodup := List.nodup_singleton 0
  have hall : ∀ i : Fin 1, i ∈ ([0] : List (Fin 1)) := by
    intro i; rw [List.mem_singleton]; exact Subsingleton.elim _ _
  -- строки: актив `(1, y = 1)`, якорь `(1, y = 0)`; двойственная точка `x₀ = 1/2`
  have hrow : ∀ (r : Fin 1 ⊕ Fin 1) (v : Fin 1 → ℝ), dotp (rowsK oneV oneM oneM r) v = v 0 := by
    intro r v
    rcases r with i | l <;> simp [rowsK, dotp, oneV, oneM]
  have hphi : phi (rowsK oneV oneM oneM) (targetsK oneV oneV) (barK (κ := Fin 1) Finset.univ)
      (fun _ => 1 / 2) = 1 / 2 := by
    simp only [phi, barK, Finset.sum_disjSum, hrow]
    simp [targetsK, oneV]; norm_num
  have hclass : ∃ (A₀ : Finset (Fin 1)) (x₀ : Fin 1 → ℝ), A₀.card ≤ 1
      ∧ IsNormal (rowsK oneV oneM oneM) (targetsK oneV oneV) (barK (κ := Fin 1) A₀) x₀
      ∧ (∀ r ∈ barK (κ := Fin 1) A₀, r.isLeft →
          0 ≤ targetsK oneV oneV r - dotp (rowsK oneV oneM oneM r) x₀)
      ∧ (∀ S' : Finset (Fin 1), S'.card ≤ 1 → ∀ u : Fin 1 → ℝ, (∀ i ∈ S', 0 ≤ u i) →
          objLO oneV oneV oneM oneM S' u
            ≤ phi (rowsK oneV oneM oneM) (targetsK oneV oneV) (barK (κ := Fin 1) A₀) x₀)
      ∧ ∃ i₀ : Fin 1, ∀ i ∈ A₀, i ≠ i₀ →
          2 * Real.sqrt ((1 / 10) * phi (rowsK oneV oneM oneM) (targetsK oneV oneV)
              (barK (κ := Fin 1) A₀) x₀ / Fintype.card (Fin 1))
            ≤ targetsK oneV oneV (Sum.inl i : Fin 1 ⊕ Fin 1)
              - dotp (rowsK oneV oneM oneM (Sum.inl i)) x₀ := by
    refine ⟨Finset.univ, fun _ => 1 / 2, by simp, ?_, ?_, ?_, ⟨0, fun i _ hi => absurd
      (Subsingleton.elim i 0) hi⟩⟩
    · intro v
      simp only [mom, barK, Finset.sum_disjSum, hrow]
      simp [targetsK, oneV]; ring
    · intro r _ hr
      rcases r with i | l
      · rw [hrow]; simp [targetsK, oneV]; norm_num
      · simp at hr
    · intro S' hS' u hu
      rw [hphi]
      refine le_trans (objLO_le_QLO (P := oneM) (G := oneM) hd hG hPS hu (fun _ => 1 / 2)) ?_
      have hS'1 : (S'.card : ℝ) ≤ 1 := by exact_mod_cast hS'
      have hq : QLO oneV oneV oneM oneM S' (fun _ => 1 / 2) = 1 / 4 + S'.card * (1 / 4) := by
        simp [QLO, quadf, dotp, oneM, oneV, Finset.sum_const]
        norm_num
      rw [hq]; linarith
  obtain ⟨_, _, ⟨R₀, hR₀, w₀, hw₀, hbest⟩, hall4⟩ := main_theorem_sf (m := oneV) (d := oneV)
    (B := oneM) (Sf := oneM) (P := oneM) (G := oneM) hd hG hPS (k := 1) le_rfl (ε := 1 / 10)
    (by norm_num) (by norm_num) (by norm_num : (0:ℝ) < 1 / 2) hLatt hJlog hnd hall hclass
  obtain ⟨_, hval, _⟩ := hall4 R₀ hR₀ w₀ hw₀ hbest
  refine ⟨R₀, hR₀, w₀, hw₀, ?_⟩
  have h1 := hval Finset.univ (by simp) (fun _ => 1 / 2) (fun _ _ => by norm_num)
  have h2 : objLO oneV oneV oneM oneM Finset.univ (fun _ => 1 / 2) = 1 / 2 := by
    simp [objLO, Vmat, oneV, oneM]; norm_num
  rw [h2] at h1
  linarith

/-! ### Непустота класса: два актива, ровно один тугой

Один фактор, два актива: `m = (3, 8/5)`, `d = 1`, `B = (1, 1)`, `Σ_f = G = P = 1`, `k = 2`,
`ε = 1/100`, `L = 9/2` (значение первого актива), `J = ⌈log₂(578/225)⌉ = 2`, порядок `[0, 1]`.
Оптимум `A₀ = {0, 1}`, двойственная точка `x₀ = 23/15`, веса (невязки) `r = (22/15, 1/15)`,
`OPT = 338/75`. Порог класса `2√(ε·OPT/K) ≈ 0.42`: актив `1` (`r = 1/15`) — тугой (`i₀ = 1`),
актив `0` (`r = 22/15`) — нет; гипотеза класса проверяется содержательно. Заключение: лучшая пара
со значением `≥ (1 − 5ε)·OPT = (19/20)·(338/75)`. -/

/-- Доходности примера с двумя активами. -/
noncomputable def twoM : Fin 2 → ℝ := ![3, 8 / 5]

/-- Остаточные дисперсии примера с двумя активами. -/
noncomputable def twoD : Fin 2 → ℝ := fun _ => 1

/-- Нагрузки примера с двумя активами. -/
noncomputable def twoB : Fin 2 → Fin 1 → ℝ := fun _ _ => 1

theorem sf_instance_two :
    ∃ R₀ ∈ sfCandidates twoM twoD twoB oneM 2 (1 / 100) (9 / 2) 2 [0, 1],
      ∃ w₀ : Fin 2 → ℝ, (∀ i ∈ R₀, 0 ≤ w₀ i) ∧
        (19 / 20 : ℝ) * (338 / 75) ≤ objLO twoM twoD twoB oneM R₀ w₀ := by
  have hd : ∀ i, 0 < twoD i := fun _ => one_pos
  have hG : ∀ j j' : Fin 1, ∑ l : Fin 1, oneM l j * oneM l j' = oneM j j' := by
    intro j j'; simp [oneM]
  have hPS : ∀ j j' : Fin 1, ∑ l : Fin 1, oneM j l * oneM l j' = if j = j' then 1 else 0 := by
    intro j j'; simp [oneM, Subsingleton.elim j j']
  have hVd : ∀ i, Vmat twoD twoB oneM i i = 2 := by
    intro i; simp [Vmat, twoD, twoB, oneM]; norm_num
  have hLatt : ∃ i, max (twoM i) 0 ^ 2 / Vmat twoD twoB oneM i i = 9 / 2 :=
    ⟨0, by rw [hVd]; norm_num [twoM]⟩
  have hJlog : (2:ℕ) = ⌈Real.logb 2 ((∑ i, max (twoM i) 0 ^ 2 / twoD i) / (9 / 2))⌉₊ := by
    have h2 : (∑ i, max (twoM i) 0 ^ 2 / twoD i) / (9 / 2) = 578 / 225 := by
      norm_num [twoM, twoD, Fin.sum_univ_two]
    rw [h2]
    symm
    rw [Nat.ceil_eq_iff (by norm_num)]
    constructor
    · rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
      norm_num
    · rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
      norm_num
  have hnd : ([0, 1] : List (Fin 2)).Nodup := by decide
  have hall : ∀ i : Fin 2, i ∈ ([0, 1] : List (Fin 2)) := by decide
  have hrow : ∀ (r : Fin 2 ⊕ Fin 1) (v : Fin 1 → ℝ), dotp (rowsK twoD twoB oneM r) v = v 0 := by
    intro r v
    rcases r with i | l <;> simp [rowsK, dotp, twoD, twoB, oneM]
  have htgt : ∀ i : Fin 2, targetsK twoM twoD (Sum.inl i : Fin 2 ⊕ Fin 1) = twoM i := by
    intro i; simp [targetsK, twoD]
  have hphi : phi (rowsK twoD twoB oneM) (targetsK twoM twoD) (barK (κ := Fin 1) Finset.univ)
      (fun _ => 23 / 15) = 338 / 75 := by
    simp only [phi, barK, Finset.sum_disjSum, hrow, htgt]
    simp [targetsK, twoM, Fin.sum_univ_two]; norm_num
  have hclass : ∃ (A₀ : Finset (Fin 2)) (x₀ : Fin 1 → ℝ), A₀.card ≤ 2
      ∧ IsNormal (rowsK twoD twoB oneM) (targetsK twoM twoD) (barK (κ := Fin 1) A₀) x₀
      ∧ (∀ r ∈ barK (κ := Fin 1) A₀, r.isLeft →
          0 ≤ targetsK twoM twoD r - dotp (rowsK twoD twoB oneM r) x₀)
      ∧ (∀ S' : Finset (Fin 2), S'.card ≤ 2 → ∀ u : Fin 2 → ℝ, (∀ i ∈ S', 0 ≤ u i) →
          objLO twoM twoD twoB oneM S' u
            ≤ phi (rowsK twoD twoB oneM) (targetsK twoM twoD) (barK (κ := Fin 1) A₀) x₀)
      ∧ ∃ i₀ : Fin 2, ∀ i ∈ A₀, i ≠ i₀ →
          2 * Real.sqrt ((1 / 100) * phi (rowsK twoD twoB oneM) (targetsK twoM twoD)
              (barK (κ := Fin 1) A₀) x₀ / Fintype.card (Fin 1))
            ≤ targetsK twoM twoD (Sum.inl i : Fin 2 ⊕ Fin 1)
              - dotp (rowsK twoD twoB oneM (Sum.inl i)) x₀ := by
    refine ⟨Finset.univ, fun _ => 23 / 15, by simp, ?_, ?_, ?_, ⟨1, fun i _ hi => ?_⟩⟩
    · intro v
      simp only [mom, barK, Finset.sum_disjSum, hrow, htgt]
      simp [targetsK, twoM, Fin.sum_univ_two]; ring
    · intro r _ hr
      rcases r with i | l
      · rw [hrow, htgt]; fin_cases i <;> norm_num [twoM]
      · simp at hr
    · intro S' _ u hu
      rw [hphi]
      refine le_trans (objLO_le_QLO (P := oneM) (G := oneM) hd hG hPS hu (fun _ => 23 / 15)) ?_
      have hq : QLO twoM twoD twoB oneM S' (fun _ => 23 / 15)
          ≤ QLO twoM twoD twoB oneM Finset.univ (fun _ => 23 / 15) := by
        simp only [QLO]
        have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S')
          (f := fun i => (max (twoM i - dotp (twoB i) (fun _ => (23 : ℝ) / 15)) 0) ^ 2 / twoD i)
          (fun i _ _ => div_nonneg (sq_nonneg _) (hd i).le)
        linarith
      have hu : QLO twoM twoD twoB oneM Finset.univ (fun _ => 23 / 15) = 338 / 75 := by
        simp [QLO, quadf, dotp, oneM, twoM, twoD, twoB, Fin.sum_univ_two]; norm_num
      linarith
    · -- единственный нетугой актив — `0`: `2√(ε·OPT) ≤ 22/15`
      have hi0 : i = 0 := by
        fin_cases i
        · rfl
        · exact absurd rfl hi
      subst hi0
      rw [hphi, htgt, hrow]
      have hs : Real.sqrt ((1 / 100) * (338 / 75) / ((Fintype.card (Fin 1) : ℕ) : ℝ))
          ≤ Real.sqrt ((11 / 15) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        norm_num
      rw [Real.sqrt_sq (by norm_num)] at hs
      norm_num [twoM] at hs ⊢
      linarith
  obtain ⟨_, _, ⟨R₀, hR₀, w₀, hw₀, hbest⟩, hall4⟩ := main_theorem_sf (m := twoM) (d := twoD)
    (B := twoB) (Sf := oneM) (P := oneM) (G := oneM) hd hG hPS (k := 2) (by norm_num)
    (ε := 1 / 100) (by norm_num) (by norm_num) (by norm_num : (0:ℝ) < 9 / 2) hLatt hJlog hnd
    hall hclass
  obtain ⟨_, hval, _⟩ := hall4 R₀ hR₀ w₀ hw₀ hbest
  refine ⟨R₀, hR₀, w₀, hw₀, ?_⟩
  have h1 := hval Finset.univ (by simp) (fun i => if i = 0 then 22 / 15 else 1 / 15)
    (fun i _ => by split_ifs <;> norm_num)
  have h2 : objLO twoM twoD twoB oneM Finset.univ (fun i => if i = 0 then 22 / 15 else 1 / 15)
      = 338 / 75 := by
    simp [objLO, Vmat, twoM, twoD, twoB, oneM, Fin.sum_univ_two]; norm_num
  rw [h2] at h1
  linarith

/-! ### Непустота гипотез при `K = 2` факторах

Один актив, два фактора: `m = d = 1`, `B = (1, 0)` (`B₀₀ = 1`, `B₀₁ = 0`), `Σ_f = G = P = I₂`
(так что `V₀₀ = d₀ + BΣ_fB' = 2`), `k = 1`, `ε = 1/10`, `L = m²/V₀₀ = 1/2` (значение
одиночного актива), `J = ⌈log₂((m²/d)/L)⌉ = ⌈log₂ 2⌉ = 1`, порядок `[0]`. Строки `barK {0}`:
строка актива `B₀/√d₀ = (1, 0)` с целью `m/√d = 1` и две якорные строки — строки `G`, `(1, 0)`
и `(0, 1)`, с целью `0`. Оптимум `A₀ = {0}`, двойственная точка (минимум наименьших квадратов)
`x₀ = (1/2, 0)`, `OPT = φ = 1/4 + 1/4 + 0 = 1/2`, невязка актива `1/2 ≥ 0`; оптимальность —
слабая двойственность `objLO ≤ QLO(x₀) = 1/4 + |S'|/4 ≤ 1/2`; класс выполнен (единственный
актив — сам `i₀`). Все гипотезы `main_theorem_sf` выполнены при `K = 2`; заключение — как в
`sf_instance`: лучшая пара со значением `≥ (1 − 5ε)·OPT = 1/4`. -/

/-- Нагрузки примера с двумя факторами: `B = (1, 0)`. -/
noncomputable def k2B : Fin 1 → Fin 2 → ℝ := fun _ => ![1, 0]

/-- Единичная матрица `2 × 2` (`Σ_f = G = P = I₂`) для примера с двумя факторами. -/
noncomputable def k2I : Fin 2 → Fin 2 → ℝ := fun j j' => if j = j' then 1 else 0

theorem sf_instance_K2 :
    ∃ R₀ ∈ sfCandidates oneV oneV k2B k2I 1 (1 / 10) (1 / 2) 1 [0],
      ∃ w₀ : Fin 1 → ℝ, (∀ i ∈ R₀, 0 ≤ w₀ i) ∧
        (1 / 4 : ℝ) ≤ objLO oneV oneV k2B k2I R₀ w₀ := by
  have hd : ∀ i, 0 < oneV i := fun _ => one_pos
  have hG : ∀ j j' : Fin 2, ∑ l : Fin 2, k2I l j * k2I l j' = k2I j j' := by
    intro j j'; fin_cases j <;> fin_cases j' <;> simp [k2I]
  have hPS : ∀ j j' : Fin 2, ∑ l : Fin 2, k2I j l * k2I l j' = if j = j' then 1 else 0 := by
    intro j j'; fin_cases j <;> fin_cases j' <;> simp [k2I]
  have hVd : ∀ i, Vmat oneV k2B k2I i i = 2 := by
    intro i; simp [Vmat, oneV, k2B, k2I, Fin.sum_univ_two]; norm_num
  have hLatt : ∃ i, max (oneV i) 0 ^ 2 / Vmat oneV k2B k2I i i = 1 / 2 :=
    ⟨0, by rw [hVd]; simp [oneV]⟩
  have hJlog : (1:ℕ) = ⌈Real.logb 2 ((∑ i, max (oneV i) 0 ^ 2 / oneV i) / (1 / 2))⌉₊ := by
    have h2 : (∑ i, max (oneV i) 0 ^ 2 / oneV i) / (1 / 2) = 2 := by norm_num [oneV]
    rw [h2, Real.logb_self_eq_one (by norm_num)]
    simp
  have hnd : ([0] : List (Fin 1)).Nodup := List.nodup_singleton 0
  have hall : ∀ i : Fin 1, i ∈ ([0] : List (Fin 1)) := by
    intro i; rw [List.mem_singleton]; exact Subsingleton.elim _ _
  -- строки: актив `(1, 0)` с целью `1`, якорные `(1, 0)`, `(0, 1)` с целью `0`; `x₀ = (1/2, 0)`
  have hrowL : ∀ (i : Fin 1) (v : Fin 2 → ℝ), dotp (rowsK oneV k2B k2I (Sum.inl i)) v = v 0 := by
    intro i v; simp [rowsK, dotp, oneV, k2B, Fin.sum_univ_two]
  have hrowR : ∀ (l : Fin 2) (v : Fin 2 → ℝ), dotp (rowsK oneV k2B k2I (Sum.inr l)) v = v l := by
    intro l v; simp [rowsK, dotp, k2I]
  have hphi : phi (rowsK oneV k2B k2I) (targetsK oneV oneV) (barK (κ := Fin 2) Finset.univ)
      ![1 / 2, 0] = 1 / 2 := by
    simp only [phi, barK, Finset.sum_disjSum, hrowL, hrowR]
    simp [targetsK, oneV, Fin.sum_univ_two]; norm_num
  have hclass : ∃ (A₀ : Finset (Fin 1)) (x₀ : Fin 2 → ℝ), A₀.card ≤ 1
      ∧ IsNormal (rowsK oneV k2B k2I) (targetsK oneV oneV) (barK (κ := Fin 2) A₀) x₀
      ∧ (∀ r ∈ barK (κ := Fin 2) A₀, r.isLeft →
          0 ≤ targetsK oneV oneV r - dotp (rowsK oneV k2B k2I r) x₀)
      ∧ (∀ S' : Finset (Fin 1), S'.card ≤ 1 → ∀ u : Fin 1 → ℝ, (∀ i ∈ S', 0 ≤ u i) →
          objLO oneV oneV k2B k2I S' u
            ≤ phi (rowsK oneV k2B k2I) (targetsK oneV oneV) (barK (κ := Fin 2) A₀) x₀)
      ∧ ∃ i₀ : Fin 1, ∀ i ∈ A₀, i ≠ i₀ →
          2 * Real.sqrt ((1 / 10) * phi (rowsK oneV k2B k2I) (targetsK oneV oneV)
              (barK (κ := Fin 2) A₀) x₀ / Fintype.card (Fin 2))
            ≤ targetsK oneV oneV (Sum.inl i : Fin 1 ⊕ Fin 2)
              - dotp (rowsK oneV k2B k2I (Sum.inl i)) x₀ := by
    refine ⟨Finset.univ, ![1 / 2, 0], by simp, ?_, ?_, ?_, ⟨0, fun i _ hi => absurd
      (Subsingleton.elim i 0) hi⟩⟩
    · intro v
      simp only [mom, barK, Finset.sum_disjSum, hrowL, hrowR]
      simp [targetsK, oneV, Fin.sum_univ_two]; ring
    · intro r _ hr
      rcases r with i | l
      · rw [hrowL]; simp [targetsK, oneV]; norm_num
      · simp at hr
    · intro S' hS' u hu
      rw [hphi]
      refine le_trans (objLO_le_QLO (P := k2I) (G := k2I) hd hG hPS hu ![1 / 2, 0]) ?_
      have hS'1 : (S'.card : ℝ) ≤ 1 := by exact_mod_cast hS'
      have hq : QLO oneV oneV k2B k2I S' ![1 / 2, 0] = 1 / 4 + S'.card * (1 / 4) := by
        simp [QLO, quadf, dotp, k2I, oneV, k2B, Fin.sum_univ_two, Finset.sum_const]
        norm_num
      rw [hq]; linarith
  obtain ⟨_, _, ⟨R₀, hR₀, w₀, hw₀, hbest⟩, hall4⟩ := main_theorem_sf (m := oneV) (d := oneV)
    (B := k2B) (Sf := k2I) (P := k2I) (G := k2I) hd hG hPS (k := 1) le_rfl (ε := 1 / 10)
    (by norm_num) (by norm_num) (by norm_num : (0:ℝ) < 1 / 2) hLatt hJlog hnd hall hclass
  obtain ⟨_, hval, _⟩ := hall4 R₀ hR₀ w₀ hw₀ hbest
  refine ⟨R₀, hR₀, w₀, hw₀, ?_⟩
  have h1 := hval Finset.univ (by simp) (fun _ => 1 / 2) (fun _ _ => by norm_num)
  have h2 : objLO oneV oneV k2B k2I Finset.univ (fun _ => 1 / 2) = 1 / 2 := by
    simp [objLO, Vmat, oneV, k2B, k2I, Fin.sum_univ_two]; norm_num
  rw [h2] at h1
  linarith

end SparseSharpe.Factor
