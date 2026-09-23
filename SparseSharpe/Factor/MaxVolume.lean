import SparseSharpe.Factor.LeastSquares

set_option linter.style.header false

/-!
# Максимально-объёмная `K`-ка строк: коэффициенты Крамера и зажим формы Грама

Это **замена Леммы G при `K ≥ 2`**. В одномерном случае сетка строилась вокруг точек
`r_j = m_j/β_j` «самого тяжёлого» актива. При `K ≥ 2` нуль-множество актива —
гиперплоскость, и понятие «самый тяжёлый» от направления зависит. Правильный
K-мерный заменитель — **максимально-объёмная `K`-ка строк**: набор `T = (T_1,…,T_K)`
индексов из `S`, на котором `|det[a_{T_1};…;a_{T_K}]|` максимален.

Два следствия максимальности (оба — чистая линейная алгебра):

* `abs_cf_le_one` — коэффициенты разложения любой строки `a_i` (`i ∈ S`) по строкам
  `K`-ки не превосходят `1` по модулю. Доказательство: по правилу Крамера коэффициент
  равен отношению двух определителей, и числитель — определитель `K`-ки `T` с заменой
  `T_l → i`, то есть тоже `K`-ки из `S`;
* `gram_le` и `le_gram` — **зажим формы Грама**: в координатах невязок `K`-ки

      ‖h‖² ≤ gram(S, v) ≤ |S|·K·‖h‖²,    h_l := ⟨a_{T_l}, v⟩.

  В матричной записи это `I ⪯ A_T^{-T} Κ(S) A_T⁻¹ ⪯ |S|K·I`. Верхняя оценка и есть
  то, из-за чего сетка по `h` с шагом `√(εV/(K·C))` даёт `φ_S(t) ≤ (1+ε)F(S)`,
  а нижняя — то, из-за чего аддитивное округление матрицы `Κ̃` оказывается
  мультипликативным (см. `Factor/FPTASK.lean`).
-/

namespace SparseSharpe.Factor

open Finset Matrix

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Матрица `K`-ки строк: строка `l` — это `a (T l)`. -/
noncomputable def rowMat (a : ι → κ → ℝ) (T : κ → ι) : Matrix κ κ ℝ :=
  Matrix.of fun l j => a (T l) j

/-- Коэффициент Крамера: доля `l`-й строки `K`-ки в разложении строки `a i`. -/
noncomputable def cf (a : ι → κ → ℝ) (T : κ → ι) (i : ι) (l : κ) : ℝ :=
  (rowMat a (Function.update T l i)).det / (rowMat a T).det

/-- «`T` максимально-объёмна в `S`»: все `T l` лежат в `S`, и `|det|` максимален. -/
def MaxVol (a : ι → κ → ℝ) (S : Finset ι) (T : κ → ι) : Prop :=
  (∀ l, T l ∈ S) ∧ ∀ T' : κ → ι, (∀ l, T' l ∈ S) → |(rowMat a T').det| ≤ |(rowMat a T).det|

variable {a : ι → κ → ℝ} {S : Finset ι} {T : κ → ι}

lemma rowMat_update (a : ι → κ → ℝ) (T : κ → ι) (l : κ) (i : ι) :
    rowMat a (Function.update T l i) = (rowMat a T).updateRow l (a i) := by
  ext l' j
  by_cases h : l' = l
  · subst h; simp [rowMat, Matrix.updateRow_apply]
  · simp [rowMat, Matrix.updateRow_apply, h, Function.update_apply]

/-- **Правило Крамера.** При `det ≠ 0` всякая строка раскладывается по `K`-ке:
`a i = Σ_l cf(i,l) · a (T l)`. Максимальность объёма здесь не нужна. -/
theorem row_eq_sum_cf (hdet : (rowMat a T).det ≠ 0) (i : ι) (j : κ) :
    a i j = ∑ l, cf a T i l * a (T l) j := by
  set M : Matrix κ κ ℝ := (rowMat a T)ᵀ with hM
  have hMdet : M.det = (rowMat a T).det := by rw [hM, Matrix.det_transpose]
  have hcr : M *ᵥ M.cramer (a i) = M.det • (a i) := Matrix.mulVec_cramer M (a i)
  have hcr_j : ∑ l, M j l * M.cramer (a i) l = M.det * a i j := by
    have := congrFun hcr j
    simpa [Matrix.mulVec, dotProduct] using this
  have hcram : ∀ l, M.cramer (a i) l = (rowMat a (Function.update T l i)).det := by
    intro l
    rw [Matrix.cramer_apply, hM, Matrix.updateCol_transpose, Matrix.det_transpose,
      rowMat_update]
  have hMentry : ∀ l, M j l = a (T l) j := by intro l; simp [hM, rowMat]
  have : ∑ l, a (T l) j * (rowMat a (Function.update T l i)).det = (rowMat a T).det * a i j := by
    rw [← hMdet, ← hcr_j]
    exact Finset.sum_congr rfl fun l _ => by rw [hMentry l, hcram l]
  have hsum : ∑ l, cf a T i l * a (T l) j
      = (∑ l, a (T l) j * (rowMat a (Function.update T l i)).det) / (rowMat a T).det := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun l _ => by rw [cf]; ring
  rw [hsum, this]
  field_simp

/-- **Максимально-объёмная `K`-ка существует**: `|det|` — функция на конечном множестве
`K`-ок со значениями в `S`, и если это множество непусто, максимум достигается. -/
theorem exists_maxvol [Fintype ι] [DecidableEq ι] (a : ι → κ → ℝ) (S : Finset ι)
    (T₀ : κ → ι) (hT₀ : ∀ l, T₀ l ∈ S) : ∃ T, MaxVol a S T := by
  classical
  set 𝒯 : Finset (κ → ι) := Finset.univ.filter (fun T => ∀ l, T l ∈ S) with h𝒯
  have hmem : T₀ ∈ 𝒯 := by simp [h𝒯, hT₀]
  obtain ⟨T, hT, hmax⟩ := 𝒯.exists_max_image (fun T => |(rowMat a T).det|) ⟨T₀, hmem⟩
  refine ⟨T, ?_, fun T' hT' => hmax T' (by simp [h𝒯, hT'])⟩
  simpa [h𝒯] using (Finset.mem_filter.mp hT).2

/-- **Ключевое следствие максимальности объёма.** Коэффициенты разложения строк
из `S` по максимально-объёмной `K`-ке не превосходят `1` по модулю. -/
theorem abs_cf_le_one (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0)
    {i : ι} (hi : i ∈ S) (l : κ) : |cf a T i l| ≤ 1 := by
  obtain ⟨hTS, hmx⟩ := hmax
  have hmem : ∀ l', Function.update T l i l' ∈ S := by
    intro l'
    by_cases h : l' = l
    · subst h; simpa using hi
    · simpa [Function.update_apply, h] using hTS l'
  have := hmx (Function.update T l i) hmem
  rw [cf, abs_div]
  rw [div_le_one (abs_pos.mpr hdet)]
  exact this



/-! ### Зажим формы Грама в координатах `K`-ки

`gramK a T v = Σ_l ⟨a_{T_l}, v⟩²` — квадрат нормы направления `v` в координатах
невязок `K`-ки. В матричной записи `gramK = ‖A_T v‖²`, а зажим
`gramK ≤ gram(S) ≤ |S|·K·gramK` — это `I ⪯ A_T^{-T}Κ(S)A_T⁻¹ ⪯ |S|K·I`. -/

/-- Квадрат нормы направления в координатах `K`-ки. -/
noncomputable def gramK (a : ι → κ → ℝ) (T : κ → ι) (v : κ → ℝ) : ℝ :=
  ∑ l, (dotp (a (T l)) v) ^ 2

lemma gramK_nonneg (a : ι → κ → ℝ) (T : κ → ι) (v : κ → ℝ) : 0 ≤ gramK a T v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Разложение скалярного произведения по `K`-ке. -/
lemma dotp_eq_sum_cf (hdet : (rowMat a T).det ≠ 0) (i : ι) (v : κ → ℝ) :
    dotp (a i) v = ∑ l, cf a T i l * dotp (a (T l)) v := by
  simp only [dotp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [row_eq_sum_cf hdet i j, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- **Поточечная часть зажима.** Для любой строки `i ∈ S` максимально-объёмной `K`-ки

    ⟨a_i,v⟩² ≤ K · gramK(v).

Это то место, где используется `|cf| ≤ 1`. -/
theorem sq_dotp_le_card_mul_gramK (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0)
    {i : ι} (hi : i ∈ S) (v : κ → ℝ) :
    (dotp (a i) v) ^ 2 ≤ (Fintype.card κ : ℝ) * gramK a T v := by
  have hdec := dotp_eq_sum_cf hdet i v
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset κ)
    (fun l => cf a T i l) (fun l => dotp (a (T l)) v)
  have hc : ∑ l, (cf a T i l) ^ 2 ≤ (Fintype.card κ : ℝ) := by
    calc ∑ l, (cf a T i l) ^ 2 ≤ ∑ _l : κ, (1:ℝ) :=
          Finset.sum_le_sum fun l _ => by
            have h := abs_cf_le_one hmax hdet hi l
            nlinarith [abs_nonneg (cf a T i l), sq_abs (cf a T i l)]
      _ = (Fintype.card κ : ℝ) := by simp
  have hnn := gramK_nonneg a T v
  calc (dotp (a i) v) ^ 2 = (∑ l, cf a T i l * dotp (a (T l)) v) ^ 2 := by rw [hdec]
    _ ≤ (∑ l, (cf a T i l) ^ 2) * gramK a T v := by simpa [gramK] using hcs
    _ ≤ (Fintype.card κ : ℝ) * gramK a T v := mul_le_mul_of_nonneg_right hc hnn

/-- **Верхняя часть зажима.** `gram(S,v) ≤ |S|·K·gramK(v)` для максимально-объёмной `K`-ки.
Это и есть причина, по которой сетка по невязкам одной `K`-ки работает. -/
theorem gram_le_card_mul_gramK (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0)
    (v : κ → ℝ) :
    gram a S v ≤ (S.card * Fintype.card κ : ℝ) * gramK a T v := by
  calc gram a S v = ∑ i ∈ S, (dotp (a i) v) ^ 2 := rfl
    _ ≤ ∑ _i ∈ S, (Fintype.card κ : ℝ) * gramK a T v :=
        Finset.sum_le_sum fun i hi => sq_dotp_le_card_mul_gramK hmax hdet hi v
    _ = (S.card * Fintype.card κ : ℝ) * gramK a T v := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- `K`-ка с ненулевым определителем не имеет повторов. -/
lemma injective_of_det_ne_zero (hdet : (rowMat a T).det ≠ 0) : Function.Injective T := by
  intro l l' h
  by_contra hne
  exact hdet (Matrix.det_zero_of_row_eq hne (by funext j; simp [rowMat, h]))

/-- Сумма неотрицательной функции по `K`-ке не превосходит суммы по объемлющему `S`. -/
lemma sum_comp_le (hTS : ∀ l, T l ∈ S) (hinj : Function.Injective T)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) : ∑ l, f (T l) ≤ ∑ i ∈ S, f i := by
  classical
  have himg : (Finset.univ.image T) ⊆ S := by
    intro i hi
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hi
    exact hTS l
  calc ∑ l, f (T l) = ∑ i ∈ Finset.univ.image T, f i := by
        rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    _ ≤ ∑ i ∈ S, f i := Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => hf _

/-- **Нижняя часть зажима.** `gramK(v) ≤ gram(S,v)`: строки `K`-ки сами лежат в `S`. -/
theorem gramK_le_gram (hTS : ∀ l, T l ∈ S) (hdet : (rowMat a T).det ≠ 0) (v : κ → ℝ) :
    gramK a T v ≤ gram a S v :=
  sum_comp_le hTS (injective_of_det_ne_zero hdet) (fun i => (dotp (a i) v) ^ 2)
    (fun _ => sq_nonneg _)

/-! ### Следствия для случая `T ⊆ R ⊆ S`

Ключ к Теореме M (`theory_note_v5.md`, §8): если максимально-объёмная `K`-ка
набора `S` целиком лежит в подмножестве `R`, то форма Грама `R` мажорирует форму
Грама всего `S` с постоянным множителем `|S|·K` — **независимо от того, какие
строки `S` в `R` не попали и насколько они длинные**. -/

/-- `⟨a_i,v⟩² ≤ K·gram(R,v)` при `i ∈ S`, `T ⊆ R`.
В матричной записи это `a_i'Κ(R)⁻¹a_i ≤ K` (численно: `code/check_lo_theoremM.py`). -/
theorem sq_dotp_le_card_mul_gram_of_subset (hmax : MaxVol a S T)
    (hdet : (rowMat a T).det ≠ 0) {i : ι} (hi : i ∈ S) {R : Finset ι}
    (hTR : ∀ l, T l ∈ R) (v : κ → ℝ) :
    (dotp (a i) v) ^ 2 ≤ (Fintype.card κ : ℝ) * gram a R v :=
  le_trans (sq_dotp_le_card_mul_gramK hmax hdet hi v)
    (mul_le_mul_of_nonneg_left (gramK_le_gram hTR hdet v) (Nat.cast_nonneg _))

/-- **Гипотеза `hKR` с множителем.** `gram(S,v) ≤ |S|·K·gram(R,v)` при `T ⊆ R`. -/
theorem gram_le_card_mul_gram_of_subset (hmax : MaxVol a S T)
    (hdet : (rowMat a T).det ≠ 0) {R : Finset ι} (hTR : ∀ l, T l ∈ R) (v : κ → ℝ) :
    gram a S v ≤ (S.card * Fintype.card κ : ℝ) * gram a R v := by
  refine le_trans (gram_le_card_mul_gramK hmax hdet v) ?_
  refine mul_le_mul_of_nonneg_left (gramK_le_gram hTR hdet v) ?_
  positivity

end SparseSharpe.Factor
