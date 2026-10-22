import SparseSharpe.Factor.ScaleFreeScheme

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Схема без ω для long-only при любом фиксированном `K` — на всех входах

Классификация закрыта: схема без `ω` существует для long-only задачи при любом фиксированном
числе факторов `K`, без условия на оптимум (в `Factor/ScaleFreeScheme.lean` был класс «не больше
одной малой позиции»). Устройство (строки `rowsK d B G`, цели `targetsK m d`, обрезаются строки
активов):

* **два базиса.** Свидетель строится в координатах Крамера `K`-ки `T`, максимально-объёмной среди
  *немалых* строк оптимума (якоря и активы с весом `r_i(x₀) ≥ τ`): у строк `T` нет проблемы
  знака — либо это якоря, либо у них запас `τ`. Узел берётся на решётке в координатах невязок
  другой `K`-ки `T₂`, максимально-объёмной среди немалых строк и строк `J'` (ниже), так что в
  узле невязки всех этих строк отличаются от невязок оптимума не больше чем на `D = K·s`;
* **Каратеодори.** Малые активы `J` оптимума (вес `< τ`, их может быть до `k`) заменяются не более
  чем `K + 1` из них (`J'`) с неотрицательными весами `μ` той же суммы `W`, сохраняющими вектор
  `Σ_J r_j a_j` (`exists_carath`); цель падает не больше чем на `2W²` (`rowObj_carath`,
  `carath_loss_le`), веса при этом не пересчитываются: в свидетеле строки `J'` получают
  фиксированные веса `μ`, и для них нужна лишь точность узла;
* **свидетель с заданными весами** (`wGen`, `rowObj_wGen_ge`): веса `v_j` строк вне `T`
  произвольны, веса строк `T` дополняют их до стационарных; если `v_j = resC_j(x)` вне `J'`, то
  `obj ≥ ψ_X(x) − Σ_{J'}(μ_j − r_j(x))² − Σ_l(ϖ_l − ρ_l(x))²`.

Схема (`univFamily`, `univCandidates`): догадки `V = L·2^j`; все `K`-ки `T`, все `K`-ки `T₂`, все
наборы `J'` из не более чем `K + 1` активов (`optSet f`, `f : Option κ → Option ι`); узлы
`x(T₂, z)` с `ρ_{T₂}(x) = s·z`, `|z|_∞ ≤ Z`; в узле — рюкзак `knap` по активам не из `T` и `J'` с
`|c_i|_∞ ≤ 1` (координаты Крамера `T`), ключ `sfKey` (ключ Крамера, счёт, счётчик) с шириной
`η`, `ζ` и коробкой `sfBox`; кандидаты — `T_A ∪ J' ∪ R` с не более чем `k` активами. Параметры:
`s = √(εV)/(12k(k+1)K√K)`, `η = √(εV)/(12k²√K)`, `ζ = εV/k`, `Z = ⌈12k(k+1)K√(2K/ε)⌉ + 1`,
`Z_κ = ⌈12k²√K√(k(4+ε)/ε)⌉ + k`, `Z_q = ⌈(4+ε)k/ε⌉` — ни `ω`, ни величин входа.

Главное: `main_theorem_univ` — из данных, гарантия `1 − 2ε` (как у Main Theorem), размер
`(J+1)·(M+K)^{2K}·(M+1)^{K+1}·(2Z+1)^K·(|box|+1)`; величины входа — только в числе догадок `J+1`.
-/

namespace SparseSharpe.Factor

open Finset

/-! ### Свидетель с заданными весами и стационарность в координатах Крамера -/

section RowCert

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {cl : ι → Bool} {T : κ → ι}

/-- Веса строк `T`, дополняющие веса `v` строк `X ∖ T` до стационарных:
`ϖ_l = −Σ_{j∈X∖T} v_j c_{jl}`. -/
noncomputable def omegaV (a : ι → κ → ℝ) (T : κ → ι) (X : Finset ι) (v : ι → ℝ) (l : κ) : ℝ :=
  -∑ j ∈ X \ rowsT T, v j * cf a T j l

/-- **Свидетель с заданными весами:** `v_j` вне `T`, `ϖ_l` на строках `T`. -/
noncomputable def wGen (a : ι → κ → ℝ) (T : κ → ι) (X : Finset ι) (v : ι → ℝ) (j : ι) : ℝ :=
  if j ∈ rowsT T then ∑ l, (if T l = j then omegaV a T X v l else 0) else v j

lemma wGen_T (hinj : Function.Injective T) (X : Finset ι) (v : ι → ℝ) (l : κ) :
    wGen a T X v (T l) = omegaV a T X v l := by
  rw [wGen, ite_eq_left (mem_rowsT T l)]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb; rw [ite_eq_right (fun h => hb (hinj h))]
  · intro h; exact absurd (Finset.mem_univ l) h

lemma wGen_of_not_mem {j : ι} (hj : j ∉ rowsT T) (X : Finset ι) (v : ι → ℝ) :
    wGen a T X v j = v j := by
  rw [wGen, ite_eq_right hj]

omit [DecidableEq ι] in
/-- Разложение суммы `Σ_U v_j⟨a_j, h⟩` по строкам `K`-ки. -/
lemma sum_v_dotp_eq (hdet : (rowMat a T).det ≠ 0) (U : Finset ι) (v : ι → ℝ) (h : κ → ℝ) :
    ∑ j ∈ U, v j * dotp (a j) h = ∑ l, (∑ j ∈ U, v j * cf a T j l) * dotp (a (T l)) h := by
  have e : ∀ j ∈ U, v j * dotp (a j) h = ∑ l, v j * cf a T j l * dotp (a (T l)) h := by
    intro j _
    rw [dotp_eq_sum_cf hdet j h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul]

/-- Свидетель с заданными весами стационарен: `Σ_{j∈X} w_j a_j = 0`. -/
lemma isStat_wGen (hdet : (rowMat a T).det ≠ 0) {X : Finset ι} (hTX : rowsT T ⊆ X)
    (v : ι → ℝ) : RowStat a X (wGen a T X v) := by
  intro h
  have hinj := injective_of_det_ne_zero hdet
  have hsplit := Finset.sum_sdiff hTX (f := fun j => wGen a T X v j * dotp (a j) h)
  have h1 : ∑ j ∈ X \ rowsT T, wGen a T X v j * dotp (a j) h
      = ∑ l, (∑ j ∈ X \ rowsT T, v j * cf a T j l) * dotp (a (T l)) h := by
    rw [← sum_v_dotp_eq hdet]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [wGen_of_not_mem (Finset.mem_sdiff.mp hj).2]
  have h2 : ∑ j ∈ rowsT T, wGen a T X v j * dotp (a j) h
      = ∑ l, omegaV a T X v l * dotp (a (T l)) h := by
    rw [rowsT, Finset.sum_image (fun l₁ _ l₂ _ h => hinj h)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [wGen_T hinj]
  rw [← hsplit, h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun l _ => ?_
  simp only [omegaV]; ring

omit [DecidableEq κ] [DecidableEq ι] in
/-- `resC_j(x)² ≤ r_j(x)²`. -/
lemma sq_resC_le_sq (j : ι) (x : κ → ℝ) :
    resC a y cl j x ^ 2 ≤ (y j - dotp (a j) x) ^ 2 := by
  by_cases hc : cl j
  · simp only [resC, hc, ite_true]
    rcases le_or_gt 0 (y j - dotp (a j) x) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h.le, zero_pow two_ne_zero]; positivity
  · simp [resC, hc]

/-- **Оценка свидетеля с заданными весами.** Если `v_j = resC_j(x)` у строк `X ∖ T` вне `Jp`, то
`obj(X, w) ≥ ψ_X(x) − Σ_{j∈(X∖T)∩Jp}(v_j − r_j(x))² − Σ_l(ϖ_l − ρ_l(x))²`; активность строк `T`
в `x` не нужна. -/
theorem rowObj_wGen_ge (hdet : (rowMat a T).det ≠ 0) {X Jp : Finset ι} (hTX : rowsT T ⊆ X)
    (v : ι → ℝ) (x : κ → ℝ) (hv : ∀ j ∈ X \ rowsT T, j ∉ Jp → v j = resC a y cl j x) :
    psiC a y cl X x
        - ∑ j ∈ (X \ rowsT T).filter (· ∈ Jp), (v j - (y j - dotp (a j) x)) ^ 2
        - ∑ l, (omegaV a T X v l - rhoT a y T x l) ^ 2
      ≤ rowObj y X (wGen a T X v) := by
  have hinj := injective_of_det_ne_zero hdet
  rw [rowObj_eq_of_stat (isStat_wGen hdet hTX v) x]
  rw [← Finset.sum_sdiff hTX (f := fun j => (y j - dotp (a j) x) ^ 2
    - (wGen a T X v j - (y j - dotp (a j) x)) ^ 2)]
  rw [psiC, ← Finset.sum_sdiff hTX (f := fun j => resC a y cl j x ^ 2)]
  have hT1 : ∑ j ∈ rowsT T, ((y j - dotp (a j) x) ^ 2
        - (wGen a T X v j - (y j - dotp (a j) x)) ^ 2)
      = ∑ l, (rhoT a y T x l ^ 2 - (omegaV a T X v l - rhoT a y T x l) ^ 2) := by
    rw [rowsT, Finset.sum_image (fun l₁ _ l₂ _ h => hinj h)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [wGen_T hinj]; rfl
  have hT2 : ∑ j ∈ rowsT T, resC a y cl j x ^ 2 ≤ ∑ l, rhoT a y T x l ^ 2 := by
    rw [rowsT, Finset.sum_image (fun l₁ _ l₂ _ h => hinj h)]
    exact Finset.sum_le_sum fun l _ => sq_resC_le_sq (T l) x
  have hN : ∑ j ∈ X \ rowsT T, resC a y cl j x ^ 2
        - ∑ j ∈ (X \ rowsT T).filter (· ∈ Jp), (v j - (y j - dotp (a j) x)) ^ 2
      ≤ ∑ j ∈ X \ rowsT T, ((y j - dotp (a j) x) ^ 2
        - (wGen a T X v j - (y j - dotp (a j) x)) ^ 2) := by
    rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [wGen_of_not_mem (Finset.mem_sdiff.mp hj).2]
    by_cases hJ : j ∈ Jp
    · simp only [hJ, ite_true]
      have := sq_resC_le_sq (a := a) (y := y) (cl := cl) j x
      linarith
    · simp only [hJ, ite_false, sub_zero]
      rw [hv j hj hJ, sq_sub_sq_resC]
  have hT3 : ∑ l, (rhoT a y T x l ^ 2 - (omegaV a T X v l - rhoT a y T x l) ^ 2)
      = ∑ l, rhoT a y T x l ^ 2 - ∑ l, (omegaV a T X v l - rhoT a y T x l) ^ 2 :=
    Finset.sum_sub_distrib _ _
  rw [hT1, hT3]
  linarith

/-- **Стационарность в координатах Крамера:** `ω_{T l} + Σ_{j∈S∖T} ω_j c_{jl} = 0`. -/
lemma cramer_stat (hdet : (rowMat a T).det ≠ 0) {S : Finset ι} (hTS : rowsT T ⊆ S)
    {ω : ι → ℝ} (hst : RowStat a S ω) (l : κ) :
    ω (T l) + ∑ j ∈ S \ rowsT T, ω j * cf a T j l = 0 := by
  have hinj := injective_of_det_ne_zero hdet
  obtain ⟨v, hv⟩ := exists_point_with_residuals hdet (fun l' => if l' = l then (1:ℝ) else 0)
  have h0 := hst v
  have hc : ∀ j, dotp (a j) v = cf a T j l := by
    intro j
    rw [dotp_eq_sum_cf hdet j v]
    simp [hv]
  rw [← Finset.sum_sdiff hTS] at h0
  simp only [hc] at h0
  have hT : ∑ j ∈ rowsT T, ω j * cf a T j l = ω (T l) := by
    rw [rowsT, Finset.sum_image (fun l₁ _ l₂ _ h => hinj h)]
    rw [Finset.sum_eq_single l]
    · rw [cf_self hdet]; simp
    · intro b _ hb; rw [cf_self hdet, ite_eq_right hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ l) h
  linarith

end RowCert

/-! ### Каратеодори для малых строк -/

section Carath

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι]

omit [DecidableEq ι] in
/-- `Σ x_j² ≤ (Σ x_j)²` при `x ≥ 0`. -/
lemma sum_sq_le_sq_sum {J : Finset ι} {f : ι → ℝ} (hf : ∀ j ∈ J, 0 ≤ f j) :
    ∑ j ∈ J, f j ^ 2 ≤ (∑ j ∈ J, f j) ^ 2 := by
  rw [sq (∑ j ∈ J, f j), Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hf hj) (hf j hj)

omit [DecidableEq κ] [DecidableEq ι] in
/-- **Каратеодори для строк.** Неотрицательная комбинация `Σ_{j∈J} r_j a_j` представляется не
более чем `K + 1` строками `J` с неотрицательными коэффициентами той же суммы. -/
theorem exists_carath (a : ι → κ → ℝ) (J : Finset ι) (r : ι → ℝ) (hr : ∀ j ∈ J, 0 ≤ r j) :
    ∃ J' ⊆ J, J'.card ≤ Fintype.card κ + 1 ∧ ∃ μ : ι → ℝ, (∀ j ∈ J', 0 ≤ μ j)
      ∧ ∑ j ∈ J', μ j = ∑ j ∈ J, r j
      ∧ ∀ c, ∑ j ∈ J', μ j * a j c = ∑ j ∈ J, r j * a j c := by
  classical
  set W := ∑ j ∈ J, r j with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg hr
  rcases hW0.eq_or_lt with h0 | hpos
  · have hz : ∀ j ∈ J, r j = 0 := (Finset.sum_eq_zero_iff_of_nonneg hr).mp h0.symm
    refine ⟨∅, Finset.empty_subset _, by simp, fun _ => 0, by simp, ?_, fun c => ?_⟩
    · simp [← h0]
    · simp only [Finset.sum_empty]
      rw [Finset.sum_eq_zero fun j hj => by rw [hz j hj, zero_mul]]
  · set p : κ → ℝ := J.centerMass r a with hp
    have hpmem : p ∈ convexHull ℝ (a '' ↑J) :=
      Finset.centerMass_mem_convexHull J hr hpos (fun j hj => Set.mem_image_of_mem a hj)
    rw [convexHull_eq_union] at hpmem
    simp only [Set.mem_iUnion] at hpmem
    obtain ⟨t, hts, hind, hpt⟩ := hpmem
    have hcard : t.card ≤ Fintype.card κ + 1 := by
      have h1 := hind.card_le_finrank_succ
      have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → κ → ℝ)))
          ≤ Fintype.card κ := by
        calc _ ≤ Module.finrank ℝ (κ → ℝ) := Submodule.finrank_le _
          _ = Fintype.card κ := Module.finrank_fintype_fun_eq_card ℝ
      rw [Fintype.card_coe] at h1
      omega
    rw [Finset.mem_convexHull'] at hpt
    obtain ⟨w, hw0, hw1, hwp⟩ := hpt
    have hex : ∀ u ∈ t, ∃ j ∈ J, a j = u := by
      intro u hu
      obtain ⟨j, hj, hju⟩ := hts hu
      exact ⟨j, hj, hju⟩
    obtain ⟨j₀, -⟩ := Finset.nonempty_of_sum_ne_zero hpos.ne'
    have : Nonempty ι := ⟨j₀⟩
    choose! g hgJ hga using hex
    have hginj : Set.InjOn g (t : Set (κ → ℝ)) := by
      intro u hu u' hu' h
      rw [← hga u hu, ← hga u' hu', h]
    refine ⟨t.image g, ?_, ?_, fun j => W * w (a j), ?_, ?_, fun c => ?_⟩
    · intro j hj
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
      exact hgJ u hu
    · rw [Finset.card_image_of_injOn hginj]; exact hcard
    · intro j hj
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
      change 0 ≤ W * w (a (g u))
      rw [hga u hu]
      exact mul_nonneg hpos.le (hw0 u hu)
    · rw [Finset.sum_image (fun u hu u' hu' h => hginj hu hu' h)]
      rw [Finset.sum_congr rfl fun u hu => by rw [hga u hu], ← Finset.mul_sum, hw1, mul_one]
    · rw [Finset.sum_image (fun u hu u' hu' h => hginj hu hu' h)]
      have e1 : ∑ u ∈ t, W * w (a (g u)) * a (g u) c = W * ∑ u ∈ t, w u * u c := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [hga u hu]; ring
      rw [e1]
      have e2 : ∑ u ∈ t, w u * u c = p c := by
        rw [← hwp]
        simp [Finset.sum_apply, smul_eq_mul]
      rw [e2, hp, Finset.centerMass]
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      rw [← hW, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]

variable {a : ι → κ → ℝ} {y : ι → ℝ}

omit [DecidableEq κ] in
/-- **Цель после замены малых строк.** `S = N ∪ J`, `J' ⊆ J`, веса `μ` на `J'` сохраняют вектор
`Σ_J r_j(x₀)a_j`. Тогда веса `r(x₀)` на `N` и `μ` на `J'` стационарны, и их цель равна
`φ_S(x₀) − Σ_{J∖J'} r_j(x₀)² − Σ_{J'} (μ_j − r_j(x₀))²`. -/
lemma rowObj_carath {S N J J' : Finset ι} {x₀ : κ → ℝ} {μ : ι → ℝ}
    (hS : S = N ∪ J) (hdisj : Disjoint N J) (hJ' : J' ⊆ J) (hnorm : IsNormal a y S x₀)
    (hμ : ∀ c, ∑ j ∈ J', μ j * a j c = ∑ j ∈ J, (y j - dotp (a j) x₀) * a j c) :
    RowStat a (N ∪ J') (fun j => if j ∈ J' then μ j else y j - dotp (a j) x₀)
    ∧ rowObj y (N ∪ J') (fun j => if j ∈ J' then μ j else y j - dotp (a j) x₀)
      = phi a y S x₀ - ∑ j ∈ J \ J', (y j - dotp (a j) x₀) ^ 2
        - ∑ j ∈ J', (μ j - (y j - dotp (a j) x₀)) ^ 2 := by
  classical
  set ω : ι → ℝ := fun j => if j ∈ J' then μ j else y j - dotp (a j) x₀ with hω
  have hdN : Disjoint N J' := Finset.disjoint_of_subset_right hJ' hdisj
  have hωN : ∀ j ∈ N, ω j = y j - dotp (a j) x₀ := by
    intro j hj
    have : j ∉ J' := Finset.disjoint_left.mp hdN hj
    simp [hω, this]
  have hωJ : ∀ j ∈ J', ω j = μ j := by
    intro j hj; simp [hω, hj]
  have hstat : RowStat a (N ∪ J') ω := by
    intro v
    rw [Finset.sum_union hdN]
    have h1 : ∑ j ∈ J', ω j * dotp (a j) v
        = ∑ j ∈ J, (y j - dotp (a j) x₀) * dotp (a j) v := by
      rw [Finset.sum_congr rfl fun j hj => by rw [hωJ j hj]]
      simp only [dotp, Finset.mul_sum]
      rw [Finset.sum_comm, Finset.sum_comm (s := J)]
      refine Finset.sum_congr rfl fun c _ => ?_
      have := hμ c
      calc ∑ j ∈ J', μ j * (a j c * v c) = (∑ j ∈ J', μ j * a j c) * v c := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = (∑ j ∈ J, (y j - ∑ c', a j c' * x₀ c') * a j c) * v c := by
            rw [this]; rfl
        _ = ∑ j ∈ J, (y j - ∑ c', a j c' * x₀ c') * (a j c * v c) := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1, Finset.sum_congr rfl fun j hj => by rw [hωN j hj]]
    have h2 := hnorm v
    rw [mom, hS, Finset.sum_union hdisj] at h2
    exact h2
  refine ⟨hstat, ?_⟩
  rw [rowObj_eq_of_stat hstat x₀, Finset.sum_union hdN]
  have hNsum : ∑ j ∈ N, ((y j - dotp (a j) x₀) ^ 2 - (ω j - (y j - dotp (a j) x₀)) ^ 2)
      = ∑ j ∈ N, (y j - dotp (a j) x₀) ^ 2 := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hωN j hj]; ring
  have hJsum : ∑ j ∈ J', ((y j - dotp (a j) x₀) ^ 2 - (ω j - (y j - dotp (a j) x₀)) ^ 2)
      = ∑ j ∈ J', (y j - dotp (a j) x₀) ^ 2 - ∑ j ∈ J', (μ j - (y j - dotp (a j) x₀)) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hωJ j hj]
  have hphi : phi a y S x₀ = ∑ j ∈ N, (y j - dotp (a j) x₀) ^ 2
      + (∑ j ∈ J \ J', (y j - dotp (a j) x₀) ^ 2 + ∑ j ∈ J', (y j - dotp (a j) x₀) ^ 2) := by
    rw [phi, hS, Finset.sum_union hdisj, Finset.sum_sdiff hJ']
    congr 1 <;> refine Finset.sum_congr rfl fun j _ => by ring
  rw [hNsum, hJsum, hphi]; ring

/-- **Потеря от замены:** `Σ_{J∖J'} r² + Σ_{J'}(μ − r)² ≤ 2W²` при `r, μ ≥ 0`,
`Σ_{J'}μ = W = Σ_J r`. -/
lemma carath_loss_le {J J' : Finset ι} {r μ : ι → ℝ} (hJ' : J' ⊆ J)
    (hr : ∀ j ∈ J, 0 ≤ r j) (hμ : ∀ j ∈ J', 0 ≤ μ j) (hsum : ∑ j ∈ J', μ j = ∑ j ∈ J, r j) :
    ∑ j ∈ J \ J', r j ^ 2 + ∑ j ∈ J', (μ j - r j) ^ 2 ≤ 2 * (∑ j ∈ J, r j) ^ 2 := by
  have h1 : ∑ j ∈ J', (μ j - r j) ^ 2 ≤ ∑ j ∈ J', μ j ^ 2 + ∑ j ∈ J', r j ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j hj => ?_
    have := mul_nonneg (hμ j hj) (hr j (hJ' hj))
    nlinarith
  have h2 : ∑ j ∈ J \ J', r j ^ 2 + ∑ j ∈ J', r j ^ 2 = ∑ j ∈ J, r j ^ 2 :=
    Finset.sum_sdiff hJ'
  have h3 := sum_sq_le_sq_sum hr
  have h4 := sum_sq_le_sq_sum hμ
  rw [hsum] at h4
  linarith

end Carath

/-! ### Определения схемы -/

section UnivDefs

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Шаг решётки по невязкам `K`-ки сетки: `s = √(εV)/(12k(k+1)K√K)`. -/
noncomputable def univStep (κ : Type*) [Fintype κ] (k : ℕ) (ε V : ℝ) : ℝ :=
  Real.sqrt (ε * V) / (12 * k * (k + 1) * Fintype.card κ * Real.sqrt (Fintype.card κ))

/-- Ширина ключа Крамера `η = √(εV)/(12k²√K)`. -/
noncomputable def univEta (κ : Type*) [Fintype κ] (k : ℕ) (ε V : ℝ) : ℝ :=
  Real.sqrt (ε * V) / (12 * (k : ℝ) ^ 2 * Real.sqrt (Fintype.card κ))

/-- Радиус номеров узлов `Z = ⌈12k(k+1)K√(2K/ε)⌉ + 1` — без величин входа. -/
noncomputable def univZ (κ : Type*) [Fintype κ] (k : ℕ) (ε : ℝ) : ℕ :=
  ⌈12 * (k : ℝ) * (k + 1) * Fintype.card κ * Real.sqrt (2 * Fintype.card κ / ε)⌉₊ + 1

/-- Граница ключа Крамера `Z_κ = ⌈12k²√K·√(k(4+ε)/ε)⌉ + k`. -/
noncomputable def univZk (κ : Type*) [Fintype κ] (k : ℕ) (ε : ℝ) : ℤ :=
  ⌈12 * (k : ℝ) ^ 2 * Real.sqrt (Fintype.card κ) * Real.sqrt (k * (4 + ε) / ε)⌉ + k

/-- Граница округлённого счёта `Z_q = ⌈(4+ε)k/ε⌉`. -/
noncomputable def univZq (k : ℕ) (ε : ℝ) : ℤ := ⌈(4 + ε) * k / ε⌉

/-- Активы, которые принимает `f : Option κ → Option ι` (не больше `K + 1` штук). -/
def optSet (f : Option κ → Option ι) : Finset ι :=
  Finset.univ.filter (fun i => ∃ p, f p = some i)

/-- Допуск актива в рюкзак: не из `T`, не из `J'`, `|c_i|_∞ ≤ 1` в координатах Крамера `T`. -/
noncomputable def univAdm (a : ι ⊕ κ → κ → ℝ) (T : κ → ι ⊕ κ) (Jp : Finset ι) (i : ι) : Bool :=
  decide ((Sum.inl i : ι ⊕ κ) ∉ rowsT T ∧ i ∉ Jp ∧ ∀ m, |cf a T (Sum.inl i) m| ≤ 1)

/-- Значение для отбора в корзине — счёт `resC_i²` (для гарантии выбор не важен). -/
noncomputable def univVal (a : ι ⊕ κ → κ → ℝ) (y : ι ⊕ κ → ℝ) (x : κ → ℝ) (i : ι) : ℝ :=
  resC a y (fun r => r.isLeft) (Sum.inl i) x ^ 2

/-- **Таблица схемы** в узле `z` решётки `K`-ки `T₂` при базисе свидетеля `T` и принудительных
активах `J'`: рюкзак по допущенным активам с ключом `sfKey` в координатах Крамера `T`. -/
noncomputable def univTable (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ) (ε V : ℝ)
    (T T₂ : κ → ι ⊕ κ) (Jp : Finset ι) (z : κ → ℤ) (La : List ι) : Finset (Finset ι) :=
  knap (univVal (rowsK d B G) (targetsK m d)
      (sfNode (rowsK d B G) (targetsK m d) T₂ (univStep κ k ε V) z))
    (sfKey (rowsK d B G) (targetsK m d) (fun r => r.isLeft) T (univEta κ k ε V) (sfZeta k ε V)
      (sfNode (rowsK d B G) (targetsK m d) T₂ (univStep κ k ε V) z))
    (sfBox κ (univZk κ k ε) (univZq k ε) k)
    (La.filter (univAdm (rowsK d B G) T Jp))

/-- **Семейство при одной догадке:** все `K`-ки `T`, `T₂`, наборы `J'` (`f : Option κ → Option ι`)
и узлы; кандидаты `T_A ∪ J' ∪ R` с не более чем `k` активами. -/
noncomputable def univFamily (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ) (ε V : ℝ)
    (La : List ι) : Finset (Finset ι) :=
  (Finset.univ : Finset (κ → ι ⊕ κ)).biUnion fun T =>
    (Finset.univ : Finset (κ → ι ⊕ κ)).biUnion fun T₂ =>
      (Finset.univ : Finset (Option κ → Option ι)).biUnion fun f =>
        (nodeBox (κ := κ) (univZ κ k ε)).biUnion fun z =>
          ((univTable m d B G k ε V T T₂ (optSet f) z La).image
            (fun R => assetsT T ∪ optSet f ∪ R)).filter (fun W => W.card ≤ k)

/-- **Семейство кандидатов** по всем догадкам `V_j = L·2^j`, `j ≤ J`. -/
noncomputable def univCandidates (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ)
    (ε L : ℝ) (J : ℕ) (La : List ι) : Finset (Finset ι) :=
  (Finset.range (J + 1)).biUnion fun j => univFamily m d B G k ε (L * 2 ^ j) La

/-- Число ключей коробки `(2Z_κ+1)^K(Z_q+1)(k+1)`. -/
noncomputable def univBoxBound (κ : Type*) [Fintype κ] (k : ℕ) (ε : ℝ) : ℕ :=
  (2 * univZk κ k ε + 1).toNat ^ Fintype.card κ * ((univZq k ε + 1).toNat * (k + 1))

omit [Fintype ι] in
lemma card_univTable_le (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ) (ε V : ℝ)
    (T T₂ : κ → ι ⊕ κ) (Jp : Finset ι) (z : κ → ℤ) (La : List ι) :
    (univTable m d B G k ε V T T₂ Jp z La).card ≤ univBoxBound κ k ε + 1 := by
  unfold univTable
  refine le_trans (knap_card_le _ _ _ _) (le_of_eq ?_)
  rw [card_sfBox, univBoxBound]

lemma card_univFamily_le (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ) (ε V : ℝ)
    (La : List ι) :
    (univFamily m d B G k ε V La).card
      ≤ (Fintype.card ι + Fintype.card κ) ^ Fintype.card κ
        * ((Fintype.card ι + Fintype.card κ) ^ Fintype.card κ
          * ((Fintype.card ι + 1) ^ (Fintype.card κ + 1)
            * ((2 * univZ κ k ε + 1) ^ Fintype.card κ * (univBoxBound κ k ε + 1)))) := by
  unfold univFamily
  have hT : (Finset.univ : Finset (κ → ι ⊕ κ)).card
      = (Fintype.card ι + Fintype.card κ) ^ Fintype.card κ := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_sum]
  have hf : (Finset.univ : Finset (Option κ → Option ι)).card
      = (Fintype.card ι + 1) ^ (Fintype.card κ + 1) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_option, Fintype.card_option]
  refine le_trans Finset.card_biUnion_le ?_
  rw [← hT]
  refine Finset.sum_le_card_nsmul _ _ _ fun T _ => ?_
  refine le_trans Finset.card_biUnion_le ?_
  refine Finset.sum_le_card_nsmul _ _ _ fun T₂ _ => ?_
  refine le_trans Finset.card_biUnion_le ?_
  rw [← hf]
  refine Finset.sum_le_card_nsmul _ _ _ fun f _ => ?_
  refine le_trans Finset.card_biUnion_le ?_
  rw [← card_nodeBox (κ := κ) (univZ κ k ε)]
  refine Finset.sum_le_card_nsmul _ _ _ fun z _ => ?_
  refine le_trans (Finset.card_filter_le _ _) (le_trans Finset.card_image_le ?_)
  exact card_univTable_le m d B G k ε V T T₂ (optSet f) z La

/-- **Размер семейства:** `(J+1)·(M+K)^K·(M+K)^K·(M+1)^{K+1}·(2Z+1)^K·(|box|+1)`;
`Z = ⌈12k(k+1)K√(2K/ε)⌉ + 1`, `|box| = (2Z_κ+1)^K(Z_q+1)(k+1)`,
`Z_κ = ⌈12k²√K√(k(4+ε)/ε)⌉ + k`, `Z_q = ⌈(4+ε)k/ε⌉` — ни `ω`, ни величин входа: они входят
только через число догадок `J + 1`. -/
theorem card_univCandidates_le (m d : ι → ℝ) (B : ι → κ → ℝ) (G : κ → κ → ℝ) (k : ℕ)
    (ε L : ℝ) (J : ℕ) (La : List ι) :
    (univCandidates m d B G k ε L J La).card
      ≤ (J + 1) * ((Fintype.card ι + Fintype.card κ) ^ Fintype.card κ
        * ((Fintype.card ι + Fintype.card κ) ^ Fintype.card κ
          * ((Fintype.card ι + 1) ^ (Fintype.card κ + 1)
            * ((2 * univZ κ k ε + 1) ^ Fintype.card κ * (univBoxBound κ k ε + 1))))) := by
  unfold univCandidates
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ _
    (fun j _ => card_univFamily_le m d B G k ε (L * 2 ^ j) La)) ?_
  rw [Finset.card_range, smul_eq_mul]

/-- У каждого кандидата не больше `k` активов. -/
theorem card_le_of_mem_univCandidates {m d : ι → ℝ} {B : ι → κ → ℝ} {G : κ → κ → ℝ} {k : ℕ}
    {ε L : ℝ} {J : ℕ} {La : List ι} {W : Finset ι}
    (hW : W ∈ univCandidates m d B G k ε L J La) : W.card ≤ k := by
  unfold univCandidates univFamily at hW
  simp only [Finset.mem_biUnion, Finset.mem_filter] at hW
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hW⟩ := hW
  exact hW.2

omit [DecidableEq κ] in
/-- Любой набор из не более чем `K + 1` активов — это `optSet f` для некоторого `f`. -/
lemma exists_optSet {S : Finset ι} (hS : S.card ≤ Fintype.card κ + 1) :
    ∃ f : Option κ → Option ι, optSet f = S := by
  classical
  have hc : Fintype.card S ≤ Fintype.card (Option κ) := by
    rw [Fintype.card_coe, Fintype.card_option]; exact hS
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨fun p => if h : ∃ s : S, e s = p then some (Classical.choose h).1 else none, ?_⟩
  ext i
  simp only [optSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp⟩
    by_cases h : ∃ s : S, e s = p
    · rw [dite_eq_left h, Option.some.injEq] at hp
      rw [← hp]; exact (Classical.choose h).2
    · rw [dite_eq_right h] at hp; exact absurd hp (by simp)
  · intro hi
    refine ⟨e ⟨i, hi⟩, ?_⟩
    have h : ∃ s : S, e s = e ⟨i, hi⟩ := ⟨⟨i, hi⟩, rfl⟩
    rw [dite_eq_left h, Option.some.injEq]
    have := e.injective (Classical.choose_spec h)
    rw [this]

end UnivDefs


/-! ### Параметры схемы: тождества и оценки -/

section UnivParams

variable {κ : Type*} [Fintype κ] [Nonempty κ]

lemma one_le_sqrt_card : (1 : ℝ) ≤ Real.sqrt (Fintype.card κ) := by
  rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_le_sqrt (by exact_mod_cast Fintype.card_pos)

lemma univStep_pos {k : ℕ} (hk : 1 ≤ k) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V) :
    0 < univStep κ k ε V := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast hk
  have h2 := card_pos_real (κ := κ)
  have h3 : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr h2
  rw [univStep]; positivity

lemma univEta_pos {k : ℕ} (hk : 1 ≤ k) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V) :
    0 < univEta κ k ε V := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast hk
  have h3 : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr card_pos_real
  rw [univEta]; positivity

/-- `K·s = √(εV)/(12k(k+1)√K)`. -/
lemma univ_Ks {k : ℕ} (hk : 1 ≤ k) (ε V : ℝ) :
    (Fintype.card κ : ℝ) * univStep κ k ε V
      = Real.sqrt (ε * V) / (12 * k * (k + 1) * Real.sqrt (Fintype.card κ)) := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast hk
  have h2 := card_pos_real (κ := κ)
  have h3 : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr h2
  rw [univStep]; field_simp

/-- Допуск свидетеля: `(k+1)·K·s + kη = √(εV)/(6k√K)`. -/
lemma univ_err {k : ℕ} (hk : 1 ≤ k) (ε V : ℝ) :
    ((k : ℝ) + 1) * ((Fintype.card κ : ℝ) * univStep κ k ε V) + k * univEta κ k ε V
      = Real.sqrt (ε * V) / (6 * k * Real.sqrt (Fintype.card κ)) := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast hk
  have h3 : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr card_pos_real
  rw [univ_Ks hk, univEta]; field_simp; ring

/-- `K·(√(εV)/(6k√K))² = εV/(36k²)`. -/
lemma univ_err_sq {k : ℕ} (hk : 1 ≤ k) {ε V : ℝ} (hε : 0 ≤ ε) (hV : 0 ≤ V) :
    (Fintype.card κ : ℝ) * (Real.sqrt (ε * V) / (6 * k * Real.sqrt (Fintype.card κ))) ^ 2
      = ε * V / (36 * (k : ℝ) ^ 2) := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast hk
  have h2 := card_pos_real (κ := κ)
  have h3 : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr h2
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hε hV), Real.sq_sqrt h2.le]
  field_simp; ring

/-- **Запас:** `K·s + ((k+1)·K·s + kη) ≤ τ = √(εV)/(3k)`. -/
lemma univ_margin {k : ℕ} (hk : 1 ≤ k) (ε V : ℝ) :
    (Fintype.card κ : ℝ) * univStep κ k ε V
        + (((k : ℝ) + 1) * ((Fintype.card κ : ℝ) * univStep κ k ε V) + k * univEta κ k ε V)
      ≤ Real.sqrt (ε * V) / (3 * k) := by
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs1 := one_le_sqrt_card (κ := κ)
  have hq : 0 ≤ Real.sqrt (ε * V) := Real.sqrt_nonneg _
  rw [univ_err hk, univ_Ks hk]
  have hk0 : (0 : ℝ) < k := by linarith
  have e1 : Real.sqrt (ε * V) / (12 * k * (k + 1) * Real.sqrt (Fintype.card κ))
      ≤ Real.sqrt (ε * V) / (24 * k) := by
    apply div_le_div_of_nonneg_left hq (by positivity)
    have h2 : (2 : ℝ) ≤ k + 1 := by linarith
    calc (24 : ℝ) * k = 12 * k * 2 * 1 := by ring
      _ ≤ 12 * k * (k + 1) * Real.sqrt (Fintype.card κ) := by gcongr
  have e2 : Real.sqrt (ε * V) / (6 * k * Real.sqrt (Fintype.card κ))
      ≤ Real.sqrt (ε * V) / (6 * k) := by
    apply div_le_div_of_nonneg_left hq (by positivity)
    calc (6 : ℝ) * k = 6 * k * 1 := by ring
      _ ≤ 6 * k * Real.sqrt (Fintype.card κ) := by gcongr
  have e3 : Real.sqrt (ε * V) / (24 * k) + Real.sqrt (ε * V) / (6 * k)
      = 5 / 8 * (Real.sqrt (ε * V) / (3 * k)) := by
    field_simp; ring
  have e4 : 0 ≤ Real.sqrt (ε * V) / (3 * k) := by positivity
  linarith

/-- `2(K+1)(K·s)² ≤ εV/144`. -/
lemma univ_D_sq {k : ℕ} (hk : 1 ≤ k) {ε V : ℝ} (hε : 0 ≤ ε) (hV : 0 ≤ V) :
    2 * ((Fintype.card κ : ℝ) + 1) * ((Fintype.card κ : ℝ) * univStep κ k ε V) ^ 2
      ≤ ε * V / 144 := by
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 := card_pos_real (κ := κ)
  have hK1 : (1 : ℝ) ≤ Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have h3 : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr h2
  have hqq : Real.sqrt (ε * V) ^ 2 = ε * V := Real.sq_sqrt (mul_nonneg hε hV)
  rw [univ_Ks hk, div_pow, mul_pow, mul_pow, mul_pow, hqq, Real.sq_sqrt h2.le]
  have hεV : 0 ≤ ε * V := mul_nonneg hε hV
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
  rw [show 2 * ((Fintype.card κ : ℝ) + 1) * (ε * V) * 144
      = (ε * V) * (288 * ((Fintype.card κ : ℝ) + 1)) by ring]
  rw [show ε * V * (12 ^ 2 * (k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2 * Fintype.card κ)
      = (ε * V) * (144 * (k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2 * Fintype.card κ) by ring]
  apply mul_le_mul_of_nonneg_left _ hεV
  have ha : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hb : (4 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
  have hk2 : (4 : ℝ) ≤ (k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2 := by
    calc (4 : ℝ) = 1 * 4 := by ring
      _ ≤ (k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2 := mul_le_mul ha hb (by norm_num) (by positivity)
  nlinarith

/-- `2k(K·s)² ≤ εV`. -/
lemma univ_D_sq_k {k : ℕ} (hk : 1 ≤ k) {ε V : ℝ} (hε : 0 ≤ ε) (hV : 0 ≤ V) :
    2 * (k : ℝ) * ((Fintype.card κ : ℝ) * univStep κ k ε V) ^ 2 ≤ ε * V := by
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 := card_pos_real (κ := κ)
  have hK1 : (1 : ℝ) ≤ Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have hqq : Real.sqrt (ε * V) ^ 2 = ε * V := Real.sq_sqrt (mul_nonneg hε hV)
  rw [univ_Ks hk, div_pow, mul_pow, mul_pow, mul_pow, hqq, Real.sq_sqrt h2.le]
  have hεV : 0 ≤ ε * V := mul_nonneg hε hV
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  rw [show 2 * (k : ℝ) * (ε * V) = (ε * V) * (2 * k) by ring]
  apply mul_le_mul_of_nonneg_left _ hεV
  have hk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hk3 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
  calc 2 * (k : ℝ) ≤ 144 * (k : ℝ) ^ 2 * 1 * 1 := by nlinarith
    _ ≤ 144 * (k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2 * Fintype.card κ := by gcongr
    _ = 12 ^ 2 * (k : ℝ) ^ 2 * ((k : ℝ) + 1) ^ 2 * Fintype.card κ := by norm_num

/-- Радиус решётки в шагах: `12k(k+1)K√(2K/ε)·s = √(2V)`. -/
lemma univ_node_radius {k : ℕ} (hk : 1 ≤ k) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V) :
    12 * (k : ℝ) * (k + 1) * Fintype.card κ * Real.sqrt (2 * Fintype.card κ / ε)
      * univStep κ k ε V = Real.sqrt (2 * V) := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast hk
  have hK := card_pos_real (κ := κ)
  have hsK : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr hK
  have h1' : Real.sqrt (2 * Fintype.card κ / ε) * Real.sqrt (ε * V)
      = Real.sqrt (2 * V) * Real.sqrt (Fintype.card κ) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1; field_simp
  have e : 12 * (k : ℝ) * (k + 1) * Fintype.card κ * Real.sqrt (2 * Fintype.card κ / ε)
      * univStep κ k ε V
      = Real.sqrt (2 * Fintype.card κ / ε) * Real.sqrt (ε * V) / Real.sqrt (Fintype.card κ) := by
    rw [univStep]; field_simp
  rw [e, h1']
  field_simp

/-- Радиус ключа в шагах `η`: `√(k(4+ε)V)/η = 12k²√K·√(k(4+ε)/ε)`. -/
lemma univ_key_radius {k : ℕ} (hk : 1 ≤ k) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V) :
    Real.sqrt ((k : ℝ) * ((4 + ε) * V)) / univEta κ k ε V
      = 12 * (k : ℝ) ^ 2 * Real.sqrt (Fintype.card κ) * Real.sqrt (k * (4 + ε) / ε) := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast hk
  have hK := card_pos_real (κ := κ)
  have hsK : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr hK
  have hsq : 0 < Real.sqrt (ε * V) := Real.sqrt_pos.mpr (mul_pos hε hV)
  have e1 : Real.sqrt ((k : ℝ) * ((4 + ε) * V))
      = Real.sqrt (k * (4 + ε) / ε) * Real.sqrt (ε * V) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1; field_simp
  rw [e1, univEta]
  field_simp

/-- Радиус счёта в шагах `ζ`: `(4+ε)V/ζ = (4+ε)k/ε`. -/
lemma univ_score_radius {k : ℕ} (hk : 1 ≤ k) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V) :
    (4 + ε) * V / sfZeta k ε V = (4 + ε) * k / ε := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [sfZeta]; field_simp

/-- `k²·(√(εV)/(3k))² = εV/9`. -/
lemma univ_tau_sq {k : ℕ} (hk : 1 ≤ k) {ε V : ℝ} (hε : 0 ≤ ε) (hV : 0 ≤ V) :
    (k : ℝ) ^ 2 * (Real.sqrt (ε * V) / (3 * k)) ^ 2 = ε * V / 9 := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_pow, mul_pow, Real.sq_sqrt (mul_nonneg hε hV)]
  field_simp; ring

end UnivParams

/-! ### Шаг схемы: свидетель для представителя -/

section UnivCore

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {a : ι ⊕ κ → κ → ℝ} {y : ι ⊕ κ → ℝ} {T : κ → ι ⊕ κ}

lemma union_sdiff_of_disjoint {ρ : Type*} [DecidableEq ρ] {Y Z U : Finset ρ}
    (h : Disjoint Z U) : (Y ∪ Z) \ U = (Y \ U) ∪ Z := by
  rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_self_of_disjoint h]

omit [Fintype ι] in
/-- **Значение кандидата `T_A ∪ J' ∪ R` (свидетель с заданными весами).** `base = barK(T_A)`
содержит строки `T`; целевые строки `Y = base ∪ U_S ∪ J'` стационарны с весами `r(x₀)` вне `J'`
и `μ ≥ 0` на `J'`; у строк `Y` в узле `x` невязки отличаются от невязок в `x₀` не больше чем на
`D`; у строк `base ∪ U_S` `|c|_∞ ≤ 1`; обрезаемые строки `T` имеют запас `τ`; представитель `R`
имеет ключ, близкий к ключу `U_S` (`|κ_R − κ_{U_S}|_∞ ≤ kη`), и счёт не меньше счёта `U_S` минус
`kζ`. Тогда для кандидата `X = base ∪ J' ∪ R` при всех `x'`
`ψ_X(x') ≥ obj(Y, ω') − kζ − Σ_{J'}(μ_j − r_j(x))² − K((k+1)D + kη)²`. -/
theorem univ_cert [Nonempty κ] (hdet : (rowMat a T).det ≠ 0) {base Jr : Finset (ι ⊕ κ)}
    {R US : Finset ι}
    {μ : ι ⊕ κ → ℝ} {x₀ x : κ → ℝ} {k : ℕ} {D η τ ζ : ℝ}
    (hTb : rowsT T ⊆ base) (hdJ : Disjoint base Jr) (hdR : Disjoint base (R.map (inlE ι κ)))
    (hdU : Disjoint base (US.map (inlE ι κ))) (hdJR : Disjoint Jr (R.map (inlE ι κ)))
    (hdJU : Disjoint Jr (US.map (inlE ι κ))) (hμ : ∀ j ∈ Jr, 0 ≤ μ j)
    (hstat : RowStat a (base ∪ US.map (inlE ι κ) ∪ Jr)
      (fun j => if j ∈ Jr then μ j else y j - dotp (a j) x₀))
    (hself : ∀ j ∈ base ∪ US.map (inlE ι κ), j.isLeft → 0 ≤ y j - dotp (a j) x₀)
    (hTmarg : ∀ l, (T l).isLeft → τ ≤ y (T l) - dotp (a (T l)) x₀)
    (hD : ∀ j ∈ base ∪ US.map (inlE ι κ) ∪ Jr,
      |(y j - dotp (a j) x) - (y j - dotp (a j) x₀)| ≤ D)
    (hcf : ∀ j ∈ base ∪ US.map (inlE ι κ), ∀ l, |cf a T j l| ≤ 1)
    (hkey : ∀ l, |kapA a y T R x l - kapA a y T US x l| ≤ k * η)
    (hscore : scoreA a y US x ≤ scoreA a y R x + k * ζ)
    (hcard : (base \ rowsT T).card + US.card ≤ k)
    (hthr : D + (((k : ℝ) + 1) * D + k * η) ≤ τ) (x' : κ → ℝ) :
    rowObj y (base ∪ US.map (inlE ι κ) ∪ Jr)
        (fun j => if j ∈ Jr then μ j else y j - dotp (a j) x₀)
        - k * ζ - ∑ j ∈ Jr, (μ j - (y j - dotp (a j) x)) ^ 2
        - Fintype.card κ * (((k : ℝ) + 1) * D + k * η) ^ 2
      ≤ psiC a y (fun r => r.isLeft) (base ∪ Jr ∪ R.map (inlE ι κ)) x' := by
  classical
  set cl : ι ⊕ κ → Bool := fun r => r.isLeft with hcl
  set Rr := R.map (inlE ι κ) with hRr
  set Ur := US.map (inlE ι κ) with hUr
  set X := base ∪ Jr ∪ Rr with hX
  set Y := base ∪ Ur ∪ Jr with hY
  set ω' : ι ⊕ κ → ℝ := fun j => if j ∈ Jr then μ j else y j - dotp (a j) x₀ with hω'
  set v : ι ⊕ κ → ℝ := fun j => if j ∈ Jr then μ j else resC a y cl j x with hv
  have hinj := injective_of_det_ne_zero hdet
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD (T (Classical.arbitrary κ)) (by
    have := hTb (mem_rowsT T (Classical.arbitrary κ))
    exact Finset.mem_union_left _ (Finset.mem_union_left _ this)))
  have hη0 : 0 ≤ (k : ℝ) * η := le_trans (abs_nonneg _) (hkey (Classical.arbitrary κ))
  -- непересечения со строками `T`
  have hJT : Disjoint Jr (rowsT T) := Finset.disjoint_of_subset_right hTb hdJ.symm
  have hRT : Disjoint Rr (rowsT T) := Finset.disjoint_of_subset_right hTb hdR.symm
  have hUT : Disjoint Ur (rowsT T) := Finset.disjoint_of_subset_right hTb hdU.symm
  have hTX : rowsT T ⊆ X := fun j hj => Finset.mem_union_left _ (Finset.mem_union_left _ (hTb hj))
  have hTY : rowsT T ⊆ Y := fun j hj => Finset.mem_union_left _ (Finset.mem_union_left _ (hTb hj))
  have hXT : X \ rowsT T = ((base \ rowsT T) ∪ Jr) ∪ Rr := by
    rw [hX, union_sdiff_of_disjoint hRT, union_sdiff_of_disjoint hJT]
  have hYT : Y \ rowsT T = ((base \ rowsT T) ∪ Ur) ∪ Jr := by
    rw [hY, union_sdiff_of_disjoint hJT, union_sdiff_of_disjoint hUT]
  have hd1 : Disjoint (base \ rowsT T) Jr := Finset.disjoint_of_subset_left Finset.sdiff_subset hdJ
  have hd2 : Disjoint ((base \ rowsT T) ∪ Jr) Rr :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_of_subset_left Finset.sdiff_subset hdR, hdJR⟩
  have hd3 : Disjoint (base \ rowsT T) Ur := Finset.disjoint_of_subset_left Finset.sdiff_subset hdU
  have hd4 : Disjoint ((base \ rowsT T) ∪ Ur) Jr :=
    Finset.disjoint_union_left.mpr ⟨hd1, hdJU.symm⟩
  have hbUr : Disjoint base Ur := hdU
  -- значения весов на кусках
  have hω'n : ∀ j, j ∉ Jr → ω' j = y j - dotp (a j) x₀ := fun j hj => by simp [hω', hj]
  have hvn : ∀ j, j ∉ Jr → v j = resC a y cl j x := fun j hj => by simp [hv, hj]
  have hvJ : ∀ j ∈ Jr, v j = μ j := fun j hj => by simp [hv, hj]
  have hω'J : ∀ j ∈ Jr, ω' j = μ j := fun j hj => by simp [hω', hj]
  have hnotJ_b : ∀ j ∈ base, j ∉ Jr := fun j hj => Finset.disjoint_left.mp hdJ hj
  have hnotJ_R : ∀ j ∈ Rr, j ∉ Jr := fun j hj hJ => Finset.disjoint_left.mp hdJR hJ hj
  have hnotJ_U : ∀ j ∈ Ur, j ∉ Jr := fun j hj hJ => Finset.disjoint_left.mp hdJU hJ hj
  -- на строках `base ∪ U_S` в `x₀`: `r = resC`
  have hres0 : ∀ j ∈ base ∪ Ur, y j - dotp (a j) x₀ = resC a y cl j x₀ := by
    intro j hj
    by_cases hc : cl j
    · simp only [resC, hc, ite_true]; exact (max_eq_left (hself j hj hc)).symm
    · simp only [resC, hc, ite_false, Bool.false_eq_true]
  have hDj : ∀ j ∈ base ∪ Ur, |resC a y cl j x₀ - resC a y cl j x| ≤ D := by
    intro j hj
    rw [abs_sub_comm]
    exact le_trans (abs_resC_sub_le j x x₀) (hD j (Finset.mem_union_left _ hj))
  -- отклонение свидетеля: `E_l = ϖ_l − ρ_l(x)`
  have hE : ∀ l, |omegaV a T X v l - rhoT a y T x l| ≤ ((k : ℝ) + 1) * D + k * η := by
    intro l
    have hcs := cramer_stat hdet hTY hstat l
    have hTl : ω' (T l) = rhoT a y T x₀ l := by
      rw [hω'n _ (fun h => Finset.disjoint_left.mp hJT h (mem_rowsT T l))]; rfl
    rw [hTl, hYT, Finset.sum_union hd4, Finset.sum_union hd3] at hcs
    have hX1 : omegaV a T X v l = -(∑ j ∈ base \ rowsT T, v j * cf a T j l
        + ∑ j ∈ Jr, v j * cf a T j l + ∑ j ∈ Rr, v j * cf a T j l) := by
      rw [omegaV, hXT, Finset.sum_union hd2, Finset.sum_union hd1]
    have eJ : ∑ j ∈ Jr, v j * cf a T j l = ∑ j ∈ Jr, ω' j * cf a T j l :=
      Finset.sum_congr rfl fun j hj => by rw [hvJ j hj, hω'J j hj]
    have eB : ∑ j ∈ base \ rowsT T, ω' j * cf a T j l - ∑ j ∈ base \ rowsT T, v j * cf a T j l
        = ∑ j ∈ base \ rowsT T, (resC a y cl j x₀ - resC a y cl j x) * cf a T j l := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjb := (Finset.mem_sdiff.mp hj).1
      rw [hω'n j (hnotJ_b j hjb), hvn j (hnotJ_b j hjb),
        hres0 j (Finset.mem_union_left _ hjb)]; ring
    have eU : ∑ j ∈ Ur, ω' j * cf a T j l - ∑ j ∈ Rr, v j * cf a T j l
        = ∑ j ∈ Ur, (resC a y cl j x₀ - resC a y cl j x) * cf a T j l
          + (kapA a y T US x l - kapA a y T R x l) := by
      have h1 : ∑ j ∈ Ur, ω' j * cf a T j l = ∑ j ∈ Ur, resC a y cl j x₀ * cf a T j l :=
        Finset.sum_congr rfl fun j hj => by
          rw [hω'n j (hnotJ_U j hj), hres0 j (Finset.mem_union_right _ hj)]
      have h2 : ∑ j ∈ Rr, v j * cf a T j l = kapA a y T R x l := by
        simp only [kapA, kapC]
        exact Finset.sum_congr rfl fun j hj => by rw [hvn j (hnotJ_R j hj)]
      have h3 : kapA a y T US x l = ∑ j ∈ Ur, resC a y cl j x * cf a T j l := rfl
      rw [h1, h2, h3]
      have : ∑ j ∈ Ur, (resC a y cl j x₀ - resC a y cl j x) * cf a T j l
          = ∑ j ∈ Ur, resC a y cl j x₀ * cf a T j l
            - ∑ j ∈ Ur, resC a y cl j x * cf a T j l := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [this]; ring
    have hEeq : omegaV a T X v l - rhoT a y T x l
        = (rhoT a y T x₀ l - rhoT a y T x l)
          + ∑ j ∈ base \ rowsT T, (resC a y cl j x₀ - resC a y cl j x) * cf a T j l
          + ∑ j ∈ Ur, (resC a y cl j x₀ - resC a y cl j x) * cf a T j l
          + (kapA a y T US x l - kapA a y T R x l) := by
      rw [hX1]; linarith [hcs, eJ, eB, eU]
    rw [hEeq]
    -- оценки слагаемых
    have hρ : |rhoT a y T x₀ l - rhoT a y T x l| ≤ D := by
      have := hD (T l) (Finset.mem_union_left _ (Finset.mem_union_left _ (hTb (mem_rowsT T l))))
      rw [abs_sub_comm]; simpa [rhoT] using this
    have hsumB : |∑ j ∈ base \ rowsT T, (resC a y cl j x₀ - resC a y cl j x) * cf a T j l|
        ≤ (base \ rowsT T).card * D := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hcB : ((base \ rowsT T).card : ℝ) * D = ∑ _j ∈ base \ rowsT T, D := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [hcB]
      refine Finset.sum_le_sum fun j hj => ?_
      have hjb := (Finset.mem_sdiff.mp hj).1
      rw [abs_mul]
      calc |resC a y cl j x₀ - resC a y cl j x| * |cf a T j l| ≤ D * 1 :=
            mul_le_mul (hDj j (Finset.mem_union_left _ hjb))
              (hcf j (Finset.mem_union_left _ hjb) l) (abs_nonneg _) hD0
        _ = D := mul_one D
    have hsumU : |∑ j ∈ Ur, (resC a y cl j x₀ - resC a y cl j x) * cf a T j l|
        ≤ US.card * D := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hcU : (US.card : ℝ) * D = ∑ _j ∈ Ur, D := by
        rw [Finset.sum_const, hUr, Finset.card_map, nsmul_eq_mul]
      rw [hcU]
      refine Finset.sum_le_sum fun j hj => ?_
      rw [abs_mul]
      calc |resC a y cl j x₀ - resC a y cl j x| * |cf a T j l| ≤ D * 1 :=
            mul_le_mul (hDj j (Finset.mem_union_right _ hj))
              (hcf j (Finset.mem_union_right _ hj) l) (abs_nonneg _) hD0
        _ = D := mul_one D
    have hk' := hkey l
    rw [abs_sub_comm] at hk'
    have hc : ((base \ rowsT T).card : ℝ) + US.card ≤ k := by exact_mod_cast hcard
    calc |(rhoT a y T x₀ l - rhoT a y T x l)
          + ∑ j ∈ base \ rowsT T, (resC a y cl j x₀ - resC a y cl j x) * cf a T j l
          + ∑ j ∈ Ur, (resC a y cl j x₀ - resC a y cl j x) * cf a T j l
          + (kapA a y T US x l - kapA a y T R x l)|
        ≤ |rhoT a y T x₀ l - rhoT a y T x l|
          + |∑ j ∈ base \ rowsT T, (resC a y cl j x₀ - resC a y cl j x) * cf a T j l|
          + |∑ j ∈ Ur, (resC a y cl j x₀ - resC a y cl j x) * cf a T j l|
          + |kapA a y T US x l - kapA a y T R x l| := by
          have t1 := abs_add_le ((rhoT a y T x₀ l - rhoT a y T x l)
            + ∑ j ∈ base \ rowsT T, (resC a y cl j x₀ - resC a y cl j x) * cf a T j l
            + ∑ j ∈ Ur, (resC a y cl j x₀ - resC a y cl j x) * cf a T j l)
            (kapA a y T US x l - kapA a y T R x l)
          have t2 := abs_add_le ((rhoT a y T x₀ l - rhoT a y T x l)
            + ∑ j ∈ base \ rowsT T, (resC a y cl j x₀ - resC a y cl j x) * cf a T j l)
            (∑ j ∈ Ur, (resC a y cl j x₀ - resC a y cl j x) * cf a T j l)
          have t3 := abs_add_le (rhoT a y T x₀ l - rhoT a y T x l)
            (∑ j ∈ base \ rowsT T, (resC a y cl j x₀ - resC a y cl j x) * cf a T j l)
          linarith
      _ ≤ D + (base \ rowsT T).card * D + US.card * D + k * η := by linarith
      _ ≤ ((k : ℝ) + 1) * D + k * η := by nlinarith
  -- знаки: свидетель неотрицателен на обрезаемых строках `X`
  have hsign : ∀ j ∈ X, cl j → 0 ≤ wGen a T X v j := by
    intro j _ hc
    by_cases hjT : j ∈ rowsT T
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hjT
      rw [wGen_T hinj]
      have h1 := hE l
      rw [abs_le] at h1
      have hρ : rhoT a y T x₀ l - D ≤ rhoT a y T x l := by
        have := hD (T l) (Finset.mem_union_left _ (Finset.mem_union_left _ (hTb (mem_rowsT T l))))
        rw [abs_le] at this
        simp only [rhoT]; linarith [this.1]
      have hm := hTmarg l hc
      have : τ ≤ rhoT a y T x₀ l := hm
      linarith [h1.1]
    · rw [wGen_of_not_mem hjT]
      by_cases hJ : j ∈ Jr
      · rw [hvJ j hJ]; exact hμ j hJ
      · rw [hvn j hJ]; exact resC_nonneg_of_clip hc
  -- слабая двойственность для кандидата
  have hweak := rowObj_le_psiC (y := y) (isStat_wGen hdet hTX v) hsign x'
  have hge := rowObj_wGen_ge (cl := cl) hdet hTX v x (Jp := Jr)
    (fun j _ hJ => hvn j hJ)
  -- фильтр — это `J'`
  have hfilt : (X \ rowsT T).filter (· ∈ Jr) = Jr := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h
      exact ⟨⟨Finset.mem_union_left _ (Finset.mem_union_right _ h),
        fun hT => Finset.disjoint_left.mp hJT h hT⟩, h⟩
  rw [hfilt] at hge
  have hJsum : ∑ j ∈ Jr, (v j - (y j - dotp (a j) x)) ^ 2
      = ∑ j ∈ Jr, (μ j - (y j - dotp (a j) x)) ^ 2 :=
    Finset.sum_congr rfl fun j hj => by rw [hvJ j hj]
  rw [hJsum] at hge
  -- `Σ_l E_l² ≤ K·((k+1)D + kη)²`
  have hEsq : ∑ l, (omegaV a T X v l - rhoT a y T x l) ^ 2
      ≤ Fintype.card κ * (((k : ℝ) + 1) * D + k * η) ^ 2 := by
    calc ∑ l, (omegaV a T X v l - rhoT a y T x l) ^ 2
        ≤ ∑ _l : κ, (((k : ℝ) + 1) * D + k * η) ^ 2 := by
          refine Finset.sum_le_sum fun l _ => ?_
          have h := pow_le_pow_left₀ (abs_nonneg _) (hE l) 2
          rwa [sq_abs] at h
      _ = Fintype.card κ * (((k : ℝ) + 1) * D + k * η) ^ 2 := by simp
  -- `ψ_X(x) ≥ ψ_Y(x) − kζ`
  have hψXY : psiC a y cl Y x - k * ζ ≤ psiC a y cl X x := by
    have eX : psiC a y cl X x = psiC a y cl base x + psiC a y cl Jr x + scoreA a y R x := by
      rw [hX, psiC, Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdR, hdJR⟩),
        Finset.sum_union hdJ]
      simp only [scoreA, hRr, Finset.sum_map]; rfl
    have eY : psiC a y cl Y x = psiC a y cl base x + scoreA a y US x + psiC a y cl Jr x := by
      rw [hY, psiC, Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdJ, hdJU.symm⟩),
        Finset.sum_union hbUr]
      simp only [scoreA, hUr, Finset.sum_map]; rfl
    rw [eX, eY]; linarith
  -- слабая двойственность для цели
  have hweakY : rowObj y Y ω' ≤ psiC a y cl Y x := by
    refine rowObj_le_psiC hstat (fun j hj hc => ?_) x
    by_cases hJ : j ∈ Jr
    · rw [hω'J j hJ]; exact hμ j hJ
    · rw [hω'n j hJ]
      have hjbU : j ∈ base ∪ Ur := by
        rcases Finset.mem_union.mp hj with h | h
        · exact h
        · exact absurd h hJ
      exact hself j hjbU hc
  linarith

end UnivCore

/-! ### Представитель корзины -/

section UnivRep

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {a : ι ⊕ κ → κ → ℝ} {y : ι ⊕ κ → ℝ} {T : κ → ι ⊕ κ}

/-- **Представитель корзины.** В таблице рюкзака (допуск `univAdm`, ключ `sfKey`) есть набор `R`
той же мощности, что `U_S = A_N ∖ T_A`, из допущенных активов (не из `T`, не из `J'`), с
`|κ_R − κ_{U_S}|_∞ ≤ kη` и счётом не меньше счёта `U_S` минус `kζ`. -/
theorem univ_rep_exists {AN Jp : Finset ι} {x : κ → ℝ} {k : ℕ} {η ζ : ℝ} {Zk Zq : ℤ}
    {La : List ι} (hη : 0 < η) (hζ : 0 < ζ) (hnd : La.Nodup)
    (hall : ∀ i, i ∈ La) (hcfS : ∀ j ∈ barK (κ := κ) AN, ∀ m, |cf a T j m| ≤ 1)
    (hANk : AN.card ≤ k) (hdisj : Disjoint AN Jp)
    (hZk : Real.sqrt ((AN \ assetsT T).card * scoreA a y (AN \ assetsT T) x) / η + k ≤ Zk)
    (hZq : scoreA a y (AN \ assetsT T) x / ζ ≤ Zq) :
    ∃ R ∈ knap (univVal a y x) (sfKey a y (fun r => r.isLeft) T η ζ x)
        (sfBox κ Zk Zq k) (La.filter (univAdm a T Jp)),
      R.card = (AN \ assetsT T).card
      ∧ (∀ i ∈ R, (Sum.inl i : ι ⊕ κ) ∉ rowsT T ∧ i ∉ Jp)
      ∧ (∀ m, |kapA a y T R x m - kapA a y T (AN \ assetsT T) x m| ≤ k * η)
      ∧ scoreA a y (AN \ assetsT T) x ≤ scoreA a y R x + k * ζ := by
  classical
  set US := AN \ assetsT T with hUS
  have hnotT : ∀ i ∈ US, (Sum.inl i : ι ⊕ κ) ∉ rowsT T := fun i hi hT =>
    (Finset.mem_sdiff.mp hi).2 (mem_assetsT.mpr hT)
  have hnotJ : ∀ i ∈ US, i ∉ Jp := fun i hi hJ =>
    Finset.disjoint_left.mp hdisj (Finset.mem_sdiff.mp hi).1 hJ
  have hUSA : ∀ i ∈ US, (Sum.inl i : ι ⊕ κ) ∈ barK (κ := κ) AN := fun i hi =>
    inl_mem_barK (Finset.mem_sdiff.mp hi).1
  have hUSk : US.card ≤ k := le_trans (Finset.card_le_card Finset.sdiff_subset) hANk
  have hbox := sfKey_sum_mem_box (a := a) (y := y) (cl := fun r => r.isLeft) (T := T) (x := x)
    hη hζ (fun i _ => rfl) (fun i hi m => hcfS _ (hUSA i hi) m) hUSk hZk hZq
  have hUSL : US ⊆ (La.filter (univAdm a T Jp)).toFinset := by
    intro i hi
    rw [List.mem_toFinset, List.mem_filter]
    refine ⟨hall i, ?_⟩
    simp only [univAdm, decide_eq_true_eq]
    exact ⟨hnotT i hi, hnotJ i hi, fun m => hcfS _ (hUSA i hi) m⟩
  obtain ⟨R, hRmem, hRkey, -⟩ := knap_spec (univVal a y x)
    (sfKey a y (fun r => r.isLeft) T η ζ x) (sfBox κ Zk Zq k) (La.filter (univAdm a T Jp))
    (hnd.filter _) US hUSL hbox
  have hRL := knap_mem (univVal a y x)
    (sfKey a y (fun r => r.isLeft) T η ζ x) (sfBox κ Zk Zq k) (La.filter (univAdm a T Jp)) R hRmem
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
  have hk1 : 1 ≤ k ∨ US.card = 0 := by
    rcases Nat.eq_zero_or_pos US.card with h | h
    · exact Or.inr h
    · exact Or.inl (le_trans h hUSk)
  refine ⟨R, hRmem, hcardR, fun i hi => ?_, fun m => ?_, ?_⟩
  · have h := hRL hi
    rw [List.mem_toFinset, List.mem_filter] at h
    simp only [univAdm, decide_eq_true_eq] at h
    exact ⟨h.2.1, h.2.2.1⟩
  · rcases hk1 with hk1 | h0
    · refine (abs_kap_sub_lt_of_key_eq hη (by omega) ?_ ?_ ?_ m).le
      · rw [Finset.card_map, hcardR]; exact hUSk
      · rw [Finset.card_map, Finset.card_map, hcardR]
      · rw [Finset.sum_map, Finset.sum_map]; exact hkey1
    · have hR0 : R = ∅ := Finset.card_eq_zero.mp (hcardR.trans h0)
      have hU0 : US = ∅ := Finset.card_eq_zero.mp h0
      simp only [kapA, kapC, hR0, hU0, Finset.map_empty, Finset.sum_empty, sub_zero, abs_zero]
      positivity
  · rcases hk1 with hk1 | h0
    · have hlt := abs_sum_sub_lt_of_floor_eq
        (f := fun i => resC a y (fun r => r.isLeft) (Sum.inl i) x ^ 2) hζ (by omega) hUSk
        hcardR.symm hkey2.symm
      rw [abs_lt] at hlt
      simp only [scoreA]
      linarith [hlt.2]
    · have hR0 : R = ∅ := Finset.card_eq_zero.mp (hcardR.trans h0)
      have hU0 : US = ∅ := Finset.card_eq_zero.mp h0
      simp only [scoreA, hR0, hU0, Finset.sum_empty, zero_add]
      positivity

end UnivRep

/-- `u² ≤ 2w² + 2D²` при `|u − w| ≤ D`. -/
lemma sq_le_two_sq_add {u w D : ℝ} (h : |u - w| ≤ D) : u ^ 2 ≤ 2 * w ^ 2 + 2 * D ^ 2 := by
  have h1 : (u - w) ^ 2 ≤ D ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  nlinarith [sq_nonneg (u - 2 * w)]

/-! ### Одна догадка -/

section UnivOneGuess

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- **Шаг схемы при одной догадке — без условия на оптимум.** `A₀` — набор активов, `|A₀| ≤ k`,
`x₀` — двойственная точка (нормальные уравнения `barK A₀`, все активы активны),
`F = φ(barK A₀, x₀) = F_LO(A₀)`, догадка `V ≤ F ≤ 2V`. Тогда в `univFamily` есть кандидат `W` с
`ψ_{W̄}(x') ≥ (1 − 2ε)·F` при всех `x'`, то есть `F_LO(W) ≥ (1 − 2ε)·F_LO(A₀)`. Ни в гипотезах,
ни в схеме нет `ω`. -/
theorem univ_one_guess [Nonempty κ] (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    {A₀ : Finset ι} {x₀ : κ → ℝ} (hA₀k : A₀.card ≤ k)
    (hnorm : IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀)
    (hself : ∀ r ∈ barK (κ := κ) A₀, r.isLeft →
      0 ≤ targetsK m d r - dotp (rowsK d B G r) x₀)
    (hVF : V ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀)
    (hFV : phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀ ≤ 2 * V) :
    ∃ W ∈ univFamily m d B G k ε V La, ∀ x' : κ → ℝ,
      (1 - 2 * ε) * phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀
        ≤ psiC (rowsK d B G) (targetsK m d) (fun r => r.isLeft) (barK (κ := κ) W) x' := by
  classical
  set a := rowsK d B G with ha
  set y := targetsK m d with hy
  set cl : ι ⊕ κ → Bool := fun r => r.isLeft with hcl
  set F := phi a y (barK (κ := κ) A₀) x₀ with hF
  set r : ι ⊕ κ → ℝ := fun j => y j - dotp (a j) x₀ with hr
  set τ := Real.sqrt (ε * V) / (3 * k) with hτ
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hK := card_pos_real (κ := κ)
  have hτ0 : 0 ≤ τ := by positivity
  -- малые (`AJ`) и немалые (`AN`) активы оптимума
  set AJ := A₀.filter (fun i => r (Sum.inl i) < τ) with hAJ
  set AN := A₀.filter (fun i => ¬ r (Sum.inl i) < τ) with hAN
  have hA₀eq : AN ∪ AJ = A₀ := by
    rw [Finset.union_comm]
    exact Finset.filter_union_filter_not_eq (p := fun i => r (Sum.inl i) < τ) A₀
  have hdNJ : Disjoint AN AJ :=
    (Finset.disjoint_filter_filter_not A₀ A₀ (fun i => r (Sum.inl i) < τ)).symm
  have hANA : AN ⊆ A₀ := Finset.filter_subset _ _
  have hAJA : AJ ⊆ A₀ := Finset.filter_subset _ _
  have hr0 : ∀ i ∈ A₀, 0 ≤ r (Sum.inl i) := fun i hi => hself _ (inl_mem_barK hi) rfl
  -- Каратеодори на малых активах
  obtain ⟨J'a, hJ'sub, hJ'card, μa, hμa0, hμsum, hμvec⟩ :=
    exists_carath (fun i => a (Sum.inl i)) AJ (fun i => r (Sum.inl i))
      (fun i hi => hr0 i (hAJA hi))
  set Jr := J'a.map (inlE ι κ) with hJr
  set μ : ι ⊕ κ → ℝ := Sum.elim μa (fun _ => 0) with hμ
  have hμ0 : ∀ j ∈ Jr, 0 ≤ μ j := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    exact hμa0 i hi
  have hSeq : barK (κ := κ) A₀ = barK (κ := κ) AN ∪ AJ.map (inlE ι κ) := by
    rw [← barK_union_map, hA₀eq]
  have hcar := rowObj_carath (a := a) (y := y) (S := barK (κ := κ) A₀) (N := barK (κ := κ) AN)
    (J := AJ.map (inlE ι κ)) (J' := Jr) (x₀ := x₀) (μ := μ) hSeq (disjoint_barK_map hdNJ)
    (Finset.map_subset_map.mpr hJ'sub) hnorm (fun c => by
      rw [Finset.sum_map, Finset.sum_map]
      exact hμvec c)
  obtain ⟨hstat0, hobj0⟩ := hcar
  -- потеря от замены: `≤ 2W²`, `W ≤ kτ`
  set W := ∑ i ∈ AJ, r (Sum.inl i) with hW
  have hloss := carath_loss_le (J := AJ.map (inlE ι κ)) (J' := Jr) (r := r) (μ := μ)
    (Finset.map_subset_map.mpr hJ'sub)
    (fun j hj => by obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj; exact hr0 i (hAJA hi)) hμ0
    (by rw [Finset.sum_map, Finset.sum_map]; exact hμsum)
  have hWmap : ∑ j ∈ AJ.map (inlE ι κ), r j = W := by rw [Finset.sum_map]; rfl
  rw [hWmap] at hloss
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i hi => hr0 i (hAJA hi)
  have hWk : W ≤ k * τ := by
    calc W ≤ ∑ _i ∈ AJ, τ := Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2.le
      _ = AJ.card * τ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ k * τ := by
          have : (AJ.card : ℝ) ≤ k := by
            exact_mod_cast le_trans (Finset.card_le_card hAJA) hA₀k
          exact mul_le_mul_of_nonneg_right this hτ0
  -- базис свидетеля `T` (немалые строки) и базис решётки `T₂` (немалые строки и `J'`)
  obtain ⟨T, hmaxT⟩ := exists_maxvol_barK (d := d) (B := B) (G := G) (S := AN)
  have hdetT : (rowMat a T).det ≠ 0 := maxvol_det_ne_zero (P := P) (Sf := Sf) hmaxT hG hPS
  obtain ⟨T₂, hmaxT₂⟩ := exists_maxvol_barK (d := d) (B := B) (G := G) (S := AN ∪ J'a)
  have hdetT₂ : (rowMat a T₂).det ≠ 0 :=
    maxvol_det_ne_zero (P := P) (Sf := Sf) hmaxT₂ hG hPS
  have hTAN : rowsT T ⊆ barK (κ := κ) AN := by
    intro j hj
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hj
    exact hmaxT.1 l
  have hTA : assetsT T ⊆ AN := assetsT_subset hTAN
  have hcfT : ∀ j ∈ barK (κ := κ) AN, ∀ l, |cf a T j l| ≤ 1 :=
    fun j hj l => abs_cf_le_one hmaxT hdetT hj l
  -- узел
  set s := univStep κ k ε V with hs
  have hs0 : 0 < s := univStep_pos hk1 hε hV
  obtain ⟨z, -, hzs, hzb⟩ := exists_corner hs0 (rhoT a y T₂ x₀) (fun _ => 0)
  set x := sfNode a y T₂ s z with hx
  have hrho : ∀ mm, rhoT a y T₂ x mm = s * z mm := fun mm => sfNode_rho hdetT₂ s z mm
  have hD2 : ∀ mm, |rhoT a y T₂ x mm - rhoT a y T₂ x₀ mm| ≤ s := by
    intro mm; rw [hrho]; exact hzs mm
  set D := (Fintype.card κ : ℝ) * s with hDdef
  have hD0 : 0 ≤ D := by positivity
  have hbarAJ : barK (κ := κ) (AN ∪ J'a) = barK (κ := κ) AN ∪ Jr := barK_union_map AN J'a
  have hDrow : ∀ j ∈ barK (κ := κ) AN ∪ Jr,
      |(y j - dotp (a j) x) - (y j - dotp (a j) x₀)| ≤ D := by
    intro j hj
    rw [← hbarAJ] at hj
    exact abs_res_sub_le hdetT₂ (fun mm => abs_cf_le_one hmaxT₂ hdetT₂ hj mm) hD2
  -- номер узла в коробке
  have hsubA : AN ∪ J'a ⊆ A₀ := Finset.union_subset hANA (le_trans hJ'sub hAJA)
  have hzZ : z ∈ nodeBox (κ := κ) (univZ κ k ε) := by
    refine mem_nodeBox_of_abs_le fun mm => ?_
    have hρ0 : |rhoT a y T₂ x₀ mm| ≤ Real.sqrt (2 * V) := by
      have hmem : T₂ mm ∈ barK (κ := κ) A₀ := by
        have h1 := hmaxT₂.1 mm
        rcases hT : T₂ mm with i | l
        · rw [hT] at h1
          have : i ∈ AN ∪ J'a := by simpa [barK, Finset.inl_mem_disjSum] using h1
          exact inl_mem_barK (hsubA this)
        · exact inr_mem_barK A₀ l
      have hsq1 : (rhoT a y T₂ x₀ mm) ^ 2 ≤ F := by
        have h1 := Finset.single_le_sum
          (f := fun j => (dotp (a j) x₀ - y j) ^ 2) (fun _ _ => sq_nonneg _) hmem
        have h2 : (rhoT a y T₂ x₀ mm) ^ 2 = (dotp (a (T₂ mm)) x₀ - y (T₂ mm)) ^ 2 := by
          simp only [rhoT]; ring
        rw [h2, hF, phi]; exact h1
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
    have hb : |rhoT a y T₂ x₀ mm| / s
        ≤ 12 * (k : ℝ) * (k + 1) * Fintype.card κ * Real.sqrt (2 * Fintype.card κ / ε) := by
      rw [div_le_iff₀ hs0, univ_node_radius hk1 hε hV]; exact hρ0
    have hceil : 12 * (k : ℝ) * (k + 1) * Fintype.card κ * Real.sqrt (2 * Fintype.card κ / ε)
        ≤ (⌈12 * (k : ℝ) * (k + 1) * Fintype.card κ
            * Real.sqrt (2 * Fintype.card κ / ε)⌉₊ : ℝ) := Nat.le_ceil _
    have hz := hzb mm
    rw [univZ]; push_cast
    linarith
  -- цель в узле: `U_S = A_N ∖ T_A`
  set US := AN \ assetsT T with hUS
  set base := barK (κ := κ) (assetsT T) with hbase
  have hNeq : barK (κ := κ) AN = base ∪ US.map (inlE ι κ) := by
    rw [hbase, ← barK_union_map, Finset.union_sdiff_of_subset hTA]
  have hUSk : US.card ≤ k :=
    le_trans (Finset.card_le_card Finset.sdiff_subset) (le_trans (Finset.card_le_card hANA) hA₀k)
  have hη0 := univEta_pos (κ := κ) hk1 hε hV
  have hζ0 := sfZeta_pos hk1 hε hV
  -- счёт `U_S` в узле: `≤ (4+ε)V`
  have hscoreUS : scoreA a y US x ≤ (4 + ε) * V := by
    have h1 : ∀ i ∈ US, resC a y cl (Sum.inl i) x ^ 2
        ≤ 2 * r (Sum.inl i) ^ 2 + 2 * D ^ 2 := by
      intro i hi
      have hmem : (Sum.inl i : ι ⊕ κ) ∈ barK (κ := κ) AN ∪ Jr :=
        Finset.mem_union_left _ (inl_mem_barK (Finset.mem_sdiff.mp hi).1)
      have hb := hDrow _ hmem
      have h2 := sq_resC_le_sq (a := a) (y := y) (cl := cl) (Sum.inl i) x
      have := sq_le_two_sq_add hb
      linarith
    have h2 : ∑ i ∈ US, r (Sum.inl i) ^ 2 ≤ F := by
      have hsub : US.map (inlE ι κ) ⊆ barK (κ := κ) A₀ := by
        intro j hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
        exact inl_mem_barK (hANA (Finset.mem_sdiff.mp hi).1)
      have := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (f := fun j => (dotp (a j) x₀ - y j) ^ 2) (fun _ _ _ => sq_nonneg _)
      rw [Finset.sum_map] at this
      rw [hF, phi]
      calc ∑ i ∈ US, r (Sum.inl i) ^ 2
          = ∑ i ∈ US, (dotp (a ((inlE ι κ) i)) x₀ - y ((inlE ι κ) i)) ^ 2 :=
            Finset.sum_congr rfl fun i _ => by
              rw [show (inlE ι κ) i = Sum.inl i from rfl]; simp only [hr]; ring
        _ ≤ _ := this
    have h3 : scoreA a y US x ≤ 2 * F + 2 * US.card * D ^ 2 := by
      calc scoreA a y US x = ∑ i ∈ US, resC a y cl (Sum.inl i) x ^ 2 := rfl
        _ ≤ ∑ i ∈ US, (2 * r (Sum.inl i) ^ 2 + 2 * D ^ 2) := Finset.sum_le_sum h1
        _ = 2 * ∑ i ∈ US, r (Sum.inl i) ^ 2 + 2 * US.card * D ^ 2 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ 2 * F + 2 * US.card * D ^ 2 := by linarith
    have h4 : 2 * (US.card : ℝ) * D ^ 2 ≤ 2 * k * D ^ 2 := by
      have : (US.card : ℝ) ≤ k := by exact_mod_cast hUSk
      have hD2' : 0 ≤ D ^ 2 := sq_nonneg _
      nlinarith
    have h5 := univ_D_sq_k (κ := κ) hk1 hε.le hV.le
    nlinarith
  have hZk : Real.sqrt (US.card * scoreA a y US x) / univEta κ k ε V + k ≤ univZk κ k ε := by
    have h1 : Real.sqrt (US.card * scoreA a y US x) ≤ Real.sqrt ((k : ℝ) * ((4 + ε) * V)) := by
      refine Real.sqrt_le_sqrt ?_
      have hc : (US.card : ℝ) ≤ k := by exact_mod_cast hUSk
      have hs0' : 0 ≤ scoreA a y US x := Finset.sum_nonneg fun _ _ => sq_nonneg _
      exact mul_le_mul hc hscoreUS hs0' (by positivity)
    have h2 := univ_key_radius (κ := κ) hk1 hε hV
    have h3 : 12 * (k : ℝ) ^ 2 * Real.sqrt (Fintype.card κ) * Real.sqrt (k * (4 + ε) / ε)
        ≤ (⌈12 * (k : ℝ) ^ 2 * Real.sqrt (Fintype.card κ) * Real.sqrt (k * (4 + ε) / ε)⌉ : ℝ) :=
      Int.le_ceil _
    have h4 := div_le_div_of_nonneg_right h1 hη0.le
    rw [univZk]; push_cast
    linarith
  have hZq : scoreA a y US x / sfZeta k ε V ≤ univZq k ε := by
    have h1 := div_le_div_of_nonneg_right hscoreUS hζ0.le
    rw [univ_score_radius hk1 hε hV] at h1
    have h2 : (4 + ε) * (k : ℝ) / ε ≤ (⌈(4 + ε) * (k : ℝ) / ε⌉ : ℝ) := Int.le_ceil _
    rw [univZq]
    linarith
  have hdisjNJ' : Disjoint AN J'a := Finset.disjoint_of_subset_right hJ'sub hdNJ
  have hANk : AN.card ≤ k := le_trans (Finset.card_le_card hANA) hA₀k
  obtain ⟨R, hRmem, hcardR, hRadm, hkeyc, hscore⟩ :=
    univ_rep_exists (a := a) (y := y) (T := T) (x := x) (La := La)
      (Zk := univZk κ k ε) (Zq := univZq k ε) hη0 hζ0 hnd hall hcfT hANk hdisjNJ' hZk hZq
  -- набор `J'` как `optSet f`
  obtain ⟨f, hf⟩ := exists_optSet (κ := κ) (S := J'a) hJ'card
  -- свидетель
  have hdTJ : Disjoint (assetsT T) J'a := Finset.disjoint_of_subset_left hTA hdisjNJ'
  have hdTR : Disjoint (assetsT T) R := by
    rw [Finset.disjoint_left]
    intro i hiT hiR
    exact (hRadm i hiR).1 (mem_assetsT.mp hiT)
  have hdTU : Disjoint (assetsT T) US := Finset.disjoint_sdiff
  have hdJ'R : Disjoint J'a R := by
    rw [Finset.disjoint_left]
    intro i hiJ hiR
    exact (hRadm i hiR).2 hiJ
  have hdJ'U : Disjoint J'a US :=
    Finset.disjoint_of_subset_right Finset.sdiff_subset hdisjNJ'.symm
  have hstat : RowStat a (base ∪ US.map (inlE ι κ) ∪ Jr)
      (fun j => if j ∈ Jr then μ j else y j - dotp (a j) x₀) := by
    rw [← hNeq]; exact hstat0
  have hself' : ∀ j ∈ base ∪ US.map (inlE ι κ), j.isLeft → 0 ≤ y j - dotp (a j) x₀ := by
    rw [← hNeq]
    intro j hj hc
    refine hself j ?_ hc
    rw [hSeq]; exact Finset.mem_union_left _ hj
  have hTmarg : ∀ l, (T l).isLeft → τ ≤ y (T l) - dotp (a (T l)) x₀ := by
    intro l hc
    have h1 := hmaxT.1 l
    rcases hT : T l with i | j
    · rw [hT] at h1
      have hi : i ∈ AN := by simpa [barK, Finset.inl_mem_disjSum] using h1
      have := (Finset.mem_filter.mp hi).2
      exact not_lt.mp this
    · rw [hT] at hc; simp at hc
  have hD' : ∀ j ∈ base ∪ US.map (inlE ι κ) ∪ Jr,
      |(y j - dotp (a j) x) - (y j - dotp (a j) x₀)| ≤ D := by
    rw [← hNeq]; exact hDrow
  have hcf' : ∀ j ∈ base ∪ US.map (inlE ι κ), ∀ l, |cf a T j l| ≤ 1 := by
    rw [← hNeq]; exact hcfT
  have hcard : (base \ rowsT T).card + US.card ≤ k := by
    have h1 : (base \ rowsT T).card = (assetsT T).card := by
      rw [Finset.card_sdiff_of_subset (rowsT_subset_barK_assetsT T), card_barK,
        card_rowsT hdetT]
      omega
    have h2 : US.card = AN.card - (assetsT T).card := Finset.card_sdiff_of_subset hTA
    have h3 : (assetsT T).card ≤ AN.card := Finset.card_le_card hTA
    omega
  have hthr : D + (((k : ℝ) + 1) * D + k * univEta κ k ε V) ≤ τ := univ_margin hk1 ε V
  have hcert := univ_cert (μ := μ) (x₀ := x₀) (x := x) (k := k) (D := D)
    (η := univEta κ k ε V) (τ := τ) (ζ := sfZeta k ε V) hdetT
    (rowsT_subset_barK_assetsT T) (disjoint_barK_map hdTJ) (disjoint_barK_map hdTR)
    (disjoint_barK_map hdTU) ((Finset.disjoint_map _).mpr hdJ'R)
    ((Finset.disjoint_map _).mpr hdJ'U) hμ0 hstat hself' hTmarg hD' hcf' hkeyc hscore hcard hthr
  -- кандидат
  refine ⟨assetsT T ∪ J'a ∪ R, ?_, fun x' => ?_⟩
  · have hRT : R ∈ univTable m d B G k ε V T T₂ (optSet f) z La := by
      unfold univTable; rw [hf]; exact hRmem
    have hcardW : (assetsT T ∪ J'a ∪ R).card ≤ k := by
      calc (assetsT T ∪ J'a ∪ R).card ≤ (assetsT T ∪ J'a).card + R.card :=
            Finset.card_union_le _ _
        _ ≤ (assetsT T).card + J'a.card + R.card := by
            have := Finset.card_union_le (assetsT T) J'a; omega
        _ = (assetsT T).card + US.card + J'a.card := by rw [hcardR]; ring
        _ = AN.card + J'a.card := by
            rw [Finset.card_sdiff_of_subset hTA]
            have := Finset.card_le_card hTA; omega
        _ ≤ AN.card + AJ.card := by have := Finset.card_le_card hJ'sub; omega
        _ = A₀.card := by rw [← Finset.card_union_of_disjoint hdNJ, hA₀eq]
        _ ≤ k := hA₀k
    unfold univFamily
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter,
      Finset.mem_image]
    exact ⟨T, T₂, f, z, hzZ, ⟨R, hRT, by rw [hf]⟩, hcardW⟩
  · -- значение
    have hX : barK (κ := κ) (assetsT T ∪ J'a ∪ R) = base ∪ Jr ∪ R.map (inlE ι κ) := by
      rw [barK_union_map, barK_union_map]
    rw [hX]
    have hc : rowObj y (base ∪ US.map (inlE ι κ) ∪ Jr)
          (fun j => if j ∈ Jr then μ j else y j - dotp (a j) x₀)
        - k * sfZeta k ε V - ∑ j ∈ Jr, (μ j - (y j - dotp (a j) x)) ^ 2
        - Fintype.card κ * (((k : ℝ) + 1) * D + k * univEta κ k ε V) ^ 2
        ≤ psiC a y cl (base ∪ Jr ∪ R.map (inlE ι κ)) x' := hcert x'
    -- `obj(Y, ω') = F − потеря ≥ F − 2W²`
    have hobj : F - 2 * W ^ 2 ≤ rowObj y (base ∪ US.map (inlE ι κ) ∪ Jr)
        (fun j => if j ∈ Jr then μ j else y j - dotp (a j) x₀) := by
      rw [← hNeq, hobj0]
      have : ∑ j ∈ AJ.map (inlE ι κ) \ Jr, (y j - dotp (a j) x₀) ^ 2
          + ∑ j ∈ Jr, (μ j - (y j - dotp (a j) x₀)) ^ 2 ≤ 2 * W ^ 2 := hloss
      linarith
    -- член `J'`: `≤ 4W² + 2(K+1)D²`
    have hJ'term : ∑ j ∈ Jr, (μ j - (y j - dotp (a j) x)) ^ 2
        ≤ 4 * W ^ 2 + 2 * ((Fintype.card κ : ℝ) + 1) * D ^ 2 := by
      have h1 : ∀ j ∈ Jr, (μ j - (y j - dotp (a j) x)) ^ 2
          ≤ 2 * (μ j - (y j - dotp (a j) x₀)) ^ 2 + 2 * D ^ 2 := by
        intro j hj
        have hb := hDrow j (Finset.mem_union_right _ hj)
        have hb' : |(μ j - (y j - dotp (a j) x)) - (μ j - (y j - dotp (a j) x₀))| ≤ D := by
          rw [show (μ j - (y j - dotp (a j) x)) - (μ j - (y j - dotp (a j) x₀))
            = -((y j - dotp (a j) x) - (y j - dotp (a j) x₀)) by ring, abs_neg]
          exact hb
        exact sq_le_two_sq_add hb'
      have h2 : ∑ j ∈ Jr, (μ j - (y j - dotp (a j) x₀)) ^ 2 ≤ 2 * W ^ 2 := by
        have h0 : 0 ≤ ∑ j ∈ AJ.map (inlE ι κ) \ Jr, (y j - dotp (a j) x₀) ^ 2 :=
          Finset.sum_nonneg fun _ _ => sq_nonneg _
        have : ∑ j ∈ AJ.map (inlE ι κ) \ Jr, (y j - dotp (a j) x₀) ^ 2
            + ∑ j ∈ Jr, (μ j - (y j - dotp (a j) x₀)) ^ 2 ≤ 2 * W ^ 2 := hloss
        linarith
      have h3 : (Jr.card : ℝ) ≤ Fintype.card κ + 1 := by
        rw [hJr, Finset.card_map]; exact_mod_cast hJ'card
      calc ∑ j ∈ Jr, (μ j - (y j - dotp (a j) x)) ^ 2
          ≤ ∑ j ∈ Jr, (2 * (μ j - (y j - dotp (a j) x₀)) ^ 2 + 2 * D ^ 2) :=
            Finset.sum_le_sum h1
        _ = 2 * ∑ j ∈ Jr, (μ j - (y j - dotp (a j) x₀)) ^ 2 + 2 * Jr.card * D ^ 2 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ 4 * W ^ 2 + 2 * ((Fintype.card κ : ℝ) + 1) * D ^ 2 := by
            have hD2' : 0 ≤ D ^ 2 := sq_nonneg _
            have : 2 * (Jr.card : ℝ) * D ^ 2 ≤ 2 * ((Fintype.card κ : ℝ) + 1) * D ^ 2 := by
              have := mul_le_mul_of_nonneg_right h3 hD2'
              linarith
            linarith
    -- числа
    have hWτ : W ^ 2 ≤ ε * V / 9 := by
      have h1 : W ^ 2 ≤ (k * τ) ^ 2 := pow_le_pow_left₀ hW0 hWk 2
      have h2 := univ_tau_sq hk1 hε.le hV.le
      rw [mul_pow] at h1
      rw [hτ] at h1
      linarith
    have hζk : (k : ℝ) * sfZeta k ε V = ε * V := k_sfZeta hk1 ε V
    have hE2 : (Fintype.card κ : ℝ) * (((k : ℝ) + 1) * D + k * univEta κ k ε V) ^ 2
        ≤ ε * V / 36 := by
      rw [hDdef, univ_err hk1, univ_err_sq hk1 hε.le hV.le]
      have h36 : (36 : ℝ) ≤ 36 * (k : ℝ) ^ 2 := by
        have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
        have : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
        linarith
      exact div_le_div_of_nonneg_left (by positivity) (by norm_num) h36
    have hD2 : 2 * ((Fintype.card κ : ℝ) + 1) * D ^ 2 ≤ ε * V / 144 :=
      univ_D_sq hk1 hε.le hV.le
    have hεV : ε * V ≤ ε * F := mul_le_mul_of_nonneg_left hVF hε.le
    have hεV0 : 0 ≤ ε * V := by positivity
    have hfin : (1 - 2 * ε) * F = F - 2 * (ε * F) := by ring
    rw [hfin]
    linarith

end UnivOneGuess

/-! ### Сквозная теорема из данных -/

section MainUniv

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- **В семействе схемы есть хороший кандидат** при любой вилке `L ≤ F ≤ 2^(J+1)L` для любого
набора `A₀` (`|A₀| ≤ k`, все активы активны в двойственной точке `x₀`), `F = F_LO(A₀)`. -/
theorem exists_good_univCandidate [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε L : ℝ} (hε : 0 < ε) (hL0 : 0 < L) {J : ℕ}
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La)
    {A₀ : Finset ι} {x₀ : κ → ℝ} (hA₀k : A₀.card ≤ k)
    (hnorm : IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀)
    (hself : ∀ r ∈ barK (κ := κ) A₀, r.isLeft →
      0 ≤ targetsK m d r - dotp (rowsK d B G r) x₀)
    (hLF : L ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀)
    (hFJ : phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀ ≤ 2 ^ (J + 1) * L) :
    ∃ W ∈ univCandidates m d B G k ε L J La, ∃ w : ι → ℝ, (∀ i ∈ W, 0 ≤ w i) ∧
      (1 - 2 * ε) * phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀
        ≤ objLO m d B Sf W w := by
  obtain ⟨j, hjJ, hVF, hFV⟩ := exists_doubling_guess_succ J hL0 hLF hFJ
  have hV : 0 < L * 2 ^ j := by positivity
  obtain ⟨W, hW, hval⟩ := univ_one_guess (Sf := Sf) (P := P) hG hPS hk1 hε hV hnd hall hA₀k
    hnorm hself hVF hFV
  obtain ⟨w, hw, hwv⟩ := exists_portfolio_of_psiC_ge (Sf := Sf) (P := P) hd hG hPS hval
  refine ⟨W, ?_, w, hw, hwv⟩
  unfold univCandidates
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (by omega), hW⟩

/-- **Схема без `ω` для long-only при любом фиксированном `K` — из данных, без условия на
оптимум.**

`V = diag(d) + BΣ_fB'`, `d > 0`, `G'G = Σ_f⁻¹`, `K ≥ 1`, `k ≥ 1`, `0 < ε < 1/2`,
`L = (m_i)_+²/V_ii > 0` — значение одиночного актива (естественный выбор — максимум по `i`),
`J = ⌈log₂((Σ_i(m_i)_+²/d_i)/L)⌉`, `La` — все активы без повторов. Тогда семейство
`univCandidates` обладает свойствами:
(1) размер не больше `(J+1)·(M+K)^K·(M+K)^K·(M+1)^{K+1}·(2Z+1)^K·(|box|+1)`
(`card_univCandidates_le`) — ни `ω`, ни величин входа, кроме числа догадок `J + 1`;
(2) у каждого кандидата не больше `k` активов; (3) лучшая пара существует; (4) для любой лучшей
пары `(R₀, w₀)` значение не меньше `(1 − 2ε)` от значения **любого** long-only портфеля с не
более чем `k` именами, а полностью инвестированный портфель `w₀/Σw₀` имеет коэффициент Шарпа не
меньше `√(1 − 2ε)` от коэффициента Шарпа любого такого портфеля с положительной доходностью. -/
theorem main_theorem_univ [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε L : ℝ} (hε : 0 < ε) (hε1 : 2 * ε < 1)
    (hL0 : 0 < L) (hLatt : ∃ i, max (m i) 0 ^ 2 / Vmat d B Sf i i = L)
    {J : ℕ} (hJ : J = ⌈Real.logb 2 ((∑ i, max (m i) 0 ^ 2 / d i) / L)⌉₊)
    {La : List ι} (hnd : La.Nodup) (hall : ∀ i, i ∈ La) :
    (univCandidates m d B G k ε L J La).card
        ≤ (J + 1) * ((Fintype.card ι + Fintype.card κ) ^ Fintype.card κ
          * ((Fintype.card ι + Fintype.card κ) ^ Fintype.card κ
            * ((Fintype.card ι + 1) ^ (Fintype.card κ + 1)
              * ((2 * univZ κ k ε + 1) ^ Fintype.card κ * (univBoxBound κ k ε + 1)))))
    ∧ (∀ W ∈ univCandidates m d B G k ε L J La, W.card ≤ k)
    ∧ (∃ R₀ ∈ univCandidates m d B G k ε L J La, ∃ w₀ : ι → ℝ,
        (∀ i ∈ R₀, 0 ≤ w₀ i) ∧
        ∀ R ∈ univCandidates m d B G k ε L J La, ∀ w : ι → ℝ,
          (∀ i ∈ R, 0 ≤ w i) → objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀)
    ∧ ∀ R₀ ∈ univCandidates m d B G k ε L J La, ∀ w₀ : ι → ℝ,
        (∀ i ∈ R₀, 0 ≤ w₀ i) →
        (∀ R ∈ univCandidates m d B G k ε L J La, ∀ w : ι → ℝ,
          (∀ i ∈ R, 0 ≤ w i) → objLO m d B Sf R w ≤ objLO m d B Sf R₀ w₀) →
        R₀.card ≤ k
        ∧ (∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
            (1 - 2 * ε) * objLO m d B Sf S' u ≤ objLO m d B Sf R₀ w₀)
        ∧ (∀ i ∈ R₀, 0 ≤ (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i)
        ∧ ∑ i ∈ R₀, (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i = 1
        ∧ ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
            0 < pRet m S' u →
            Real.sqrt (1 - 2 * ε) * sharpe m d B Sf S' u
              ≤ sharpe m d B Sf R₀ (fun i => (∑ j ∈ R₀, w₀ j)⁻¹ * w₀ i) := by
  -- оптимум: носитель `S` и его самосогласованный подноситель `A₀`
  obtain ⟨S, hSk, Fopt, hFoptG, hSopt⟩ := exists_optimal_support (m := m) (d := d) (B := B)
    (Sf := Sf) (P := P) (G := G) hd hG hPS k
  obtain ⟨A₀, -, x₀, hA₀S, hnorm, hself, hgreat⟩ :=
    exists_optimal_selfconsistent (m := m) (d := d) (B := B) (Sf := Sf) (P := P) (G := G)
      hd hG hPS S
  have hFeq : phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀ = Fopt :=
    hgreat.unique hFoptG
  have hA₀k : A₀.card ≤ k := le_trans hA₀S hSk
  have hopt : ∀ S' : Finset ι, S'.card ≤ k → ∀ u : ι → ℝ, (∀ i ∈ S', 0 ≤ u i) →
      objLO m d B Sf S' u ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀ := by
    rw [hFeq]; exact hSopt
  set F := phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) x₀ with hF
  -- вилка `[L, 2^(J+1)L]` без `ω`
  obtain ⟨ia, hia⟩ := hLatt
  have hLF : L ≤ F := hia ▸ opt_ge_single_of_opt (B := B) hd hG hPS hk1 hopt ia
  have hFU : F ≤ ∑ i, max (m i) 0 ^ 2 / d i := by
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
  obtain ⟨W, hW, w, hw, hgood⟩ := exists_good_univCandidate (Sf := Sf) (P := P) hd hG hPS hk1
    hε hL0 hnd hall hA₀k hnorm hself hLF hFJ
  refine ⟨card_univCandidates_le m d B G k ε L J La,
    fun R hR => card_le_of_mem_univCandidates hR,
    exists_best_set_of_family (P := P) (G := G) hd hG hPS ⟨W, hW⟩, ?_⟩
  intro R₀ hR₀ w₀ hw₀ hbest
  have hval : (1 - 2 * ε) * F ≤ objLO m d B Sf R₀ w₀ := le_trans hgood (hbest W hW w hw)
  obtain ⟨hx0, hx1, hxs⟩ := best_pair_sharpe_uniform (B := B) hd hG hPS
    (by linarith : ε < 1 / 2) (lt_of_lt_of_le hL0 hLF) hopt hw₀ hval
  refine ⟨card_le_of_mem_univCandidates hR₀, fun S' hS' u hu => ?_, hx0, hx1, hxs⟩
  have hub := hopt S' hS' u hu
  have hcoef : (0:ℝ) ≤ 1 - 2 * ε := by linarith
  linarith [mul_le_mul_of_nonneg_left hub hcoef]

end MainUniv

/-! ### Пример: два фактора, обе позиции оптимума малы

Два одинаковых актива, два фактора: `m = d = (1, 1)`, `B_i = (1, 0)`, `Σ_f = G = P = I₂`, так что
`V = [[2, 1], [1, 2]]`; `k = 2`, `ε = 1/10`, `L = m_i²/V_ii = 1/2`,
`J = ⌈log₂((Σ_i m_i²/d_i)/L)⌉ = ⌈log₂ 4⌉ = 2`, порядок `[0, 1]`. Оптимальный портфель
`w* = V⁻¹m = (1/3, 1/3)`, `OPT = 2/3`, двойственная точка `x₀ = (2/3, 0)`; **обе** позиции малы:
`√d_i·w*_i = 1/3 < 2√(ε·OPT/K) = 2/√30` (`univ_instance_two_small`) — у этого оптимума не одна, а
две малые позиции, так что в класс схемы одного кортежа (`main_theorem_sf`, Замечание 5.15) он не
попадает; сквозная теорема `main_theorem_univ` применима без условий и даёт лучшую пару со значением
`≥ (1 − 2ε)·OPT = 8/15` (`univ_instance_two`). -/

/-- Единичный вектор длины `2` (`m = d = (1, 1)`). -/
noncomputable def twoOnes : Fin 2 → ℝ := fun _ => 1

/-- Нагрузки примера: оба актива `B_i = (1, 0)`. -/
noncomputable def twoBK : Fin 2 → Fin 2 → ℝ := fun _ => ![1, 0]

theorem univ_instance_two :
    ∃ R₀ ∈ univCandidates twoOnes twoOnes twoBK k2I 2 (1 / 10) (1 / 2) 2 [0, 1],
      ∃ w₀ : Fin 2 → ℝ, (∀ i ∈ R₀, 0 ≤ w₀ i) ∧
        (8 / 15 : ℝ) ≤ objLO twoOnes twoOnes twoBK k2I R₀ w₀ := by
  have hd : ∀ i, 0 < twoOnes i := fun _ => one_pos
  have hG : ∀ j j' : Fin 2, ∑ l : Fin 2, k2I l j * k2I l j' = k2I j j' := by
    intro j j'; fin_cases j <;> fin_cases j' <;> simp [k2I]
  have hPS : ∀ j j' : Fin 2, ∑ l : Fin 2, k2I j l * k2I l j' = if j = j' then 1 else 0 := by
    intro j j'; fin_cases j <;> fin_cases j' <;> simp [k2I]
  have hVd : ∀ i, Vmat twoOnes twoBK k2I i i = 2 := by
    intro i; simp [Vmat, twoOnes, twoBK, k2I, Fin.sum_univ_two]; norm_num
  have hLatt : ∃ i, max (twoOnes i) 0 ^ 2 / Vmat twoOnes twoBK k2I i i = 1 / 2 :=
    ⟨0, by rw [hVd]; simp [twoOnes]⟩
  have hJlog : (2:ℕ) = ⌈Real.logb 2 ((∑ i, max (twoOnes i) 0 ^ 2 / twoOnes i) / (1 / 2))⌉₊ := by
    have h2 : (∑ i, max (twoOnes i) 0 ^ 2 / twoOnes i) / (1 / 2) = (2 : ℝ) ^ (2 : ℕ) := by
      norm_num [twoOnes, Fin.sum_univ_two]
    rw [h2, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  have hnd : ([0, 1] : List (Fin 2)).Nodup := by decide
  have hall : ∀ i : Fin 2, i ∈ ([0, 1] : List (Fin 2)) := by decide
  obtain ⟨_, _, ⟨R₀, hR₀, w₀, hw₀, hbest⟩, hall4⟩ := main_theorem_univ (m := twoOnes)
    (d := twoOnes) (B := twoBK) (Sf := k2I) (P := k2I) (G := k2I) hd hG hPS (k := 2)
    (by norm_num) (ε := 1 / 10) (by norm_num) (by norm_num) (by norm_num : (0:ℝ) < 1 / 2)
    hLatt hJlog hnd hall
  obtain ⟨_, hval, _⟩ := hall4 R₀ hR₀ w₀ hw₀ hbest
  refine ⟨R₀, hR₀, w₀, hw₀, ?_⟩
  have h1 := hval Finset.univ (by simp) (fun _ => 1 / 3) (fun _ _ => by norm_num)
  have h2 : objLO twoOnes twoOnes twoBK k2I Finset.univ (fun _ => 1 / 3) = 2 / 3 := by
    simp [objLO, Vmat, twoOnes, twoBK, k2I, Fin.sum_univ_two]; norm_num
  rw [h2] at h1
  linarith

/-- **Оптимум примера имеет две малые позиции.** Носитель `A₀ = {0, 1}` с двойственной точкой
`x₀ = (2/3, 0)`: нормальные уравнения, активность, значение `φ = 2/3`, оптимальность среди всех
long-only портфелей с не более чем двумя именами, и невязки (веса `√d_i w*_i`) обоих активов
равны `1/3 < 2√(ε·OPT/K)` при `ε = 1/10`, `K = 2`. -/
theorem univ_instance_two_small :
    IsNormal (rowsK twoOnes twoBK k2I) (targetsK twoOnes twoOnes)
        (barK (κ := Fin 2) Finset.univ) ![2 / 3, 0]
    ∧ (∀ r ∈ barK (κ := Fin 2) (Finset.univ : Finset (Fin 2)), r.isLeft →
        0 ≤ targetsK twoOnes twoOnes r - dotp (rowsK twoOnes twoBK k2I r) ![2 / 3, 0])
    ∧ phi (rowsK twoOnes twoBK k2I) (targetsK twoOnes twoOnes)
        (barK (κ := Fin 2) Finset.univ) ![2 / 3, 0] = 2 / 3
    ∧ (∀ S' : Finset (Fin 2), S'.card ≤ 2 → ∀ u : Fin 2 → ℝ, (∀ i ∈ S', 0 ≤ u i) →
        objLO twoOnes twoOnes twoBK k2I S' u ≤ 2 / 3)
    ∧ ∀ i : Fin 2,
        targetsK twoOnes twoOnes (Sum.inl i : Fin 2 ⊕ Fin 2)
            - dotp (rowsK twoOnes twoBK k2I (Sum.inl i)) ![2 / 3, 0] = 1 / 3
        ∧ (1 / 3 : ℝ) < 2 * Real.sqrt ((1 / 10) * (2 / 3) / Fintype.card (Fin 2)) := by
  have hd : ∀ i, 0 < twoOnes i := fun _ => one_pos
  have hG : ∀ j j' : Fin 2, ∑ l : Fin 2, k2I l j * k2I l j' = k2I j j' := by
    intro j j'; fin_cases j <;> fin_cases j' <;> simp [k2I]
  have hPS : ∀ j j' : Fin 2, ∑ l : Fin 2, k2I j l * k2I l j' = if j = j' then 1 else 0 := by
    intro j j'; fin_cases j <;> fin_cases j' <;> simp [k2I]
  have hrowL : ∀ (i : Fin 2) (v : Fin 2 → ℝ),
      dotp (rowsK twoOnes twoBK k2I (Sum.inl i)) v = v 0 := by
    intro i v; simp [rowsK, dotp, twoOnes, twoBK, Fin.sum_univ_two]
  have hrowR : ∀ (l : Fin 2) (v : Fin 2 → ℝ),
      dotp (rowsK twoOnes twoBK k2I (Sum.inr l)) v = v l := by
    intro l v; simp [rowsK, dotp, k2I]
  have hres : ∀ i : Fin 2, targetsK twoOnes twoOnes (Sum.inl i : Fin 2 ⊕ Fin 2)
      - dotp (rowsK twoOnes twoBK k2I (Sum.inl i)) ![2 / 3, 0] = 1 / 3 := by
    intro i; rw [hrowL]; simp [targetsK, twoOnes]; norm_num
  refine ⟨?_, ?_, ?_, ?_, fun i => ⟨hres i, ?_⟩⟩
  · intro v
    simp only [mom, barK, Finset.sum_disjSum, hrowL, hrowR]
    simp [targetsK, twoOnes, Fin.sum_univ_two]; ring
  · intro r _ hr
    rcases r with i | l
    · rw [hres i]; norm_num
    · simp at hr
  · simp only [phi, barK, Finset.sum_disjSum, hrowL, hrowR]
    simp [targetsK, twoOnes, Fin.sum_univ_two]; norm_num
  · intro S' hS' u hu
    refine le_trans (objLO_le_QLO (P := k2I) (G := k2I) hd hG hPS hu ![2 / 3, 0]) ?_
    have hS'1 : (S'.card : ℝ) ≤ 2 := by exact_mod_cast hS'
    have hq : QLO twoOnes twoOnes twoBK k2I S' ![2 / 3, 0] = 4 / 9 + S'.card * (1 / 9) := by
      simp [QLO, quadf, dotp, k2I, twoOnes, twoBK, Fin.sum_univ_two, Finset.sum_const]
      norm_num
    rw [hq]; linarith
  · rw [Fintype.card_fin]
    have h : (1 / 6 : ℝ) < Real.sqrt ((1 / 10) * (2 / 3) / (2 : ℕ)) := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith

end SparseSharpe.Factor
