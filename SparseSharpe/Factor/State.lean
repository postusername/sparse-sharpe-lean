import SparseSharpe.Factor.FPTASK

set_option linter.style.header false

/-!
# Состояние динамики в координатах `K`-ки и что из его округления следует

Динамика §3 спецификации хранит три величины, **аддитивные по активам**:

    Q(U)  = Σ_{i∈Ū} (⟨a_i,t⟩ − y_i)²            — скаляр
    M̃(U) = (Σ_{i∈Ū} cf(i,l)(y_i − ⟨a_i,t⟩))_l   — вектор в ℝ^K   (`momK`)
    Κ̃(U) = (Σ_{i∈Ū} cf(i,l)cf(i,l'))_{ll'}      — матрица K×K    (`gramK2`)

Здесь `cf` — коэффициенты Крамера максимально-объёмной `K`-ки, то есть это в точности
`A_T^{-T}(…)A_T⁻¹`-координаты, но выписанные без обращения матриц.

Файл доказывает две вещи, ради которых координаты `K`-ки и нужны:

* `mom_close` — евклидова близость `M̃` даёт нужную гипотезу шага FPTAS;
* `gram_half_of_entrywise` — **поэлементная (аддитивная!) близость `Κ̃` с точностью
  `1/(2K)` даёт мультипликативную оценку `gram(R,·) ≥ ½·gram(S,·)`.**
  Это и есть причина, по которой корзин по `Κ̃` нужно `poly(k,K)` штук, а не
  псевдополиномиально много: в координатах `K`-ки `Κ̃(S) ⪰ I` (нижняя часть зажима),
  поэтому аддитивное округление на фиксированном масштабе автоматически
  оказывается мультипликативным.

Итог — `fptasK_at_grid_node`: узел сетки плюс три свойства представителя ⟹
`F(R) ≥ (1 − 17ε/8)·F(S)`.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {S R : Finset ι} {T : κ → ι} {t th : κ → ℝ}

/-- Координаты направления `v` в невязках `K`-ки: `h_l(v) = ⟨a_{T_l}, v⟩`. -/
noncomputable def hcoord (a : ι → κ → ℝ) (T : κ → ι) (v : κ → ℝ) : κ → ℝ :=
  fun l => dotp (a (T l)) v

lemma gramK_eq_sum_hcoord (a : ι → κ → ℝ) (T : κ → ι) (v : κ → ℝ) :
    gramK a T v = ∑ l, (hcoord a T v l) ^ 2 := rfl

/-- Первый момент состояния динамики в координатах `K`-ки. -/
noncomputable def momK (a : ι → κ → ℝ) (y : ι → ℝ) (T : κ → ι) (U : Finset ι) (t : κ → ℝ) :
    κ → ℝ := fun l => ∑ i ∈ U, cf a T i l * (y i - dotp (a i) t)

/-- Форма Грама состояния динамики в координатах `K`-ки (матрица `Κ̃`). -/
noncomputable def gramK2 (a : ι → κ → ℝ) (T : κ → ι) (U : Finset ι) : κ → κ → ℝ :=
  fun l l' => ∑ i ∈ U, cf a T i l * cf a T i l'

/-- Обе величины аддитивны по носителю: шаг «взять актив `i`» сдвигает их на один и тот
же вклад у представителя и у истинного префикса. Это и позволяет вести по ним динамику. -/
lemma momK_insert [DecidableEq ι] {U : Finset ι} {i : ι} (hi : i ∉ U) (l : κ) :
    momK a y T (insert i U) t l = cf a T i l * (y i - dotp (a i) t) + momK a y T U t l := by
  simp [momK, Finset.sum_insert hi]

lemma gramK2_insert [DecidableEq ι] {U : Finset ι} {i : ι} (hi : i ∉ U) (l l' : κ) :
    gramK2 a T (insert i U) l l' = cf a T i l * cf a T i l' + gramK2 a T U l l' := by
  simp [gramK2, Finset.sum_insert hi]

lemma phi_insert [DecidableEq ι] {U : Finset ι} {i : ι} (hi : i ∉ U) :
    phi a y (insert i U) t = (dotp (a i) t - y i) ^ 2 + phi a y U t := by
  simp [phi, Finset.sum_insert hi]

/-- Первый момент через координаты `K`-ки. -/
theorem mom_eq_momK (hdet : (rowMat a T).det ≠ 0) (U : Finset ι) (v : κ → ℝ) :
    mom a y U t v = ∑ l, momK a y T U t l * hcoord a T v l := by
  simp only [mom, momK, hcoord, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotp_eq_sum_cf hdet i v, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- Форма Грама через координаты `K`-ки. -/
theorem gram_eq_gramK2 (hdet : (rowMat a T).det ≠ 0) (U : Finset ι) (v : κ → ℝ) :
    gram a U v = ∑ l, ∑ l', gramK2 a T U l l' * (hcoord a T v l * hcoord a T v l') := by
  have key : ∀ l l', gramK2 a T U l l' * (hcoord a T v l * hcoord a T v l')
      = ∑ i ∈ U, (cf a T i l * hcoord a T v l) * (cf a T i l' * hcoord a T v l') := by
    intro l l'
    rw [gramK2, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  calc gram a U v
      = ∑ i ∈ U, (∑ l, cf a T i l * hcoord a T v l)
          * (∑ l', cf a T i l' * hcoord a T v l') := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hcoord]
        rw [← dotp_eq_sum_cf hdet i v, ← sq]
    _ = ∑ i ∈ U, ∑ l, ∑ l',
          (cf a T i l * hcoord a T v l) * (cf a T i l' * hcoord a T v l') :=
        Finset.sum_congr rfl fun i _ => Finset.sum_mul_sum _ _ _ _
    _ = ∑ l, ∑ l', ∑ i ∈ U,
          (cf a T i l * hcoord a T v l) * (cf a T i l' * hcoord a T v l') := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ l, ∑ l', gramK2 a T U l l' * (hcoord a T v l * hcoord a T v l') :=
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => (key l l').symm

/-- **Из евклидовой близости `M̃` — гипотеза шага FPTAS.** -/
theorem mom_close (hdet : (rowMat a T).det ≠ 0) (hTS : ∀ l, T l ∈ S) {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hD : ∑ l, (momK a y T R t l - momK a y T S t l) ^ 2 ≤ Δ ^ 2) (v : κ → ℝ) :
    mom a y R t v - mom a y S t v ≤ Δ * Real.sqrt (gram a S v) := by
  have hrep : mom a y R t v - mom a y S t v
      = ∑ l, (momK a y T R t l - momK a y T S t l) * hcoord a T v l := by
    rw [mom_eq_momK hdet R v, mom_eq_momK hdet S v, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hcs := sum_mul_le_sqrt (fun l => momK a y T R t l - momK a y T S t l) (hcoord a T v)
  have h1 : Real.sqrt (∑ l, (momK a y T R t l - momK a y T S t l) ^ 2) ≤ Δ := by
    rw [show Δ = Real.sqrt (Δ ^ 2) from (Real.sqrt_sq hΔ0).symm]
    exact Real.sqrt_le_sqrt hD
  have h2 : Real.sqrt (∑ l, (hcoord a T v l) ^ 2) ≤ Real.sqrt (gram a S v) := by
    rw [← gramK_eq_sum_hcoord]
    exact Real.sqrt_le_sqrt (gramK_le_gram hTS hdet v)
  have hnn1 : (0:ℝ) ≤ Real.sqrt (∑ l, (hcoord a T v l) ^ 2) := Real.sqrt_nonneg _
  have hnn2 : (0:ℝ) ≤ Real.sqrt (∑ l, (momK a y T R t l - momK a y T S t l) ^ 2) :=
    Real.sqrt_nonneg _
  calc mom a y R t v - mom a y S t v
      = ∑ l, (momK a y T R t l - momK a y T S t l) * hcoord a T v l := hrep
    _ ≤ Real.sqrt (∑ l, (momK a y T R t l - momK a y T S t l) ^ 2)
          * Real.sqrt (∑ l, (hcoord a T v l) ^ 2) := hcs
    _ ≤ Δ * Real.sqrt (gram a S v) := by
        apply mul_le_mul h1 h2 hnn1 hΔ0

/-- **Аддитивное округление `Κ̃` оказывается мультипликативным.**
Поэлементная близость с точностью `ξ ≤ 1/(2K)` даёт `gram(R,·) ≥ ½·gram(S,·)` —
именно потому, что в координатах `K`-ки `gramK ≤ gram(S,·)` (нижняя часть зажима). -/
theorem gram_half_of_entrywise (hdet : (rowMat a T).det ≠ 0) (hTS : ∀ l, T l ∈ S) {ξ : ℝ}
    (hξ0 : 0 ≤ ξ) (hξ : ξ * (Fintype.card κ : ℝ) ≤ 1 / 2)
    (hclose : ∀ l l', |gramK2 a T R l l' - gramK2 a T S l l'| ≤ ξ) (v : κ → ℝ) :
    gram a S v / 2 ≤ gram a R v := by
  set h := hcoord a T v with hh
  -- |gram R v − gram S v| ≤ ξ (Σ|h_l|)² ≤ ξ·K·gramK ≤ ½·gramK ≤ ½·gram S v
  have hdiff : gram a R v - gram a S v
      = ∑ l, ∑ l', (gramK2 a T R l l' - gramK2 a T S l l') * (h l * h l') := by
    rw [gram_eq_gramK2 hdet R v, gram_eq_gramK2 hdet S v, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l' _ => by ring
  have hbound : |gram a R v - gram a S v| ≤ ξ * (∑ l, |h l|) ^ 2 := by
    rw [hdiff]
    calc |∑ l, ∑ l', (gramK2 a T R l l' - gramK2 a T S l l') * (h l * h l')|
        ≤ ∑ l, |∑ l', (gramK2 a T R l l' - gramK2 a T S l l') * (h l * h l')| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l, ∑ l', ξ * (|h l| * |h l'|) := by
          refine Finset.sum_le_sum fun l _ => ?_
          calc |∑ l', (gramK2 a T R l l' - gramK2 a T S l l') * (h l * h l')|
              ≤ ∑ l', |(gramK2 a T R l l' - gramK2 a T S l l') * (h l * h l')| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ l', ξ * (|h l| * |h l'|) := by
                refine Finset.sum_le_sum fun l' _ => ?_
                rw [abs_mul, abs_mul]
                exact mul_le_mul_of_nonneg_right (hclose l l') (by positivity)
      _ = ξ * (∑ l, |h l|) ^ 2 := by
          rw [sq, Finset.sum_mul_sum]
          simp only [Finset.mul_sum]
  have hcheb : (∑ l, |h l|) ^ 2 ≤ (Fintype.card κ : ℝ) * ∑ l, (h l) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset κ)) (f := fun l => |h l|)
    simpa [Finset.card_univ, sq_abs] using this
  have hgK : ∑ l, (h l) ^ 2 = gramK a T v := (gramK_eq_sum_hcoord a T v).symm
  have hlow : gramK a T v ≤ gram a S v := gramK_le_gram hTS hdet v
  have hK0 : 0 ≤ gramK a T v := gramK_nonneg a T v
  have hfinal : |gram a R v - gram a S v| ≤ gram a S v / 2 := by
    have h1 : ξ * (∑ l, |h l|) ^ 2 ≤ ξ * ((Fintype.card κ : ℝ) * gramK a T v) := by
      rw [← hgK]; exact mul_le_mul_of_nonneg_left hcheb hξ0
    have h2 : ξ * ((Fintype.card κ : ℝ) * gramK a T v) ≤ (1/2) * gramK a T v := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hξ hK0
    linarith [hbound, h1, h2, hlow]
  have := abs_le.mp hfinal
  linarith [this.1]

/-! ### Диапазоны корзин: в них нет величин входа

Это `K`-мерный аналог `Mt_range_over_precision` — того единственного факта, из-за
которого алгоритм получается FPTAS, а не псевдополиномиальным. -/

/-- Диапазон корзин по `Κ̃`: элементы матрицы состояния не превосходят `|U|` по модулю.
Никаких величин входа: коэффициенты Крамера ограничены единицей. -/
theorem abs_gramK2_le (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0)
    {U : Finset ι} (hU : U ⊆ S) (l l' : κ) : |gramK2 a T U l l'| ≤ (U.card : ℝ) := by
  calc |gramK2 a T U l l'| ≤ ∑ i ∈ U, |cf a T i l * cf a T i l'| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ U, (1:ℝ) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [abs_mul]
        have h1 := abs_cf_le_one hmax hdet (hU hi) l
        have h2 := abs_cf_le_one hmax hdet (hU hi) l'
        nlinarith [abs_nonneg (cf a T i l), abs_nonneg (cf a T i l')]
    _ = (U.card : ℝ) := by simp

/-- Диапазон корзин по `M̃`: `|M̃_l(U)| ≤ √(|U|·Q_t(U))`, где `Q_t(U) = φ_U(t)`.
Опять же — только через `Q`, то есть через `F` и `ε`, но не через величины входа. -/
theorem abs_momK_le (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0)
    {U : Finset ι} (hU : U ⊆ S) (l : κ) :
    |momK a y T U t l| ≤ Real.sqrt ((U.card : ℝ) * phi a y U t) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq U (fun i => cf a T i l)
    (fun i => y i - dotp (a i) t)
  have hc1 : ∑ i ∈ U, (cf a T i l) ^ 2 ≤ (U.card : ℝ) := by
    calc ∑ i ∈ U, (cf a T i l) ^ 2 ≤ ∑ _i ∈ U, (1:ℝ) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have h := abs_cf_le_one hmax hdet (hU hi) l
          nlinarith [abs_nonneg (cf a T i l), sq_abs (cf a T i l)]
      _ = (U.card : ℝ) := by simp
  have hc2 : ∑ i ∈ U, (y i - dotp (a i) t) ^ 2 = phi a y U t := by
    rw [phi]; exact Finset.sum_congr rfl fun i _ => by ring
  have hsq : (momK a y T U t l) ^ 2 ≤ (U.card : ℝ) * phi a y U t := by
    have h0 : (0:ℝ) ≤ phi a y U t := phi_nonneg a y U t
    calc (momK a y T U t l) ^ 2
        = (∑ i ∈ U, cf a T i l * (y i - dotp (a i) t)) ^ 2 := by rw [momK]
      _ ≤ (∑ i ∈ U, (cf a T i l) ^ 2) * ∑ i ∈ U, (y i - dotp (a i) t) ^ 2 := hcs
      _ ≤ (U.card : ℝ) * phi a y U t := by
          rw [hc2]; exact mul_le_mul_of_nonneg_right hc1 h0
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hsq

/-- Диапазон корзин по `M̃`, выраженный через объемлющее `S`: годится для **всех**
префиксов `U ⊆ S` сразу. Состояния динамики, вышедшие за эту коробку, отбрасываются —
префиксы оптимального носителя в ней остаются, а число состояний остаётся полиномиальным. -/
theorem abs_momK_le_of_subset (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0)
    {U : Finset ι} (hU : U ⊆ S) (l : κ) :
    |momK a y T U t l| ≤ Real.sqrt ((S.card : ℝ) * phi a y S t) := by
  refine le_trans (abs_momK_le hmax hdet hU l) (Real.sqrt_le_sqrt ?_)
  have h1 : (U.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hU
  have h2 : phi a y U t ≤ phi a y S t := phi_mono hU t
  have h3 : (0:ℝ) ≤ phi a y U t := phi_nonneg a y U t
  have h4 : (0:ℝ) ≤ (U.card : ℝ) := by positivity
  nlinarith

/-- **Отношение «диапазон корзин по `M̃` / ширина корзины» не содержит величин входа.**
При `F ≤ 2V`, `Q ≤ (1+ε)F`, ширине корзины `η = √(εV)/(2(k+1)√K)` и `|U| ≤ N`

    √(N·2(1+ε)V) / η  =  2(k+1)√K·√(2N(1+ε)/ε),

то есть `V` сокращается полностью: корзин `O(k√(KN/ε))` штук при любом масштабе входа.
Это `K`-мерный аналог `Mt_range_over_precision`. -/
theorem momK_range_over_precision {V ε N kk Kc : ℝ} (hV : 0 < V) (hε : 0 < ε)
    (hN : 0 ≤ N) (hkk : 0 < kk) (hKc : 0 < Kc) (hε1 : 0 ≤ 1 + ε) :
    Real.sqrt (N * (2 * (1 + ε) * V)) / (Real.sqrt (ε * V) / (2 * kk * Real.sqrt Kc))
      = 2 * kk * Real.sqrt Kc * Real.sqrt (2 * N * (1 + ε) / ε) := by
  have hεV : (0:ℝ) < ε * V := by positivity
  have hb : Real.sqrt (ε * V) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hεV)
  have hc : (2 * kk * Real.sqrt Kc) ≠ 0 := by positivity
  have h1 : Real.sqrt (N * (2 * (1 + ε) * V)) / Real.sqrt (ε * V)
      = Real.sqrt (2 * N * (1 + ε) / ε) := by
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  rw [div_eq_iff hb] at h1
  rw [h1]
  field_simp

/-- **Итог одного узла сетки (K факторов).** Собрано всё: Теорема H даёт `Q ≤ (1+ε)F`,
координаты `K`-ки переводят округление динамики в гипотезы шага, шаг даёт оценку. -/
theorem fptasK_at_grid_node (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0)
    (hnormal : IsNormal a y S th) {ε Δ ξ C : ℝ}
    (hC : (S.card * Fintype.card κ : ℝ) ≤ C) (hCpos : 0 < C)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ^ 2 ≤ ε * phi a y S th / 16)
    (hnode : gramK a T (t - th) ≤ ε * phi a y S th / C)
    (hQR : phi a y S t ≤ phi a y R t)
    (hMclose : ∑ l, (momK a y T R t l - momK a y T S t l) ^ 2 ≤ Δ ^ 2)
    (hξ0 : 0 ≤ ξ) (hξ : ξ * (Fintype.card κ : ℝ) ≤ 1 / 2)
    (hKclose : ∀ l l', |gramK2 a T R l l' - gramK2 a T S l l'| ≤ ξ) (v : κ → ℝ) :
    (1 - 17 * ε / 8) * phi a y S th ≤ phi a y R (t + v) := by
  have hQ : phi a y S t ≤ (1 + ε) * phi a y S th := theoremH hmax hdet hnormal hC hCpos hnode
  exact fptasK_step hnormal hΔ0 hΔ hQ hQR
    (mom_close hdet hmax.1 hΔ0 hMclose)
    (gram_half_of_entrywise hdet hmax.1 hξ0 hξ hKclose) v

end SparseSharpe.Factor
