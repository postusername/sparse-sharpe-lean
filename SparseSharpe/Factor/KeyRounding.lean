import SparseSharpe.Factor.Rounding
import SparseSharpe.Factor.StateCount
import SparseSharpe.Factor.GridFilter

set_option linter.style.header false

/-!
# Связка «округлённый ключ → `ApproxBucket`»

`Factor/Rounding.lean` требует от соседей по корзине допуск в безразмерной форме
`|Δmom(v)| ≤ η√(gram_S(v))`, `|Δgram(v)| ≤ ζ·gram_S(v)`. Динамика же хранит
ключ `keyOf` (`Factor/StateCount.lean`): округлённые `M̃_l = Σ_{i∈U}c_{il}r_i(t)`
с шагом `η` и `Κ̃_{ll'} = Σ_{i∈U}c_{il}c_{il'}` с шагом `ξ`.

Здесь доказано, что вместе с условием вытеснения одно влечёт другое:

    φ_S(t) ≤ φ_R(t)  ∧  keyOf(R) = keyOf(S)   ⟹   ApproxBucket a y S R t (√K·η) (K·ξ).

Условие вытеснения `hQ` округлённый ключ сам по себе не даёт; в динамике его
обеспечивает выбор представителя корзины с наибольшим `Q_t`
(`repOf_spec`, `survivors_spec` в `Factor/DPRun.lean`).

Два шага. Первый момент: `mom(t,v) = Σ_l M̃_l·⟨a_{T_l},v⟩` (`mom_eq_momK`), и
`Σ_l⟨a_{T_l},v⟩² = gramK(v) ≤ gram_S(v)` (`gramK_le_gram`), поэтому
Коши–Буняковский даёт `|Δmom(v)| ≤ ‖ΔM̃‖·√(gram_S(v))`, а совпадение ключа даёт
`|ΔM̃_l| < η`, то есть `‖ΔM̃‖ < √K·η` (`mom_close` из `State.lean`).
Форма Грама: `gram(v) = Σ_{ll'}Κ̃_{ll'}h_lh_{l'}`, поэлементная близость `ξ`
даёт `|Δgram(v)| ≤ ξ(Σ_l|h_l|)² ≤ ξK·gramK(v) ≤ ξK·gram_S(v)`.

Вместе с `Factor/Rounding.lean` и `Factor/GridFilter.lean` это замыкает цепочку
«сетка → ключ → шаг динамики» для long-only: остаётся только связка с самой
реализацией динамики (какой набор оказывается представителем корзины).
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {S R : Finset ι} {T : κ → ι} {t : κ → ℝ}

/-- Совпадение округлений влечёт близость: `⌊x/η⌋ = ⌊z/η⌋ → |x − z| ≤ η`. -/
lemma abs_sub_le_of_floor_eq {x z η : ℝ} (hη : 0 < η) (h : ⌊x / η⌋ = ⌊z / η⌋) :
    |x - z| ≤ η := by
  have hx1 : (⌊x / η⌋ : ℝ) ≤ x / η := Int.floor_le _
  have hx2 : x / η < (⌊x / η⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hz1 : (⌊z / η⌋ : ℝ) ≤ z / η := Int.floor_le _
  have hz2 : z / η < (⌊z / η⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  rw [h] at hx1 hx2
  have hd : |x / η - z / η| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have : |x - z| / η ≤ 1 := by
    rw [← abs_of_pos hη, ← abs_div]
    have : (x - z) / η = x / η - z / η := by ring
    rw [this]
    simpa using hd
  rw [div_le_one hη] at this
  exact this

/-- **Относительная близость форм Грама.** Поэлементная близость `Κ̃` с шагом `ξ`
даёт `|gram_R(v) − gram_S(v)| ≤ ξK·gram_S(v)`. -/
theorem gram_rel_close (hdet : (rowMat a T).det ≠ 0) (hTS : ∀ l, T l ∈ S) {ξ : ℝ}
    (hξ0 : 0 ≤ ξ) (hclose : ∀ l l', |gramK2 a T R l l' - gramK2 a T S l l'| ≤ ξ)
    (v : κ → ℝ) :
    |gram a R v - gram a S v| ≤ (ξ * (Fintype.card κ : ℝ)) * gram a S v := by
  set h := hcoord a T v with hh
  have hdiff : gram a R v - gram a S v
      = ∑ l, ∑ l', (gramK2 a T R l l' - gramK2 a T S l l') * (h l * h l') := by
    rw [gram_eq_gramK2 hdet R v, gram_eq_gramK2 hdet S v, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l' _ => by rw [hh]; ring
  -- поточечная оценка и свёртка в `(Σ|h_l|)²`
  have hbound : |gram a R v - gram a S v| ≤ ξ * (∑ l, |h l|) ^ 2 := by
    rw [hdiff]
    calc |∑ l, ∑ l', (gramK2 a T R l l' - gramK2 a T S l l') * (h l * h l')|
        ≤ ∑ l, |∑ l', (gramK2 a T R l l' - gramK2 a T S l l') * (h l * h l')| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l, ∑ l', |(gramK2 a T R l l' - gramK2 a T S l l') * (h l * h l')| :=
          Finset.sum_le_sum fun l _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l, ∑ l', ξ * (|h l| * |h l'|) := by
          refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun l' _ => ?_
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_right (hclose l l') (by positivity)
      _ = ξ * (∑ l, |h l|) ^ 2 := by
          rw [sq, Finset.sum_mul_sum]
          simp only [Finset.mul_sum]
  -- `(Σ|h_l|)² ≤ K·gramK(v) ≤ K·gram_S(v)`
  have hcs : (∑ l, |h l|) ^ 2 ≤ (Fintype.card κ : ℝ) * ∑ l, (h l) ^ 2 := by
    have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset κ)
      (fun _ => (1:ℝ)) (fun l => |h l|)
    have hone : ∑ _l : κ, (1:ℝ) ^ 2 = (Fintype.card κ : ℝ) := by simp
    have habs : ∀ l, (|h l|) ^ 2 = (h l) ^ 2 := fun l => sq_abs (h l)
    have hprod : ∑ l : κ, (1:ℝ) * |h l| = ∑ l, |h l| :=
      Finset.sum_congr rfl fun l _ => one_mul _
    rw [hprod, hone] at hcs0
    simpa only [habs] using hcs0
  have hgk : ∑ l, (h l) ^ 2 ≤ gram a S v := by
    rw [hh, ← gramK_eq_sum_hcoord]
    exact gramK_le_gram hTS hdet v
  have hKnn : (0:ℝ) ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  have step1 : ξ * (∑ l, |h l|) ^ 2 ≤ ξ * ((Fintype.card κ : ℝ) * ∑ l, (h l) ^ 2) :=
    mul_le_mul_of_nonneg_left hcs hξ0
  have step2 : ξ * ((Fintype.card κ : ℝ) * ∑ l, (h l) ^ 2)
      ≤ ξ * ((Fintype.card κ : ℝ) * gram a S v) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgk hKnn) hξ0
  have hring : (ξ * (Fintype.card κ : ℝ)) * gram a S v
      = ξ * ((Fintype.card κ : ℝ) * gram a S v) := by ring
  rw [hring]
  linarith [hbound, step1, step2]

/-- **Округлённый ключ даёт `ApproxBucket`.** -/
theorem approxBucket_of_key (hdet : (rowMat a T).det ≠ 0) (hTS : ∀ l, T l ∈ S)
    (hQ : phi a y S t ≤ phi a y R t) {Δ ξ : ℝ} (hΔ0 : 0 ≤ Δ) (hξ0 : 0 ≤ ξ)
    (hmomD : ∑ l, (momK a y T R t l - momK a y T S t l) ^ 2 ≤ Δ ^ 2)
    (hgramD : ∀ l l', |gramK2 a T R l l' - gramK2 a T S l l'| ≤ ξ) :
    ApproxBucket a y S R t Δ (ξ * (Fintype.card κ : ℝ)) where
  Q := hQ
  mom := by
    intro v
    have h1 := mom_close (S := S) (R := R) hdet hTS hΔ0 hmomD v
    have h2 := mom_close (S := S) (R := R) hdet hTS hΔ0 hmomD (-v)
    have hmneg : ∀ U : Finset ι, mom a y U t (-v) = -mom a y U t v := by
      intro U
      have : (-v) = (-1 : ℝ) • v := by
        funext j; simp
      rw [this, mom_smul]; ring
    rw [hmneg R, hmneg S, gram_neg] at h2
    rw [abs_le]
    constructor <;> linarith
  gram := fun v => gram_rel_close hdet hTS hξ0 hgramD v

/-- **Итог: совпадение ключей динамики влечёт `ApproxBucket`.**
Шаг `η` по `M̃` превращается в `√K·η`, шаг `ξ` по `Κ̃` — в `K·ξ`. -/
theorem approxBucket_of_keyOf_eq (hdet : (rowMat a T).det ≠ 0) (hTS : ∀ l, T l ∈ S)
    (hQ : phi a y S t ≤ phi a y R t) {η ξ : ℝ} (hη : 0 < η) (hξ : 0 < ξ)
    (hkey : keyOf a y T t η ξ R = keyOf a y T t η ξ S) :
    ApproxBucket a y S R t (Real.sqrt (Fintype.card κ : ℝ) * η) (ξ * (Fintype.card κ : ℝ)) := by
  have hmomeq : ∀ l, ⌊momK a y T R t l / η⌋ = ⌊momK a y T S t l / η⌋ := by
    intro l
    have := congrArg Prod.fst hkey
    exact congrFun this l
  have hgrameq : ∀ l l', ⌊gramK2 a T R l l' / ξ⌋ = ⌊gramK2 a T S l l' / ξ⌋ := by
    intro l l'
    have h1 := congrArg (fun p => p.2.1) hkey
    exact congrFun (congrFun h1 l) l'
  have hmomD : ∑ l, (momK a y T R t l - momK a y T S t l) ^ 2
      ≤ (Real.sqrt (Fintype.card κ : ℝ) * η) ^ 2 := by
    have hterm : ∀ l ∈ (Finset.univ : Finset κ),
        (momK a y T R t l - momK a y T S t l) ^ 2 ≤ η ^ 2 := by
      intro l _
      have := abs_sub_le_of_floor_eq hη (hmomeq l)
      nlinarith [abs_nonneg (momK a y T R t l - momK a y T S t l),
        sq_abs (momK a y T R t l - momK a y T S t l), this]
    have hsum : ∑ l, (momK a y T R t l - momK a y T S t l) ^ 2
        ≤ (Fintype.card κ : ℝ) * η ^ 2 := by
      calc ∑ l, (momK a y T R t l - momK a y T S t l) ^ 2
          ≤ ∑ _l : κ, η ^ 2 := Finset.sum_le_sum hterm
        _ = (Fintype.card κ : ℝ) * η ^ 2 := by simp [Finset.sum_const, mul_comm]
    have hsq : (Real.sqrt (Fintype.card κ : ℝ) * η) ^ 2 = (Fintype.card κ : ℝ) * η ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [hsq]; exact hsum
  exact approxBucket_of_key hdet hTS hQ (by positivity) hξ.le hmomD
    (fun l l' => abs_sub_le_of_floor_eq hξ (hgrameq l l'))

/-! ### Шаг динамики целиком, в терминах самого алгоритма -/

/-- **Шаг LO-K‴ в терминах округлённого ключа и узла сетки.**

Гипотезы — ровно то, чем алгоритм располагает:

* `hkey` — `R` лежит в той же корзине динамики, что носитель оптимума `S̄`
  (совпадают округлённые `M̃` и `Κ̃` и размер носителя);
* `hQ` — `R` вытеснил `S̄` (значение в узле не меньше);
* `hfilterR` — `R` прошёл знаковый фильтр порога `−θ₀`;
* `hgapS` — зазор узла у `S̄` плюс цена округления не больше `θ₀²`: сетка
  `exists_node_closing_step_half` даёт зазор `≤ θ₀²/2`, а выбор `η`, `ξ` — цену
  округления `≤ θ₀²/2` (`bucketErr_le_half`); `exists_node_closing_step` с полным
  запасом `θ₀²` для этого не годится;
* `hErr` — цена округления не больше `ε·F(S̄)` (достаточно `η ≤ √(εF/(12K))`,
  см. `bucketErr_le_of_small`).

Вывод: `F_LO(R) ≥ (1−2ε)·F(S̄) ≥ (1−2ε)·F_LO(S)`. -/
theorem psiC_ge_of_rounded_key_at_node [DecidableEq ι] {cl : ι → Bool} {thS thR : κ → ℝ}
    {η ξ ε γ V : ℝ} {n : ℕ}
    (hdet : (rowMat a T).det ≠ 0) (hTS : ∀ l, T l ∈ S)
    (hnormS : IsNormal a y S thS) (hnormR : IsNormal a y R thR)
    (hQ : phi a y S t ≤ phi a y R t)
    (hkey : keyOf a y T t η ξ R = keyOf a y T t η ξ S)
    (hη : 0 < η) (hξ : 0 < ξ)
    (hζ2 : 2 * (ξ * (Fintype.card κ : ℝ)) < 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hV : 0 < V)
    (hn : 0 < n) (hcard : (R.card : ℝ) ≤ (n : ℝ))
    (hanchR : ∀ i ∈ R, ¬ cl i → y i = 0)
    (hcondR : ∀ v : κ → ℝ, γ * gram a R v ≤ gram a (anchorSet cl R) v)
    (hfilterR : ∀ i ∈ R, cl i → -theta0 ε γ V n ≤ y i - dotp (a i) t)
    (hgapS : (phi a y S t - phi a y S thS)
      + bucketErr (Real.sqrt (Fintype.card κ : ℝ) * η) (ξ * (Fintype.card κ : ℝ))
        (phi a y S t - phi a y S thS) ≤ theta0 ε γ V n ^ 2)
    (hErr : bucketErr (Real.sqrt (Fintype.card κ : ℝ) * η) (ξ * (Fintype.card κ : ℝ))
      (phi a y S t - phi a y S thS) ≤ ε * phi a y S thS)
    (hVF : V ≤ phi a y S thS
      - bucketErr (Real.sqrt (Fintype.card κ : ℝ) * η) (ξ * (Fintype.card κ : ℝ))
        (phi a y S t - phi a y S thS))
    (t' : κ → ℝ) :
    (1 - 2 * ε) * phi a y S thS ≤ psiC a y cl R t' := by
  have hb := approxBucket_of_keyOf_eq hdet hTS hQ hη hξ hkey
  have hηb : (0:ℝ) ≤ Real.sqrt (Fintype.card κ : ℝ) * η := by positivity
  have hζb : (0:ℝ) ≤ ξ * (Fintype.card κ : ℝ) := by positivity
  have hFR : V ≤ phi a y R thR :=
    le_trans hVF (phi_normal_ge_of_approxBucket' hb hηb hζb hζ2 hnormS hnormR)
  exact psiC_ge_of_approxBucket_calibrated hb hnormS hnormR hηb hζb hζ2
    (theta0_nonneg hε.le) hγ hγ1 hε hε1 hanchR hcondR hfilterR hgapS
    (cal_of_theta0 hγ hV hn hcard hFR hε.le) hErr t'

end SparseSharpe.Factor
