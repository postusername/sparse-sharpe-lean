import SparseSharpe.Factor.DPRun

set_option linter.style.header false

/-!
# Стоимость: число узлов и число состояний — величины без данных входа

`theory_note_v6.md`, §12.4, пункт 2: «утверждения вида "алгоритм работает за
`poly(...)` шагов" в Lean нет — для этого нужна модель вычислений». Модели
вычислений тут по-прежнему нет, и она здесь не нужна: всё, из чего складывается
время работы, — это **две конечные величины**, число узлов сетки и размер
таблицы динамики. Обе уже ограничены (`exists_node_closing_step_half`,
`survivors_card_le`, `card_keyBox`), но границы записаны через `ε_g`, `η`, `ξ`,
то есть через параметры калибровки. Здесь параметры подставлены, и обе границы
выписаны как явные выражения от

    M (число активов),  n ≥ 2|S̄|,  K,  1/ε,  1/√γ

и **только** от них: ни `m`, ни `B`, ни `d`, ни `Σ_f`, ни масштаб `V` в них не
входят. Это и есть содержательная часть утверждения о полиномиальности:
при фиксированном `K` обе величины полиномиальны, а перебор `K`-ок и догадок
`V` даёт ещё два множителя, `(M+K)^K` и `O(log(F_max/F_min))`.

Главные утверждения:

* `zmax_le` — номера узлов не больше `23nK/(ε√γ) + 1/2`;
* `nodeCount_le` — узлов не больше `(46nK/(ε√γ) + 4)^K`;
* `momRange_over_eta_le` — отношение «диапазон корзин по `M̃` / ширина `η`»
  не больше `256·M·√K·n/(ε√γ)`;
* `survivors_card_le_explicit` — размер таблицы динамики не больше явного
  произведения трёх множителей от тех же величин;
* `algoCost` и `algoCost_poly` — сводный счётчик и его оценка.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {T : κ → ι} {t : κ → ℝ}

/-! ### Коробка номеров узлов -/

/-- Номера узлов сетки с `|z_l| ≤ Z`. -/
def nodeBox (Z : ℕ) : Finset (κ → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(Z : ℤ)) (Z : ℤ)

lemma card_nodeBox (Z : ℕ) :
    (nodeBox (κ := κ) Z).card = (2 * Z + 1) ^ Fintype.card κ := by
  simp only [nodeBox, Fintype.card_piFinset, Int.card_Icc]
  rw [Finset.prod_const, Finset.card_univ]
  congr 1
  omega

lemma mem_nodeBox_of_abs_le {z : κ → ℤ} {Z : ℕ} (h : ∀ l, |(z l : ℝ)| ≤ (Z : ℝ)) :
    z ∈ nodeBox (κ := κ) Z := by
  simp only [nodeBox, Fintype.mem_piFinset, Finset.mem_Icc]
  intro l
  have := h l
  rw [abs_le] at this
  constructor
  · exact_mod_cast this.1
  · exact_mod_cast this.2

/-! ### Номера узлов: явная граница -/

/-- **Диапазон номеров узлов не содержит данных входа.**
При `C ≤ nK` и `ε_g = ε²γ/(1024n)` граница из `exists_node_closing_step_half`
не превосходит `23nK/(ε√γ) + 1/2`. -/
theorem zmax_le {ε γ C : ℝ} {n Kc : ℕ} (hε : 0 < ε) (hγ : 0 < γ)
    (hn : 0 < n) (hK : 0 < Kc) (hCpos : 0 < C) (hC : C ≤ (n : ℝ) * (Kc : ℝ)) :
    Real.sqrt ((Kc : ℝ) * C / (2 * (ε ^ 2 * γ / (1024 * (n : ℝ))))) + 1 / 2
      ≤ 23 * (n : ℝ) * (Kc : ℝ) / (ε * Real.sqrt γ) + 1 / 2 := by
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hK0 : (0:ℝ) < (Kc : ℝ) := by exact_mod_cast hK
  have hsγ : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ
  have hsq : Real.sqrt γ ^ 2 = γ := Real.sq_sqrt hγ.le
  have hbnd : (0:ℝ) ≤ 23 * (n : ℝ) * (Kc : ℝ) / (ε * Real.sqrt γ) := by positivity
  have hgoal : (Kc : ℝ) * C / (2 * (ε ^ 2 * γ / (1024 * (n : ℝ))))
      = 512 * (n : ℝ) * ((Kc : ℝ) * C) / (ε ^ 2 * γ) := by
    field_simp; ring
  have hrhs : (23 * (n : ℝ) * (Kc : ℝ) / (ε * Real.sqrt γ)) ^ 2
      = 529 * ((n : ℝ) * (Kc : ℝ)) ^ 2 / (ε ^ 2 * γ) := by
    have hden : (ε * Real.sqrt γ) ^ 2 = ε ^ 2 * γ := by rw [mul_pow, hsq]
    rw [div_pow, hden]; ring
  have key : (Kc : ℝ) * C / (2 * (ε ^ 2 * γ / (1024 * (n : ℝ))))
      ≤ (23 * (n : ℝ) * (Kc : ℝ) / (ε * Real.sqrt γ)) ^ 2 := by
    rw [hgoal, hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
    have hCle : (Kc : ℝ) * C ≤ (Kc : ℝ) * ((n : ℝ) * (Kc : ℝ)) :=
      mul_le_mul_of_nonneg_left hC hK0.le
    have hE : (0:ℝ) < ε ^ 2 * γ := by positivity
    have hcoef : (0:ℝ) ≤ 512 * (n : ℝ) * (ε ^ 2 * γ) := by positivity
    have h1 : 512 * (n : ℝ) * ((Kc : ℝ) * C) * (ε ^ 2 * γ)
        ≤ 512 * (n : ℝ) * ((Kc : ℝ) * ((n : ℝ) * (Kc : ℝ))) * (ε ^ 2 * γ) := by
      nlinarith [mul_le_mul_of_nonneg_left hCle hcoef]
    have h2 : (0:ℝ) ≤ ((n : ℝ) * (Kc : ℝ)) ^ 2 * (ε ^ 2 * γ) :=
      mul_nonneg (sq_nonneg _) hE.le
    nlinarith [h1, h2]
  have hstep : Real.sqrt ((Kc : ℝ) * C / (2 * (ε ^ 2 * γ / (1024 * (n : ℝ)))))
      ≤ 23 * (n : ℝ) * (Kc : ℝ) / (ε * Real.sqrt γ) := by
    calc Real.sqrt ((Kc : ℝ) * C / (2 * (ε ^ 2 * γ / (1024 * (n : ℝ)))))
        ≤ Real.sqrt ((23 * (n : ℝ) * (Kc : ℝ) / (ε * Real.sqrt γ)) ^ 2) :=
          Real.sqrt_le_sqrt key
      _ = 23 * (n : ℝ) * (Kc : ℝ) / (ε * Real.sqrt γ) := Real.sqrt_sq hbnd
  linarith

/-- Номера узлов, выданные `exists_node_closing_step_half`, лежат в явной коробке. -/
theorem mem_nodeBox_of_grid {ε γ C : ℝ} {n : ℕ} {z : κ → ℤ}
    (hε : 0 < ε) (hγ : 0 < γ) (hn : 0 < n) (hK : 0 < Fintype.card κ)
    (hCpos : 0 < C) (hC : C ≤ (n : ℝ) * (Fintype.card κ : ℝ))
    (hz : ∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C
      / (2 * (ε ^ 2 * γ / (1024 * (n : ℝ))))) + 1 / 2) :
    z ∈ nodeBox (κ := κ)
      ⌈23 * (n : ℝ) * (Fintype.card κ : ℝ) / (ε * Real.sqrt γ) + 1 / 2⌉₊ := by
  refine mem_nodeBox_of_abs_le fun l => ?_
  refine le_trans (le_trans (hz l) (zmax_le hε hγ hn hK hCpos hC)) ?_
  exact Nat.le_ceil _

/-- **Число узлов сетки не содержит данных входа.** -/
theorem card_nodeBox_explicit {ε γ : ℝ} {n : ℕ} :
    (nodeBox (κ := κ)
      ⌈23 * (n : ℝ) * (Fintype.card κ : ℝ) / (ε * Real.sqrt γ) + 1 / 2⌉₊).card
      = (2 * ⌈23 * (n : ℝ) * (Fintype.card κ : ℝ) / (ε * Real.sqrt γ) + 1 / 2⌉₊ + 1)
          ^ Fintype.card κ :=
  card_nodeBox _

/-- **Число узлов: явная оценка сверху.** Округление вверх стоит не больше
единицы, поэтому `(2⌈x + 1/2⌉ + 1)^K ≤ (2x + 4)^K` при `x = 23nK/(ε√γ)`. -/
theorem nodeCount_le {ε γ : ℝ} {n : ℕ}
    (hx : 0 ≤ 23 * (n : ℝ) * (Fintype.card κ : ℝ) / (ε * Real.sqrt γ)) :
    ((nodeBox (κ := κ)
        ⌈23 * (n : ℝ) * (Fintype.card κ : ℝ) / (ε * Real.sqrt γ) + 1 / 2⌉₊).card : ℝ)
      ≤ (46 * (n : ℝ) * (Fintype.card κ : ℝ) / (ε * Real.sqrt γ) + 4)
          ^ Fintype.card κ := by
  set x : ℝ := 23 * (n : ℝ) * (Fintype.card κ : ℝ) / (ε * Real.sqrt γ) with hxdef
  rw [card_nodeBox]
  push_cast
  refine pow_le_pow_left₀ (by positivity) ?_ _
  have hceil : ((⌈x + 1 / 2⌉₊ : ℕ) : ℝ) ≤ x + 3 / 2 := by
    have := Nat.ceil_lt_add_one (by linarith : (0:ℝ) ≤ x + 1 / 2)
    linarith
  have : 46 * (n : ℝ) * (Fintype.card κ : ℝ) / (ε * Real.sqrt γ) = 2 * x := by
    rw [hxdef]; ring
  rw [this]
  linarith

/-! ### Ширина корзины: отношение «диапазон / шаг» тоже без данных входа -/

/-- **Отношение «диапазон корзин по `M̃` / ширина корзины `η`» не содержит данных
входа.** При выборе алгоритма `η = θ₀/(8√K·M)` и при `Q ≤ 4V`, `|S̄| ≤ n`

    √(|S̄|·Q)/η  ≤  256·M·√K·n/(ε√γ) .

Масштаб `V` сокращается полностью: он входит в `√Q` как `√V` и в `η` как `√V`. -/
theorem momRange_over_eta_le {ε γ V Q η : ℝ} {n Sc Mn Kc : ℕ}
    (hε : 0 < ε) (hγ : 0 < γ) (hV : 0 < V) (hn : 0 < n) (hK : 0 < Kc) (hM : 0 < Mn)
    (hη : η = theta0 ε γ V n / (8 * Real.sqrt (Kc : ℝ) * (Mn : ℝ)))
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ 4 * V) (hSc : (Sc : ℝ) ≤ (n : ℝ)) :
    Real.sqrt ((Sc : ℝ) * Q) / η
      ≤ 256 * (Mn : ℝ) * Real.sqrt (Kc : ℝ) * (n : ℝ) / (ε * Real.sqrt γ) := by
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hK0 : (0:ℝ) < (Kc : ℝ) := by exact_mod_cast hK
  have hM0 : (0:ℝ) < (Mn : ℝ) := by exact_mod_cast hM
  have hsγ : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsK : 0 < Real.sqrt (Kc : ℝ) := Real.sqrt_pos.mpr hK0
  have hgv : Real.sqrt (γ * V) = Real.sqrt γ * Real.sqrt V := Real.sqrt_mul hγ.le V
  -- `η` в раскрытом виде
  have hη' : η = ε * Real.sqrt γ * Real.sqrt V
      / (128 * Real.sqrt (n : ℝ) * Real.sqrt (Kc : ℝ) * (Mn : ℝ)) := by
    rw [hη, theta0, hgv]; field_simp; ring
  have hηpos : 0 < η := by rw [hη']; positivity
  rw [div_le_iff₀ hηpos]
  -- правая часть равна `2√(nV)`
  have heq : 256 * (Mn : ℝ) * Real.sqrt (Kc : ℝ) * (n : ℝ) / (ε * Real.sqrt γ) * η
      = 2 * ((n : ℝ) / Real.sqrt (n : ℝ)) * Real.sqrt V := by
    rw [hη']; field_simp; ring
  rw [heq, Real.div_sqrt, mul_assoc, ← Real.sqrt_mul hn0.le V]
  -- слева `√(|S̄|·Q) ≤ √(4nV) = 2√(nV)`
  have hle : (Sc : ℝ) * Q ≤ 4 * ((n : ℝ) * V) := by nlinarith [hQ0, hQ, hSc, hn0.le, hV.le]
  calc Real.sqrt ((Sc : ℝ) * Q) ≤ Real.sqrt (4 * ((n : ℝ) * V)) := Real.sqrt_le_sqrt hle
    _ = 2 * Real.sqrt ((n : ℝ) * V) := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by norm_num)]

/-! ### Размер таблицы динамики: явная оценка -/

lemma keyBox_mono {cM cK cM' cK' : ℤ} {N N' : ℕ} (hM : cM ≤ cM') (hK : cK ≤ cK')
    (hN : N ≤ N') : keyBox (κ := κ) cM cK N ⊆ keyBox (κ := κ) cM' cK' N' := by
  intro x hx
  rw [keyBox, Finset.mem_product, Finset.mem_product] at hx ⊢
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · simp only [Fintype.mem_piFinset, Finset.mem_Icc] at h1 ⊢
    intro l; have := h1 l; omega
  · simp only [Fintype.mem_piFinset, Finset.mem_Icc] at h2 ⊢
    intro l l'; have := h2 l l'; omega
  · simp only [Finset.mem_range] at h3 ⊢; omega

/-- **Размер таблицы через безразмерное отношение `D` и границу `N` на мощность.**
Это `card_states_le_of_ratio`, перенесённая с образа степенного множества на
саму таблицу динамики. -/
theorem survivors_card_le_of_ratio {S : Finset ι} (hmax : MaxVol a S T)
    (hdet : (rowMat a T).det ≠ 0) {η ξ : ℝ} (hη : 0 < η) (hξ : 0 < ξ)
    (adm : ι → Bool) (base : Finset ι) (L : List ι)
    (hbase : base ⊆ S) (hL : ∀ i ∈ L.toFinset, i ∈ S)
    {D : ℝ} (hD : Real.sqrt ((S.card : ℝ) * phi a y S t) / η ≤ D)
    {N : ℕ} (hN : S.card ≤ N) :
    (survivors (fun V => phi a y V t) (keyOf a y T t η ξ) adm base L).card
      ≤ (2 * ⌈D⌉ + 1).toNat ^ Fintype.card κ
        * ((2 * ⌈(N : ℝ) / ξ⌉ + 1).toNat ^ (Fintype.card κ * Fintype.card κ) * (N + 1)) := by
  refine le_trans (survivors_card_le hmax hdet hη hξ adm base L hbase hL) ?_
  have hNc : ((S.card : ℝ)) / ξ ≤ (N : ℝ) / ξ :=
    div_le_div_of_nonneg_right (by exact_mod_cast hN) hξ.le
  refine le_trans (Finset.card_le_card (keyBox_mono (Int.ceil_mono hD)
    (Int.ceil_mono hNc) hN)) ?_
  refine le_of_eq (card_keyBox _ _ ?_ ?_ _)
  · have : (0:ℝ) ≤ D := le_trans (div_nonneg (Real.sqrt_nonneg _) hη.le) hD
    exact Int.ceil_nonneg this
  · exact Int.ceil_nonneg (by positivity)

/-! ### Сводная оценка стоимости шага -/

/-- **Стоимость одного запуска динамики: обе величины явные.**

При выборе параметров §3 спецификации `SPEC_LO_K3.md`
(`η = θ₀/(8√K·M)`, `ξ = 1/(8MK)`, `C ≤ nK`, `|S̄| ≤ n`, `Q_τ ≤ 4V`):

* номер узла лежит в коробке размера `(2⌈23nK/(ε√γ) + 1/2⌉ + 1)^K`;
* таблица динамики не больше
  `(2⌈256M√K·n/(ε√γ)⌉+1)^K · (2⌈8nMK⌉+1)^{K²} · (n+1)`.

В обеих правых частях нет ни `m`, ни `B`, ни `d`, ни `Σ_f`, ни масштаба `V` —
только `M`, `n`, `K`, `1/ε` и `1/√γ`. При фиксированном `K` это полиномы.
Вместе с перебором `K`-ок (`(M+K)^K` вариантов) и сеткой догадок
(`O(log(F_max/F_min))` значений) это и есть утверждение о полиномиальности;
модель вычислений для него не нужна, потому что обе величины конечны и
ограничены явно. -/
theorem lo_fptas_cost {S : Finset ι} (hmax : MaxVol a S T)
    (hdet : (rowMat a T).det ≠ 0)
    {ε γ V C η ξ : ℝ} {n Mn : ℕ} {z : κ → ℤ}
    (hε : 0 < ε) (hγ : 0 < γ) (hV : 0 < V) (hn : 0 < n) (hM : 0 < Mn)
    (hKc : 0 < Fintype.card κ)
    (hCpos : 0 < C) (hC : C ≤ (n : ℝ) * (Fintype.card κ : ℝ))
    (hzb : ∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C
      / (2 * (ε ^ 2 * γ / (1024 * (n : ℝ))))) + 1 / 2)
    (hηdef : η = theta0 ε γ V n / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Mn : ℝ)))
    (hξdef : ξ = 1 / (8 * (Mn : ℝ) * (Fintype.card κ : ℝ)))
    (hQ : phi a y S t ≤ 4 * V) (hScard : S.card ≤ n)
    (adm : ι → Bool) (base : Finset ι) (L : List ι)
    (hbase : base ⊆ S) (hL : ∀ i ∈ L.toFinset, i ∈ S) :
    z ∈ nodeBox (κ := κ)
        ⌈23 * (n : ℝ) * (Fintype.card κ : ℝ) / (ε * Real.sqrt γ) + 1 / 2⌉₊
    ∧ (survivors (fun W => phi a y W t) (keyOf a y T t η ξ) adm base L).card
      ≤ (2 * ⌈256 * (Mn : ℝ) * Real.sqrt (Fintype.card κ : ℝ) * (n : ℝ)
            / (ε * Real.sqrt γ)⌉ + 1).toNat ^ Fintype.card κ
        * ((2 * ⌈(n : ℝ) * (8 * (Mn : ℝ) * (Fintype.card κ : ℝ))⌉ + 1).toNat
            ^ (Fintype.card κ * Fintype.card κ) * (n + 1)) := by
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hM0 : (0:ℝ) < (Mn : ℝ) := by exact_mod_cast hM
  have hK0 : (0:ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast hKc
  have hηpos : 0 < η := by
    rw [hηdef, theta0]
    have : 0 < Real.sqrt (γ * V) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have hξpos : 0 < ξ := by rw [hξdef]; positivity
  refine ⟨mem_nodeBox_of_grid hε hγ hn hKc hCpos hC hzb, ?_⟩
  have hD := momRange_over_eta_le (Sc := S.card) (Mn := Mn) (Kc := Fintype.card κ)
    hε hγ hV hn hKc hM hηdef (phi_nonneg a y S t) hQ (by exact_mod_cast hScard)
  have hres := survivors_card_le_of_ratio hmax hdet hηpos hξpos adm base L hbase hL hD hScard
  have hxi : (n : ℝ) / ξ = (n : ℝ) * (8 * (Mn : ℝ) * (Fintype.card κ : ℝ)) := by
    rw [hξdef]; field_simp
  rwa [hxi] at hres

/-! ### Непустота: формула числа узлов считает то, что надо -/

/-- При `K = 1` и `Z = 2` узлов ровно пять: `z ∈ {−2,−1,0,1,2}`. -/
example : (nodeBox (κ := Fin 1) 2).card = 5 := by
  rw [card_nodeBox]; norm_num

/-- При `K = 2` и `Z = 1` узлов девять. -/
example : (nodeBox (κ := Fin 2) 1).card = 9 := by
  rw [card_nodeBox]; norm_num

/-! ### Стоимость в `δ`-цепочке

В `lo_fptas_block` сетка строится с `ε_g = ε/(32c)`, а порог —
`θ₀ = √(εV/(8c))`. Подстановка даёт те же две величины, но через константу
покрытия `c` и границу `N ≥ |Ā|` на мощность **носителя с якорями**
(в приложении `N = k + K`), а не через размер вселенной `n` и `1/√γ`:

* номера узлов не больше `4K·√(N·c/ε) + 1/2` (`zmax_le_block`);
* отношение «диапазон корзин / ширина» не больше `48·M·√K·√(N·c/ε)`
  (`momRange_over_eta_le_block`). -/

/-- **Номера узлов в `δ`-цепочке.** При `C ≤ N·K` граница из
`exists_node_closing_step_block` не превосходит `4K·√(N·c/ε) + 1/2`. -/
theorem zmax_le_block {ε c C : ℝ} {N Kc : ℕ} (hε : 0 < ε) (hc : 0 < c)
    (hN : 0 < N) (hK : 0 < Kc) (hCpos : 0 < C) (hC : C ≤ (N : ℝ) * (Kc : ℝ)) :
    Real.sqrt ((Kc : ℝ) * C / (2 * (ε / (32 * c)))) + 1 / 2
      ≤ 4 * (Kc : ℝ) * Real.sqrt ((N : ℝ) * c / ε) + 1 / 2 := by
  have hN0 : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hK0 : (0:ℝ) < (Kc : ℝ) := by exact_mod_cast hK
  have hbnd : (0:ℝ) ≤ 4 * (Kc : ℝ) * Real.sqrt ((N : ℝ) * c / ε) := by positivity
  have hsq : Real.sqrt ((N : ℝ) * c / ε) ^ 2 = (N : ℝ) * c / ε := Real.sq_sqrt (by positivity)
  have hgoal : (Kc : ℝ) * C / (2 * (ε / (32 * c))) = 16 * ((Kc : ℝ) * C) * c / ε := by
    field_simp; ring
  have hrhs : (4 * (Kc : ℝ) * Real.sqrt ((N : ℝ) * c / ε)) ^ 2
      = 16 * (Kc : ℝ) ^ 2 * ((N : ℝ) * c / ε) := by
    rw [mul_pow, hsq]; ring
  have key : (Kc : ℝ) * C / (2 * (ε / (32 * c)))
      ≤ (4 * (Kc : ℝ) * Real.sqrt ((N : ℝ) * c / ε)) ^ 2 := by
    rw [hgoal, hrhs]
    have hCle : (Kc : ℝ) * C ≤ (Kc : ℝ) * ((N : ℝ) * (Kc : ℝ)) :=
      mul_le_mul_of_nonneg_left hC hK0.le
    have h1 : 16 * ((Kc : ℝ) * C) * c / ε ≤ 16 * ((Kc : ℝ) * ((N : ℝ) * (Kc : ℝ))) * c / ε := by
      apply div_le_div_of_nonneg_right _ hε.le
      nlinarith [hCle, hc.le]
    have h2 : 16 * ((Kc : ℝ) * ((N : ℝ) * (Kc : ℝ))) * c / ε
        = 16 * (Kc : ℝ) ^ 2 * ((N : ℝ) * c / ε) := by ring
    linarith
  have hstep : Real.sqrt ((Kc : ℝ) * C / (2 * (ε / (32 * c))))
      ≤ 4 * (Kc : ℝ) * Real.sqrt ((N : ℝ) * c / ε) := by
    calc Real.sqrt ((Kc : ℝ) * C / (2 * (ε / (32 * c))))
        ≤ Real.sqrt ((4 * (Kc : ℝ) * Real.sqrt ((N : ℝ) * c / ε)) ^ 2) :=
          Real.sqrt_le_sqrt key
      _ = 4 * (Kc : ℝ) * Real.sqrt ((N : ℝ) * c / ε) := Real.sqrt_sq hbnd
  linarith

/-- Номера узлов `δ`-цепочки лежат в явной коробке. -/
theorem mem_nodeBox_of_grid_block {ε c C : ℝ} {N : ℕ} {z : κ → ℤ}
    (hε : 0 < ε) (hc : 0 < c) (hN : 0 < N) (hK : 0 < Fintype.card κ)
    (hCpos : 0 < C) (hC : C ≤ (N : ℝ) * (Fintype.card κ : ℝ))
    (hz : ∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C
      / (2 * (ε / (32 * c)))) + 1 / 2) :
    z ∈ nodeBox (κ := κ)
      ⌈4 * (Fintype.card κ : ℝ) * Real.sqrt ((N : ℝ) * c / ε) + 1 / 2⌉₊ := by
  refine mem_nodeBox_of_abs_le fun l => ?_
  refine le_trans (le_trans (hz l) (zmax_le_block hε hc hN hK hCpos hC)) ?_
  exact Nat.le_ceil _

/-- **Число узлов `δ`-цепочки:** не больше `(8K·√(N·c/ε) + 4)^K`. -/
theorem nodeCount_le_block {ε c : ℝ} {N : ℕ}
    (hx : 0 ≤ 4 * (Fintype.card κ : ℝ) * Real.sqrt ((N : ℝ) * c / ε)) :
    ((nodeBox (κ := κ)
        ⌈4 * (Fintype.card κ : ℝ) * Real.sqrt ((N : ℝ) * c / ε) + 1 / 2⌉₊).card : ℝ)
      ≤ (8 * (Fintype.card κ : ℝ) * Real.sqrt ((N : ℝ) * c / ε) + 4)
          ^ Fintype.card κ := by
  set x : ℝ := 4 * (Fintype.card κ : ℝ) * Real.sqrt ((N : ℝ) * c / ε) with hxdef
  rw [card_nodeBox]
  push_cast
  refine pow_le_pow_left₀ (by positivity) ?_ _
  have hceil : ((⌈x + 1 / 2⌉₊ : ℕ) : ℝ) ≤ x + 3 / 2 := by
    have := Nat.ceil_lt_add_one (by linarith : (0:ℝ) ≤ x + 1 / 2)
    linarith
  have : 8 * (Fintype.card κ : ℝ) * Real.sqrt ((N : ℝ) * c / ε) = 2 * x := by
    rw [hxdef]; ring
  rw [this]
  linarith

/-- **Отношение «диапазон корзин / ширина» в `δ`-цепочке.** При
`η = θ₀/(8√K·M)`, `θ₀ = √(εV/(8c))`, `Q ≤ 4V`, `|Ā| ≤ N`:

    √(|Ā|·Q)/η ≤ 48·M·√K·√(N·c/ε) .

Масштаб `V` снова сокращается. -/
theorem momRange_over_eta_le_block {ε c V Q η : ℝ} {N Sc Mn Kc : ℕ}
    (hε : 0 < ε) (hc : 0 < c) (hV : 0 < V) (hN : 0 < N) (hK : 0 < Kc) (hM : 0 < Mn)
    (hη : η = theta0B ε V c / (8 * Real.sqrt (Kc : ℝ) * (Mn : ℝ)))
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ 4 * V) (hSc : (Sc : ℝ) ≤ (N : ℝ)) :
    Real.sqrt ((Sc : ℝ) * Q) / η
      ≤ 48 * (Mn : ℝ) * Real.sqrt (Kc : ℝ) * Real.sqrt ((N : ℝ) * c / ε) := by
  have hN0 : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hK0 : (0:ℝ) < (Kc : ℝ) := by exact_mod_cast hK
  have hM0 : (0:ℝ) < (Mn : ℝ) := by exact_mod_cast hM
  have hsK : 0 < Real.sqrt (Kc : ℝ) := Real.sqrt_pos.mpr hK0
  have hθpos : 0 < theta0B ε V c := Real.sqrt_pos.mpr (by positivity)
  have hηpos : 0 < η := by rw [hη]; positivity
  rw [div_le_iff₀ hηpos]
  -- `√(Nc/ε)·√(εV/(8c)) = √(NV/8)`
  have hprod : Real.sqrt ((N : ℝ) * c / ε) * theta0B ε V c = Real.sqrt ((N : ℝ) * V / 8) := by
    rw [theta0B, ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  -- правая часть: `48·M·√K·√(Nc/ε)·η = 6·√(NV/8)`
  have hR : 48 * (Mn : ℝ) * Real.sqrt (Kc : ℝ) * Real.sqrt ((N : ℝ) * c / ε) * η
      = 6 * Real.sqrt ((N : ℝ) * V / 8) := by
    rw [hη, ← hprod]
    field_simp
    ring
  rw [hR]
  -- `√(Sc·Q) ≤ √(4NV) = 2√(NV) ≤ 6·√(NV/8)`, так как `√8 ≤ 3`
  have hle : (Sc : ℝ) * Q ≤ 4 * ((N : ℝ) * V) := by nlinarith [hQ0, hQ, hSc, hN0.le, hV.le]
  have h1 : Real.sqrt ((Sc : ℝ) * Q) ≤ 2 * Real.sqrt ((N : ℝ) * V) := by
    calc Real.sqrt ((Sc : ℝ) * Q) ≤ Real.sqrt (4 * ((N : ℝ) * V)) := Real.sqrt_le_sqrt hle
      _ = 2 * Real.sqrt ((N : ℝ) * V) := by
          rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by norm_num)]
  have h2 : Real.sqrt ((N : ℝ) * V) ≤ 3 * Real.sqrt ((N : ℝ) * V / 8) := by
    have h8 : (N : ℝ) * V = 8 * ((N : ℝ) * V / 8) := by ring
    rw [h8, Real.sqrt_mul (by norm_num)]
    have hs8 : Real.sqrt 8 ≤ 3 := by
      rw [show (3:ℝ) = Real.sqrt (3 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hnn : 0 ≤ Real.sqrt (8 * ((N : ℝ) * V / 8) / 8) := Real.sqrt_nonneg _
    have : 8 * ((N : ℝ) * V / 8) / 8 = (N : ℝ) * V / 8 := by ring
    rw [this] at hnn ⊢
    exact mul_le_mul_of_nonneg_right hs8 (Real.sqrt_nonneg _)
  linarith

/-- **Стоимость одного запуска динамики в `δ`-цепочке: обе величины явные.**

При `η = θ₀/(8√K·M)`, `θ₀ = √(εV/(8c))`, `ξ = 1/(8MK)`, `C ≤ NK`, `|Ā| ≤ N`,
`Q_τ ≤ 4V`:

* номер узла лежит в коробке размера `(2⌈4K√(Nc/ε) + 1/2⌉ + 1)^K`;
* таблица динамики не больше
  `(2⌈48M√K·√(Nc/ε)⌉+1)^K · (2⌈8NMK⌉+1)^{K²} · (N+1)`.

В правых частях — только `M`, `N`, `K`, `1/ε` и константа покрытия `c`. При
`c = k(1 + kω)` (`anchorCover_of_sysVar`) и `N = k + K` это полином от `M`, `k`,
`1/ε` и `ω = max_i B_i'Σ_fB_i/d_i` при фиксированном `K`; размер вселенной
входит только множителем `M`. -/
theorem lo_fptas_cost_block {S : Finset ι} (hmax : MaxVol a S T)
    (hdet : (rowMat a T).det ≠ 0)
    {ε c V C η ξ : ℝ} {N Mn : ℕ} {z : κ → ℤ}
    (hε : 0 < ε) (hc : 0 < c) (hV : 0 < V) (hN : 0 < N) (hM : 0 < Mn)
    (hKc : 0 < Fintype.card κ)
    (hCpos : 0 < C) (hC : C ≤ (N : ℝ) * (Fintype.card κ : ℝ))
    (hzb : ∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C
      / (2 * (ε / (32 * c)))) + 1 / 2)
    (hηdef : η = theta0B ε V c / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Mn : ℝ)))
    (hξdef : ξ = 1 / (8 * (Mn : ℝ) * (Fintype.card κ : ℝ)))
    (hQ : phi a y S t ≤ 4 * V) (hScard : S.card ≤ N)
    (adm : ι → Bool) (base : Finset ι) (L : List ι)
    (hbase : base ⊆ S) (hL : ∀ i ∈ L.toFinset, i ∈ S) :
    z ∈ nodeBox (κ := κ)
        ⌈4 * (Fintype.card κ : ℝ) * Real.sqrt ((N : ℝ) * c / ε) + 1 / 2⌉₊
    ∧ (survivors (fun W => phi a y W t) (keyOf a y T t η ξ) adm base L).card
      ≤ (2 * ⌈48 * (Mn : ℝ) * Real.sqrt (Fintype.card κ : ℝ)
            * Real.sqrt ((N : ℝ) * c / ε)⌉ + 1).toNat ^ Fintype.card κ
        * ((2 * ⌈(N : ℝ) * (8 * (Mn : ℝ) * (Fintype.card κ : ℝ))⌉ + 1).toNat
            ^ (Fintype.card κ * Fintype.card κ) * (N + 1)) := by
  have hM0 : (0:ℝ) < (Mn : ℝ) := by exact_mod_cast hM
  have hK0 : (0:ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast hKc
  have hηpos : 0 < η := by
    rw [hηdef]
    have : 0 < theta0B ε V c := Real.sqrt_pos.mpr (by positivity)
    have : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr hK0
    positivity
  have hξpos : 0 < ξ := by rw [hξdef]; positivity
  refine ⟨mem_nodeBox_of_grid_block hε hc hN hKc hCpos hC hzb, ?_⟩
  have hD := momRange_over_eta_le_block (Sc := S.card) (Mn := Mn) (Kc := Fintype.card κ)
    hε hc hV hN hKc hM hηdef (phi_nonneg a y S t) hQ (by exact_mod_cast hScard)
  have hres := survivors_card_le_of_ratio hmax hdet hηpos hξpos adm base L hbase hL hD hScard
  have hxi : (N : ℝ) / ξ = (N : ℝ) * (8 * (Mn : ℝ) * (Fintype.card κ : ℝ)) := by
    rw [hξdef]; field_simp
  rwa [hxi] at hres

end SparseSharpe.Factor
