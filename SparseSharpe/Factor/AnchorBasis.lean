import SparseSharpe.Factor.GuaranteeBlock
import SparseSharpe.Factor.Cost

set_option linter.style.header false

/-!
# Без перебора `K`-ок: сетка и ключ в координатах якорных строк (C.4)

Внешний цикл спецификации перебирает `K`-ки строк `T` (`(M+K)^K` вариантов), потому
что сетке и ключу нужна **максимально-объёмная** `K`-ка оптимального носителя `Ā`, а
`Ā` заранее неизвестен. Максимальность объёма используется ровно в двух местах:

* зажим формы Грама `gram_S(v) ≤ |S|·K·gram_T(v)` (сетка, `theoremH`);
* `|cf| ≤ 1` для коэффициентов Крамера (диапазон ключа, `keyOf_mem_keyBox`).

Здесь обе гипотезы заменены **поточечной** оценкой плеча
`⟨a_i,v⟩² ≤ w_i·gram_T(v)` для строк `i ∈ S`. Из неё:

* `gram_le_of_pointwise` — зажим с константой `Σ_{i∈S} w_i`;
* `abs_cf_le_of_pointwise` — `|cf_{il}| ≤ √w_i`.

Максимально-объёмная `K`-ка — частный случай (`w_i = K`). Но у якорных строк такая
оценка есть **без всякого выбора**: `⟨a_i,v⟩² ≤ ω_i·gram_anch(v)`, `ω_i = B_i'Σ_fB_i/d_i`
(`sq_dotp_asset_le`, Коши–Буняковский в метрике `Σ_f⁻¹`), а якоря лежат в каждом `Ā`.
Отсюда `lo_fptas_portfolio_anchor`: гарантия `(1−2ε)` с **одной** сеткой в
координатах якорей при любом `C ≥ K + kω` (можно взять `C = K + kω`), и стоимость
`lo_fptas_cost_rho` с `ρ = √max(1, ω)` (`abs_cf_anchor_le`): число узлов и размер
таблицы. Перебор `(M+K)^K` исчезает; платой служат множители `ω` в числе узлов и
`ρ^{2K²}` в диапазоне ключа — при `ω ≤ 1` плата нулевая, при больших `ω` якорная
схема может оказаться дороже перебора (`code/check_anchor_basis.py`).

Что это **не** даёт: локально максимально-объёмная `K`-ка (Гореинов и др.) перебор не
убирает — она локальна относительно неизвестного `Ā`.
-/

namespace SparseSharpe.Factor

open Finset Matrix

set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {S : Finset ι} {T : κ → ι} {th t : κ → ℝ}

/-! ### Поточечная оценка плеча вместо максимальности объёма -/

/-- Зажим формы Грама из поточечной оценки плеча. -/
theorem gram_le_of_pointwise {w : ι → ℝ}
    (hpt : ∀ i ∈ S, ∀ v, (dotp (a i) v) ^ 2 ≤ w i * gramK a T v) (v : κ → ℝ) :
    gram a S v ≤ (∑ i ∈ S, w i) * gramK a T v := by
  rw [gram, Finset.sum_mul]
  exact Finset.sum_le_sum fun i hi => hpt i hi v

/-- Коэффициенты Крамера из поточечной оценки плеча: `|cf_{il}| ≤ √w`. -/
theorem abs_cf_le_of_pointwise (hdet : (rowMat a T).det ≠ 0) {i : ι} {w : ℝ}
    (hpt : ∀ v, (dotp (a i) v) ^ 2 ≤ w * gramK a T v) (l : κ) :
    |cf a T i l| ≤ Real.sqrt w := by
  obtain ⟨v, hv⟩ := exists_point_with_residuals hdet (fun l' => if l' = l then 1 else 0)
  have h1 : dotp (a i) v = cf a T i l := by
    rw [dotp_eq_sum_cf hdet i v]
    simp [hv]
  have h2 : gramK a T v = 1 := by
    simp [gramK, hv]
  have h3 := hpt v
  rw [h1, h2, mul_one] at h3
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h3

/-- Максимально-объёмная `K`-ка удовлетворяет поточечной оценке с `w_i = K`:
старые оценки — частный случай новых. -/
theorem pointwise_of_maxvol (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0)
    {i : ι} (hi : i ∈ S) (v : κ → ℝ) :
    (dotp (a i) v) ^ 2 ≤ (Fintype.card κ : ℝ) * gramK a T v :=
  sq_dotp_le_card_mul_gramK hmax hdet hi v

/-- Максимально-объёмная `K`-ка даёт зажим общего вида с `C ≥ |A|·K`: старая
сквозная теорема `lo_fptas_block` — частный случай `lo_fptas_block_clamp`. -/
theorem clamp_of_maxvol (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0) {C : ℝ}
    (hC : (S.card * Fintype.card κ : ℝ) ≤ C) (v : κ → ℝ) :
    gram a S v ≤ C * gramK a T v :=
  le_trans (gram_le_card_mul_gramK hmax hdet v)
    (mul_le_mul_of_nonneg_right hC (gramK_nonneg a T v))

/-! ### Сетка при зажиме общего вида -/

/-- **Теорема H при зажиме общего вида.** -/
theorem theoremH_clamp (hnormal : IsNormal a y S th) {ε C : ℝ}
    (hclamp : ∀ v, gram a S v ≤ C * gramK a T v) (hCpos : 0 < C)
    (hh : gramK a T (t - th) ≤ ε * phi a y S th / C) :
    phi a y S t ≤ (1 + ε) * phi a y S th := by
  have hg := hclamp (t - th)
  have h3 : C * gramK a T (t - th) ≤ C * (ε * phi a y S th / C) :=
    mul_le_mul_of_nonneg_left hh hCpos.le
  have h4 : C * (ε * phi a y S th / C) = ε * phi a y S th := by field_simp
  rw [phi_eq_add hnormal t]
  linarith

/-- **Годный узел сетки при зажиме общего вида.** Как `exists_grid_node`, но вместо
максимальности объёма — `K`-ка внутри `S` (`hTS`) и зажим `gram_S ≤ C·gram_T`. -/
theorem exists_grid_node_clamp (hTS : ∀ l, T l ∈ S) (hdet : (rowMat a T).det ≠ 0)
    (hnormal : IsNormal a y S th) {ε C V s : ℝ}
    (hclamp : ∀ v, gram a S v ≤ C * gramK a T v) (hCpos : 0 < C)
    (hε : 0 < ε) (hV : 0 < V) (hVF : V ≤ phi a y S th) (hFV : phi a y S th ≤ 2 * V)
    (hKc : 0 < (Fintype.card κ : ℝ))
    (hs : s = 2 * Real.sqrt (ε * V / ((Fintype.card κ : ℝ) * C))) :
    ∃ z : κ → ℤ,
      (∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C / (2 * ε)) + 1 / 2) ∧
      (∀ t : κ → ℝ, (∀ l, dotp (a (T l)) t = y (T l) + s * (z l : ℝ)) →
        phi a y S t ≤ (1 + ε) * phi a y S th) := by
  set Kc := (Fintype.card κ : ℝ) with hKcdef
  set F := phi a y S th with hFdef
  have hspos : 0 < s := by
    rw [hs]; have : 0 < ε * V / (Kc * C) := by positivity
    simpa using (Real.sqrt_pos.mpr this)
  set r : ι → ℝ := fun i => y i - dotp (a i) th with hr
  have hFr : F = ∑ i ∈ S, (r i) ^ 2 := by
    rw [hFdef, phi]; exact Finset.sum_congr rfl fun i _ => by rw [hr]; ring
  have hrT : ∀ l, (r (T l)) ^ 2 ≤ F := by
    intro l
    have hsum := sum_comp_le hTS (injective_of_det_ne_zero hdet)
      (fun i => (r i) ^ 2) (fun _ => sq_nonneg _)
    have hterm : (r (T l)) ^ 2 ≤ ∑ l', (r (T l')) ^ 2 :=
      Finset.single_le_sum (f := fun l' => (r (T l')) ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ l)
    rw [hFr]; linarith
  obtain ⟨z, hz1, hz2⟩ := exists_grid_point s hspos (fun l => -(r (T l)))
  refine ⟨z, fun l => ?_, fun t ht => ?_⟩
  · have habs : |(-(r (T l)))| ≤ Real.sqrt (2 * V) := by
      have h1 : (r (T l)) ^ 2 ≤ 2 * V := le_trans (hrT l) hFV
      rw [abs_neg, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt h1
    have h2 := hz2 l
    have h3 : |(-(r (T l)))| / s ≤ Real.sqrt (2 * V) / s := by gcongr
    have h4 : Real.sqrt (2 * V) / s = Real.sqrt (Kc * C / (2 * ε)) := by
      rw [hs]; exact grid_ratio hV hε hCpos hKc
    linarith [h2, h3, h4 ▸ h3]
  · have hdev : ∀ l, dotp (a (T l)) (t - th) = s * (z l : ℝ) - (-(r (T l))) := by
      intro l
      rw [dotp_sub, ht l, hr]
      ring
    have hgK : gramK a T (t - th) ≤ Kc * s ^ 2 / 4 := by
      rw [gramK]
      calc ∑ l, (dotp (a (T l)) (t - th)) ^ 2
          = ∑ l, (s * (z l : ℝ) - (-(r (T l)))) ^ 2 :=
            Finset.sum_congr rfl fun l _ => by rw [hdev l]
        _ ≤ ∑ _l : κ, (s / 2) ^ 2 := by
            refine Finset.sum_le_sum fun l _ => ?_
            have := hz1 l
            nlinarith [abs_nonneg (s * (z l : ℝ) - (-(r (T l)))),
              sq_abs (s * (z l : ℝ) - (-(r (T l)))), hspos]
        _ = Kc * s ^ 2 / 4 := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hKcdef]; ring
    have hs2 : s ^ 2 = 4 * (ε * V / (Kc * C)) := by
      rw [hs, mul_pow, Real.sq_sqrt (by positivity)]
      ring
    have hfin : gramK a T (t - th) ≤ ε * F / C := by
      have h1 : Kc * s ^ 2 / 4 = ε * V / C := by
        rw [hs2]; field_simp
      have h2 : ε * V / C ≤ ε * F / C := by gcongr
      linarith [hgK, h1 ▸ hgK]
    exact theoremH_clamp hnormal hclamp hCpos hfin

/-- Узел, закрывающий шаг `δ`-цепочки, при зажиме общего вида
(аналог `exists_node_closing_step_block`). -/
theorem exists_node_closing_step_clamp {cl : ι → Bool}
    (hTS : ∀ l, T l ∈ S) (hdet : (rowMat a T).det ≠ 0) (hnormal : IsNormal a y S th)
    {ε V C c s : ℝ}
    (hclamp : ∀ v, gram a S v ≤ C * gramK a T v) (hCpos : 0 < C)
    (hε : 0 < ε) (hc : 0 < c) (hV : 0 < V)
    (hVF : V ≤ phi a y S th) (hFV : phi a y S th ≤ 2 * V)
    (hKc : 0 < (Fintype.card κ : ℝ))
    (hs : s = 2 * Real.sqrt ((ε / (32 * c)) * V / ((Fintype.card κ : ℝ) * C)))
    (hself : ∀ i ∈ S, cl i → 0 ≤ y i - dotp (a i) th) :
    ∃ z : κ → ℤ,
      (∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C
        / (2 * (ε / (32 * c)))) + 1 / 2) ∧
      (∀ t : κ → ℝ, (∀ l, dotp (a (T l)) t = y (T l) + s * (z l : ℝ)) →
        phi a y S t - phi a y S th ≤ theta0B ε V c ^ 2 / 2
        ∧ (∀ i ∈ S, cl i → -theta0B ε V c ≤ y i - dotp (a i) t)) := by
  set εg : ℝ := ε / (32 * c) with hεg
  have hεgpos : 0 < εg := by rw [hεg]; positivity
  obtain ⟨z, hz1, hz2⟩ :=
    exists_grid_node_clamp hTS hdet hnormal hclamp hCpos hεgpos hV hVF hFV hKc hs
  refine ⟨z, hz1, fun t ht => ?_⟩
  have hphi := hz2 t ht
  have hgap : phi a y S t - phi a y S th ≤ theta0B ε V c ^ 2 / 2 := by
    rw [theta0B_sq hε.le hV.le hc.le]
    have h1 : phi a y S t - phi a y S th ≤ εg * phi a y S th := by linarith
    have h2 : εg * phi a y S th ≤ εg * (2 * V) :=
      mul_le_mul_of_nonneg_left hFV hεgpos.le
    have h3 : εg * (2 * V) = ε * V / (8 * c) / 2 := by
      rw [hεg]; field_simp; ring
    linarith
  have hgap' : phi a y S t - phi a y S th ≤ theta0B ε V c ^ 2 := by
    have : (0:ℝ) ≤ theta0B ε V c ^ 2 := sq_nonneg _
    linarith
  exact ⟨hgap, node_filter_admits hnormal theta0B_nonneg hself hgap'⟩

/-! ### Диапазон ключа при ограниченных коэффициентах -/

/-- `|Κ̃_{ll'}(U)| ≤ |U|·ρ²` при `|cf| ≤ ρ` на `S ⊇ U`. -/
theorem abs_gramK2_le_rho {ρ : ℝ} (hcf : ∀ i ∈ S, ∀ l, |cf a T i l| ≤ ρ)
    {U : Finset ι} (hU : U ⊆ S) (l l' : κ) :
    |gramK2 a T U l l'| ≤ (U.card : ℝ) * ρ ^ 2 := by
  calc |gramK2 a T U l l'| ≤ ∑ i ∈ U, |cf a T i l * cf a T i l'| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ U, ρ ^ 2 := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [abs_mul, sq]
        exact mul_le_mul (hcf i (hU hi) l) (hcf i (hU hi) l') (abs_nonneg _)
          (le_trans (abs_nonneg _) (hcf i (hU hi) l))
    _ = (U.card : ℝ) * ρ ^ 2 := by simp

/-- `|M̃_l(U)| ≤ ρ·√(|U|·φ_U(t))` при `|cf| ≤ ρ`. -/
theorem abs_momK_le_rho {ρ : ℝ} (hρ : 0 ≤ ρ) (hcf : ∀ i ∈ S, ∀ l, |cf a T i l| ≤ ρ)
    {U : Finset ι} (hU : U ⊆ S) (l : κ) :
    |momK a y T U t l| ≤ ρ * Real.sqrt ((U.card : ℝ) * phi a y U t) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq U (fun i => cf a T i l)
    (fun i => y i - dotp (a i) t)
  have hc1 : ∑ i ∈ U, (cf a T i l) ^ 2 ≤ (U.card : ℝ) * ρ ^ 2 := by
    calc ∑ i ∈ U, (cf a T i l) ^ 2 ≤ ∑ _i ∈ U, ρ ^ 2 := by
          refine Finset.sum_le_sum fun i hi => ?_
          have h := hcf i (hU hi) l
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = (U.card : ℝ) * ρ ^ 2 := by simp
  have hc2 : ∑ i ∈ U, (y i - dotp (a i) t) ^ 2 = phi a y U t := by
    rw [phi]; exact Finset.sum_congr rfl fun i _ => by ring
  have h0 : (0:ℝ) ≤ phi a y U t := phi_nonneg a y U t
  have hsq : (momK a y T U t l) ^ 2 ≤ (ρ * Real.sqrt ((U.card : ℝ) * phi a y U t)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    calc (momK a y T U t l) ^ 2
        = (∑ i ∈ U, cf a T i l * (y i - dotp (a i) t)) ^ 2 := by rw [momK]
      _ ≤ (∑ i ∈ U, (cf a T i l) ^ 2) * ∑ i ∈ U, (y i - dotp (a i) t) ^ 2 := hcs
      _ ≤ ((U.card : ℝ) * ρ ^ 2) * phi a y U t := by
          rw [hc2]; exact mul_le_mul_of_nonneg_right hc1 h0
      _ = ρ ^ 2 * ((U.card : ℝ) * phi a y U t) := by ring
  have hnn : 0 ≤ ρ * Real.sqrt ((U.card : ℝ) * phi a y U t) :=
    mul_nonneg hρ (Real.sqrt_nonneg _)
  exact abs_le_of_sq_le_sq' hsq hnn |> fun h => abs_le.mpr ⟨h.1, h.2⟩

/-- Ключ любого подмножества `S` лежит в коробке с множителями `ρ` и `ρ²`. -/
theorem keyOf_mem_keyBox_rho {ρ : ℝ} (hρ : 0 ≤ ρ) (hcf : ∀ i ∈ S, ∀ l, |cf a T i l| ≤ ρ)
    {η ξ : ℝ} (hη : 0 < η) (hξ : 0 < ξ) {U : Finset ι} (hU : U ⊆ S) :
    keyOf a y T t η ξ U ∈
      keyBox (κ := κ) ⌈ρ * Real.sqrt ((S.card : ℝ) * phi a y S t) / η⌉
             ⌈(S.card : ℝ) * ρ ^ 2 / ξ⌉ S.card := by
  rw [keyOf, keyBox, Finset.mem_product, Finset.mem_product]
  constructor
  · simp only [Fintype.mem_piFinset]
    intro l
    refine floor_div_mem_Icc (le_trans (abs_momK_le_rho hρ hcf hU l) ?_) hη
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hρ
    have h1 : (U.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hU
    have h2 : phi a y U t ≤ phi a y S t := phi_mono hU t
    have h3 : (0:ℝ) ≤ phi a y U t := phi_nonneg a y U t
    nlinarith
  constructor
  · simp only [Fintype.mem_piFinset]
    intro l l'
    refine floor_div_mem_Icc ?_ hξ
    refine le_trans (abs_gramK2_le_rho hcf hU l l') ?_
    have h1 : (U.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hU
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  · simp only [Finset.mem_range]
    exact Nat.lt_succ_iff.mpr (Finset.card_le_card hU)

/-- **Размер таблицы динамики при `|cf| ≤ ρ`.** -/
theorem survivors_card_le_rho [DecidableEq ι] {ρ : ℝ} (hρ : 0 ≤ ρ) (hcf : ∀ i ∈ S, ∀ l, |cf a T i l| ≤ ρ)
    {η ξ : ℝ} (hη : 0 < η) (hξ : 0 < ξ)
    (adm : ι → Bool) (base : Finset ι) (L : List ι)
    (hbase : base ⊆ S) (hL : ∀ i ∈ L.toFinset, i ∈ S)
    {D : ℝ} (hD : ρ * Real.sqrt ((S.card : ℝ) * phi a y S t) / η ≤ D)
    {N : ℕ} (hN : S.card ≤ N) :
    (survivors (fun V => phi a y V t) (keyOf a y T t η ξ) adm base L).card
      ≤ (2 * ⌈D⌉ + 1).toNat ^ Fintype.card κ
        * ((2 * ⌈(N : ℝ) * ρ ^ 2 / ξ⌉ + 1).toNat ^ (Fintype.card κ * Fintype.card κ)
          * (N + 1)) := by
  have hsub : (survivors (fun V => phi a y V t) (keyOf a y T t η ξ) adm base L).card
      ≤ (keyBox (κ := κ) ⌈ρ * Real.sqrt ((S.card : ℝ) * phi a y S t) / η⌉
          ⌈(S.card : ℝ) * ρ ^ 2 / ξ⌉ S.card).card := by
    rw [← Finset.card_image_of_injOn
      (key_injOn_survivors (fun V => phi a y V t) (keyOf a y T t η ξ) adm base L)]
    refine Finset.card_le_card ?_
    intro k hk
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨_, hsubR, _⟩ := survivors_mem _ _ adm base L R hR
    refine keyOf_mem_keyBox_rho hρ hcf hη hξ ?_
    intro x hx
    rcases Finset.mem_union.mp (hsubR hx) with hb | hl
    · exact hbase hb
    · exact hL x hl
  refine le_trans hsub ?_
  have hNc : (S.card : ℝ) * ρ ^ 2 / ξ ≤ (N : ℝ) * ρ ^ 2 / ξ := by
    apply div_le_div_of_nonneg_right _ hξ.le
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hN) (sq_nonneg _)
  refine le_trans (Finset.card_le_card (keyBox_mono (Int.ceil_mono hD)
    (Int.ceil_mono hNc) hN)) ?_
  refine le_of_eq (card_keyBox _ _ ?_ ?_ _)
  · have : (0:ℝ) ≤ D := le_trans (div_nonneg (by positivity) hη.le) hD
    exact Int.ceil_nonneg this
  · exact Int.ceil_nonneg (by positivity)

/-! ### Стоимость при ограниченных коэффициентах -/

/-- **Стоимость одного запуска динамики при `|cf| ≤ ρ` и зажиме с константой `C`.**
Номер узла — в коробке `(2⌈√(16K·C·c/ε) + 1/2⌉ + 1)^K`; таблица не больше
`(2⌈ρ·48M√K·√(Nc/ε)⌉+1)^K · (2⌈8NMKρ²⌉+1)^{K²} · (N+1)`. При `ρ = 1`, `C = NK`
это `lo_fptas_cost_block`. -/
theorem lo_fptas_cost_rho [DecidableEq ι] {S : Finset ι} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hcf : ∀ i ∈ S, ∀ l, |cf a T i l| ≤ ρ)
    {ε c V C η ξ : ℝ} {N Mn : ℕ} {z : κ → ℤ}
    (hε : 0 < ε) (hc : 0 < c) (hV : 0 < V) (hN : 0 < N) (hM : 0 < Mn)
    (hKc : 0 < Fintype.card κ)
    (hzb : ∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C
      / (2 * (ε / (32 * c)))) + 1 / 2)
    (hηdef : η = theta0B ε V c / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Mn : ℝ)))
    (hξdef : ξ = 1 / (8 * (Mn : ℝ) * (Fintype.card κ : ℝ)))
    (hQ : phi a y S t ≤ 4 * V) (hScard : S.card ≤ N)
    (adm : ι → Bool) (base : Finset ι) (L : List ι)
    (hbase : base ⊆ S) (hL : ∀ i ∈ L.toFinset, i ∈ S) :
    z ∈ nodeBox (κ := κ)
        ⌈Real.sqrt ((Fintype.card κ : ℝ) * C / (2 * (ε / (32 * c)))) + 1 / 2⌉₊
    ∧ (survivors (fun W => phi a y W t) (keyOf a y T t η ξ) adm base L).card
      ≤ (2 * ⌈ρ * (48 * (Mn : ℝ) * Real.sqrt (Fintype.card κ : ℝ)
            * Real.sqrt ((N : ℝ) * c / ε))⌉ + 1).toNat ^ Fintype.card κ
        * ((2 * ⌈(N : ℝ) * ρ ^ 2 * (8 * (Mn : ℝ) * (Fintype.card κ : ℝ))⌉ + 1).toNat
            ^ (Fintype.card κ * Fintype.card κ) * (N + 1)) := by
  have hM0 : (0:ℝ) < (Mn : ℝ) := by exact_mod_cast hM
  have hK0 : (0:ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast hKc
  have hηpos : 0 < η := by
    rw [hηdef]
    have : 0 < theta0B ε V c := Real.sqrt_pos.mpr (by positivity)
    have : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr hK0
    positivity
  have hξpos : 0 < ξ := by rw [hξdef]; positivity
  refine ⟨mem_nodeBox_of_abs_le fun l => le_trans (hzb l) (Nat.le_ceil _), ?_⟩
  have hD0 := momRange_over_eta_le_block (Sc := S.card) (Mn := Mn) (Kc := Fintype.card κ)
    hε hc hV hN hKc hM hηdef (phi_nonneg a y S t) hQ (by exact_mod_cast hScard)
  have hD : ρ * Real.sqrt ((S.card : ℝ) * phi a y S t) / η
      ≤ ρ * (48 * (Mn : ℝ) * Real.sqrt (Fintype.card κ : ℝ)
            * Real.sqrt ((N : ℝ) * c / ε)) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hD0 hρ
  have hres := survivors_card_le_rho hρ hcf hηpos hξpos adm base L hbase hL hD hScard
  have hxi : (N : ℝ) * ρ ^ 2 / ξ = (N : ℝ) * ρ ^ 2 * (8 * (Mn : ℝ) * (Fintype.card κ : ℝ)) := by
    rw [hξdef]; field_simp
  rwa [hxi] at hres

/-! ### C.5: насколько можно улучшить константу зажима

Сетке нужен **равномерный** зажим `gram_S(v) ≤ C·gram_T(v)` при всех `v` сразу.
Объёмная выборка (Deshpande и др., Avron–Boutsidis, Dereziński–Warmuth) даёт множитель
`K+1` только **в среднем** и для одного вектора правых частей, поэтому напрямую сюда
не переносится. Здесь — обе стороны для равномерного зажима:

* `gram_le_improved` — для максимально-объёмной `K`-ки `C = 1 + K(|S| − K)` (вместо
  `|S|·K`: строки самой `K`-ки дают ровно `gram_T`);
* `clamp_lower_blocks` — нижняя граница: на `K ≥ 1` блоках по `m` одинаковых строк
  `e_l` (`|S| = mK`) **любая** `K`-ка требует `C ≥ m = |S|/K` (в точке `v = 1`,
  `clamp_const_ge_blocks`; там `K ≥ 1` — гипотеза `[Nonempty κ]`). При `K = 1`
  верхняя и нижняя границы совпадают (`|S|`), так что константа `1 + K(|S| − K)`
  точна при `K = 1`, а в общем случае отличается от наилучшей не больше чем в `K²` раз.
-/

/-- **Улучшенный зажим для максимально-объёмной `K`-ки:** `C = 1 + K(|S| − K)`. -/
theorem gram_le_improved [DecidableEq ι] (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0)
    (v : κ → ℝ) :
    gram a S v ≤ (1 + (Fintype.card κ : ℝ) * ((S.card : ℝ) - Fintype.card κ))
      * gramK a T v := by
  have hinj : Function.Injective T := injective_of_det_ne_zero hdet
  set TS : Finset ι := Finset.univ.image T with hTS
  have hsub : TS ⊆ S := by
    intro x hx
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hx
    exact hmax.1 l
  have hcardTS : TS.card = Fintype.card κ := by
    rw [hTS, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have hsplit := Finset.sum_sdiff (f := fun i => (dotp (a i) v) ^ 2) hsub
  have hT : ∑ i ∈ TS, (dotp (a i) v) ^ 2 = gramK a T v := by
    rw [hTS, Finset.sum_image (fun x _ y _ h => hinj h)]
    rfl
  have hrest : ∑ i ∈ S \ TS, (dotp (a i) v) ^ 2
      ≤ ((S \ TS).card : ℝ) * ((Fintype.card κ : ℝ) * gramK a T v) := by
    calc ∑ i ∈ S \ TS, (dotp (a i) v) ^ 2
        ≤ ∑ _i ∈ S \ TS, (Fintype.card κ : ℝ) * gramK a T v :=
          Finset.sum_le_sum fun i hi =>
            sq_dotp_le_card_mul_gramK hmax hdet (Finset.mem_sdiff.mp hi).1 v
      _ = ((S \ TS).card : ℝ) * ((Fintype.card κ : ℝ) * gramK a T v) := by simp
  have hcard : ((S \ TS).card : ℝ) = (S.card : ℝ) - Fintype.card κ := by
    rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub), hcardTS]
  rw [gram, ← hsplit, hT]
  rw [hcard] at hrest
  nlinarith [gramK_nonneg a T v]

/-- Строки «`K` блоков по `m` одинаковых строк `e_l`»: строка `(l, j)` равна `e_l`. -/
def blockRows (κ : Type*) [DecidableEq κ] (m : ℕ) : κ × Fin m → κ → ℝ :=
  fun p j => if p.1 = j then 1 else 0

/-- **Нижняя граница зажима.** Для любой `K`-ки `T` строк блочного семейства в точке
`v = 1`: `gram_S(v) = m·gram_T(v)`. При `K ≥ 1` здесь `|S| = mK`, так что всякая
константа равномерного зажима не меньше `m = |S|/K` (`clamp_const_ge_blocks`). -/
theorem clamp_lower_blocks (m : ℕ) (T : κ → κ × Fin m) :
    gram (blockRows κ m) Finset.univ (fun _ => 1)
      = (m : ℝ) * gramK (blockRows κ m) T (fun _ => 1) := by
  have hdot : ∀ p : κ × Fin m, dotp (blockRows κ m p) (fun _ => 1) = 1 := by
    intro p
    simp [dotp, blockRows]
  simp only [gram, gramK, hdot]
  simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  ring

/-- Следствие: при `K ≥ 1` (`[Nonempty κ]`) всякая константа равномерного зажима
`C ≥ m`. (Существование `T : κ → κ × Fin m` при непустом `κ` влечёт `m ≥ 1`.) -/
theorem clamp_const_ge_blocks {m : ℕ} [Nonempty κ] (T : κ → κ × Fin m) {C : ℝ}
    (hclamp : ∀ v, gram (blockRows κ m) Finset.univ v ≤ C * gramK (blockRows κ m) T v) :
    (m : ℝ) ≤ C := by
  have h := hclamp (fun _ => 1)
  rw [clamp_lower_blocks m T] at h
  have hpos : 0 < gramK (blockRows κ m) T (fun _ => 1) := by
    have hdot : ∀ p : κ × Fin m, dotp (blockRows κ m p) (fun _ => 1) = 1 := by
      intro p; simp [dotp, blockRows]
    simp only [gramK, hdot]
    simp [Fintype.card_pos]
  exact le_of_mul_le_mul_right h hpos

/-! ### Сквозная теорема при зажиме общего вида -/

variable [DecidableEq ι] in
/-- **Сквозная гарантия `δ`-цепочки при зажиме общего вида.** То же, что
`lo_fptas_block`, но вместо максимально-объёмной `K`-ки — любая невырожденная `K`-ка
внутри `A` (`hTA`) с зажимом `gram_A ≤ C·gram_T` (`hclamp`). При `T` = якорные строки
обе гипотезы выполнены без выбора `T` (`lo_fptas_portfolio_anchor`). -/
theorem lo_fptas_block_clamp {S A base : Finset ι} {cl : ι → Bool} {thA : κ → ℝ}
    {η ξ ε V C c s : ℝ} {k : ℕ} {L : List ι}
    (hTA : ∀ l, T l ∈ A) (hdet : (rowMat a T).det ≠ 0)
    (hnormA : IsNormal a y A thA)
    (hclamp : ∀ v, gram a A v ≤ C * gramK a T v) (hCpos : 0 < C)
    (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hc : 1 ≤ c) (hV : 0 < V)
    (hVF : V ≤ phi a y A thA) (hFV : phi a y A thA ≤ 2 * V)
    (hKc : 0 < (Fintype.card κ : ℝ))
    (hs : s = 2 * Real.sqrt ((ε / (32 * c)) * V / ((Fintype.card κ : ℝ) * C)))
    (hselfA : ∀ i ∈ A, cl i → 0 ≤ y i - dotp (a i) thA)
    (hη : 0 < η) (hξ : 0 < ξ)
    (hnd : L.Nodup) (hdisj : ∀ i ∈ L, i ∉ base)
    (hbA : base ⊆ A) (hAL : A ⊆ base ∪ L.toFinset)
    (hAS : A ⊆ S) (hbaseS : base ⊆ S) (hLS : ∀ i ∈ L.toFinset, i ∈ S)
    (hanchBase : anchorSet cl S ⊆ base) (hbaseAnch : ∀ i ∈ base, ¬ cl i)
    (hcov : AnchorCover a y cl S base k c) (hk : A.card ≤ base.card + k)
    {Tb : κ → ι} (hTb : ∀ l, Tb l ∈ base) (hdetBase : (rowMat a Tb).det ≠ 0)
    (hηθ : 8 * (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
      ≤ theta0B ε V c)
    (hζ8 : ((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ) ≤ 1/8) :
    ∃ z : κ → ℤ,
      (∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C
        / (2 * (ε / (32 * c)))) + 1 / 2) ∧
      ∀ t : κ → ℝ, (∀ l, dotp (a (T l)) t = y (T l) + s * (z l : ℝ)) →
        ∃ adm : ι → Bool,
          (∀ i, adm i → -theta0B ε V c ≤ y i - dotp (a i) t) ∧
          (∀ i ∈ A, i ∉ base → adm i) ∧
          ∃ R ∈ survivors (fun W => phi a y W t) (keyOf a y T t η ξ) adm base L,
            R.card = A.card ∧
            ∀ t' : κ → ℝ, (1 - 2 * ε) * phi a y A thA ≤ psiC a y cl R t' := by
  classical
  have hcpos : 0 < c := by linarith
  obtain ⟨z, hz1, hz2⟩ := exists_node_closing_step_clamp (a := a) (y := y) (cl := cl)
    (S := A) (T := T) (th := thA) hTA hdet hnormA hclamp hCpos hε hcpos hV hVF hFV hKc hs
    hselfA
  refine ⟨z, hz1, fun t ht => ?_⟩
  obtain ⟨hgapA, hadmitA⟩ := hz2 t ht
  have hadmA : ∀ i ∈ A, i ∉ base → decide (-theta0B ε V c ≤ y i - dotp (a i) t) = true := by
    intro i hiA hib
    refine decide_eq_true ?_
    by_cases hcl : cl i
    · exact hadmitA i hiA hcl
    · exact absurd (hanchBase (Finset.mem_filter.mpr ⟨hAS hiA, by simpa using hcl⟩)) hib
  refine ⟨fun i => decide (-theta0B ε V c ≤ y i - dotp (a i) t), ?_, hadmA, ?_⟩
  · intro i hi
    exact of_decide_eq_true hi
  · have hgap0 : 0 ≤ phi a y A t - phi a y A thA := by
      have := phi_min hnormA t; linarith
    have hθ0 : 0 ≤ theta0B ε V c := theta0B_nonneg
    have hθsq : theta0B ε V c ^ 2 = ε * V / (8 * c) := theta0B_sq hε.le hV.le hcpos.le
    have hF : 0 ≤ phi a y A thA := phi_nonneg a y A thA
    -- цена округления не больше половины запаса `θ₀²`
    have hr1 : bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
        (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
        (phi a y A t - phi a y A thA) ≤ theta0B ε V c ^ 2 / 2 :=
      bucketErr_le_half (by positivity) (by positivity) hθ0 hηθ hζ8 hgap0 hgapA
    -- и не больше `ε·F(Ā)`: `θ₀²/2 = εV/(16c) ≤ εV ≤ εF`
    have hr2 : bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
        (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
        (phi a y A t - phi a y A thA) ≤ ε * phi a y A thA := by
      refine le_trans hr1 ?_
      rw [hθsq]
      have h1 : ε * V / (8 * c) / 2 ≤ ε * V := by
        rw [div_div, div_le_iff₀ (by positivity)]
        nlinarith [mul_pos hε hV]
      have h2 : ε * V ≤ ε * phi a y A thA := mul_le_mul_of_nonneg_left hVF hε.le
      linarith
    -- калибровка: `c(2θ₀)² = εV/2 ≤ εF(Ā)/2 ≤ ε(F(Ā) − err)`
    have hcalA : c * (2 * theta0B ε V c) ^ 2
        ≤ ε * (phi a y A thA
          - bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
            (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
            (phi a y A t - phi a y A thA)) := by
      have hlhs : c * (2 * theta0B ε V c) ^ 2 = ε * V / 2 := by
        rw [mul_pow, hθsq]; field_simp; ring
      have hhalf : phi a y A thA / 2 ≤ phi a y A thA
          - bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
            (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
            (phi a y A t - phi a y A thA) := by
        nlinarith [hr2, hε1, hF]
      rw [hlhs]
      nlinarith [hVF, hhalf, hε.le]
    have hgapT : (phi a y A t - phi a y A thA)
        + bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
          (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
          (phi a y A t - phi a y A thA) ≤ theta0B ε V c ^ 2 := by linarith
    exact lo_fptas_step_block hdet hTA hη hξ hθ0 hε (by linarith)
      _ hnd hdisj hbA hAL hadmA hnormA hbaseS hLS hbaseAnch hcov hk
      (fun i hi => of_decide_eq_true hi) hTb hdetBase (by linarith) hgapT hr2 hcalA

/-! ### Портфельная форма: сетка в координатах якорей -/

section Portfolio

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- **Гарантия без перебора `K`-ок.** Как `lo_fptas_portfolio_block`, но сетка и ключ
строятся в координатах **якорных строк** — одна `K`-ка на всю задачу, выбирать её не
нужно. Цена: вместо `C ≥ |Ā|·K` нужно `C ≥ K + kω`, где `ω ≥ B_i'Σ_fB_i/d_i` на
носителе (можно взять `C = K + kω`). Вывод тот же: узел с ограниченными номерами,
в котором фильтр допускает
носитель, и носитель той же мощности с портфелем `w ≥ 0`,
`objLO ≥ (1−2ε)·F(Ā₀)`. -/
theorem lo_fptas_portfolio_anchor [Nonempty κ]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {cand A₀ : Finset ι} {La : List ι} {thA : κ → ℝ}
    {η ξ ε V C c s ω : ℝ} {k : ℕ}
    (hnormA : IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA)
    (hsys : ∀ i ∈ A₀, sysVar B Sf i / d i ≤ ω) (hω : 0 ≤ ω)
    (hC : (Fintype.card κ : ℝ) + (k : ℝ) * ω ≤ C) (hCpos : 0 < C)
    (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hc : 1 ≤ c) (hV : 0 < V)
    (hVF : V ≤ phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA)
    (hFV : phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA ≤ 2 * V)
    (hKc : 0 < (Fintype.card κ : ℝ))
    (hs : s = 2 * Real.sqrt ((ε / (32 * c)) * V / ((Fintype.card κ : ℝ) * C)))
    (hselfA : ∀ x ∈ barK (κ := κ) A₀, (Sum.isLeft x) →
      0 ≤ targetsK m d x - dotp (rowsK d B G x) thA)
    (hη : 0 < η) (hξ : 0 < ξ)
    (hnd : La.Nodup) (hA₀La : A₀ ⊆ La.toFinset) (hLcand : ∀ i ∈ La, i ∈ cand)
    (hcov : AnchorCover (rowsK d B G) (targetsK m d) (fun r => Sum.isLeft r)
      (barK (κ := κ) cand) (anchorRows ι κ) k c)
    (hkA : A₀.card ≤ k) (hA₀cand : A₀ ⊆ cand)
    (hηθ : 8 * (Real.sqrt (Fintype.card κ : ℝ) * ((La.length : ℝ) * η))
      ≤ theta0B ε V c)
    (hζ8 : ((La.length : ℝ) * ξ) * (Fintype.card κ : ℝ) ≤ 1/8) :
    ∃ z : κ → ℤ,
      (∀ l, |(z l : ℝ)| ≤ Real.sqrt ((Fintype.card κ : ℝ) * C
        / (2 * (ε / (32 * c)))) + 1 / 2) ∧
      ∀ t : κ → ℝ, (∀ l, dotp (rowsK d B G (Sum.inr l)) t
          = targetsK m d (Sum.inr l) + s * (z l : ℝ)) →
        ∃ adm : (ι ⊕ κ) → Bool,
          (∀ x, adm x → -theta0B ε V c
            ≤ targetsK m d x - dotp (rowsK d B G x) t) ∧
          (∀ x ∈ barK (κ := κ) A₀, x ∉ anchorRows ι κ → adm x) ∧
          ∃ R ∈ survivors (fun W => phi (rowsK d B G) (targetsK m d) W t)
              (keyOf (rowsK d B G) (targetsK m d) (fun l => Sum.inr l) t η ξ) adm (anchorRows ι κ)
              (La.map Sum.inl),
            (assetsOf (κ := κ) R).card = A₀.card
            ∧ ∃ w : ι → ℝ, (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i)
              ∧ (1 - 2 * ε) * phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA
                ≤ objLO m d B Sf (assetsOf (κ := κ) R) w := by
  classical
  set a := rowsK d B G with ha
  set y := targetsK m d with hy
  set L : List (ι ⊕ κ) := La.map Sum.inl with hL
  have hndL : L.Nodup := hnd.map (fun _ _ h => by injection h)
  have hdisj : ∀ x ∈ L, x ∉ anchorRows ι κ := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    intro hc
    exact (not_isLeft_of_mem_anchorRows hc) (by simp)
  have hbA : anchorRows ι κ ⊆ barK (κ := κ) A₀ := anchorRows_subset_barK A₀
  have hAL : barK (κ := κ) A₀ ⊆ anchorRows ι κ ∪ L.toFinset := by
    intro x hx
    rcases x with i | l
    · refine Finset.mem_union_right _ ?_
      have hiA : i ∈ A₀ := by simpa [barK, Finset.inl_mem_disjSum] using hx
      refine List.mem_toFinset.mpr ?_
      exact List.mem_map.mpr ⟨i, List.mem_toFinset.mp (hA₀La hiA), rfl⟩
    · exact Finset.mem_union_left _ (inr_mem_anchorRows l)
  have hAS : barK (κ := κ) A₀ ⊆ barK (κ := κ) cand := by
    intro x hx
    rcases x with i | l
    · have : i ∈ A₀ := by simpa [barK, Finset.inl_mem_disjSum] using hx
      simpa [barK, Finset.inl_mem_disjSum] using hA₀cand this
    · exact inr_mem_barK cand l
  have hbaseS : anchorRows ι κ ⊆ barK (κ := κ) cand := anchorRows_subset_barK cand
  have hLS : ∀ x ∈ L.toFinset, x ∈ barK (κ := κ) cand := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    simpa [barK, Finset.inl_mem_disjSum] using hLcand i hi
  have hanchBase : anchorSet (fun r : ι ⊕ κ => Sum.isLeft r) (barK (κ := κ) cand)
      ⊆ anchorRows ι κ := by
    intro x hx
    obtain ⟨_, hx2⟩ := Finset.mem_filter.mp hx
    rcases x with i | l
    · simp at hx2
    · exact inr_mem_anchorRows l
  have hbaseAnch : ∀ x ∈ anchorRows ι κ, ¬ (Sum.isLeft x) :=
    fun _ hx => not_isLeft_of_mem_anchorRows hx
  have hk : (barK (κ := κ) A₀).card ≤ (anchorRows ι κ).card + k := by
    rw [card_barK, card_anchorRows]; omega
  -- зажим формы Грама в координатах якорей: `gram_Ā ≤ (K + Σ_{A₀} ω_i)·gram_anch`
  have hclamp : ∀ v, gram a (barK (κ := κ) A₀) v
      ≤ C * gramK a (fun l => (Sum.inr l : ι ⊕ κ)) v := by
    intro v
    have hgK : gramK a (fun l => (Sum.inr l : ι ⊕ κ)) v
        = gram (rowsK d B G) (anchorRows ι κ) v := by
      rw [gram_anchorRows]; simp [gramK, ha, rowsK, dotp]
    have hpt : ∀ x ∈ barK (κ := κ) A₀, ∀ v, (dotp (a x) v) ^ 2
        ≤ (Sum.elim (fun i => sysVar B Sf i / d i) (fun _ => (1:ℝ)) x)
          * gramK a (fun l => (Sum.inr l : ι ⊕ κ)) v := by
      intro x _ v
      have hgK' : gramK a (fun l => (Sum.inr l : ι ⊕ κ)) v
          = gram (rowsK d B G) (anchorRows ι κ) v := by
        rw [gram_anchorRows]; simp [gramK, ha, rowsK, dotp]
      rcases x with i | l
      · rw [hgK']; exact sq_dotp_asset_le hd hG hPS i v
      · simp only [Sum.elim_inr, one_mul, gramK]
        exact Finset.single_le_sum (f := fun l' => (dotp (a (Sum.inr l')) v) ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ l)
    refine le_trans (gram_le_of_pointwise hpt v) ?_
    refine mul_le_mul_of_nonneg_right ?_ (gramK_nonneg _ _ _)
    have hsum : ∑ x ∈ barK (κ := κ) A₀, Sum.elim (fun i => sysVar B Sf i / d i)
        (fun _ => (1:ℝ)) x = (∑ i ∈ A₀, sysVar B Sf i / d i) + (Fintype.card κ : ℝ) := by
      simp [barK, Finset.sum_disjSum]
    rw [hsum]
    have h1 : ∑ i ∈ A₀, sysVar B Sf i / d i ≤ (A₀.card : ℝ) * ω := by
      calc ∑ i ∈ A₀, sysVar B Sf i / d i ≤ ∑ _i ∈ A₀, ω := Finset.sum_le_sum hsys
        _ = (A₀.card : ℝ) * ω := by simp
    have h2 : (A₀.card : ℝ) * ω ≤ (k : ℝ) * ω :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hkA) hω
    linarith
  obtain ⟨z, hz1, hz2⟩ := lo_fptas_block_clamp (a := a) (y := y) (cl := fun r => Sum.isLeft r)
    (S := barK (κ := κ) cand) (A := barK (κ := κ) A₀) (base := anchorRows ι κ)
    (T := fun l => (Sum.inr l : ι ⊕ κ)) (thA := thA) (η := η) (ξ := ξ) (ε := ε) (V := V)
    (C := C) (c := c) (s := s)
    (k := k) (L := L) (Tb := fun l => (Sum.inr l : ι ⊕ κ))
    (fun l => inr_mem_barK A₀ l)
    (det_anchor_ne_zero (d := d) (B := B) (P := P) (Sf := Sf) hG hPS) hnormA hclamp hCpos hε hε1 hc hV hVF hFV hKc hs hselfA hη hξ
    hndL hdisj hbA hAL hAS hbaseS hLS hanchBase hbaseAnch hcov hk
    (fun l => inr_mem_anchorRows l)
    (det_anchor_ne_zero (d := d) (B := B) (P := P) (Sf := Sf) hG hPS)
    (by rwa [hL, List.length_map]) (by rwa [hL, List.length_map])
  refine ⟨z, hz1, fun t ht => ?_⟩
  obtain ⟨adm, hadm1, hadm2, R, hR, hcard, hval⟩ := hz2 t ht
  refine ⟨adm, hadm1, hadm2, R, hR, ?_, ?_⟩
  · have := card_assetsOf_eq (survivors_mem _ _ adm _ L R hR).1 hbA hcard
    rwa [assetsOf_barK] at this
  · set R₀ := assetsOf (κ := κ) R with hR₀
    have hReq : R = barK (κ := κ) R₀ :=
      barK_assetsOf (survivors_mem _ _ adm _ L R hR).1
    obtain ⟨zv, hleast, hgreat⟩ :=
      isGreatest_objLO_isLeast_QLO (Sf := Sf) (P := P) (G := G) hd hG hPS R₀
    obtain ⟨t₁, ht₁⟩ := hleast.1
    obtain ⟨w, hw, hwv⟩ := hgreat.1
    refine ⟨w, hw, ?_⟩
    rw [← hwv, ht₁, ← QLO_eq_psiC (P := P) hd hG]
    have := hval t₁
    rwa [hReq] at this

/-- **Коэффициенты Крамера в базисе якорей.** Для строк `Ā₀` (активы и якоря)
`|cf_{xl}| ≤ √(max 1 ω)`, если `ω ≥ B_i'Σ_fB_i/d_i` на `A₀`. -/
theorem abs_cf_anchor_le (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {A₀ : Finset ι} {ω : ℝ} (hsys : ∀ i ∈ A₀, sysVar B Sf i / d i ≤ ω)
    (x : ι ⊕ κ) (hx : x ∈ barK (κ := κ) A₀) (l : κ) :
    |cf (rowsK d B G) (fun l => (Sum.inr l : ι ⊕ κ)) x l| ≤ Real.sqrt (max 1 ω) := by
  have hdet := det_anchor_ne_zero (d := d) (B := B) (P := P) (Sf := Sf) hG hPS
  have hgK : ∀ v, gramK (rowsK d B G) (fun l => (Sum.inr l : ι ⊕ κ)) v
      = gram (rowsK d B G) (anchorRows ι κ) v := by
    intro v; rw [gram_anchorRows]; simp [gramK, rowsK, dotp]
  refine abs_cf_le_of_pointwise hdet (fun v => ?_) l
  rcases x with i | l'
  · have hi : i ∈ A₀ := by simpa [barK, Finset.inl_mem_disjSum] using hx
    rw [hgK]
    refine le_trans (sq_dotp_asset_le hd hG hPS i v) ?_
    refine mul_le_mul_of_nonneg_right (le_trans (hsys i hi) (le_max_right _ _))
      (gram_nonneg _ _ _)
  · have h1 : (dotp (rowsK d B G (Sum.inr l')) v) ^ 2
        ≤ gramK (rowsK d B G) (fun l => (Sum.inr l : ι ⊕ κ)) v := by
      simp only [gramK]
      exact Finset.single_le_sum
        (f := fun l'' => (dotp (rowsK d B G (Sum.inr l'')) v) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ l')
    have h2 : 0 ≤ gramK (rowsK d B G) (fun l => (Sum.inr l : ι ⊕ κ)) v := gramK_nonneg _ _ _
    nlinarith [le_max_left 1 ω]

end Portfolio

end SparseSharpe.Factor
