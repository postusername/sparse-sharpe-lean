import SparseSharpe.Factor.AdditiveKey
import SparseSharpe.Factor.ClippedNode

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Динамика без матрицы Грама: шаг в одном узле (задача L5 ТЗ, сессия 23)

В узле `τ ∈ ℝ^K` у актива `i` есть **счёт** `s_i = (m_i − ⟨B_i,τ⟩)_+²/d_i` и **вектор**
`v_i = w_i(τ)·GΣ_fB_i ∈ ℝ^K`, `w_i(τ) = (m_i − ⟨B_i,τ⟩)_+/d_i`. По тождеству дефекта
(`objLO_wclip_deficit`, `defect_eq_sum_sq`) для любого набора `R`

    objLO(R, w(τ)) = τ'Σ_f⁻¹τ + Σ_{i∈R} s_i − ‖Gτ − Σ_{i∈R} v_i‖²,

и набор влияет на правую часть только через `Σ_R s_i`, `Σ_R v_i`. Ключ набора —
`(Σ_{i∈R} ⌊v_i/η⌋ ∈ ℤ^K, |R|)`, он **точно аддитивен**: динамика — это рюкзак
`knap` (`Factor/AdditiveKey.lean`).

* `clip_node_step` — если ключ набора `R` совпал с ключом `S`, то
  `objLO(R, w(τ)) ≥ objLO(S, w(τ)) − 2e·√D_S − e²`, `e = √K·|S|·η`, `D_S` — дефект `S`;
* `clip_box_bound` — ключи подмножеств `S` лежат в коробке `‖·‖_∞ ≤ Q`, если
  `ω·k·σ ≤ ((Q − k)η)²`, где `σ ≥ Σ_{i∈S} s_i`.

Сквозная гарантия (узел сетки, оценка размера семейства, догадки) — ниже в этом файле и в
`Factor/ClippedTrading.lean`.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-! ### Данные рюкзака в узле -/

/-- Счёт актива в узле: `s_i(τ) = (m_i − ⟨B_i,τ⟩)_+²/d_i`. -/
noncomputable def clipScore (m d : ι → ℝ) (B : ι → κ → ℝ) (τ : κ → ℝ) (i : ι) : ℝ :=
  max (m i - dotp (B i) τ) 0 ^ 2 / d i

/-- Вклад актива в ключ: `(⌊v_i/η⌋, 1) ∈ ℤ^K × ℕ`. -/
noncomputable def clipKeyItem (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf G : κ → κ → ℝ) (η : ℝ)
    (τ : κ → ℝ) (i : ι) : (κ → ℤ) × ℕ :=
  (fun l => ⌊vcoord G Sf B (wclip m d B τ) i l / η⌋, 1)

/-- Коробка ключей: `|z_l| ≤ Q`, размер не больше `k`. -/
noncomputable def clipBox (κ : Type*) [Fintype κ] [DecidableEq κ] (Q k : ℕ) :
    Finset ((κ → ℤ) × ℕ) :=
  (Fintype.piFinset fun _ : κ => Finset.Icc (-(Q : ℤ)) (Q : ℤ)) ×ˢ Finset.range (k + 1)

lemma card_clipBox (Q k : ℕ) : (clipBox κ Q k).card = (2 * Q + 1) ^ Fintype.card κ * (k + 1) := by
  rw [clipBox, Finset.card_product, Fintype.card_piFinset, Finset.card_range]
  congr 1
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ]
  congr 1
  omega

/-- **Таблица динамики в узле `τ`.** -/
noncomputable def clipTable (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf G : κ → κ → ℝ) (η : ℝ)
    (Q k : ℕ) (L : List ι) (τ : κ → ℝ) : Finset (Finset ι) :=
  knap (fun i => clipScore m d B τ i) (clipKeyItem m d B Sf G η τ) (clipBox κ Q k) L

/-- Размер таблицы в одном узле: `(k+1)(2Q+1)^K + 1`, **не зависит от `M`**. -/
theorem card_clipTable_le (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf G : κ → κ → ℝ) (η : ℝ)
    (Q k : ℕ) (L : List ι) (τ : κ → ℝ) :
    (clipTable m d B Sf G η Q k L τ).card ≤ (2 * Q + 1) ^ Fintype.card κ * (k + 1) + 1 := by
  have := knap_card_le (fun i => clipScore m d B τ i) (clipKeyItem m d B Sf G η τ)
    (clipBox κ Q k) L
  rw [card_clipBox] at this
  exact this

/-! ### Сумма ключей -/

lemma sum_clipKeyItem_fst (U : Finset ι) (η : ℝ) (τ : κ → ℝ) (l : κ) :
    (∑ i ∈ U, clipKeyItem m d B Sf G η τ i).1 l
      = ∑ i ∈ U, ⌊vcoord G Sf B (wclip m d B τ) i l / η⌋ := by
  rw [Prod.fst_sum, Finset.sum_apply]
  rfl

lemma sum_clipKeyItem_snd (U : Finset ι) (η : ℝ) (τ : κ → ℝ) :
    (∑ i ∈ U, clipKeyItem m d B Sf G η τ i).2 = U.card := by
  rw [Prod.snd_sum]
  simp [clipKeyItem]

/-- Из равенства ключей: те же размеры. -/
lemma clip_key_card {R U : Finset ι} {τ : κ → ℝ} {η : ℝ}
    (hkey : ∑ i ∈ R, clipKeyItem m d B Sf G η τ i = ∑ i ∈ U, clipKeyItem m d B Sf G η τ i) :
    R.card = U.card := by
  have := congrArg Prod.snd hkey
  rwa [sum_clipKeyItem_snd, sum_clipKeyItem_snd] at this

/-- Из равенства ключей: `|Σ_R v_l − Σ_U v_l| ≤ |U|·η` по каждой координате. -/
lemma clip_key_close (hη : 0 < η) {R U : Finset ι} {τ : κ → ℝ}
    (hkey : ∑ i ∈ R, clipKeyItem m d B Sf G η τ i = ∑ i ∈ U, clipKeyItem m d B Sf G η τ i)
    (l : κ) :
    |∑ i ∈ R, vcoord G Sf B (wclip m d B τ) i l - ∑ i ∈ U, vcoord G Sf B (wclip m d B τ) i l|
      ≤ U.card * η := by
  have hcard : R.card = U.card := clip_key_card hkey
  have hz : ∑ i ∈ R, ⌊vcoord G Sf B (wclip m d B τ) i l / η⌋
      = ∑ i ∈ U, ⌊vcoord G Sf B (wclip m d B τ) i l / η⌋ := by
    have := congrFun (congrArg Prod.fst hkey) l
    rwa [sum_clipKeyItem_fst, sum_clipKeyItem_fst] at this
  -- для каждого множества: `η Σ⌊v/η⌋ ≤ Σ v < η Σ⌊v/η⌋ + |X| η`
  have hbound : ∀ X : Finset ι,
      η * (∑ i ∈ X, ⌊vcoord G Sf B (wclip m d B τ) i l / η⌋ : ℤ)
        ≤ ∑ i ∈ X, vcoord G Sf B (wclip m d B τ) i l ∧
      ∑ i ∈ X, vcoord G Sf B (wclip m d B τ) i l
        ≤ η * (∑ i ∈ X, ⌊vcoord G Sf B (wclip m d B τ) i l / η⌋ : ℤ) + X.card * η := by
    intro X
    constructor
    · push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have := Int.floor_le (vcoord G Sf B (wclip m d B τ) i l / η)
      calc η * (⌊vcoord G Sf B (wclip m d B τ) i l / η⌋ : ℝ)
          ≤ η * (vcoord G Sf B (wclip m d B τ) i l / η) :=
            mul_le_mul_of_nonneg_left this hη.le
        _ = vcoord G Sf B (wclip m d B τ) i l := by field_simp
    · push_cast
      rw [Finset.mul_sum]
      have hterm : ∀ i ∈ X, vcoord G Sf B (wclip m d B τ) i l
          ≤ η * (⌊vcoord G Sf B (wclip m d B τ) i l / η⌋ : ℝ) + η := by
        intro i _
        have := Int.lt_floor_add_one (vcoord G Sf B (wclip m d B τ) i l / η)
        have h2 : η * (vcoord G Sf B (wclip m d B τ) i l / η)
            ≤ η * ((⌊vcoord G Sf B (wclip m d B τ) i l / η⌋ : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left this.le hη.le
        have h3 : η * (vcoord G Sf B (wclip m d B τ) i l / η)
            = vcoord G Sf B (wclip m d B τ) i l := by field_simp
        linarith
      calc ∑ i ∈ X, vcoord G Sf B (wclip m d B τ) i l
          ≤ ∑ i ∈ X, (η * (⌊vcoord G Sf B (wclip m d B τ) i l / η⌋ : ℝ) + η) :=
            Finset.sum_le_sum hterm
        _ = ∑ i ∈ X, η * (⌊vcoord G Sf B (wclip m d B τ) i l / η⌋ : ℝ) + X.card * η := by
            rw [Finset.sum_add_distrib]; simp
  obtain ⟨hR1, hR2⟩ := hbound R
  obtain ⟨hU1, hU2⟩ := hbound U
  rw [hz] at hR1 hR2
  rw [hcard] at hR2
  rw [abs_le]
  constructor <;> nlinarith

/-! ### Неравенство треугольника для сумм квадратов -/

lemma sum_sq_add_le {ι' : Type*} (s : Finset ι') (a b : ι' → ℝ) :
    ∑ i ∈ s, (a i + b i) ^ 2
      ≤ (Real.sqrt (∑ i ∈ s, a i ^ 2) + Real.sqrt (∑ i ∈ s, b i ^ 2)) ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s a b
  have ha : 0 ≤ ∑ i ∈ s, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : 0 ≤ ∑ i ∈ s, b i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hab : ∑ i ∈ s, a i * b i
      ≤ Real.sqrt (∑ i ∈ s, a i ^ 2) * Real.sqrt (∑ i ∈ s, b i ^ 2) := by
    rw [← Real.sqrt_mul ha]
    exact Real.le_sqrt_of_sq_le hcs
  have hexp : ∑ i ∈ s, (a i + b i) ^ 2
      = ∑ i ∈ s, a i ^ 2 + 2 * ∑ i ∈ s, a i * b i + ∑ i ∈ s, b i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hexp]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]

/-! ### Один шаг: представитель корзины -/

/-- **Шаг динамики в узле.** Пусть `S` — любой набор с `|S| ≤ k`, и ключи всех его подмножеств
лежат в коробке (`hbox`). Тогда в таблице есть набор `R` с `|R| = |S|`, для которого

    objLO(R, w(τ)) ≥ objLO(S, w(τ)) − 2e·√D_S − e²,

где `D_S = (Σ_f B_S'w(τ) − τ)'Σ_f⁻¹(Σ_f B_S'w(τ) − τ)` — дефект `S` в узле, а
`e = √K·|S|·η` — ошибка округления ключа. -/
theorem clip_node_step (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {η : ℝ} (hη : 0 < η) {Q k : ℕ} {S : Finset ι} (hSk : S.card ≤ k) {τ : κ → ℝ}
    (hbox : ∀ U ⊆ S, ∀ l, |∑ i ∈ U, ⌊vcoord G Sf B (wclip m d B τ) i l / η⌋| ≤ (Q : ℤ))
    {L : List ι} (hnd : L.Nodup) (hL : ∀ i, i ∈ L) :
    ∃ R ∈ clipTable m d B Sf G η Q k L τ, R.card = S.card ∧
      objLO m d B Sf S (wclip m d B τ)
        - (2 * (Real.sqrt (Fintype.card κ) * (S.card * η))
              * Real.sqrt (quadf P (tw Sf B S (wclip m d B τ) - τ))
            + (Real.sqrt (Fintype.card κ) * (S.card * η)) ^ 2)
        ≤ objLO m d B Sf R (wclip m d B τ) := by
  classical
  -- ключи подмножеств `S` лежат в коробке
  have hbox' : ∀ U' ⊆ S, ∑ j ∈ U', clipKeyItem m d B Sf G η τ j ∈ clipBox κ Q k := by
    intro U' hU'
    rw [clipBox, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun l => ?_, ?_⟩
    · rw [Finset.mem_Icc, ← abs_le, sum_clipKeyItem_fst]
      exact hbox U' hU' l
    · rw [sum_clipKeyItem_snd]
      have := Finset.card_le_card hU'
      omega
  have hSL : S ⊆ L.toFinset := fun i _ => List.mem_toFinset.mpr (hL i)
  obtain ⟨R, hR, hkey, hval⟩ := knap_spec (fun i => clipScore m d B τ i)
    (clipKeyItem m d B Sf G η τ) (clipBox κ Q k) L hnd S hSL hbox'
  have hcard := clip_key_card (m := m) (d := d) (B := B) (Sf := Sf) (G := G) hkey
  refine ⟨R, hR, hcard, ?_⟩
  set w := wclip m d B τ with hw
  set Kc : ℝ := (Fintype.card κ : ℝ) with hKc
  set e : ℝ := Real.sqrt Kc * (S.card * η) with he
  have hKc0 : 0 ≤ Kc := Nat.cast_nonneg _
  have he0 : 0 ≤ e := mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hη.le)
  -- дефекты в координатах
  have hDR := defect_eq_sum_sq (B := B) (Sf := Sf) hG R w τ
  have hDS := defect_eq_sum_sq (B := B) (Sf := Sf) hG S w τ
  set vR : κ → ℝ := fun l => ∑ i ∈ R, vcoord G Sf B w i l with hvR
  set vS : κ → ℝ := fun l => ∑ i ∈ S, vcoord G Sf B w i l with hvS
  set gt : κ → ℝ := fun l => dotp (G l) τ with hgt
  have hsplit : ∀ l, vR l - gt l = (vS l - gt l) + (vR l - vS l) := fun l => by ring
  have hsum_b : ∑ l, (vR l - vS l) ^ 2 ≤ Kc * (S.card * η) ^ 2 := by
    calc ∑ l, (vR l - vS l) ^ 2 ≤ ∑ _l : κ, (S.card * η) ^ 2 := by
          refine Finset.sum_le_sum fun l _ => ?_
          have := clip_key_close (m := m) (d := d) (B := B) (Sf := Sf) (G := G) hη hkey l
          exact sq_le_sq' (by linarith [(abs_le.mp this).1]) (by linarith [(abs_le.mp this).2])
      _ = Kc * (S.card * η) ^ 2 := by simp [hKc]
  have hsqrt_b : Real.sqrt (∑ l, (vR l - vS l) ^ 2) ≤ e := by
    calc Real.sqrt (∑ l, (vR l - vS l) ^ 2) ≤ Real.sqrt (Kc * (S.card * η) ^ 2) :=
          Real.sqrt_le_sqrt hsum_b
      _ = e := by
          rw [Real.sqrt_mul hKc0, Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg _) hη.le)]
  have hDS0 : 0 ≤ quadf P (tw Sf B S w - τ) := defect_nonneg hG S w τ
  set DS := quadf P (tw Sf B S w - τ) with hDSdef
  have hDSsq : ∑ l, (vS l - gt l) ^ 2 = DS := hDS.symm
  have hDR_le : quadf P (tw Sf B R w - τ) ≤ (Real.sqrt DS + e) ^ 2 := by
    rw [hDR]
    have h1 := sum_sq_add_le Finset.univ (fun l => vS l - gt l) (fun l => vR l - vS l)
    have h2 : ∑ l, (vR l - gt l) ^ 2 = ∑ l, ((vS l - gt l) + (vR l - vS l)) ^ 2 :=
      Finset.sum_congr rfl fun l _ => by rw [hsplit l]
    rw [h2]
    refine le_trans h1 ?_
    rw [hDSsq]
    have : Real.sqrt DS + Real.sqrt (∑ l, (vR l - vS l) ^ 2) ≤ Real.sqrt DS + e := by linarith
    exact pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) this 2
  -- значения
  have hQR : objLO m d B Sf R w = quadf P τ + ∑ i ∈ R, clipScore m d B τ i
      - quadf P (tw Sf B R w - τ) := by
    rw [hw, objLO_wclip_deficit hd hG hPS R τ, QLO]; rfl
  have hQS : objLO m d B Sf S w = quadf P τ + ∑ i ∈ S, clipScore m d B τ i - DS := by
    rw [hw, objLO_wclip_deficit hd hG hPS S τ, QLO]; rfl
  have hDSeq : DS = Real.sqrt DS ^ 2 := (Real.sq_sqrt hDS0).symm
  rw [hQR, hQS]
  nlinarith [hval, hDR_le, hDSeq, Real.sqrt_nonneg DS]

/-! ### Коробка: ключи подмножеств носителя -/

/-- Счёт неотрицателен. -/
lemma clipScore_nonneg (hd : ∀ i, 0 < d i) (τ : κ → ℝ) (i : ι) :
    0 ≤ clipScore m d B τ i :=
  div_nonneg (sq_nonneg _) (hd i).le

/-- `d_i·w_i² = s_i`. -/
lemma d_mul_wclip_sq (hd : ∀ i, 0 < d i) (τ : κ → ℝ) (i : ι) :
    d i * wclip m d B τ i ^ 2 = clipScore m d B τ i := by
  have := (hd i).ne'
  simp only [wclip, clipScore]
  field_simp

/-- Длина вектора `v_i`: `|v_il| ≤ √(ω s_i)`, если `B_i'Σ_fB_i ≤ ω d_i`. -/
lemma abs_vcoord_le (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {ω : ℝ} {i : ι}
    (hsys : sysVar B Sf i / d i ≤ ω) (τ : κ → ℝ) (l : κ) :
    |vcoord G Sf B (wclip m d B τ) i l| ≤ Real.sqrt (ω * clipScore m d B τ i) := by
  apply Real.abs_le_sqrt
  have h1 := vcoord_sq_le (B := B) hG hPS (wclip m d B τ) i l
  have h2 : sysVar B Sf i ≤ ω * d i := by
    have := (div_le_iff₀ (hd i)).mp hsys
    linarith
  calc vcoord G Sf B (wclip m d B τ) i l ^ 2
      ≤ wclip m d B τ i ^ 2 * sysVar B Sf i := h1
    _ ≤ wclip m d B τ i ^ 2 * (ω * d i) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = ω * (d i * wclip m d B τ i ^ 2) := by ring
    _ = ω * clipScore m d B τ i := by rw [d_mul_wclip_sq hd]

/-- `|⌊x⌋| ≤ |x| + 1`. -/
lemma abs_floor_le (x : ℝ) : |(⌊x⌋ : ℝ)| ≤ |x| + 1 := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  rw [abs_le]
  constructor <;> cases' abs_cases x with h h <;> linarith [h.1, h.2]

/-- **Коробка.** Если `|S| ≤ k`, `B_i'Σ_fB_i ≤ ω d_i` на `S`, `Σ_{i∈S} s_i ≤ σ` и
`ω k σ ≤ ((Q − k) η)²`, то все суммы `Σ_{i∈U} ⌊v_il/η⌋`, `U ⊆ S`, по модулю не больше `Q`. -/
theorem clip_box_bound (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {η : ℝ} (hη : 0 < η) {τ : κ → ℝ} {S : Finset ι} {k Q : ℕ} (hSk : S.card ≤ k)
    {ω σ : ℝ} (hω : 0 ≤ ω) (hsys : ∀ i ∈ S, sysVar B Sf i / d i ≤ ω)
    (hσ : ∑ i ∈ S, clipScore m d B τ i ≤ σ) (hQk : (k : ℝ) ≤ Q)
    (hQ : ω * k * σ ≤ (((Q : ℝ) - k) * η) ^ 2) :
    ∀ U ⊆ S, ∀ l, |∑ i ∈ U, ⌊vcoord G Sf B (wclip m d B τ) i l / η⌋| ≤ (Q : ℤ) := by
  intro U hU l
  set g : ι → ℝ := fun i => Real.sqrt (ω * clipScore m d B τ i) with hg
  -- Коши–Буняковский: `(Σ_U g)² ≤ |U|·ω·Σ_U s ≤ k ω σ`
  have hsumg : ∑ i ∈ U, g i ≤ ((Q : ℝ) - k) * η := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq U (fun _ => (1 : ℝ)) g
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
    have hg2 : ∑ i ∈ U, g i ^ 2 = ω * ∑ i ∈ U, clipScore m d B τ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hg]
      exact Real.sq_sqrt (mul_nonneg hω (clipScore_nonneg hd τ i))
    rw [hg2] at hcs
    have hUS : ∑ i ∈ U, clipScore m d B τ i ≤ ∑ i ∈ S, clipScore m d B τ i :=
      Finset.sum_le_sum_of_subset_of_nonneg hU fun i _ _ => clipScore_nonneg hd τ i
    have hUk : (U.card : ℝ) ≤ k := by
      exact_mod_cast le_trans (Finset.card_le_card hU) hSk
    have h1 : (∑ i ∈ U, g i) ^ 2 ≤ (((Q : ℝ) - k) * η) ^ 2 := by
      refine le_trans hcs (le_trans ?_ hQ)
      have hs0 : 0 ≤ ∑ i ∈ U, clipScore m d B τ i :=
        Finset.sum_nonneg fun i _ => clipScore_nonneg hd τ i
      calc (U.card : ℝ) * (ω * ∑ i ∈ U, clipScore m d B τ i)
          ≤ k * (ω * σ) := by
            apply mul_le_mul hUk _ (mul_nonneg hω hs0) (Nat.cast_nonneg _)
            exact mul_le_mul_of_nonneg_left (le_trans hUS hσ) hω
        _ = ω * k * σ := by ring
    have hnn : 0 ≤ ((Q : ℝ) - k) * η := mul_nonneg (by linarith) hη.le
    exact abs_le_of_sq_le_sq' h1 hnn |>.2
  -- оценка суммы целых частей
  have hfloor : |((∑ i ∈ U, ⌊vcoord G Sf B (wclip m d B τ) i l / η⌋ : ℤ) : ℝ)|
      ≤ ∑ i ∈ U, (|vcoord G Sf B (wclip m d B τ) i l| / η + 1) := by
    push_cast
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
    refine le_trans (abs_floor_le _) ?_
    rw [abs_div, abs_of_pos hη]
  have hvle : ∑ i ∈ U, |vcoord G Sf B (wclip m d B τ) i l| ≤ ∑ i ∈ U, g i :=
    Finset.sum_le_sum fun i hi => abs_vcoord_le hd hG hPS (hsys i (hU hi)) τ l
  have hsplit : ∑ i ∈ U, (|vcoord G Sf B (wclip m d B τ) i l| / η + 1)
      = (∑ i ∈ U, |vcoord G Sf B (wclip m d B τ) i l|) / η + U.card := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div]; simp
  have hUk : (U.card : ℝ) ≤ k := by
    exact_mod_cast le_trans (Finset.card_le_card hU) hSk
  have hdiv : (∑ i ∈ U, |vcoord G Sf B (wclip m d B τ) i l|) / η ≤ (Q : ℝ) - k := by
    rw [div_le_iff₀ hη]
    linarith
  have hfin : |((∑ i ∈ U, ⌊vcoord G Sf B (wclip m d B τ) i l / η⌋ : ℤ) : ℝ)| ≤ (Q : ℝ) := by
    rw [hsplit] at hfloor
    linarith
  exact_mod_cast hfin

/-! ### Узлы сетки: точки с `Gτ ∈ s·ℤ^K` -/

/-- `G` обратима: `G'G = Σ_f⁻¹` обратима. -/
lemma det_G_ne_zero (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) :
    (Matrix.of G).det ≠ 0 := by
  have hPmat : (Matrix.of P) * (Matrix.of Sf) = 1 := by
    ext j j'
    simpa [Matrix.mul_apply, Matrix.one_apply] using hPS j j'
  have hPdet : (Matrix.of P).det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hPmat
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact one_ne_zero this.symm
  have hGmat : (Matrix.of G).transpose * (Matrix.of G) = Matrix.of P := by
    ext j j'
    simpa [Matrix.mul_apply, Matrix.transpose_apply] using hG j j'
  intro h
  apply hPdet
  have := congrArg Matrix.det hGmat
  rw [Matrix.det_mul, Matrix.det_transpose, h, mul_zero] at this
  exact this.symm

/-- Узел с индексом `z ∈ ℤ^K` и шагом `s`: точка `τ` с `Gτ = s·z`. -/
noncomputable def nodeOf (G : κ → κ → ℝ) (s : ℝ) (z : κ → ℤ) : κ → ℝ :=
  Matrix.mulVec (Matrix.of G)⁻¹ (fun l => s * (z l : ℝ))

lemma dotp_G_nodeOf (hdet : (Matrix.of G).det ≠ 0) (s : ℝ) (z : κ → ℤ) (l : κ) :
    dotp (G l) (nodeOf G s z) = s * z l := by
  have hinv : Matrix.mulVec (Matrix.of G) (Matrix.mulVec (Matrix.of G)⁻¹ (fun l => s * (z l : ℝ)))
      = fun l => s * (z l : ℝ) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have h2 := congrFun hinv l
  simpa [Matrix.mulVec, dotProduct, dotp, nodeOf] using h2

/-- **Узел рядом с любой точкой.** Для `s > 0` и любой `t₀` есть узел `τ` с
`(τ − t₀)'Σ_f⁻¹(τ − t₀) ≤ K·(s/2)²` и `|z_l| ≤ |(Gt₀)_l|/s + 1/2`. -/
lemma exists_node_near (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hdet : (Matrix.of G).det ≠ 0) {s : ℝ} (hs : 0 < s) (t₀ : κ → ℝ) :
    ∃ z : κ → ℤ, (∀ l, |(z l : ℝ)| ≤ |dotp (G l) t₀| / s + 1 / 2) ∧
      quadf P (nodeOf G s z - t₀) ≤ (Fintype.card κ : ℝ) * (s / 2) ^ 2 := by
  obtain ⟨z, hz1, hz2⟩ := exists_grid_point s hs (fun l => dotp (G l) t₀)
  refine ⟨z, hz2, ?_⟩
  rw [quadf_eq_sum_sq hG]
  calc ∑ l, dotp (G l) (nodeOf G s z - t₀) ^ 2
      ≤ ∑ _l : κ, (s / 2) ^ 2 := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [dotp_sub', dotp_G_nodeOf hdet]
        exact sq_le_sq' (by linarith [(abs_le.mp (hz1 l)).1]) (by linarith [(abs_le.mp (hz1 l)).2])
    _ = (Fintype.card κ : ℝ) * (s / 2) ^ 2 := by simp

/-! ### Параметры схемы и семейство кандидатов -/

/-- Ширина корзины ключа: `η = √(εV/2)/(k√K)`. -/
noncomputable def clipEta (ε V : ℝ) (k K : ℕ) : ℝ :=
  Real.sqrt (ε * V / 2) / (k * Real.sqrt K)

/-- Шаг сетки в координатах `G`: `s = √(2εV)/((1+kω)√K)`. -/
noncomputable def clipStep (ε V ω : ℝ) (k K : ℕ) : ℝ :=
  Real.sqrt (2 * ε * V) / ((1 + k * ω) * Real.sqrt K)

/-- Радиус коробки ключей: `Q = k + ⌈√(5 ω k³ K/ε)⌉`. -/
noncomputable def clipQ (ε ω : ℝ) (k K : ℕ) : ℕ :=
  k + ⌈Real.sqrt (5 * ω * (k : ℝ) ^ 3 * K / ε)⌉₊

/-- Радиус сетки узлов (в индексах): `Z = ⌈(1+kω)√(K/ε) + 1/2⌉`. -/
noncomputable def clipZ (ε ω : ℝ) (k K : ℕ) : ℕ :=
  ⌈(1 + k * ω) * Real.sqrt (K / ε) + 1 / 2⌉₊

/-- **Семейство кандидатов при одной догадке `V`:** объединение таблиц по узлам сетки
`|z_l| ≤ Z`. -/
noncomputable def clipFamily (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf G : κ → κ → ℝ) (ε ω V : ℝ)
    (k : ℕ) (L : List ι) : Finset (Finset ι) :=
  (Fintype.piFinset fun _ : κ =>
      Finset.Icc (-(clipZ ε ω k (Fintype.card κ) : ℤ)) (clipZ ε ω k (Fintype.card κ))).biUnion
    (fun z => clipTable m d B Sf G (clipEta ε V k (Fintype.card κ))
      (clipQ ε ω k (Fintype.card κ)) k L (nodeOf G (clipStep ε V ω k (Fintype.card κ)) z))

/-- **Размер семейства не зависит от `M`:** не больше `(2Z+1)^K·((2Q+1)^K(k+1)+1)`. -/
theorem card_clipFamily_le (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf G : κ → κ → ℝ) (ε ω V : ℝ)
    (k : ℕ) (L : List ι) :
    (clipFamily m d B Sf G ε ω V k L).card
      ≤ (2 * clipZ ε ω k (Fintype.card κ) + 1) ^ Fintype.card κ
        * ((2 * clipQ ε ω k (Fintype.card κ) + 1) ^ Fintype.card κ * (k + 1) + 1) := by
  refine le_trans Finset.card_biUnion_le ?_
  have hnodes : (Fintype.piFinset fun _ : κ =>
      Finset.Icc (-(clipZ ε ω k (Fintype.card κ) : ℤ)) (clipZ ε ω k (Fintype.card κ))).card
      = (2 * clipZ ε ω k (Fintype.card κ) + 1) ^ Fintype.card κ := by
    rw [Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ]
    congr 1
    omega
  rw [← hnodes, ← smul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun z _ => ?_
  exact card_clipTable_le _ _ _ _ _ _ _ _ _ _

/-- Всё в таблице имеет не больше `k` активов. -/
theorem card_le_of_mem_clipTable (m d : ι → ℝ) (B : ι → κ → ℝ) (Sf G : κ → κ → ℝ) (η : ℝ)
    (Q k : ℕ) (L : List ι) (τ : κ → ℝ) {R : Finset ι}
    (hR : R ∈ clipTable m d B Sf G η Q k L τ) : R.card ≤ k := by
  rcases knap_key_mem _ _ _ L R hR with h | h
  · simp [h]
  · rw [clipBox, Finset.mem_product, Finset.mem_range] at h
    have h2 := h.2
    rw [sum_clipKeyItem_snd] at h2
    omega

/-! ### Арифметика параметров (чисто вещественные леммы) -/

lemma arith_defect {D a q ν νS ε V : ℝ} (hν1 : 1 ≤ ν) (hνSle : νS ≤ ν) (hνS0 : 0 ≤ νS)
    (hq0 : 0 ≤ q) (ha0 : 0 ≤ a) (hdef : D ≤ νS * a) (ha : a ≤ ν * q)
    (hq' : ν ^ 2 * q ≤ ε * V / 2) : D ≤ ε * V / 2 := by
  have h1 : νS * a ≤ ν * a := mul_le_mul_of_nonneg_right hνSle ha0
  have h2 : ν * a ≤ ν * (ν * q) := mul_le_mul_of_nonneg_left ha (by linarith)
  have h3 : ν * (ν * q) = ν ^ 2 * q := by ring
  linarith

lemma arith_score {a q ν ε V F Sig Qt : ℝ} (hν1 : 1 ≤ ν) (hq0 : 0 ≤ q) (ha : a ≤ ν * q)
    (hq' : ν ^ 2 * q ≤ ε * V / 2) (hε2 : ε ≤ 1 / 2) (hV : 0 < V) (hFV : F ≤ 2 * V)
    (hQt : Qt ≤ F + a) (hSig : Sig ≤ Qt) : Sig ≤ 9 * V / 4 := by
  have h1 : ν * q ≤ ν ^ 2 * q := by
    have : 0 ≤ q * (ν * ν - ν) := mul_nonneg hq0 (by nlinarith)
    nlinarith
  have h2 : ε * V / 2 ≤ V / 4 := by nlinarith
  linarith

lemma arith_final {F V ε DS e objS objR : ℝ} (hε : 0 < ε) (hV : 0 < V) (hVF : V ≤ F)
    (he0 : 0 ≤ e) (hDS0 : 0 ≤ DS) (hD : DS ≤ ε * V / 2) (he : e ≤ Real.sqrt (ε * V / 2))
    (hobjS : F - DS ≤ objS)
    (hobjR : objS - (2 * e * Real.sqrt DS + e ^ 2) ≤ objR) : (1 - 2 * ε) * F ≤ objR := by
  have hV0 : 0 ≤ ε * V / 2 := by positivity
  have hsD : Real.sqrt DS ≤ Real.sqrt (ε * V / 2) := Real.sqrt_le_sqrt hD
  have hsq : Real.sqrt (ε * V / 2) ^ 2 = ε * V / 2 := Real.sq_sqrt hV0
  have hDsq : Real.sqrt DS ^ 2 = DS := Real.sq_sqrt hDS0
  have hsum : Real.sqrt DS + e ≤ 2 * Real.sqrt (ε * V / 2) := by linarith
  have h2 := pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) he0) hsum 2
  have hexp : (Real.sqrt DS + e) ^ 2 = DS + (2 * e * Real.sqrt DS + e ^ 2) := by
    rw [add_sq, hDsq]; ring
  have h4 : (2 * Real.sqrt (ε * V / 2)) ^ 2 = 2 * ε * V := by
    rw [mul_pow, hsq]; ring
  have h5 : ε * V ≤ ε * F := mul_le_mul_of_nonneg_left hVF hε.le
  linarith

/-! ### Одна догадка: гарантия `1 − 2ε` -/

/-- **Одна догадка, одно семейство (Теорема 3.3 ТЗ с исправленным шагом сетки).**
Пусть `S` — носитель с `|S| ≤ k`, `t₀` — минимум `QLO(S,·)`, `F = QLO(S,t₀)` — его значение,
`V ≤ F ≤ 2V`, `ε ∈ (0,1/2]`, `B_i'Σ_fB_i ≤ ω d_i` для всех активов. Тогда в семействе
`clipFamily` есть набор `R` с `|R| ≤ k` и портфель `w ≥ 0` с `objLO(R,w) ≥ (1−2ε)F`. -/
theorem clip_one_guess [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {ω : ℝ} (hω : 0 ≤ ω) (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    {S : Finset ι} (hSk : S.card ≤ k) {t₀ : κ → ℝ}
    (hmin : ∀ t, QLO m d B P S t₀ ≤ QLO m d B P S t)
    {V : ℝ} (hV : 0 < V) (hVF : V ≤ QLO m d B P S t₀) (hFV : QLO m d B P S t₀ ≤ 2 * V)
    {L : List ι} (hnd : L.Nodup) (hL : ∀ i, i ∈ L) :
    ∃ R ∈ clipFamily m d B Sf G ε ω V k L, R.card ≤ k ∧
      ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (1 - 2 * ε) * QLO m d B P S t₀ ≤ objLO m d B Sf R w := by
  classical
  set Kn := Fintype.card κ with hKn
  have hKpos : 0 < (Kn : ℝ) := by exact_mod_cast Fintype.card_pos
  set sK := Real.sqrt (Kn : ℝ) with hsK
  have hsKpos : 0 < sK := Real.sqrt_pos.mpr hKpos
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set ν : ℝ := 1 + k * ω with hν
  have hν1 : 1 ≤ ν := by nlinarith [mul_nonneg hkpos.le hω]
  have hνpos : 0 < ν := by linarith
  set F := QLO m d B P S t₀ with hF
  -- параметры
  set s := clipStep ε V ω k Kn with hs
  have hspos : 0 < s :=
    div_pos (Real.sqrt_pos.mpr (by positivity)) (mul_pos hνpos hsKpos)
  set η := clipEta ε V k Kn with hηdef
  have hηpos : 0 < η :=
    div_pos (Real.sqrt_pos.mpr (by positivity)) (mul_pos hkpos hsKpos)
  have hs2 : s ^ 2 = 2 * ε * V / (ν ^ 2 * Kn) := by
    rw [hs, clipStep, div_pow, Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt hKpos.le]
  have hη2 : η ^ 2 = (ε * V / 2) / ((k : ℝ) ^ 2 * Kn) := by
    rw [hηdef, clipEta, div_pow, Real.sq_sqrt (by positivity), mul_pow,
      Real.sq_sqrt hKpos.le]
  -- узел
  have hdet := det_G_ne_zero hG hPS
  obtain ⟨z, hz, hq⟩ := exists_node_near hG hdet hspos t₀
  set τ := nodeOf G s z with hτ
  set q := quadf P (τ - t₀) with hqdef
  have hq0 : 0 ≤ q := quadf_nonneg_of_root hG _
  have hq' : ν ^ 2 * q ≤ ε * V / 2 := by
    have h1 : ν ^ 2 * ((Kn : ℝ) * (s / 2) ^ 2) = ε * V / 2 := by
      rw [div_pow, hs2]; field_simp
    have h2 : ν ^ 2 * q ≤ ν ^ 2 * ((Kn : ℝ) * (s / 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hq (sq_nonneg ν)
    linarith
  -- плечо носителя
  have hlev : levSum d B Sf S ≤ k * ω := by
    calc levSum d B Sf S = ∑ i ∈ S, sysVar B Sf i / d i := rfl
      _ ≤ ∑ i ∈ S, ω := Finset.sum_le_sum fun i _ => hsys i
      _ = S.card * ω := by simp
      _ ≤ k * ω := mul_le_mul_of_nonneg_right (by exact_mod_cast hSk) hω
  have hlev0 := levSum_nonneg (B := B) hd hG hPS S
  set νS := 1 + levSum d B Sf S with hνS
  have hνSle : νS ≤ ν := by linarith
  -- оценки в узле
  have hgap := QLO_sub_le_of_min (m := m) (B := B) (Sf := Sf) hd hG hPS hmin τ
  have hdef := defect_le (m := m) (B := B) (Sf := Sf) hd hG hPS S hmin τ
  have hQτ : F ≤ QLO m d B P S τ := hmin τ
  have ha : QLO m d B P S τ - F ≤ ν * q :=
    le_trans hgap (mul_le_mul_of_nonneg_right hνSle hq0)
  have hD : quadf P (tw Sf B S (wclip m d B τ) - τ) ≤ ε * V / 2 :=
    arith_defect hν1 hνSle (by linarith) hq0 (sub_nonneg.mpr hQτ) hdef ha hq'
  set DS := quadf P (tw Sf B S (wclip m d B τ) - τ) with hDSdef
  have hDS0 : 0 ≤ DS := defect_nonneg hG S _ τ
  -- коробка
  have hscore : ∑ i ∈ S, clipScore m d B τ i ≤ 9 * V / 4 := by
    have h0 : 0 ≤ quadf P τ := quadf_nonneg_of_root hG _
    have hQLO : QLO m d B P S τ = quadf P τ + ∑ i ∈ S, clipScore m d B τ i := rfl
    exact arith_score hν1 hq0 ha hq' hε2 hV hFV (by linarith) (by linarith)
  set Q := clipQ ε ω k Kn with hQdef
  have hXle : Real.sqrt (5 * ω * (k : ℝ) ^ 3 * Kn / ε) ≤ (Q : ℝ) - k := by
    rw [hQdef, clipQ]; push_cast; simp only [add_sub_cancel_left]
    exact Nat.le_ceil _
  have hQk : (k : ℝ) ≤ Q := by
    have := Real.sqrt_nonneg (5 * ω * (k : ℝ) ^ 3 * Kn / ε); linarith
  have hQ2 : ω * k * (9 * V / 4) ≤ (((Q : ℝ) - k) * η) ^ 2 := by
    have hX0 := Real.sqrt_nonneg (5 * ω * (k : ℝ) ^ 3 * Kn / ε)
    have hXsq : Real.sqrt (5 * ω * (k : ℝ) ^ 3 * Kn / ε) ^ 2 = 5 * ω * (k : ℝ) ^ 3 * Kn / ε :=
      Real.sq_sqrt (by positivity)
    have h1 : (5 / 2) * ω * k * V
        = Real.sqrt (5 * ω * (k : ℝ) ^ 3 * Kn / ε) ^ 2 * η ^ 2 := by
      rw [hXsq, hη2]; field_simp
    have h2 : Real.sqrt (5 * ω * (k : ℝ) ^ 3 * Kn / ε) * η ≤ ((Q : ℝ) - k) * η :=
      mul_le_mul_of_nonneg_right hXle hηpos.le
    have h3 : (Real.sqrt (5 * ω * (k : ℝ) ^ 3 * Kn / ε) * η) ^ 2 ≤ (((Q : ℝ) - k) * η) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hX0 hηpos.le) h2 2
    have h4 : ω * k * V ≥ 0 := by positivity
    have h5 : (Real.sqrt (5 * ω * (k : ℝ) ^ 3 * Kn / ε) * η) ^ 2 = (5 / 2) * ω * k * V := by
      rw [mul_pow]; exact h1.symm
    linarith [h3, h5, h4]
  have hbox := clip_box_bound (m := m) hd hG hPS hηpos hSk hω (fun i _ => hsys i) hscore hQk hQ2
  obtain ⟨R, hR, hRcard, hRobj⟩ := clip_node_step (m := m) (Q := Q) hd hG hPS hηpos hSk hbox hnd hL
  -- итог
  have he : Real.sqrt (Kn : ℝ) * (S.card * η) ≤ Real.sqrt (ε * V / 2) := by
    have h1 : Real.sqrt (Kn : ℝ) * (k * η) = Real.sqrt (ε * V / 2) := by
      rw [hηdef, clipEta, ← hsK]; field_simp
    calc Real.sqrt (Kn : ℝ) * (S.card * η) ≤ Real.sqrt (Kn : ℝ) * (k * η) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by exact_mod_cast hSk)
            hηpos.le) (Real.sqrt_nonneg _)
      _ = _ := h1
  set e := Real.sqrt (Kn : ℝ) * (S.card * η) with hedef
  have he0 : 0 ≤ e := mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hηpos.le)
  have hobjS : F - DS ≤ objLO m d B Sf S (wclip m d B τ) := by
    rw [objLO_wclip_deficit hd hG hPS S τ]; linarith
  have hfinal : (1 - 2 * ε) * F ≤ objLO m d B Sf R (wclip m d B τ) :=
    arith_final hε hV hVF he0 hDS0 hD he hobjS hRobj
  -- узел лежит в сетке
  have hzbox : ∀ l, z l ∈ Finset.Icc (-(clipZ ε ω k Kn : ℤ)) (clipZ ε ω k Kn) := by
    intro l
    rw [Finset.mem_Icc, ← abs_le]
    have hG0 : dotp (G l) t₀ ^ 2 ≤ 2 * V := by
      have h1 : dotp (G l) t₀ ^ 2 ≤ quadf P t₀ := by
        rw [quadf_eq_sum_sq hG]
        exact Finset.single_le_sum (f := fun l => dotp (G l) t₀ ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ l)
      have h2 : quadf P t₀ ≤ F := by
        have : F = quadf P t₀ + ∑ i ∈ S, max (m i - dotp (B i) t₀) 0 ^ 2 / d i := rfl
        have : 0 ≤ ∑ i ∈ S, max (m i - dotp (B i) t₀) 0 ^ 2 / d i :=
          Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hd i).le
        linarith
      linarith
    have hGabs : |dotp (G l) t₀| ≤ Real.sqrt (2 * V) := Real.abs_le_sqrt hG0
    have hzl := hz l
    have hdivle : |dotp (G l) t₀| / s ≤ Real.sqrt (2 * V) / s :=
      div_le_div_of_nonneg_right hGabs hspos.le
    have hkey : Real.sqrt (2 * V) / s = ν * Real.sqrt ((Kn : ℝ) / ε) := by
      rw [hs, clipStep, Real.sqrt_div hKpos.le, ← hsK]
      have h2 : Real.sqrt (2 * ε * V) = Real.sqrt (2 * V) * Real.sqrt ε := by
        rw [show 2 * ε * V = 2 * V * ε by ring, Real.sqrt_mul (by positivity)]
      rw [h2]
      have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
      have hs2V : 0 < Real.sqrt (2 * V) := Real.sqrt_pos.mpr (by positivity)
      field_simp
      rfl
    have hceil : ν * Real.sqrt ((Kn : ℝ) / ε) + 1 / 2 ≤ (clipZ ε ω k Kn : ℝ) := by
      rw [clipZ]; exact Nat.le_ceil _
    have hreal : |(z l : ℝ)| ≤ (clipZ ε ω k Kn : ℝ) := by
      rw [hkey] at hdivle; linarith
    exact_mod_cast hreal
  refine ⟨R, ?_, by omega, wclip m d B τ, fun i => wclip_nonneg hd τ i, hfinal⟩
  rw [clipFamily, Finset.mem_biUnion]
  exact ⟨z, Fintype.mem_piFinset.mpr hzbox, hR⟩

end SparseSharpe.Factor
