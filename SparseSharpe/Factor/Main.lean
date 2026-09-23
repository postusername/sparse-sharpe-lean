import SparseSharpe.Factor.DPBox

set_option linter.style.header false

/-!
# Главная теорема: динамика с коробкой, гарантия и стоимость одного прогона

Сквозные утверждения для `survivorsBox` (`Factor/DPBox.lean`) — динамики, которая
отбрасывает наборы с ключом вне канонической коробки `boxOf`. Для неё размер таблицы
ограничен **при любом прогоне** (`survivorsBox_card_le`), а гарантия та же, что у
`survivors`:

* `lo_fptas_step_box`, `lo_fptas_block_box` — как `lo_fptas_step_block` и
  `lo_fptas_block_clamp`, с коробкой;
* `main_theorem`, `main_theorem_anchor` — одна теорема «из входа»: данные
  `m, d, B, Σ_f`, точность `ε`, кардинальность `k`, граница `ω` плеч активов и любая
  догадка `V` с `V ≤ OPT(S) ≤ 2V` для носителя `S`, `|S| ≤ k`; всё остальное (самосогласованный
  носитель, нормальная точка, `K`-ка, параметры) выводится. Вывод: узел сетки с явной
  границей номеров, в котором динамика с коробкой возвращает носитель не длиннее `S` и
  портфель `w ≥ 0` с `2m'w − w'Vw ≥ (1−2ε)·OPT(S)`, а таблица не больше явной границы.
-/

namespace SparseSharpe.Factor

open Finset

set_option linter.unusedSectionVars false

section RowLevel

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {T : κ → ι} {t : κ → ℝ}

/-- Шаг `δ`-цепочки для динамики с коробкой (как `lo_fptas_step_block`). -/
theorem lo_fptas_step_box {S A base : Finset ι} {cl : ι → Bool} {thA : κ → ℝ}
    {η ξ ε θ₀ c : ℝ} {k : ℕ} {L : List ι}
    (hdet : (rowMat a T).det ≠ 0) (hTA : ∀ l, T l ∈ A)
    (hη : 0 < η) (hξ : 0 < ξ) (hθ₀ : 0 ≤ θ₀) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (adm : ι → Bool) (box : Finset ((κ → ℤ) × (κ → κ → ℤ) × ℕ))
    (hnd : L.Nodup) (hdisj : ∀ i ∈ L, i ∉ base)
    (hbA : base ⊆ A) (hAL : A ⊆ base ∪ L.toFinset)
    (hadmA : ∀ i ∈ A, i ∉ base → adm i)
    (hnormA : IsNormal a y A thA)
    (hbaseS : base ⊆ S) (hLS : ∀ i ∈ L.toFinset, i ∈ S)
    (hbaseAnch : ∀ i ∈ base, ¬ cl i)
    (hcov : AnchorCover a y cl S base k c) (hk : A.card ≤ base.card + k)
    (hadmFilter : ∀ i, adm i → -θ₀ ≤ y i - dotp (a i) t)
    {Tb : κ → ι} (hTb : ∀ l, Tb l ∈ base) (hdetBase : (rowMat a Tb).det ≠ 0)
    (hζ2 : 2 * (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ)) < 1)
    (hgap : (phi a y A t - phi a y A thA)
      + bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
        (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
        (phi a y A t - phi a y A thA) ≤ θ₀ ^ 2)
    (hErr : bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
      (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
      (phi a y A t - phi a y A thA) ≤ ε * phi a y A thA)
    (hcalA : c * (2 * θ₀) ^ 2
      ≤ ε * (phi a y A thA
        - bucketErr (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
          (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ))
          (phi a y A t - phi a y A thA)))
    (hbox : ∀ U' ⊆ A, ∀ V : Finset ι, KeyClose a y T t η ξ (L.length : ℝ) V U' →
      keyOf a y T t η ξ V ∈ box) :
    ∃ R ∈ survivorsBox (fun V => phi a y V t) (keyOf a y T t η ξ) adm box base L,
      R.card = A.card ∧
      ∀ t' : κ → ℝ, (1 - 2 * ε) * phi a y A thA ≤ psiC a y cl R t' := by
  obtain ⟨R, hR, hclose, hQ⟩ :=
    survivorsBox_spec (a := a) (y := y) (T := T) (t := t) hη hξ adm box base L hnd hdisj A
      hbA hAL hadmA hbox
  obtain ⟨hbaseR, hRsub, hRadm⟩ := survivorsBox_mem _ _ adm box base L R hR
  obtain ⟨thR, hnormR⟩ :=
    exists_isNormal_of_det (a := a) (V := R) (fun l => hbaseR (hTb l)) hdetBase y
  have hRS : R ⊆ S := by
    intro x hx
    rcases Finset.mem_union.mp (hRsub hx) with hb | hl
    · exact hbaseS hb
    · exact hLS x hl
  have hb : ApproxBucket a y A R t
      (Real.sqrt (Fintype.card κ : ℝ) * ((L.length : ℝ) * η))
      (((L.length : ℝ) * ξ) * (Fintype.card κ : ℝ)) :=
    hclose.toApproxBucket hdet hTA hQ (by positivity) hη.le hξ.le
  have hfilterR : ∀ i ∈ R, cl i → -θ₀ ≤ y i - dotp (a i) t := by
    intro i hi hc
    by_cases hib : i ∈ base
    · exact absurd hc (by simpa using hbaseAnch i hib)
    · exact hadmFilter i (hRadm i hi hib)
  -- зажатых строк в `R` не больше `k`: `|R| = |A| ≤ |base| + k`
  have hkR : (clipSet cl R).card ≤ k := by
    have h1 := card_clipSet_le_of_base (cl := cl) hbaseR hbaseAnch
    have h2 : R.card = A.card := hclose.card
    omega
  -- калибровка для `R`: `c(2θ₀)² ≤ ε(F(Ā) − err) ≤ ε·F(R)`
  have hFR := phi_normal_ge_of_approxBucket' hb (by positivity) (by positivity)
    hζ2 hnormA hnormR
  have hcalR : c * (2 * θ₀) ^ 2 ≤ ε * phi a y R thR := by
    have := mul_le_mul_of_nonneg_left hFR hε.le
    linarith
  have hcovR : CoveredBy a y cl R (2 * θ₀) (ε * phi a y R thR) :=
    coveredBy_of_anchorCover hcov hbaseR hRS hbaseAnch hkR hcalR
  refine ⟨R, hR, hclose.card, fun t' => ?_⟩
  exact psiC_ge_of_approxBucket_calibrated_block hb hnormA hnormR (by positivity)
    (by positivity) hζ2 hθ₀ hε hε1 hfilterR hgap hcovR hErr t'

/-- **Сквозная гарантия для динамики с коробкой** (как `lo_fptas_block_clamp`). Коробка
каноническая: `boxOf κ ρ V η ξ N |L|`, где `ρ` — граница коэффициентов Крамера на
носителе `A`, `N ≥ |A|`. -/
theorem lo_fptas_block_box {S A base : Finset ι} {cl : ι → Bool} {thA : κ → ℝ}
    {η ξ ε V C c s ρ : ℝ} {k N : ℕ} {L : List ι}
    (hTA : ∀ l, T l ∈ A) (hdet : (rowMat a T).det ≠ 0)
    (hρ : 0 ≤ ρ) (hcf : ∀ i ∈ A, ∀ l, |cf a T i l| ≤ ρ) (hAN : A.card ≤ N)
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
          adm = (fun i => decide (-theta0B ε V c ≤ y i - dotp (a i) t)) ∧
          (∀ i, adm i → -theta0B ε V c ≤ y i - dotp (a i) t) ∧
          (∀ i ∈ A, i ∉ base → adm i) ∧
          ∃ R ∈ survivorsBox (fun W => phi a y W t) (keyOf a y T t η ξ) adm
              (boxOf κ ρ V η ξ N L.length) base L,
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
  refine ⟨fun i => decide (-theta0B ε V c ≤ y i - dotp (a i) t), rfl, ?_, hadmA, ?_⟩
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
    -- коробка: `φ_Ā(τ) ≤ 4V`, так как зазор узла `≤ θ₀²/2 = εV/(16c) ≤ V`
    have hQ4 : phi a y A t ≤ 4 * V := by
      have h1 : theta0B ε V c ^ 2 / 2 ≤ V := by
        rw [hθsq]
        rw [div_div, div_le_iff₀ (by positivity)]
        nlinarith [mul_pos hε hV]
      linarith
    have hbox : ∀ U' ⊆ A, ∀ V' : Finset ι, KeyClose a y T t η ξ (L.length : ℝ) V' U' →
        keyOf a y T t η ξ V' ∈ boxOf κ ρ V η ξ N L.length :=
      fun U' hU' V' hV' => keyOf_mem_boxOf hρ hcf hAN hQ4 hη hξ le_rfl hU' hV'
    exact lo_fptas_step_box hdet hTA hη hξ hθ0 hε (by linarith)
      _ _ hnd hdisj hbA hAL hadmA hnormA hbaseS hLS hbaseAnch hcov hk
      (fun i hi => of_decide_eq_true hi) hTb hdetBase (by linarith) hgapT hr2 hcalA hbox

/-! ### Явная граница коробки -/

lemma toNat_two_ceil_mono {x x' : ℝ} (h : x ≤ x') :
    (2 * ⌈x⌉ + 1).toNat ≤ (2 * ⌈x'⌉ + 1).toNat := by
  have := Int.ceil_mono h
  exact Int.toNat_le_toNat (by omega)

/-- **Размер канонической коробки через входные величины.** При
`η = θ₀/(8√K·M)`, `θ₀ = √(εV/(8c))`, `ξ = 1/(8MK)`, `|L| = M`:

    |boxOf| ≤ (2⌈ρ·48M√K·√(Nc/ε) + M⌉ + 1)^K · (2⌈8NMKρ² + M⌉ + 1)^{K²} · (N + 1).

`V` сокращается; данных входа, кроме `c` (и `ρ`), нет. -/
theorem card_boxOf_le {ε c V η ξ ρ : ℝ} {N Mn : ℕ}
    (hε : 0 < ε) (hc : 0 < c) (hV : 0 < V) (hN : 0 < N) (hM : 0 < Mn)
    (hKc : 0 < Fintype.card κ) (hρ : 0 ≤ ρ)
    (hηdef : η = theta0B ε V c / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Mn : ℝ)))
    (hξdef : ξ = 1 / (8 * (Mn : ℝ) * (Fintype.card κ : ℝ))) :
    (boxOf κ ρ V η ξ N Mn).card
      ≤ (2 * ⌈ρ * (48 * (Mn : ℝ) * Real.sqrt (Fintype.card κ : ℝ)
            * Real.sqrt ((N : ℝ) * c / ε)) + (Mn : ℝ)⌉ + 1).toNat ^ Fintype.card κ
        * ((2 * ⌈8 * (N : ℝ) * (Mn : ℝ) * (Fintype.card κ : ℝ) * ρ ^ 2 + (Mn : ℝ)⌉ + 1).toNat
            ^ (Fintype.card κ * Fintype.card κ) * (N + 1)) := by
  have hM0 : (0:ℝ) < (Mn : ℝ) := by exact_mod_cast hM
  have hK0 : (0:ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast hKc
  have hηpos : 0 < η := by
    rw [hηdef]
    have : 0 < theta0B ε V c := Real.sqrt_pos.mpr (by positivity)
    have : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr hK0
    positivity
  have hξpos : 0 < ξ := by rw [hξdef]; positivity
  rw [card_boxOf hρ hηpos hξpos]
  have hD := momRange_over_eta_le_block (Sc := N) (Mn := Mn) (Kc := Fintype.card κ)
    (Q := 4 * V) hε hc hV hN hKc hM hηdef (by positivity) le_rfl le_rfl
  have h1 : (ρ * Real.sqrt ((N : ℝ) * (4 * V)) + (Mn : ℝ) * η) / η
      ≤ ρ * (48 * (Mn : ℝ) * Real.sqrt (Fintype.card κ : ℝ)
            * Real.sqrt ((N : ℝ) * c / ε)) + (Mn : ℝ) := by
    rw [add_div, mul_div_assoc, mul_div_assoc, div_self hηpos.ne', mul_one]
    have := mul_le_mul_of_nonneg_left hD hρ
    linarith
  have h2 : ((N : ℝ) * ρ ^ 2 + (Mn : ℝ) * ξ) / ξ
      = 8 * (N : ℝ) * (Mn : ℝ) * (Fintype.card κ : ℝ) * ρ ^ 2 + (Mn : ℝ) := by
    rw [hξdef]; field_simp
  rw [h2]
  have hA := toNat_two_ceil_mono h1
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hA _)

end RowLevel

section Portfolio

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- **Портфельная форма для динамики с коробкой.** Как `lo_fptas_portfolio_block`, но
`K`-ка `T` — любая невырожденная внутри `Ā₀` с зажимом `gram ≤ C·gram_T` и
коэффициентами `|cf| ≤ ρ` на `Ā₀`; динамика — `survivorsBox` с канонической коробкой
при `N = k + K`. -/
theorem lo_fptas_portfolio_box [Nonempty κ]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {cand A₀ : Finset ι} {La : List ι} {T : κ → (ι ⊕ κ)} {thA : κ → ℝ}
    {η ξ ε V C c s ρ : ℝ} {k : ℕ}
    (hTA : ∀ l, T l ∈ barK (κ := κ) A₀)
    (hdet : (rowMat (rowsK d B G) T).det ≠ 0)
    (hclamp : ∀ v, gram (rowsK d B G) (barK (κ := κ) A₀) v ≤ C * gramK (rowsK d B G) T v)
    (hρ : 0 ≤ ρ) (hcf : ∀ x ∈ barK (κ := κ) A₀, ∀ l, |cf (rowsK d B G) T x l| ≤ ρ)
    (hnormA : IsNormal (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) thA)
    (hCpos : 0 < C)
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
      ∀ t : κ → ℝ, (∀ l, dotp (rowsK d B G (T l)) t
          = targetsK m d (T l) + s * (z l : ℝ)) →
        ∃ adm : (ι ⊕ κ) → Bool,
          adm = (fun x => decide (-theta0B ε V c
            ≤ targetsK m d x - dotp (rowsK d B G x) t)) ∧
          (∀ x, adm x → -theta0B ε V c
            ≤ targetsK m d x - dotp (rowsK d B G x) t) ∧
          (∀ x ∈ barK (κ := κ) A₀, x ∉ anchorRows ι κ → adm x) ∧
          ∃ R ∈ survivorsBox (fun W => phi (rowsK d B G) (targetsK m d) W t)
              (keyOf (rowsK d B G) (targetsK m d) T t η ξ) adm
              (boxOf κ ρ V η ξ (k + Fintype.card κ) La.length) (anchorRows ι κ)
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
  have hAN : (barK (κ := κ) A₀).card ≤ k + Fintype.card κ := by
    rw [card_barK]; omega
  obtain ⟨z, hz1, hz2⟩ := lo_fptas_block_box (a := a) (y := y) (cl := fun r => Sum.isLeft r)
    (S := barK (κ := κ) cand) (A := barK (κ := κ) A₀) (base := anchorRows ι κ)
    (T := T) (thA := thA) (η := η) (ξ := ξ) (ε := ε) (V := V) (C := C) (c := c) (s := s)
    (ρ := ρ) (k := k) (N := k + Fintype.card κ) (L := L) (Tb := fun l => (Sum.inr l : ι ⊕ κ))
    hTA hdet hρ hcf hAN hnormA hclamp hCpos hε hε1 hc hV hVF hFV hKc hs hselfA hη hξ
    hndL hdisj hbA hAL hAS hbaseS hLS hanchBase hbaseAnch hcov hk
    (fun l => inr_mem_anchorRows l)
    (det_anchor_ne_zero (d := d) (B := B) (P := P) (Sf := Sf) hG hPS)
    (by rwa [hL, List.length_map]) (by rwa [hL, List.length_map])
  refine ⟨z, hz1, fun t ht => ?_⟩
  obtain ⟨adm, hadmEq, hadm1, hadm2, R, hR, hcard, hval⟩ := hz2 t ht
  have hlenL : L.length = La.length := by rw [hL, List.length_map]
  rw [hlenL] at hR
  refine ⟨adm, hadmEq, hadm1, hadm2, R, hR, ?_, ?_⟩
  · have := card_assetsOf_eq (survivorsBox_mem _ _ adm _ _ L R hR).1 hbA hcard
    rwa [assetsOf_barK] at this
  · set R₀ := assetsOf (κ := κ) R with hR₀
    have hReq : R = barK (κ := κ) R₀ :=
      barK_assetsOf (survivorsBox_mem _ _ adm _ _ L R hR).1
    obtain ⟨zv, hleast, hgreat⟩ :=
      isGreatest_objLO_isLeast_QLO (Sf := Sf) (P := P) (G := G) hd hG hPS R₀
    obtain ⟨t₁, ht₁⟩ := hleast.1
    obtain ⟨w, hw, hwv⟩ := hgreat.1
    refine ⟨w, hw, ?_⟩
    rw [← hwv, ht₁, ← QLO_eq_psiC (P := P) hd hG]
    have := hval t₁
    rwa [hReq] at this

/-! ### Главная теорема «из входа» -/

/-- **Главная теорема (перебор `K`-ок).** Данные: `d > 0`, `G'G = Σ_f⁻¹`, `Σ_f⁻¹Σ_f = 1`,
`K ≥ 1`, точность `0 < ε ≤ 1/2`, кардинальность `k ≥ 1`, граница плеч
`B_i'Σ_fB_i/d_i ≤ ω` для всех активов. Для любого носителя `S`, `|S| ≤ k`, со значением
`OPT(S) = max{2m'u − u'Vu : u ≥ 0 на S}` и любой догадки `V` с `V ≤ OPT(S) ≤ 2V`
(такую даёт удваивающая сетка догадок) при параметрах

    c = k(1 + kω), N = k + K, C = NK, θ₀ = √(εV/(8c)), s = 2√((ε/(32c))·V/(K·C)),
    η = θ₀/(8√K·M), ξ = 1/(8MK), L = все активы,

существуют невырожденная `K`-ка `T` (так что точка узла существует —
`exists_point_with_residuals`) и узел `z` из коробки `(2⌈4K√(Nc/ε) + 1/2⌉ + 1)^K`, в
любой точке которого динамика с коробкой (`survivorsBox`) при фильтре
`adm = {x : r_x(τ) ≥ −θ₀}` (ровно этот фильтр) возвращает носитель `R`,
`|R| ≤ |S|`, и портфель `w ≥ 0` на нём с `2m'w − w'Vw ≥ (1 − 2ε)·(2m'u − u'Vu)` для всех
`u ≥ 0` на `S`. Размер таблицы динамики с коробкой — при **любой** `K`-ке, любом узле
и любом фильтре — не больше `(2⌈48M√K√(Nc/ε) + M⌉ + 1)^K·(2⌈8NMK + M⌉ + 1)^{K²}·(N + 1) + 1`.
Все `K`-ки перебираются (`(M+K)^K` вариантов), догадки `V` — удваивающей сеткой. -/
theorem main_theorem [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    {S : Finset ι} (hkS : S.card ≤ k) {Fopt V : ℝ}
    (hFopt : IsGreatest {v : ℝ | ∃ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i)
        ∧ v = objLO m d B Sf S u} Fopt)
    (hV : 0 < V) (hVF : V ≤ Fopt) (hFV : Fopt ≤ 2 * V) :
    (∃ T : κ → (ι ⊕ κ), (rowMat (rowsK d B G) T).det ≠ 0 ∧ ∃ z : κ → ℤ,
      z ∈ nodeBox (κ := κ) ⌈4 * (Fintype.card κ : ℝ)
        * Real.sqrt (((k + Fintype.card κ : ℕ) : ℝ) * ((k : ℝ) * (1 + (k : ℝ) * ω)) / ε)
          + 1 / 2⌉₊ ∧
      ∀ t : κ → ℝ, (∀ l, dotp (rowsK d B G (T l)) t = targetsK m d (T l)
          + 2 * Real.sqrt ((ε / (32 * ((k : ℝ) * (1 + (k : ℝ) * ω)))) * V
            / ((Fintype.card κ : ℝ) * (((k + Fintype.card κ : ℕ) : ℝ)
              * (Fintype.card κ : ℝ)))) * (z l : ℝ)) →
        ∃ adm : (ι ⊕ κ) → Bool,
          adm = (fun x => decide (-theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
            ≤ targetsK m d x - dotp (rowsK d B G x) t)) ∧
          ∃ R ∈ survivorsBox (fun W => phi (rowsK d B G) (targetsK m d) W t)
              (keyOf (rowsK d B G) (targetsK m d) T t
                (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
                  / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
                (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ))))
              adm
              (boxOf κ 1 V (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
                  / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
                (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ)))
                (k + Fintype.card κ) (Fintype.card ι))
              (anchorRows ι κ) ((Finset.univ : Finset ι).toList.map Sum.inl),
            (assetsOf (κ := κ) R).card ≤ S.card
            ∧ ∃ w : ι → ℝ, (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i)
              ∧ ∀ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i) →
                  (1 - 2 * ε) * objLO m d B Sf S u
                    ≤ objLO m d B Sf (assetsOf (κ := κ) R) w)
    ∧ ∀ (T : κ → (ι ⊕ κ)) (t : κ → ℝ) (adm : (ι ⊕ κ) → Bool),
      (survivorsBox (fun W => phi (rowsK d B G) (targetsK m d) W t)
          (keyOf (rowsK d B G) (targetsK m d) T t
            (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
              / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
            (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ))))
          adm
          (boxOf κ 1 V (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
              / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
            (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ)))
            (k + Fintype.card κ) (Fintype.card ι))
          (anchorRows ι κ) ((Finset.univ : Finset ι).toList.map Sum.inl)).card
      ≤ (2 * ⌈1 * (48 * (Fintype.card ι : ℝ) * Real.sqrt (Fintype.card κ : ℝ)
            * Real.sqrt (((k + Fintype.card κ : ℕ) : ℝ) * ((k : ℝ) * (1 + (k : ℝ) * ω)) / ε))
            + (Fintype.card ι : ℝ)⌉ + 1).toNat ^ Fintype.card κ
        * ((2 * ⌈8 * ((k + Fintype.card κ : ℕ) : ℝ) * (Fintype.card ι : ℝ)
            * (Fintype.card κ : ℝ) * 1 ^ 2 + (Fintype.card ι : ℝ)⌉ + 1).toNat
            ^ (Fintype.card κ * Fintype.card κ) * (k + Fintype.card κ + 1)) + 1 := by
  classical
  set c : ℝ := (k : ℝ) * (1 + (k : ℝ) * ω) with hcdef
  set N : ℕ := k + Fintype.card κ with hNdef
  set Mn : ℕ := Fintype.card ι with hMdef
  have hK0 : 0 < Fintype.card κ := Fintype.card_pos
  have hKc : (0:ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast hK0
  have hM0 : 0 < Mn := Fintype.card_pos
  have hN0 : 0 < N := by omega
  have hc1 : (1:ℝ) ≤ c := by
    have hk : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    rw [hcdef]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (k:ℝ)) hω]
  have hcpos : (0:ℝ) < c := by linarith
  refine ⟨?_, ?_⟩
  swap
  · intro T t adm
    have := card_boxOf_le (κ := κ) (ε := ε) (c := c) (V := V) (ρ := 1) (N := N) (Mn := Mn)
      hε hcpos hV hN0 hM0 hK0 zero_le_one rfl rfl
    exact le_trans (survivorsBox_card_le _ _ _ _ _ _) (by omega)
  -- носитель оптимума, нормальная точка, `K`-ка
  obtain ⟨A₀, hA₀S, th, hcardA, hnormA, hselfA, hoptA⟩ :=
    exists_optimal_selfconsistent (m := m) (B := B) (Sf := Sf) hd hG hPS S
  have hFeq : Fopt = phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) th :=
    hFopt.unique hoptA
  obtain ⟨T, hmax⟩ := exists_maxvol_barK (d := d) (B := B) (G := G) (S := A₀)
  have hdet := maxvol_det_ne_zero (P := P) (Sf := Sf) hmax hG hPS
  have hAN : (barK (κ := κ) A₀).card ≤ N := by
    rw [card_barK, hNdef]; have := le_trans hcardA hkS; omega
  have hC : ((barK (κ := κ) A₀).card * Fintype.card κ : ℝ) ≤ (N : ℝ) * (Fintype.card κ : ℝ) := by
    have : ((barK (κ := κ) A₀).card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hAN
    exact mul_le_mul_of_nonneg_right this hKc.le
  have hCpos : (0:ℝ) < (N : ℝ) * (Fintype.card κ : ℝ) := by
    have : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN0
    positivity
  set La : List ι := (Finset.univ : Finset ι).toList with hLa
  have hLalen : La.length = Mn := by rw [hLa, Finset.length_toList, Finset.card_univ]
  have hM0r : (0:ℝ) < (Mn : ℝ) := by exact_mod_cast hM0
  have hsK : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr hKc
  have hθpos : 0 < theta0B ε V c := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨z, hz1, hz2⟩ := lo_fptas_portfolio_box (m := m) (P := P) hd hG hPS
    (cand := Finset.univ) (A₀ := A₀) (La := La) (T := T) (thA := th)
    (η := theta0B ε V c / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Mn : ℝ)))
    (ξ := 1 / (8 * (Mn : ℝ) * (Fintype.card κ : ℝ))) (ε := ε) (V := V)
    (C := (N : ℝ) * (Fintype.card κ : ℝ)) (c := c) (ρ := 1) (k := k)
    (s := 2 * Real.sqrt ((ε / (32 * c)) * V / ((Fintype.card κ : ℝ)
      * ((N : ℝ) * (Fintype.card κ : ℝ)))))
    hmax.1 hdet (clamp_of_maxvol hmax hdet hC) zero_le_one
    (fun x hx l => abs_cf_le_one hmax hdet hx l) hnormA hCpos hε hε1 hc1 hV
    (by rw [← hFeq]; exact hVF) (by rw [← hFeq]; exact hFV) hKc rfl hselfA
    (by positivity) (by positivity) (Finset.nodup_toList _)
    (by intro i _; simp [hLa]) (fun i _ => Finset.mem_univ i)
    (anchorCover_of_sysVar (m := m) hd hG hPS hω (fun i _ => hsys i))
    (le_trans hcardA hkS) (Finset.subset_univ _)
    (by rw [hLalen]; field_simp; linarith)
    (by rw [hLalen]; field_simp; norm_num)
  refine ⟨T, hdet, z, mem_nodeBox_of_grid_block hε hcpos hN0 hK0 hCpos le_rfl hz1, fun t ht => ?_⟩
  obtain ⟨adm, hadmEq, _hadm1, _hadm2, R, hR, hcard, w, hw, hval⟩ := hz2 t ht
  rw [hLalen] at hR
  refine ⟨adm, hadmEq, R, hR, ?_, w, hw, fun u hu => ?_⟩
  · rw [hcard]; exact Finset.card_le_card hA₀S
  · have hub : objLO m d B Sf S u ≤ Fopt := hFopt.2 ⟨u, hu, rfl⟩
    have hcoef : (0:ℝ) ≤ 1 - 2 * ε := by linarith
    have := mul_le_mul_of_nonneg_left hub hcoef
    rw [hFeq] at this
    linarith

/-- Зажим в координатах якорей: `gram_Ā₀ ≤ (K + kω)·gram_anch`. -/
theorem clamp_anchor (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {A₀ : Finset ι} {k : ℕ} {ω C : ℝ} (hsys : ∀ i ∈ A₀, sysVar B Sf i / d i ≤ ω)
    (hω : 0 ≤ ω) (hkA : A₀.card ≤ k) (hC : (Fintype.card κ : ℝ) + (k : ℝ) * ω ≤ C)
    (v : κ → ℝ) :
    gram (rowsK d B G) (barK (κ := κ) A₀) v
      ≤ C * gramK (rowsK d B G) (fun l => (Sum.inr l : ι ⊕ κ)) v := by
  have hgK : gramK (rowsK d B G) (fun l => (Sum.inr l : ι ⊕ κ)) v
      = gram (rowsK d B G) (anchorRows ι κ) v := by
    rw [gram_anchorRows]; simp [gramK, rowsK, dotp]
  have hpt : ∀ x ∈ barK (κ := κ) A₀, ∀ v, (dotp (rowsK d B G x) v) ^ 2
      ≤ (Sum.elim (fun i => sysVar B Sf i / d i) (fun _ => (1:ℝ)) x)
        * gramK (rowsK d B G) (fun l => (Sum.inr l : ι ⊕ κ)) v := by
    intro x _ v
    have hgK' : gramK (rowsK d B G) (fun l => (Sum.inr l : ι ⊕ κ)) v
        = gram (rowsK d B G) (anchorRows ι κ) v := by
      rw [gram_anchorRows]; simp [gramK, rowsK, dotp]
    rcases x with i | l
    · rw [hgK']; exact sq_dotp_asset_le hd hG hPS i v
    · simp only [Sum.elim_inr, one_mul, gramK]
      exact Finset.single_le_sum
        (f := fun l' => (dotp (rowsK d B G (Sum.inr l')) v) ^ 2)
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

/-- **Главная теорема без перебора `K`-ок** (сетка и ключ в координатах якорей). Как
`main_theorem`, но `K`-ка одна — якорные строки `g_1, …, g_K`; зажим `C = K + kω`;
коробка — с `ρ = √max(1, ω)`. Якорная `K`-ка невырождена (`det_anchor_ne_zero`), так что
точка узла существует; фильтр — ровно `{x : r_x(τ) ≥ −θ₀}`. Узел — в коробке `(2⌈√(16K·C·c/ε) + 1/2⌉ + 1)^K`; таблица —
не больше `(2⌈ρ·48M√K√(Nc/ε) + M⌉ + 1)^K·(2⌈8NMKρ² + M⌉ + 1)^{K²}·(N + 1) + 1`. -/
theorem main_theorem_anchor [Nonempty κ] [Nonempty ι]
    (hd : ∀ i, 0 < d i) (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} (hk1 : 1 ≤ k) {ε ω : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) (hω : 0 ≤ ω)
    (hsys : ∀ i, sysVar B Sf i / d i ≤ ω)
    {S : Finset ι} (hkS : S.card ≤ k) {Fopt V : ℝ}
    (hFopt : IsGreatest {v : ℝ | ∃ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i)
        ∧ v = objLO m d B Sf S u} Fopt)
    (hV : 0 < V) (hVF : V ≤ Fopt) (hFV : Fopt ≤ 2 * V) :
    (∃ z : κ → ℤ,
      z ∈ nodeBox (κ := κ) ⌈Real.sqrt ((Fintype.card κ : ℝ)
          * ((Fintype.card κ : ℝ) + (k : ℝ) * ω)
          / (2 * (ε / (32 * ((k : ℝ) * (1 + (k : ℝ) * ω)))))) + 1 / 2⌉₊ ∧
      ∀ t : κ → ℝ, (∀ l, dotp (rowsK d B G (Sum.inr l)) t = targetsK m d (Sum.inr l)
          + 2 * Real.sqrt ((ε / (32 * ((k : ℝ) * (1 + (k : ℝ) * ω)))) * V
            / ((Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) + (k : ℝ) * ω))) * (z l : ℝ)) →
        ∃ adm : (ι ⊕ κ) → Bool,
          adm = (fun x => decide (-theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
            ≤ targetsK m d x - dotp (rowsK d B G x) t)) ∧
          ∃ R ∈ survivorsBox (fun W => phi (rowsK d B G) (targetsK m d) W t)
              (keyOf (rowsK d B G) (targetsK m d) (fun l => Sum.inr l) t
                (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
                  / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
                (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ))))
              adm
              (boxOf κ (Real.sqrt (max 1 ω)) V (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
                  / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
                (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ)))
                (k + Fintype.card κ) (Fintype.card ι))
              (anchorRows ι κ) ((Finset.univ : Finset ι).toList.map Sum.inl),
            (assetsOf (κ := κ) R).card ≤ S.card
            ∧ ∃ w : ι → ℝ, (∀ i ∈ assetsOf (κ := κ) R, 0 ≤ w i)
              ∧ ∀ u : ι → ℝ, (∀ i ∈ S, 0 ≤ u i) →
                  (1 - 2 * ε) * objLO m d B Sf S u
                    ≤ objLO m d B Sf (assetsOf (κ := κ) R) w)
    ∧ ∀ (t : κ → ℝ) (adm : (ι ⊕ κ) → Bool),
      (survivorsBox (fun W => phi (rowsK d B G) (targetsK m d) W t)
          (keyOf (rowsK d B G) (targetsK m d) (fun l => Sum.inr l) t
            (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
              / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
            (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ))))
          adm
          (boxOf κ (Real.sqrt (max 1 ω)) V (theta0B ε V ((k : ℝ) * (1 + (k : ℝ) * ω))
              / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card ι : ℝ)))
            (1 / (8 * (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ)))
            (k + Fintype.card κ) (Fintype.card ι))
          (anchorRows ι κ) ((Finset.univ : Finset ι).toList.map Sum.inl)).card
      ≤ (2 * ⌈Real.sqrt (max 1 ω) * (48 * (Fintype.card ι : ℝ) * Real.sqrt (Fintype.card κ : ℝ)
            * Real.sqrt (((k + Fintype.card κ : ℕ) : ℝ) * ((k : ℝ) * (1 + (k : ℝ) * ω)) / ε))
            + (Fintype.card ι : ℝ)⌉ + 1).toNat ^ Fintype.card κ
        * ((2 * ⌈8 * ((k + Fintype.card κ : ℕ) : ℝ) * (Fintype.card ι : ℝ)
            * (Fintype.card κ : ℝ) * Real.sqrt (max 1 ω) ^ 2 + (Fintype.card ι : ℝ)⌉ + 1).toNat
            ^ (Fintype.card κ * Fintype.card κ) * (k + Fintype.card κ + 1)) + 1 := by
  classical
  set c : ℝ := (k : ℝ) * (1 + (k : ℝ) * ω) with hcdef
  set N : ℕ := k + Fintype.card κ with hNdef
  set Mn : ℕ := Fintype.card ι with hMdef
  set Cn : ℝ := (Fintype.card κ : ℝ) + (k : ℝ) * ω with hCndef
  have hK0 : 0 < Fintype.card κ := Fintype.card_pos
  have hKc : (0:ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast hK0
  have hM0 : 0 < Mn := Fintype.card_pos
  have hN0 : 0 < N := by omega
  have hc1 : (1:ℝ) ≤ c := by
    have hk : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    rw [hcdef]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (k:ℝ)) hω]
  have hcpos : (0:ℝ) < c := by linarith
  have hρ : (0:ℝ) ≤ Real.sqrt (max 1 ω) := Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  swap
  · intro t adm
    have := card_boxOf_le (κ := κ) (ε := ε) (c := c) (V := V) (ρ := Real.sqrt (max 1 ω))
      (N := N) (Mn := Mn) hε hcpos hV hN0 hM0 hK0 hρ rfl rfl
    exact le_trans (survivorsBox_card_le _ _ _ _ _ _) (by omega)
  obtain ⟨A₀, hA₀S, th, hcardA, hnormA, hselfA, hoptA⟩ :=
    exists_optimal_selfconsistent (m := m) (B := B) (Sf := Sf) hd hG hPS S
  have hFeq : Fopt = phi (rowsK d B G) (targetsK m d) (barK (κ := κ) A₀) th :=
    hFopt.unique hoptA
  have hkA : A₀.card ≤ k := le_trans hcardA hkS
  have hCpos : (0:ℝ) < Cn := by
    have : (0:ℝ) ≤ (k : ℝ) * ω := mul_nonneg (by positivity) hω
    rw [hCndef]; linarith
  set La : List ι := (Finset.univ : Finset ι).toList with hLa
  have hLalen : La.length = Mn := by rw [hLa, Finset.length_toList, Finset.card_univ]
  have hM0r : (0:ℝ) < (Mn : ℝ) := by exact_mod_cast hM0
  have hsK : 0 < Real.sqrt (Fintype.card κ : ℝ) := Real.sqrt_pos.mpr hKc
  have hθpos : 0 < theta0B ε V c := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨z, hz1, hz2⟩ := lo_fptas_portfolio_box (m := m) (P := P) hd hG hPS
    (cand := Finset.univ) (A₀ := A₀) (La := La) (T := fun l => (Sum.inr l : ι ⊕ κ))
    (thA := th)
    (η := theta0B ε V c / (8 * Real.sqrt (Fintype.card κ : ℝ) * (Mn : ℝ)))
    (ξ := 1 / (8 * (Mn : ℝ) * (Fintype.card κ : ℝ))) (ε := ε) (V := V)
    (C := Cn) (c := c) (ρ := Real.sqrt (max 1 ω)) (k := k)
    (s := 2 * Real.sqrt ((ε / (32 * c)) * V / ((Fintype.card κ : ℝ) * Cn)))
    (fun l => inr_mem_barK A₀ l)
    (det_anchor_ne_zero (d := d) (B := B) (P := P) (Sf := Sf) hG hPS)
    (clamp_anchor hd hG hPS (fun i _ => hsys i) hω hkA le_rfl) hρ
    (fun x hx l => abs_cf_anchor_le hd hG hPS (fun i _ => hsys i) x hx l)
    hnormA hCpos hε hε1 hc1 hV
    (by rw [← hFeq]; exact hVF) (by rw [← hFeq]; exact hFV) hKc rfl hselfA
    (by positivity) (by positivity) (Finset.nodup_toList _)
    (by intro i _; simp [hLa]) (fun i _ => Finset.mem_univ i)
    (anchorCover_of_sysVar (m := m) hd hG hPS hω (fun i _ => hsys i))
    hkA (Finset.subset_univ _)
    (by rw [hLalen]; field_simp; linarith)
    (by rw [hLalen]; field_simp; norm_num)
  refine ⟨z, mem_nodeBox_of_abs_le fun l => le_trans (hz1 l) (Nat.le_ceil _), fun t ht => ?_⟩
  obtain ⟨adm, hadmEq, _hadm1, _hadm2, R, hR, hcard, w, hw, hval⟩ := hz2 t ht
  rw [hLalen] at hR
  refine ⟨adm, hadmEq, R, hR, ?_, w, hw, fun u hu => ?_⟩
  · rw [hcard]; exact Finset.card_le_card hA₀S
  · have hub : objLO m d B Sf S u ≤ Fopt := hFopt.2 ⟨u, hu, rfl⟩
    have hcoef : (0:ℝ) ≤ 1 - 2 * ε := by linarith
    have := mul_le_mul_of_nonneg_left hub hcoef
    rw [hFeq] at this
    linarith

end Portfolio

end SparseSharpe.Factor
