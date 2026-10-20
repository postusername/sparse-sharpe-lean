import SparseSharpe.Factor.Practical
import SparseSharpe.Factor.Landscape
import SparseSharpe.Factor.ClippedNode

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Релаксация и её зазор (задачи L3, L4 ТЗ, сессия 23)

Двойственная граница `g_k(t) = t'Σ_f⁻¹t + max_{|S|≤k} Σ_{i∈S} s_i(t)` (`dualBound`) и её
минимум `G*_k = min_t g_k(t) ≥ OPT_LO(k)`.

* `dualBound_le_two_opt_nonneg` (Теорема 2.2(a) ТЗ) — при `K = 1` и `β ≥ 0` в **одной** точке
  `tS = σ_f√OPT_LO(k)` выполнено `g_k(tS) ≤ 2·OPT_LO(k)`. Гипотез о `M`, `k`, `m` нет.
* `dualBound_le_QLO_of_threshold` — поточечная форма H1(c): если `T` содержит все активы со
  счётом выше порога `σ`, не содержит активов со счётом выше `σ` вне себя и `|T| ≥ k`, то
  `g_k(t) ≤ QLO(T,t)` (без теоремы Сиона, без существования `t*`).
* `bicriteria_certificate` — проверяемый сертификат бикритериальной гарантии: если в точке `t*`
  есть вес `λ ∈ [0,1]^T` с `Σλ = k`, ККТ-стационарностью `Σ_f⁻¹t* = Σ_T λ_i w_i(t*) B_i`
  и `Σ_T λ_i s_i(t*) = верхняя сумма k счётов`, то `F_LO(T) ≥ g_k(t*)`.
* `card_support_le_of_frac` — подсчёт: при `≤ K+1` дробных `λ_i` и `Σλ = k` носитель `λ`
  содержит не более `k+K` активов.
* Контрпримеры: `mixed_sign_ratio` (разные знаки: `G*_1/OPT(1) = 1+ω`), симплекс
  (`simplex_dual_value`, `simplex_opt_lt`).
* NP-трудность при `ω ≤ 2` (`subsetSum_obj_lt_of_ne`, `ssB_scaled_lev_le`): масштабированная
  редукция Предложения 4 с `β_i = a_i/a_max ∈ [−1,1]`, `ω_i = 2β_i² ≤ 2`.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Теорема 2.2(a): одна точка даёт множитель 2 при `K = 1`, `β ≥ 0` -/

section TwoApprox

variable {m d β : ι → ℝ} {Sf P G : Unit → Unit → ℝ}

lemma P_pos_of_root (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) : 0 < P () () := by
  have h1 := hG () ()
  have h2 := hPS () ()
  simp only [Finset.univ_unique, Finset.sum_singleton, ite_true] at h1 h2
  have hne : P () () ≠ 0 := by intro h; rw [h, zero_mul] at h2; exact zero_ne_one h2
  rcases lt_or_gt_of_ne hne with h | h
  · nlinarith [sq_nonneg (G () ())]
  · exact h

/-- **Теорема 2.2(a).** `K = 1`, `β ≥ 0`, `d > 0`. Если `Fopt` ограничивает цель любого
long-only портфеля с не более чем `k` именами, то в точке `tS = √(Fopt·σ_f²)`
`g_k(tS) ≤ 2·Fopt`. -/
theorem dualBound_le_two_opt_nonneg
    (hd : ∀ i, 0 < d i) (hβ : ∀ i, 0 ≤ β i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0) {k : ℕ} {Fopt : ℝ}
    (hopt : ∀ S : Finset ι, S.card ≤ k → ∀ w : ι → ℝ, (∀ i ∈ S, 0 ≤ w i) →
        objLO m d (oneB β) Sf S w ≤ Fopt) :
    dualBound m d (oneB β) P k (fun _ => Real.sqrt (Fopt * Sf () ())) ≤ 2 * Fopt := by
  classical
  have hP := P_pos_of_root (Sf := Sf) hG hPS
  have hPSu : P () () * Sf () () = 1 := by
    have := hPS () (); simpa using this
  have hSf : 0 < Sf () () := by
    by_contra h; push Not at h
    nlinarith [mul_nonneg hP.le (neg_nonneg.mpr h)]
  have hF0 : 0 ≤ Fopt := by
    have := hopt ∅ (by simp) (fun _ => 0) (by simp)
    simpa [objLO] using this
  set tS : ℝ := Real.sqrt (Fopt * Sf () ()) with htS
  have htS0 : 0 ≤ tS := Real.sqrt_nonneg _
  have htS2 : tS ^ 2 = Fopt * Sf () () := Real.sq_sqrt (by positivity)
  have hq : quadf P (fun _ => tS) = Fopt := by
    simp only [quadf, Finset.univ_unique, Finset.sum_singleton]
    calc P () () * (tS * tS) = P () () * (Fopt * Sf () ()) := by rw [← sq, htS2]
      _ = Fopt * (P () () * Sf () ()) := by ring
      _ = Fopt := by rw [hPSu, mul_one]
  unfold dualBound
  rw [hq]
  have hsup : ((Finset.univ : Finset (Finset ι)).filter fun S => S.card ≤ k).sup'
      (supportsLe_nonempty k)
      (fun S => ∑ i ∈ S, (max (m i - dotp (oneB β i) (fun _ => tS)) 0) ^ 2 / d i) ≤ Fopt := by
    refine Finset.sup'_le _ _ fun S hS => ?_
    have hSk : S.card ≤ k := (Finset.mem_filter.mp hS).2
    obtain ⟨z, ⟨⟨t₀, hz⟩, hleast⟩, ⟨⟨wS, hwS, hwz⟩, -⟩⟩ :=
      isGreatest_objLO_isLeast_QLO (m := m) (B := oneB β) (Sf := Sf) (G := G) hd hG hPS S
    have hmin : ∀ t, QLO m d (oneB β) P S t₀ ≤ QLO m d (oneB β) P S t := by
      intro t; rw [← hz]; exact hleast ⟨t, rfl⟩
    have ht₀ : 0 ≤ t₀ () := min_QLO_nonneg hd hβ hP hmin
    have hFS : QLO m d (oneB β) P S t₀ ≤ Fopt := by
      rw [← hz, hwz]; exact hopt S hSk wS hwS
    have hdotp : ∀ (i : ι) (x : ℝ), dotp (oneB β i) (fun _ => x) = β i * x := by
      intro i x; simp [dotp, oneB]
    have hdot0 : ∀ i, dotp (oneB β i) t₀ = β i * t₀ () := by
      intro i; simp [dotp, oneB]
    -- `t₀ ≤ tS`
    have hq0 : P () () * (t₀ () * t₀ ()) ≤ Fopt := by
      have h1 : quadf P t₀ ≤ QLO m d (oneB β) P S t₀ := by
        simp only [QLO]
        have : 0 ≤ ∑ i ∈ S, (max (m i - dotp (oneB β i) t₀) 0) ^ 2 / d i :=
          Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hd i).le
        linarith
      have h2 : quadf P t₀ = P () () * (t₀ () * t₀ ()) := by
        simp [quadf]
      linarith
    have hle : t₀ () ≤ tS := by
      by_contra hlt; push Not at hlt
      have : tS * tS < t₀ () * t₀ () := mul_self_lt_mul_self htS0 hlt
      have h3 : P () () * (tS * tS) < P () () * (t₀ () * t₀ ()) :=
        mul_lt_mul_of_pos_left this hP
      have h4 : P () () * (tS * tS) = Fopt := by
        have := hq; simp only [quadf, Finset.univ_unique, Finset.sum_singleton] at this
        exact this
      linarith
    -- `s_i(tS) ≤ s_i(t₀)`
    have hterm : ∀ i ∈ S, (max (m i - dotp (oneB β i) (fun _ => tS)) 0) ^ 2 / d i
        ≤ (max (m i - dotp (oneB β i) t₀) 0) ^ 2 / d i := by
      intro i _
      rw [hdotp, hdot0]
      have hle2 : m i - β i * tS ≤ m i - β i * t₀ () := by nlinarith [hβ i]
      have hmx : max (m i - β i * tS) 0 ≤ max (m i - β i * t₀ ()) 0 := max_le_max hle2 le_rfl
      have hnn : 0 ≤ max (m i - β i * tS) 0 := le_max_right _ _
      gcongr
      exact (hd i).le
    have hsum := Finset.sum_le_sum hterm
    have hQ : ∑ i ∈ S, (max (m i - dotp (oneB β i) t₀) 0) ^ 2 / d i
        ≤ QLO m d (oneB β) P S t₀ := by
      simp only [QLO]
      have : 0 ≤ quadf P t₀ := by
        simp only [quadf, Finset.univ_unique, Finset.sum_singleton]
        have : 0 ≤ t₀ () * t₀ () := mul_self_nonneg _
        positivity
      linarith
    linarith
  linarith

end TwoApprox

/-! ### H1(c): поточечная форма и сертификат бикритериальной гарантии -/

section Bicriteria

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {m d : ι → ℝ} {B : ι → κ → ℝ} {Sf P G : κ → κ → ℝ}

/-- **Пороговая форма H1(c).** Если в точке `t` у `T` все счета не ниже `σ`, у остальных не
выше `σ`, и `|T| ≥ k`, то `g_k(t) ≤ QLO(T,t)`: двойственная граница мажорируется значением
двойственной функции набора `T`. Теорема Сиона и существование `t*` не нужны. -/
theorem dualBound_le_QLO_of_threshold (hd : ∀ i, 0 < d i) {k : ℕ} (t : κ → ℝ) {T : Finset ι}
    {σ : ℝ} (hk : k ≤ T.card)
    (hin : ∀ i ∈ T, σ ≤ (max (m i - dotp (B i) t) 0) ^ 2 / d i)
    (hout : ∀ j ∉ T, (max (m j - dotp (B j) t) 0) ^ 2 / d j ≤ σ) :
    dualBound m d B P k t ≤ QLO m d B P T t := by
  classical
  unfold dualBound QLO
  have hsup : ((Finset.univ : Finset (Finset ι)).filter fun S => S.card ≤ k).sup'
      (supportsLe_nonempty k)
      (fun S => ∑ i ∈ S, (max (m i - dotp (B i) t) 0) ^ 2 / d i)
      ≤ ∑ i ∈ T, (max (m i - dotp (B i) t) 0) ^ 2 / d i := by
    refine Finset.sup'_le _ _ fun S hS => ?_
    have hSk : S.card ≤ k := (Finset.mem_filter.mp hS).2
    exact sum_le_sum_top (v := fun i => (max (m i - dotp (B i) t) 0) ^ 2 / d i)
      (fun i => div_nonneg (sq_nonneg _) (hd i).le) (Finset.subset_univ S)
      (Or.inl (le_trans hSk hk))
      (fun i hi j _ hj => le_trans (hout j hj) (hin i hi))
  linarith

/-- Выпуклость `(x)_+²` над касательной: `(x)_+² ≥ (y)_+² + 2(y)_+(x−y)`. -/
lemma pos_sq_ge (x y : ℝ) : max y 0 ^ 2 + 2 * max y 0 * (x - y) ≤ max x 0 ^ 2 := by
  rcases le_total x 0 with hx | hx <;> rcases le_total y 0 with hy | hy
  · rw [max_eq_right hx, max_eq_right hy]; nlinarith
  · rw [max_eq_right hx, max_eq_left hy]; nlinarith [mul_nonneg hy (neg_nonneg.mpr hx)]
  · rw [max_eq_left hx, max_eq_right hy]; nlinarith [sq_nonneg x]
  · rw [max_eq_left hx, max_eq_left hy]; nlinarith [sq_nonneg (x - y)]

/-- **Сертификат бикритериальной гарантии.** Пусть в точке `t₀` задан вес `λ ∈ [0,1]^T`
(`T` — предполагаемый носитель размера `k+K`), стационарный:
`Σ_f⁻¹t₀ = Σ_{i∈T} λ_i w_i(t₀) B_i`, и такой, что `Σ_T λ_i s_i(t₀)` не меньше верхней суммы
`k` счётов. Тогда `F_LO(T) ≥ g_k(t₀)`: у носителя `T` есть long-only портфель со значением не
меньше `g_k(t₀)`. Если `t₀` минимизирует `g_k`, то `OPT_LO(k) ≤ g_k(t₀) ≤ F_LO(T) ≤ OPT_LO(|T|)`. -/
theorem bicriteria_certificate [Nonempty κ] (hd : ∀ i, 0 < d i)
    (hG : ∀ j j', ∑ l, G l j * G l j' = P j j')
    (hPS : ∀ j j', ∑ l, P j l * Sf l j' = if j = j' then 1 else 0)
    {k : ℕ} {T : Finset ι} (t₀ : κ → ℝ) (lam : ι → ℝ)
    (hlam : ∀ i ∈ T, 0 ≤ lam i ∧ lam i ≤ 1)
    (hstat : ∀ j, ∑ j', P j j' * t₀ j' = ∑ i ∈ T, lam i * wclip m d B t₀ i * B i j)
    (hval : dualBound m d B P k t₀
      ≤ quadf P t₀ + ∑ i ∈ T, lam i * ((max (m i - dotp (B i) t₀) 0) ^ 2 / d i)) :
    ∃ w : ι → ℝ, (∀ i ∈ T, 0 ≤ w i) ∧ dualBound m d B P k t₀ ≤ objLO m d B Sf T w := by
  obtain ⟨z, ⟨⟨t₁, hz⟩, hleast⟩, ⟨⟨wT, hwT, hwz⟩, -⟩⟩ :=
    isGreatest_objLO_isLeast_QLO (m := m) (B := B) (Sf := Sf) (G := G) hd hG hPS T
  refine ⟨wT, hwT, ?_⟩
  rw [← hwz]
  -- `QLO(T,t) ≥ L(t) := t'Pt + Σ λ_i s_i(t) ≥ L(t₀)` при любом `t`
  set s : ι → (κ → ℝ) → ℝ := fun i t => (max (m i - dotp (B i) t) 0) ^ 2 / d i with hs
  have hPsymm := P_symm_of_root (P := P) (G := G) hG
  have hL : ∀ t, quadf P t₀ + ∑ i ∈ T, lam i * s i t₀
      ≤ quadf P t + ∑ i ∈ T, lam i * s i t := by
    intro t
    set h : κ → ℝ := t - t₀ with hh
    have htt : t = t₀ + h := by funext j; simp [hh]
    have hadd := quadf_add hG t₀ h
    -- линейный член квадратичной части
    have hlin : ∑ j, ∑ j', P j j' * (t₀ j * h j')
        = ∑ i ∈ T, lam i * wclip m d B t₀ i * dotp (B i) h := by
      have h1 : ∑ j, ∑ j', P j j' * (t₀ j * h j') = ∑ j', (∑ j, P j' j * t₀ j) * h j' := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by rw [hPsymm j j']; ring
      rw [h1]
      have h2 : ∀ j', (∑ j, P j' j * t₀ j) = ∑ i ∈ T, lam i * wclip m d B t₀ i * B i j' :=
        fun j' => by
          have := hstat j'
          simpa using this
      simp only [h2, Finset.sum_mul, dotp, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    -- касательная для каждого актива
    have hitem : ∀ i ∈ T, lam i * s i t₀ - lam i * wclip m d B t₀ i * dotp (B i) h * 2
        ≤ lam i * s i t := by
      intro i hi
      have hdi := hd i
      have hxy : (m i - dotp (B i) t) - (m i - dotp (B i) t₀) = - dotp (B i) h := by
        rw [htt]; simp only [dotp, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
      have hp := pos_sq_ge (m i - dotp (B i) t) (m i - dotp (B i) t₀)
      rw [hxy] at hp
      have hdiv : (max (m i - dotp (B i) t₀) 0 ^ 2 + 2 * max (m i - dotp (B i) t₀) 0 * (- dotp (B i) h))
            / d i ≤ max (m i - dotp (B i) t) 0 ^ 2 / d i :=
        div_le_div_of_nonneg_right hp hdi.le
      have hl0 := (hlam i hi).1
      have hw : wclip m d B t₀ i = max (m i - dotp (B i) t₀) 0 / d i := rfl
      have h3 : s i t₀ - 2 * wclip m d B t₀ i * dotp (B i) h ≤ s i t := by
        rw [hw]
        have : (max (m i - dotp (B i) t₀) 0 ^ 2 + 2 * max (m i - dotp (B i) t₀) 0 * (- dotp (B i) h))
            / d i = s i t₀ - 2 * (max (m i - dotp (B i) t₀) 0 / d i) * dotp (B i) h := by
          simp only [hs]; field_simp; ring
        rw [this] at hdiv
        exact hdiv
      nlinarith [mul_le_mul_of_nonneg_left h3 hl0]
    have hsum := Finset.sum_le_sum hitem
    rw [Finset.sum_sub_distrib] at hsum
    have hcomm : ∑ i ∈ T, lam i * wclip m d B t₀ i * dotp (B i) h * 2
        = 2 * ∑ i ∈ T, lam i * wclip m d B t₀ i * dotp (B i) h := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    have hq0 : 0 ≤ quadf P h := quadf_nonneg_of_root hG h
    rw [htt]
    have hsplit : quadf P (t₀ + h) = quadf P t₀ + 2 * ∑ i ∈ T, lam i * wclip m d B t₀ i * dotp (B i) h
        + quadf P h := by rw [hadd, hlin]
    -- `s i (t₀ + h)` совпадает с `s i t`
    have hsame : ∀ i, s i (t₀ + h) = s i t := fun i => by rw [← htt]
    simp only [hsame]
    rw [← htt] at hsplit ⊢
    nlinarith [hsum, hcomm, hq0, hsplit]
  -- `QLO(T,t) ≥ L(t)`, поскольку `λ_i ≤ 1`
  have hQ : ∀ t, quadf P t + ∑ i ∈ T, lam i * s i t ≤ QLO m d B P T t := by
    intro t
    simp only [QLO]
    have : ∑ i ∈ T, lam i * s i t ≤ ∑ i ∈ T, (max (m i - dotp (B i) t) 0) ^ 2 / d i := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hs0 : 0 ≤ s i t := div_nonneg (sq_nonneg _) (hd i).le
      have := (hlam i hi).2
      nlinarith
    linarith
  have h1 := hL t₁
  have h2 := hQ t₁
  have h3 : QLO m d B P T t₁ = z := hz.symm
  simp only [hs] at h1 h2 hval ⊢
  linarith

/-- **Подсчёт.** Если `λ ∈ [0,1]`, `Σλ = k` (целое) и дробных координат не больше `K+1`, то
носитель `λ` содержит не более `k + K` активов. -/
theorem card_support_le_of_frac {lam : ι → ℝ} {k Kn : ℕ}
    (h01 : ∀ i, 0 ≤ lam i ∧ lam i ≤ 1) (hsum : ∑ i, lam i = k)
    (hfrac : (Finset.univ.filter fun i => 0 < lam i ∧ lam i < 1).card ≤ Kn + 1) :
    (Finset.univ.filter fun i => 0 < lam i).card ≤ k + Kn := by
  classical
  set H : Finset ι := Finset.univ.filter fun i => lam i = 1 with hH
  set F : Finset ι := Finset.univ.filter fun i => 0 < lam i ∧ lam i < 1 with hF
  set T : Finset ι := Finset.univ.filter fun i => 0 < lam i with hT
  have hdisj : Disjoint H F := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    have := (Finset.mem_filter.mp hi).2
    have := (Finset.mem_filter.mp hi').2
    linarith [(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hi').2.2]
  have hTeq : T = H ∪ F := by
    ext i
    simp only [hT, hH, hF, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hi
      rcases (h01 i).2.lt_or_eq with hlt | heq
      · exact Or.inr ⟨hi, hlt⟩
      · exact Or.inl heq
    · rintro (h | h)
      · rw [h]; exact one_pos
      · exact h.1
  have hcardT : T.card = H.card + F.card := by rw [hTeq, Finset.card_union_of_disjoint hdisj]
  -- `Σ λ = |H| + Σ_F λ`
  have hsplit : ∑ i, lam i = H.card + ∑ i ∈ F, lam i := by
    set Z : Finset ι := Finset.univ.filter fun i => lam i = 0 with hZ
    have hcover : (Finset.univ : Finset ι) = H ∪ F ∪ Z := by
      refine (Finset.eq_univ_iff_forall.mpr fun i => ?_).symm
      have := h01 i
      simp only [hH, hF, hZ, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases this.1.lt_or_eq with h0 | h0
      · rcases this.2.lt_or_eq with h1 | h1
        · exact Or.inl (Or.inr ⟨h0, h1⟩)
        · exact Or.inl (Or.inl h1)
      · exact Or.inr h0.symm
    have hd2 : Disjoint (H ∪ F) Z := by
      rw [Finset.disjoint_left]
      intro i hi hi0
      have h0 : lam i = 0 := (Finset.mem_filter.mp hi0).2
      rcases Finset.mem_union.mp hi with h | h
      · have := (Finset.mem_filter.mp h).2; linarith
      · have := (Finset.mem_filter.mp h).2.1; linarith
    rw [hcover, Finset.sum_union hd2, Finset.sum_union hdisj]
    have hz : ∑ i ∈ Z, lam i = 0 :=
      Finset.sum_eq_zero fun i hi => (Finset.mem_filter.mp hi).2
    have hh : ∑ i ∈ H, lam i = H.card := by
      have : ∀ i ∈ H, lam i = 1 := fun i hi => (Finset.mem_filter.mp hi).2
      rw [Finset.sum_congr rfl this]; simp
    rw [hz, hh]; ring
  by_cases hFe : F = ∅
  · have hFc : F.card = 0 := by rw [hFe]; simp
    have hHk : (H.card : ℝ) = k := by
      rw [hFe] at hsplit; simpa [hsum] using hsplit.symm
    have : H.card = k := by exact_mod_cast hHk
    omega
  · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hFe
    have hpos : 0 < ∑ i ∈ F, lam i :=
      Finset.sum_pos (fun i hi => (Finset.mem_filter.mp hi).2.1) ⟨i₀, hi₀⟩
    have hHk : (H.card : ℝ) < k := by rw [hsum] at hsplit; linarith
    have hHk' : H.card < k := by exact_mod_cast hHk
    omega

end Bicriteria

/-! ### Разные знаки нагрузок: зазор релаксации неограничен (`K = 1`, `M = 2`, `k = 1`) -/

section MixedSign

/-- `m = d = 1`, `β = (s, −s)`, `Σ_f = 1`: `g_1(t) ≥ 1` при любом `t`. -/
theorem mixed_sign_dual_ge_one (s t : ℝ) :
    1 ≤ dualBound (fun _ : Fin 2 => (1 : ℝ)) (fun _ => 1) (oneB ![s, -s])
      (fun _ _ => (1 : ℝ)) 1 (fun _ => t) := by
  unfold dualBound
  have hq : 0 ≤ quadf (fun _ _ : Unit => (1 : ℝ)) (fun _ => t) := by
    simp only [quadf, Finset.univ_unique, Finset.sum_singleton]; nlinarith [sq_nonneg t]
  have hmem : ∀ i : Fin 2, ({i} : Finset (Fin 2)) ∈
      ((Finset.univ : Finset (Finset (Fin 2))).filter fun S => S.card ≤ 1) := by
    intro i; simp
  have hle : ∀ i : Fin 2,
      (max (1 - dotp (oneB ![s, -s] i) (fun _ : Unit => t)) 0) ^ 2 / 1
        ≤ ((Finset.univ : Finset (Finset (Fin 2))).filter fun S => S.card ≤ 1).sup'
          (supportsLe_nonempty 1)
          (fun S => ∑ i ∈ S, (max (1 - dotp (oneB ![s, -s] i) (fun _ : Unit => t)) 0) ^ 2 / 1) := by
    intro i
    have := Finset.le_sup' (fun S : Finset (Fin 2) =>
      ∑ i ∈ S, (max (1 - dotp (oneB ![s, -s] i) (fun _ : Unit => t)) 0) ^ 2 / 1) (hmem i)
    have e : ∑ j ∈ ({i} : Finset (Fin 2)),
        (max (1 - dotp (oneB ![s, -s] j) (fun _ : Unit => t)) 0) ^ 2 / 1
        = (max (1 - dotp (oneB ![s, -s] i) (fun _ : Unit => t)) 0) ^ 2 / 1 :=
      Finset.sum_singleton _ _
    rw [e] at this
    exact this
  have hdot : ∀ i : Fin 2, dotp (oneB ![s, -s] i) (fun _ : Unit => t) = (![s, -s] i) * t := by
    intro i; simp [dotp, oneB]
  by_cases hst : s * t ≤ 0
  · have h0 := hle 0
    rw [hdot] at h0
    simp only [Matrix.cons_val_zero] at h0
    have : 1 ≤ max (1 - s * t) 0 := le_trans (by linarith) (le_max_left _ _)
    nlinarith
  · push Not at hst
    have h1 := hle 1
    rw [hdot] at h1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
    have : 1 ≤ max (1 - (-s) * t) 0 := le_trans (by nlinarith) (le_max_left _ _)
    nlinarith

/-- Одноактивный портфель: цель не больше `1/(1+s²)` (`V_ii = 1 + s²`, `m_i = 1`). -/
theorem mixed_sign_opt_le (s : ℝ) {S : Finset (Fin 2)} (hS : S.card ≤ 1) (w : Fin 2 → ℝ) :
    objLO (fun _ : Fin 2 => (1 : ℝ)) (fun _ => 1) (oneB ![s, -s]) (fun _ _ => (1 : ℝ)) S w
      ≤ 1 / (1 + s ^ 2) := by
  have hpos : 0 < 1 + s ^ 2 := by positivity
  rcases Finset.card_le_one_iff_subset_singleton.mp hS with ⟨i, hi⟩
  rcases Finset.subset_singleton_iff.mp hi with h | h
  · subst h; simp [objLO]; positivity
  · subst h
    have hV : Vmat (fun _ : Fin 2 => (1 : ℝ)) (oneB ![s, -s]) (fun _ _ : Unit => (1 : ℝ)) i i
        = 1 + s ^ 2 := by
      fin_cases i <;> simp [Vmat, oneB] <;> ring
    simp only [objLO, Finset.sum_singleton, hV]
    rw [le_div_iff₀ hpos]
    nlinarith [sq_nonneg ((1 + s ^ 2) * w i - 1)]

/-- **Зазор неограничен при разных знаках.** `(1+s²)·objLO(S,w) ≤ g_1(t)` для всех `t`, всех
`S` с `|S| ≤ 1` и всех `w`: отношение `G*_1/OPT_LO(1) ≥ 1 + ω`, `ω = s²`. -/
theorem mixed_sign_ratio (s t : ℝ) {S : Finset (Fin 2)} (hS : S.card ≤ 1) (w : Fin 2 → ℝ) :
    (1 + s ^ 2) * objLO (fun _ : Fin 2 => (1 : ℝ)) (fun _ => 1) (oneB ![s, -s])
        (fun _ _ => (1 : ℝ)) S w
      ≤ dualBound (fun _ : Fin 2 => (1 : ℝ)) (fun _ => 1) (oneB ![s, -s])
        (fun _ _ => (1 : ℝ)) 1 (fun _ => t) := by
  have hpos : 0 < 1 + s ^ 2 := by positivity
  have h1 := mixed_sign_opt_le s hS w
  have h2 := mixed_sign_dual_ge_one s t
  have : (1 + s ^ 2) * (1 / (1 + s ^ 2)) = 1 := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h1 hpos.le]

end MixedSign

/-! ### NP-трудность при `ω ≤ 2`: масштабированная редукция Предложения 4 -/

section Hardness

lemma sysVar_ssB (a : ι → ℝ) (i : ι) : sysVar (ssB a) ssSf i = 2 * a i ^ 2 := by
  simp [sysVar, ssB, ssSf]; ring

/-- Плечо актива редукции с `|β_i| ≤ 1` не больше `2`. -/
theorem ssB_lev_le {a : ι → ℝ} (h : ∀ i, |a i| ≤ 1) (i : ι) :
    sysVar (ssB a) ssSf i / ssD i ≤ 2 := by
  rw [sysVar_ssB]
  have := sq_le_one_iff_abs_le_one (a i) |>.mpr (h i)
  simp only [ssD, div_one]
  linarith

/-- **Строгий разрыв.** Если `|S| < s` или `Σ_S a_i ≠ b`, то при любом `w` цель строго меньше
`s + 2b²` (вещественные `a`, `b`). -/
theorem subsetSum_obj_lt_of_ne (a : ι → ℝ) (b : ℝ) {s : ℕ} {S : Finset ι} (hS : S.card ≤ s)
    (hne : S.card < s ∨ ∑ i ∈ S, a i ≠ b) (w : ι → ℝ) :
    objLO (ssM a b) ssD (ssB a) ssSf S w < s + 2 * b ^ 2 := by
  rw [subsetSum_obj_eq]
  have h1 : 0 ≤ ∑ i ∈ S, (w i - 1) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hlt : S.card < s
  · have hc : (S.card : ℝ) + 1 ≤ s := by exact_mod_cast hlt
    nlinarith [sq_nonneg (∑ i ∈ S, a i * w i - b)]
  · have hcard : S.card = s := le_antisymm hS (not_lt.mp hlt)
    have hne' : ∑ i ∈ S, a i ≠ b := hne.resolve_left hlt
    have hgap := subsetSum_gap a b S w
    have hA : 0 ≤ ∑ i ∈ S, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hden : 0 < 1 + 2 * ∑ i ∈ S, a i ^ 2 := by linarith
    have hpos : 0 < 2 * (∑ i ∈ S, a i - b) ^ 2 / (1 + 2 * ∑ i ∈ S, a i ^ 2) := by
      have : 0 < (∑ i ∈ S, a i - b) ^ 2 := by
        have : ∑ i ∈ S, a i - b ≠ 0 := sub_ne_zero.mpr hne'
        positivity
      positivity
    have hc : (S.card : ℝ) = s := by exact_mod_cast hcard
    linarith

/-- **Масштабированная редукция.** Для целых `a_i`, `b` и `A > 0` с `|a_i| ≤ A` положим
`β_i = a_i/A ∈ [−1,1]`, `L = b/A`: инстанс `m_i = 1 + 2Lβ_i`, `d_i = 1`, `Σ_f = 2`, `B_i = β_i`
имеет плечи `ω_i = 2β_i² ≤ 2`, значение `s + 2L²` не превосходится ни при каком `|S| ≤ s` и
`w`, и достигается неотрицательным весом тогда и только тогда, когда у K-SUBSET SUM ответ «да».
Поэтому задача NP-трудна при `ω ≤ 2` (и при `β > 0`, `m > 0`, `D = I`, если `a_i, b > 0`). -/
theorem subsetSum_reduction_scaled (a : ι → ℤ) (b : ℤ) {A : ℕ} (hA : 0 < A)
    (hamax : ∀ i, |(a i : ℝ)| ≤ A) (s : ℕ) :
    (∀ i, sysVar (ssB (fun i => (a i : ℝ) / A)) ssSf i / ssD i ≤ 2) ∧
    (∀ S : Finset ι, S.card ≤ s → ∀ w : ι → ℝ,
        objLO (ssM (fun i => (a i : ℝ) / A) ((b : ℝ) / A)) ssD
          (ssB (fun i => (a i : ℝ) / A)) ssSf S w ≤ s + 2 * ((b : ℝ) / A) ^ 2) ∧
    ((∃ S : Finset ι, S.card ≤ s ∧ ∃ w : ι → ℝ, (∀ i ∈ S, 0 ≤ w i) ∧
        objLO (ssM (fun i => (a i : ℝ) / A) ((b : ℝ) / A)) ssD
          (ssB (fun i => (a i : ℝ) / A)) ssSf S w = s + 2 * ((b : ℝ) / A) ^ 2)
      ↔ ∃ S : Finset ι, S.card = s ∧ ∑ i ∈ S, a i = b) := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  refine ⟨fun i => ssB_lev_le (fun i => ?_) i, fun S hS w => subsetSum_obj_le _ _ hS w, ⟨?_, ?_⟩⟩
  · rw [abs_div, abs_of_pos hA', div_le_one hA']; exact hamax i
  · rintro ⟨S, hS, w, -, hval⟩
    by_contra hno
    push Not at hno
    have hne : S.card < s ∨ ∑ i ∈ S, ((a i : ℝ) / A) ≠ (b : ℝ) / A := by
      by_cases hlt : S.card < s
      · exact Or.inl hlt
      · refine Or.inr fun heq => hno S (le_antisymm hS (not_lt.mp hlt)) ?_
        have : (∑ i ∈ S, (a i : ℝ)) / A = (b : ℝ) / A := by
          rw [← heq, Finset.sum_div]
        have h2 : (∑ i ∈ S, (a i : ℝ)) = b := by
          field_simp at this; exact this
        exact_mod_cast h2
    have := subsetSum_obj_lt_of_ne (fun i => (a i : ℝ) / A) ((b : ℝ) / A) hS hne w
    linarith
  · rintro ⟨S, hS, hsum⟩
    refine ⟨S, hS.le, fun _ => 1, fun _ _ => zero_le_one, ?_⟩
    have hs' : ∑ i ∈ S, ((a i : ℝ) / A) = (b : ℝ) / A := by
      rw [← Finset.sum_div]
      have : (∑ i ∈ S, (a i : ℝ)) = b := by exact_mod_cast hsum
      rw [this]
    have := subsetSum_obj_yes (fun i => (a i : ℝ) / A) ((b : ℝ) / A) hS hs'
    simpa using this

end Hardness

/-! ### Бикритериальная добавка `+K` не улучшается: правильный симплекс -/

section Simplex

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Единичная матрица как матрица `Σ_f = Σ_f⁻¹ = G`. -/
def idMat (κ : Type*) [DecidableEq κ] : κ → κ → ℝ := fun j j' => if j = j' then 1 else 0

lemma quadf_idMat (x : κ → ℝ) : quadf (idMat κ) x = ∑ j, x j ^ 2 := by
  simp only [quadf, idMat, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, sq]

/-- **Пример `K+1` активов с правильным центрированным симплексом нагрузок** (`m = d = 1`,
`Σ_f = I`, `‖B_i‖² = ω`, `⟨B_i,B_j⟩ = −ω/K`, `Σ_i B_i = 0`). В нём `g_1(t) ≥ 1` при всех `t`
(`simplex_dual_ge_one`), а любой носитель из не более чем `K` активов даёт не больше
`K²/(K+ω)` (`simplex_opt_le`). При `ω > K(K−1)` имеем `K²/(K+ω) < 1`: добавка `+K` в
бикритериальной гарантии `OPT(k) ≤ G*_k ≤ F_LO(H∪I')`, `|H∪I'| ≤ k+K`, не заменяется на
`+K−1`. -/
theorem simplex_dual_ge_one [Nonempty ι] {B : ι → κ → ℝ}
    (hcen : ∀ l, ∑ i, B i l = 0) (t : κ → ℝ) :
    1 ≤ dualBound (fun _ : ι => (1 : ℝ)) (fun _ => 1) B (idMat κ) 1 t := by
  classical
  unfold dualBound
  have hq : 0 ≤ quadf (idMat κ) t := by
    rw [quadf_idMat]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- есть актив с `⟨B_i,t⟩ ≤ 0`
  have hsum : ∑ i, dotp (B i) t = 0 := by
    simp only [dotp]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← Finset.sum_mul, hcen l, zero_mul]
  obtain ⟨i, hi⟩ : ∃ i, dotp (B i) t ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have : 0 < ∑ i, dotp (B i) t := Finset.sum_pos (fun i _ => hcon i) Finset.univ_nonempty
    linarith
  have hmem : ({i} : Finset ι) ∈ ((Finset.univ : Finset (Finset ι)).filter fun S => S.card ≤ 1) := by
    simp
  have hle := Finset.le_sup' (fun S : Finset ι =>
      ∑ i ∈ S, (max (1 - dotp (B i) t) 0) ^ 2 / 1) hmem
  have e : ∑ j ∈ ({i} : Finset ι), (max (1 - dotp (B j) t) 0) ^ 2 / 1
      = (max (1 - dotp (B i) t) 0) ^ 2 / 1 := Finset.sum_singleton _ _
  rw [e] at hle
  have h1 : 1 ≤ max (1 - dotp (B i) t) 0 := le_trans (by linarith) (le_max_left _ _)
  have h2 : (1 : ℝ) ≤ (max (1 - dotp (B i) t) 0) ^ 2 / 1 := by nlinarith
  linarith

lemma idMat_root (j j' : κ) : ∑ l, idMat κ l j * idMat κ l j' = idMat κ j j' := by
  simp only [idMat]
  by_cases h : j = j'
  · subst h; simp
  · have : ∀ l : κ, (if l = j then (1 : ℝ) else 0) * (if l = j' then 1 else 0) = 0 := by
      intro l
      by_cases hl : l = j
      · subst hl; simp [h]
      · simp [hl]
    simp [this, h]

lemma idMat_PS (j j' : κ) : ∑ l, idMat κ j l * idMat κ l j' = if j = j' then 1 else 0 := by
  simp only [idMat, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Носитель из не более чем `K = |κ|` активов: цель не больше `K²/(K+ω)`. -/
theorem simplex_opt_le [Nonempty κ] {B : ι → κ → ℝ} {ω : ℝ} (hω : 0 < ω)
    (hcard : Fintype.card ι = Fintype.card κ + 1)
    (hdiag : ∀ i, ∑ l, B i l * B i l = ω)
    (hoff : ∀ i i', i ≠ i' → ∑ l, B i l * B i' l = - ω / Fintype.card κ)
    {S : Finset ι} (hS : S.card ≤ Fintype.card κ) (w : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) :
    objLO (fun _ : ι => (1 : ℝ)) (fun _ => 1) B (idMat κ) S w
      ≤ (Fintype.card κ : ℝ) ^ 2 / (Fintype.card κ + ω) := by
  classical
  set Kn := Fintype.card κ with hKn
  have hKpos : (0 : ℝ) < Kn := by exact_mod_cast Fintype.card_pos
  -- есть актив `j ∉ S`
  obtain ⟨j, hjS⟩ : ∃ j, j ∉ S := by
    by_contra hcon
    push Not at hcon
    have : S = Finset.univ := Finset.eq_univ_of_forall hcon
    rw [this, Finset.card_univ] at hS
    omega
  set S' : Finset ι := Finset.univ.erase j with hS'
  have hS'c : S'.card = Kn := by
    rw [hS', Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]; omega
  have hSS' : S ⊆ S' := by
    intro i hi
    rw [hS', Finset.mem_erase]
    exact ⟨fun h => hjS (h ▸ hi), Finset.mem_univ i⟩
  have hd1 : ∀ i : ι, (0 : ℝ) < (fun _ : ι => (1 : ℝ)) i := fun _ => one_pos
  -- точка `t = −α B_j`, `α = K/(K+ω)`
  set α : ℝ := Kn / (Kn + ω) with hα
  have hKω : 0 < (Kn : ℝ) + ω := by positivity
  set t : κ → ℝ := fun l => -α * B j l with ht
  have hweak := objLO_le_QLO (m := fun _ : ι => (1 : ℝ)) (d := fun _ => 1) (B := B)
    (Sf := idMat κ) (P := idMat κ) (G := idMat κ) hd1
    (fun j j' => idMat_root j j') (fun j j' => idMat_PS j j') hw t
  have hmono : QLO (fun _ : ι => (1 : ℝ)) (fun _ => 1) B (idMat κ) S t
      ≤ QLO (fun _ : ι => (1 : ℝ)) (fun _ => 1) B (idMat κ) S' t := by
    simp only [QLO]
    have := Finset.sum_le_sum_of_subset_of_nonneg hSS'
      (f := fun i => (max (1 - dotp (B i) t) 0) ^ 2 / 1)
      (fun i _ _ => by positivity)
    linarith
  -- значение `QLO(S', t)`
  have hq : quadf (idMat κ) t = α ^ 2 * ω := by
    rw [quadf_idMat]
    have : ∀ l, t l ^ 2 = α ^ 2 * (B j l * B j l) := fun l => by simp only [ht]; ring
    simp only [this, ← Finset.mul_sum, hdiag j]
  have hdot : ∀ i ∈ S', dotp (B i) t = α * ω / Kn := by
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    have : dotp (B i) t = -α * ∑ l, B i l * B j l := by
      simp only [dotp, ht, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [this, hoff i j hij]; field_simp
  have hone : 1 - α * ω / Kn = Kn / (Kn + ω) := by
    simp only [hα]; field_simp; ring
  have hterm : ∀ i ∈ S', (max (1 - dotp (B i) t) 0) ^ 2 / 1 = (Kn / (Kn + ω)) ^ 2 := by
    intro i hi
    rw [hdot i hi, hone, max_eq_left (by positivity)]; ring
  have hQ : QLO (fun _ : ι => (1 : ℝ)) (fun _ => 1) B (idMat κ) S' t
      = (Kn : ℝ) ^ 2 / (Kn + ω) := by
    simp only [QLO]
    rw [hq, Finset.sum_congr rfl hterm, Finset.sum_const, hS'c, nsmul_eq_mul]
    simp only [hα]
    field_simp
    ring
  linarith

/-- Гипотезы `simplex_opt_le` выполнимы: `K = 2`, правильный треугольник нагрузок радиуса `√ω`
(для `K = 1` это `B = (√ω, −√ω)` из `mixed_sign_ratio`). -/
example {ω : ℝ} (hω : 0 < ω) :
    let B : Fin 3 → Fin 2 → ℝ := fun i l =>
      Real.sqrt ω * (![![1, 0], ![-1 / 2, Real.sqrt 3 / 2], ![-1 / 2, -(Real.sqrt 3 / 2)]] i l)
    (∀ l, ∑ i, B i l = 0) ∧ (∀ i, ∑ l, B i l * B i l = ω) ∧
      (∀ i i', i ≠ i' → ∑ l, B i l * B i' l = -ω / (Fintype.card (Fin 2) : ℝ)) := by
  intro B
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hw : Real.sqrt ω * Real.sqrt ω = ω := Real.mul_self_sqrt hω.le
  refine ⟨?_, ?_, ?_⟩
  · intro l
    fin_cases l <;> simp [B, Fin.sum_univ_succ] <;> ring
  · intro i
    fin_cases i <;> simp [B, Fin.sum_univ_succ] <;> nlinarith [h3, hw]
  · intro i i' hii
    fin_cases i <;> fin_cases i' <;> simp [B, Fin.sum_univ_succ] at hii ⊢ <;> nlinarith [h3, hw]

end Simplex

end SparseSharpe.Factor
