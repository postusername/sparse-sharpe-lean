import SparseSharpe.Inertia

set_option linter.style.header false

/-!
# Теорема C: когда минимаксный сертификат точен

`Φ(t) := max_{|S| ≤ k} φ_S(t)`, `UB := min_t Φ(t)`, `OPT := max_{|S| ≤ k} F(S)`.
Слабая двойственность даёт `OPT ≤ Φ(t)` при любом `t`.

Главное утверждение (пункт (iii) заметки, **исправленный** после того, как в первой
редакции было ошибочно заявлено «сертификат точен ⇔ связанное множество оптимально»):

  `Φ(t̂) = OPT` ⇔ найдётся связанное множество `T` (то есть `φ_T(t̂) = Φ(t̂)`)
  с **нулевым наклоном** в `t̂`, то есть с `t̂(T) = t̂`.

Оптимальности `T` недостаточно: контрпример — в `Counterexample.lean`.
-/

namespace SparseSharpe

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace OneFactor

/-- Допустимые носители: подмножества мощности не больше `k`. -/
def adm (ι : Type*) [Fintype ι] [DecidableEq ι] (k : ℕ) : Finset (Finset ι) :=
  (Finset.univ : Finset ι).powerset.filter (fun S => S.card ≤ k)

lemma empty_mem_adm (k : ℕ) : (∅ : Finset ι) ∈ adm ι k := by
  simp [adm]

lemma adm_nonempty (k : ℕ) : (adm ι k).Nonempty := ⟨∅, empty_mem_adm k⟩

/-- Сертификат при фиксированном `t`: `Φ(t) = max_{|S| ≤ k} φ_S(t)`. -/
noncomputable def Phi (P : OneFactor ι) (k : ℕ) (t : ℝ) : ℝ :=
  (adm ι k).sup' (adm_nonempty k) (fun S => P.phi S t)

/-- Оптимум задачи: `OPT = max_{|S| ≤ k} F(S)`. -/
noncomputable def OPTv (P : OneFactor ι) (k : ℕ) : ℝ :=
  (adm ι k).sup' (adm_nonempty k) (fun S => P.Fval S)

variable {P : OneFactor ι} {k : ℕ} {t : ℝ}

lemma phi_le_Phi {S : Finset ι} (hS : S ∈ adm ι k) : P.phi S t ≤ P.Phi k t :=
  Finset.le_sup' (fun S => P.phi S t) hS

lemma Fval_le_OPTv {S : Finset ι} (hS : S ∈ adm ι k) : P.Fval S ≤ P.OPTv k :=
  Finset.le_sup' (fun S => P.Fval S) hS

/-- **Слабая двойственность.** `OPT ≤ Φ(t)` при любом `t`. -/
theorem OPTv_le_Phi : P.OPTv k ≤ P.Phi k t :=
  Finset.sup'_le _ _ fun S hS => le_trans (Fval_le_phi t) (phi_le_Phi hS)

/-- Носитель, на котором достигается `OPT`. -/
lemma exists_opt : ∃ S ∈ adm ι k, P.Fval S = P.OPTv k := by
  obtain ⟨S, hS, hval⟩ := Finset.exists_mem_eq_sup' (adm_nonempty k) (fun S => P.Fval S)
  exact ⟨S, hS, hval.symm⟩

/-- Наклон `φ_S` в точке `t` равен `−2·M_t(S)`. -/
lemma slope_eq (S : Finset ι) (t : ℝ) :
    P.phi S t - P.Fval S = (P.Mt S t) ^ 2 / P.kappa S := by
  have h := Fval_eq_phi_sub (P := P) (S := S) t
  linarith

/-- **Теорема C (ii): апостериорная оценка зазора.**
Для любого связанного множества `T` (то есть `φ_T(t̂) = Φ(t̂)`) зазор сертификата
не превосходит `M_{t̂}(T)²/κ(T)`, что равно `φ_T'(t̂)²/(4κ_T)`. -/
theorem gap_le {T : Finset ι} (hT : T ∈ adm ι k) (hTie : P.phi T t = P.Phi k t) :
    P.Phi k t - P.OPTv k ≤ (P.Mt T t) ^ 2 / P.kappa T := by
  have h1 : P.Fval T ≤ P.OPTv k := Fval_le_OPTv hT
  have h2 := slope_eq (P := P) T t
  linarith [hTie ▸ h2]

/-- **Теорема C (iii): критерий точности сертификата.**
`Φ(t̂) = OPT` тогда и только тогда, когда найдётся связанное множество `T`
с нулевым наклоном в `t̂`, то есть с `t̂(T) = t̂`.

Оптимальность `T` сама по себе **не** достаточна (см. `Counterexample.lean`). -/
theorem tight_iff :
    P.Phi k t = P.OPTv k ↔ ∃ T ∈ adm ι k, P.phi T t = P.Phi k t ∧ P.that T = t := by
  constructor
  · intro htight
    obtain ⟨S, hS, hval⟩ := exists_opt (P := P) (k := k)
    have h1 : P.phi S t ≤ P.Phi k t := phi_le_Phi hS
    have h2 : P.Fval S ≤ P.phi S t := Fval_le_phi t
    have h3 : P.Phi k t = P.Fval S := by rw [htight, hval]
    have hEq : P.phi S t = P.Fval S := le_antisymm (by linarith) h2
    have h4 : P.kappa S * (t - P.that S) ^ 2 = 0 := by
      have := phi_eq_completed_square (P := P) (S := S) t
      linarith
    have h5 : (t - P.that S) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h4 with h | h
      · exact absurd h (kappa_ne_zero (P := P) (S := S))
      · exact h
    have h6 : P.that S = t := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h5
      linarith
    exact ⟨S, hS, by rw [hEq, h3], h6⟩
  · rintro ⟨T, hT, hTie, hslope⟩
    have h1 : P.phi T t = P.Fval T := by rw [← hslope]; exact phi_that
    have h2 : P.Fval T ≤ P.OPTv k := Fval_le_OPTv hT
    have h3 : P.OPTv k ≤ P.Phi k t := OPTv_le_Phi
    rw [← hTie, h1]
    linarith

/-- Переформулировка (iii) через наклон: `Φ(t̂) = OPT` ⇔ у какого-то связанного
множества `M_{t̂}(T) = 0` (то есть `φ_T'(t̂) = 0`). -/
theorem tight_iff_slope :
    P.Phi k t = P.OPTv k ↔ ∃ T ∈ adm ι k, P.phi T t = P.Phi k t ∧ P.Mt T t = 0 := by
  rw [tight_iff]
  constructor
  · rintro ⟨T, hT, hTie, hslope⟩
    exact ⟨T, hT, hTie, by rw [Mt_eq, hslope, sub_self, mul_zero]⟩
  · rintro ⟨T, hT, hTie, hM⟩
    refine ⟨T, hT, hTie, ?_⟩
    rw [Mt_eq] at hM
    rcases mul_eq_zero.mp hM with h | h
    · exact absurd h (kappa_ne_zero (P := P) (S := T))
    · linarith


/-! ### Теорема C (i): единственность top-k влечёт точность -/

/-- Оценка приращения `φ_S` при сдвиге `t ↦ t + s·u`, `0 ≤ s ≤ 1`. -/
lemma phi_shift_le {S : Finset ι} {u s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    P.phi S (t + s * u)
      ≤ P.phi S t + s * |u| * (P.kappa S * (2 * |t - P.that S| + |u|)) := by
  have hκ : 0 < P.kappa S := kappa_pos
  have e1 := phi_eq_completed_square (P := P) (S := S) (t + s * u)
  have e2 := phi_eq_completed_square (P := P) (S := S) t
  have expand : (t + s * u - P.that S) ^ 2 - (t - P.that S) ^ 2
      = s * (2 * u * (t - P.that S) + s * u ^ 2) := by ring
  have hb : 2 * u * (t - P.that S) + s * u ^ 2 ≤ |u| * (2 * |t - P.that S| + |u|) := by
    have h1 : u * (t - P.that S) ≤ |u| * |t - P.that S| := by
      calc u * (t - P.that S) ≤ |u * (t - P.that S)| := le_abs_self _
        _ = |u| * |t - P.that S| := abs_mul _ _
    have h2 : s * u ^ 2 ≤ |u| * |u| := by
      have : u ^ 2 = |u| * |u| := by rw [← abs_mul, abs_mul_self]; ring
      nlinarith [abs_nonneg u, sq_nonneg u, this]
    nlinarith [h1, h2]
  have hmul : P.kappa S * (s * (2 * u * (t - P.that S) + s * u ^ 2))
      ≤ P.kappa S * (s * (|u| * (2 * |t - P.that S| + |u|))) := by
    have := mul_le_mul_of_nonneg_left hb hs0
    exact mul_le_mul_of_nonneg_left this hκ.le
  nlinarith [e1, e2, expand, hmul]

/-- **Теорема C (i).** Если в точке минимума `t̂` функции `Φ` максимум достигается
на **единственном** носителе `T`, то `t̂` — минимизатор `φ_T`, и сертификат точен. -/
theorem that_eq_of_unique {T : Finset ι}
    (hmin : ∀ t' : ℝ, P.Phi k t ≤ P.Phi k t')
    (hT : T ∈ adm ι k) (hTie : P.phi T t = P.Phi k t)
    (huniq : ∀ S ∈ adm ι k, S ≠ T → P.phi S t < P.Phi k t) :
    P.that T = t := by
  classical
  by_contra hne
  set u : ℝ := P.that T - t with hu
  have hu0 : u ≠ 0 := sub_ne_zero.mpr hne
  have hκT : 0 < P.kappa T := kappa_pos
  -- равномерная липшицева постоянная по конечному семейству
  set Λ : ℝ := (adm ι k).sup' (adm_nonempty k)
    (fun S => P.kappa S * (2 * |t - P.that S| + |u|)) with hΛ
  have hΛ0 : 0 ≤ Λ := by
    refine le_trans ?_ (Finset.le_sup' (α := ℝ)
      (fun S => P.kappa S * (2 * |t - P.that S| + |u|)) (empty_mem_adm (ι := ι) k))
    have : (0:ℝ) ≤ P.kappa (∅ : Finset ι) := kappa_pos.le
    positivity
  -- равномерный зазор до остальных носителей
  set ρ : ℝ := P.Phi k t - (adm ι k).sup' (adm_nonempty k)
    (fun S => if S = T then 0 else P.phi S t) with hρ
  have hPhipos : 0 < P.Phi k t := by
    rcases lt_or_eq_of_le (le_trans phi_nonneg (le_of_eq hTie) :
        (0:ℝ) ≤ P.Phi k t) with h | h
    · exact h
    · exfalso
      have hz : P.phi T t = 0 := by rw [hTie, ← h]
      have hF : P.Fval T = 0 := le_antisymm (by linarith [Fval_le_phi (P := P) (S := T) t])
        (Fval_nonneg)
      have := phi_eq_completed_square (P := P) (S := T) t
      have hsq : P.kappa T * (t - P.that T) ^ 2 = 0 := by linarith
      rcases mul_eq_zero.mp hsq with h1 | h1
      · exact absurd h1 (kappa_ne_zero (P := P) (S := T))
      · exact hu0 (by
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
          simp [hu]; linarith)
  have hρpos : 0 < ρ := by
    rw [hρ, sub_pos]
    refine Finset.sup'_lt_iff (adm_nonempty k) |>.mpr fun S hS => ?_
    by_cases hST : S = T
    · simpa [hST] using hPhipos
    · simpa [hST] using huniq S hS hST
  -- выбираем шаг
  set s : ℝ := min 1 (ρ / (|u| * Λ + 1)) with hsdef
  have hden : 0 < |u| * Λ + 1 := by positivity
  have hs0 : 0 < s := lt_min (by norm_num) (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsρ : s * (|u| * Λ) < ρ := by
    have h1 : s ≤ ρ / (|u| * Λ + 1) := min_le_right _ _
    have h2 : s * (|u| * Λ) ≤ (ρ / (|u| * Λ + 1)) * (|u| * Λ) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : (ρ / (|u| * Λ + 1)) * (|u| * Λ) < ρ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith [hρpos, mul_nonneg (abs_nonneg u) hΛ0]
    linarith
  -- на сдвинутой точке максимум строго меньше
  have hstrict : P.Phi k (t + s * u) < P.Phi k t := by
    refine Finset.sup'_lt_iff (adm_nonempty k) |>.mpr fun S hS => ?_
    by_cases hST : S = T
    · subst hST
      have e := phi_eq_completed_square (P := P) (S := S) (t + s * u)
      have e2 := phi_eq_completed_square (P := P) (S := S) t
      have harg : t + s * u - P.that S = (1 - s) * (t - P.that S) := by
        rw [hu]; ring
      rw [harg] at e
      have hlt : ((1 - s) * (t - P.that S)) ^ 2 < (t - P.that S) ^ 2 := by
        have hne2 : (0:ℝ) < (t - P.that S) ^ 2 := by
          have hxne : t - P.that S ≠ 0 := by
            rw [hu] at hu0; intro h; exact hu0 (by linarith)
          positivity
        have hfac : (1 - s) ^ 2 < 1 := by nlinarith [hs0, hs1]
        calc ((1 - s) * (t - P.that S)) ^ 2 = (1 - s) ^ 2 * (t - P.that S) ^ 2 := by ring
          _ < 1 * (t - P.that S) ^ 2 := mul_lt_mul_of_pos_right hfac hne2
          _ = (t - P.that S) ^ 2 := by ring
      have hmul : P.kappa S * ((1 - s) * (t - P.that S)) ^ 2
          < P.kappa S * (t - P.that S) ^ 2 := mul_lt_mul_of_pos_left hlt hκT
      rw [← hTie]
      linarith [e, e2, hmul]
    · have hb := phi_shift_le (P := P) (S := S) (t := t) (u := u) hs0.le hs1
      have hΛS : P.kappa S * (2 * |t - P.that S| + |u|) ≤ Λ :=
        Finset.le_sup' (α := ℝ) (fun S => P.kappa S * (2 * |t - P.that S| + |u|)) hS
      have hgap : P.phi S t ≤ P.Phi k t - ρ := by
        rw [hρ]
        have hle2 : P.phi S t ≤ (adm ι k).sup' (adm_nonempty k)
            (fun S => if S = T then 0 else P.phi S t) := by
          have h0 := Finset.le_sup' (α := ℝ)
            (fun S' => if S' = T then 0 else P.phi S' t) hS
          rw [if_neg hST] at h0
          exact h0
        linarith
      have hmono : s * |u| * (P.kappa S * (2 * |t - P.that S| + |u|))
          ≤ s * |u| * Λ := by
        apply mul_le_mul_of_nonneg_left hΛS
        positivity
      have : s * |u| * Λ = s * (|u| * Λ) := by ring
      linarith [hb, hgap, hmono, hsρ, this]
  exact absurd (hmin (t + s * u)) (by linarith)

/-- Следствие: при единственности top-k сертификат точен, `Φ(t̂) = OPT`. -/
theorem tight_of_unique {T : Finset ι}
    (hmin : ∀ t' : ℝ, P.Phi k t ≤ P.Phi k t')
    (hT : T ∈ adm ι k) (hTie : P.phi T t = P.Phi k t)
    (huniq : ∀ S ∈ adm ι k, S ≠ T → P.phi S t < P.Phi k t) :
    P.Phi k t = P.OPTv k :=
  tight_iff.mpr ⟨T, hT, hTie, that_eq_of_unique hmin hT hTie huniq⟩

end OneFactor

end SparseSharpe
