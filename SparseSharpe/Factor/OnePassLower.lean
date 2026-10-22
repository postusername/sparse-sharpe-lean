import SparseSharpe.Factor.LongOnlyK
import SparseSharpe.Factor.SchemeLS

set_option linter.style.header false

/-!
# Один проход не обходится ни без `M`, ни без `ω` (`K ≥ 2` факторов)

Явная серия примеров с `K + 1` факторами, `Σ_f = I`, `d = 1`.
* «Алиса»: `n^K` активов `g ∈ {0,…,n−1}^K` с `m_g = 0` и нагрузками `B_g = A·(1, g/n)`.
* «Боб» с индексом `h`: один актив (`none`) с `m = 1` и нагрузками `−B_h`.

Пара `{h, Боб}` с весами `1/2` — точный хедж: факторная экспозиция нулевая, цель `1/2`
(`lb_pair_obj`). Любой носитель из не более чем двух активов **без** `h` даёт цель не больше
`2n²/A²` — и long-only, и long-short (`lb_obj_le`): двойственная функция в точке, где обе невязки
обнуляются, равна квадрату нормы этой точки. Поэтому при `4n² < (1 − ε)A²` каждый
`(1 − ε)`-оптимальный носитель с не более чем двумя именами содержит `h`
(`lb_mem_of_good`).

Следствие для схем, строящих семейство **за один проход** по активам (`onepass_lower`): если
после активов Алисы схема хранит множество `keep` из них (оно не зависит от того, какой актив
придёт потом), а каждый кандидат собран из хранимых активов и активов, пришедших позже, то
`keep` — все `n^K` активов Алисы. Здесь `M = n^K + 1`, а плечи `ω_g = A²(1 + |g/n|²) ≤ (K+1)A²`
(`lb_leverage_le`); при `A² = 8n²/(1 − ε)` память не меньше `min(M − 1, c·ω^{K/2})`.
-/

namespace SparseSharpe.Factor

open Finset

section OnePassLower

variable {K n : ℕ}

/-- Единичная матрица. -/
def opI (κ : Type*) [DecidableEq κ] : κ → κ → ℝ := fun j j' => if j = j' then 1 else 0

lemma opI_hG (κ : Type*) [Fintype κ] [DecidableEq κ] :
    ∀ j j', ∑ l, opI κ l j * opI κ l j' = opI κ j j' := by
  intro j j'
  simp only [opI]
  rw [Finset.sum_eq_single j]
  · by_cases h : j = j' <;> simp [h]
  · intro b _ hb; simp [hb]
  · simp

lemma opI_hPS (κ : Type*) [Fintype κ] [DecidableEq κ] :
    ∀ j j', ∑ l, opI κ j l * opI κ l j' = if j = j' then 1 else 0 := by
  intro j j'
  simp only [opI]
  rw [Finset.sum_eq_single j]
  · by_cases h : j = j' <;> simp [h]
  · intro b _ hb; simp [Ne.symm hb]
  · simp

lemma sum_opI_mul {κ : Type*} [Fintype κ] [DecidableEq κ] (u v : κ → ℝ) :
    ∑ j, ∑ j', u j * (opI κ j j' * v j') = ∑ j, u j * v j := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j]
  · simp [opI]
  · intro b _ hb; simp [opI, Ne.symm hb]
  · simp

/-- Направление `(1, g/n)`. -/
noncomputable def lbDir (g : Fin K → Fin n) : Fin (K + 1) → ℝ :=
  Fin.cons (α := fun _ => ℝ) 1 (fun l => ((g l : ℕ) : ℝ) / (n : ℝ))

/-- Нагрузки: актив Алисы `some g` — `A·(1, g/n)`, актив Боба `none` — `−A·(1, h/n)`. -/
noncomputable def lbB (A : ℝ) (h : Fin K → Fin n) :
    Option (Fin K → Fin n) → Fin (K + 1) → ℝ
  | none => fun l => -(A * lbDir h l)
  | some g => fun l => A * lbDir g l

/-- Ожидаемые избыточные доходности: `1` у Боба, `0` у Алисы. -/
def lbm : Option (Fin K → Fin n) → ℝ
  | none => 1
  | some _ => 0

/-- Идиосинкратические дисперсии `d = 1`. -/
def lbd : Option (Fin K → Fin n) → ℝ := fun _ => 1

lemma lbd_pos : ∀ i : Option (Fin K → Fin n), 0 < lbd i := fun _ => one_pos

/-- Двойственная функция long-short примера: `Σ_{i∈S}(⟨B_i,t⟩ − m_i)² + |t|²`. -/
lemma lb_phi (A : ℝ) (h : Fin K → Fin n) (S : Finset (Option (Fin K → Fin n)))
    (t : Fin (K + 1) → ℝ) :
    phi (rowsK lbd (lbB A h) (opI (Fin (K + 1)))) (targetsK lbm lbd) (barK S) t
      = ∑ i ∈ S, (dotp (lbB A h i) t - lbm i) ^ 2 + ∑ l, t l ^ 2 := by
  simp only [phi, barK, Finset.sum_disjSum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [rowsK, targetsK, lbd, dotp]
  · refine Finset.sum_congr rfl fun l _ => ?_
    have : dotp (rowsK lbd (lbB A h) (opI (Fin (K + 1))) (Sum.inr l)) t = t l := by
      simp only [rowsK, Sum.elim_inr, dotp, opI]
      rw [Finset.sum_eq_single l]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    rw [this]; simp [targetsK]

/-- Точка с двумя ненулевыми координатами: `t_0 = x₀`, `t_{l+1} = x`. -/
noncomputable def lbT (x₀ : ℝ) (l : Fin K) (x : ℝ) : Fin (K + 1) → ℝ :=
  Fin.cons (α := fun _ => ℝ) x₀ (fun l' => if l' = l then x else 0)

lemma dotp_lbDir_lbT (g : Fin K → Fin n) (x₀ : ℝ) (l : Fin K) (x : ℝ) :
    dotp (lbDir g) (lbT x₀ l x) = x₀ + ((g l : ℕ) : ℝ) / (n : ℝ) * x := by
  simp only [dotp, Fin.sum_univ_succ, lbDir, lbT, Fin.cons_zero, Fin.cons_succ]
  simp [mul_ite]

lemma sum_sq_lbT (x₀ : ℝ) (l : Fin K) (x : ℝ) :
    ∑ l', lbT x₀ l x l' ^ 2 = x₀ ^ 2 + x ^ 2 := by
  simp only [Fin.sum_univ_succ, lbT, Fin.cons_zero, Fin.cons_succ]
  simp [ite_pow]

lemma dotp_lbB_some (A : ℝ) (h g : Fin K → Fin n) (t : Fin (K + 1) → ℝ) :
    dotp (lbB A h (some g)) t = A * dotp (lbDir g) t := by
  simp only [dotp, lbB, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma dotp_lbB_none (A : ℝ) (h : Fin K → Fin n) (t : Fin (K + 1) → ℝ) :
    dotp (lbB A h none) t = -(A * dotp (lbDir h) t) := by
  simp only [dotp, lbB, Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **Точный хедж.** `{h, Боб}` с весами `1/2`: цель `1/2`. -/
theorem lb_pair_obj (A : ℝ) (h : Fin K → Fin n) :
    objLO lbm lbd (lbB A h) (opI (Fin (K + 1))) {some h, none} (fun _ => 1 / 2) = 1 / 2 := by
  have hne : (some h : Option (Fin K → Fin n)) ≠ none := Option.some_ne_none h
  have hV : ∀ i i' : Option (Fin K → Fin n),
      ∑ j, ∑ j', lbB A h i j * (opI (Fin (K + 1)) j j' * lbB A h i' j')
        = ∑ j, lbB A h i j * lbB A h i' j := fun i i' => sum_opI_mul _ _
  simp only [objLO, Vmat, Finset.sum_pair hne, hV]
  simp only [lbB, lbm, lbd, hne, Ne.symm hne, ite_true, ite_false]
  have e1 : ∑ x, -(A * lbDir h x) * -(A * lbDir h x) = ∑ x, A * lbDir h x * (A * lbDir h x) :=
    Finset.sum_congr rfl fun _ _ => by ring
  have e2 : ∑ x, A * lbDir h x * -(A * lbDir h x) = -∑ x, A * lbDir h x * (A * lbDir h x) := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring
  have e3 : ∑ x, -(A * lbDir h x) * (A * lbDir h x) = -∑ x, A * lbDir h x * (A * lbDir h x) := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2, e3]
  ring

/-- **Цель любого `(S, w)` с `|S| ≤ 2` без `h` не больше `2n²/A²`** (веса любого знака). -/
theorem lb_obj_le (hn : 0 < n) {A : ℝ} (hA : 0 < A) (h : Fin K → Fin n)
    {S : Finset (Option (Fin K → Fin n))} (hS : S.card ≤ 2) (hhS : some h ∉ S)
    (w : Option (Fin K → Fin n) → ℝ) :
    objLO lbm lbd (lbB A h) (opI (Fin (K + 1))) S w ≤ 2 * (n : ℝ) ^ 2 / A ^ 2 := by
  have hwd := fun t => objLO_le_phi_free (m := lbm) (d := lbd) (B := lbB A h)
    (Sf := opI (Fin (K + 1))) (P := opI (Fin (K + 1))) (G := opI (Fin (K + 1)))
    lbd_pos (opI_hG _) (opI_hPS _) S w t
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbound_nonneg : (0 : ℝ) ≤ 2 * (n : ℝ) ^ 2 / A ^ 2 := by positivity
  by_cases hb : (none : Option (Fin K → Fin n)) ∈ S
  · -- `S = {Боб}` или `S = {Боб, g}`, `g ≠ h`
    by_cases hg : ∃ g, some g ∈ S
    · obtain ⟨g, hgS⟩ := hg
      have hgh : g ≠ h := by rintro rfl; exact hhS hgS
      have hSeq : S = {some g, none} := by
        have hsub : ({some g, none} : Finset _) ⊆ S := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        have hcard : ({some g, none} : Finset (Option (Fin K → Fin n))).card = 2 :=
          Finset.card_pair (Option.some_ne_none g)
        exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
      -- координата, в которой `g` и `h` различаются
      obtain ⟨l, hl⟩ : ∃ l, g l ≠ h l := by
        by_contra hcon
        exact hgh (funext fun l => by_contra fun hne => hcon ⟨l, hne⟩)
      set δ : ℝ := ((h l : ℕ) : ℝ) / (n : ℝ) - ((g l : ℕ) : ℝ) / (n : ℝ) with hδ
      have hδ1 : 1 / (n : ℝ) ≤ |δ| := by
        have hne : ((h l : ℕ) : ℝ) ≠ ((g l : ℕ) : ℝ) := by
          intro hc; apply hl; exact Fin.ext (by exact_mod_cast hc.symm)
        have h1 : (1 : ℝ) ≤ |((h l : ℕ) : ℝ) - ((g l : ℕ) : ℝ)| := by
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have : ((h l : ℕ) : ℝ) + 1 ≤ ((g l : ℕ) : ℝ) := by
              have := (Nat.cast_lt (α := ℝ)).mpr (show (h l : ℕ) < g l by exact_mod_cast hlt)
              exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast hlt)
            rw [abs_of_neg (by linarith)]; linarith
          · have : ((g l : ℕ) : ℝ) + 1 ≤ ((h l : ℕ) : ℝ) := by
              exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast hgt)
            rw [abs_of_pos (by linarith)]; linarith
        have : δ = (((h l : ℕ) : ℝ) - ((g l : ℕ) : ℝ)) / n := by rw [hδ]; ring
        rw [this, abs_div, abs_of_pos hnR]
        exact div_le_div_of_nonneg_right h1 hnR.le
      have hδne : δ ≠ 0 := by
        intro h0; rw [h0, abs_zero] at hδ1; have : (0:ℝ) < 1 / n := by positivity
        linarith
      -- точка: `⟨B_g,t⟩ = 0`, `⟨B_Боб,t⟩ = 1`
      set x : ℝ := -1 / (A * δ) with hx
      set x₀ : ℝ := -(((g l : ℕ) : ℝ) / (n : ℝ)) * x with hx₀
      have hdg : dotp (lbDir g) (lbT x₀ l x) = 0 := by
        rw [dotp_lbDir_lbT, hx₀]; ring
      have hdh : dotp (lbDir h) (lbT x₀ l x) = -1 / A := by
        rw [dotp_lbDir_lbT, hx₀]
        have : ((h l : ℕ) : ℝ) / (n : ℝ) * x - ((g l : ℕ) : ℝ) / (n : ℝ) * x = δ * x := by
          rw [hδ]; ring
        rw [show -(((g l : ℕ) : ℝ) / (n : ℝ)) * x + ((h l : ℕ) : ℝ) / (n : ℝ) * x = δ * x by
          linarith, hx]
        field_simp
      have hphi := lb_phi A h S (lbT x₀ l x)
      rw [hSeq, Finset.sum_pair (Option.some_ne_none g), sum_sq_lbT] at hphi
      have hsg : dotp (lbB A h (some g)) (lbT x₀ l x) - lbm (some g) = 0 := by
        rw [dotp_lbB_some, hdg]; simp [lbm]
      have hsb : dotp (lbB A h none) (lbT x₀ l x) - lbm (none : Option (Fin K → Fin n)) = 0 := by
        have h1 : -(A * (-1 / A)) = 1 := by field_simp
        rw [dotp_lbB_none, hdh, h1]; simp [lbm]
      rw [hsg, hsb] at hphi
      have hW := hwd (lbT x₀ l x)
      rw [hSeq] at hW ⊢
      rw [hphi] at hW
      -- `x₀² + x² ≤ 2/(Aδ)² ≤ 2n²/A²`
      have hgl : (((g l : ℕ) : ℝ) / (n : ℝ)) ^ 2 ≤ 1 := by
        have h0 : (0 : ℝ) ≤ ((g l : ℕ) : ℝ) / (n : ℝ) := by positivity
        have h1 : ((g l : ℕ) : ℝ) / (n : ℝ) ≤ 1 := by
          rw [div_le_one hnR]; exact_mod_cast (g l).isLt.le
        nlinarith
      have hx2 : x ^ 2 ≤ (n : ℝ) ^ 2 / A ^ 2 := by
        rw [hx, div_pow, neg_one_sq, mul_pow]
        have hδ2 : 1 / (n : ℝ) ^ 2 ≤ δ ^ 2 := by
          have := mul_le_mul hδ1 hδ1 (by positivity) (abs_nonneg _)
          rw [abs_mul_abs_self] at this
          calc 1 / (n : ℝ) ^ 2 = 1 / (n : ℝ) * (1 / n) := by ring
            _ ≤ δ * δ := this
            _ = δ ^ 2 := by ring
        have hA2 : 0 < A ^ 2 := by positivity
        have hd2 : 0 < δ ^ 2 := by positivity
        rw [div_le_div_iff₀ (by positivity) hA2]
        have : (1 : ℝ) ≤ (n : ℝ) ^ 2 * δ ^ 2 := by
          have := mul_le_mul_of_nonneg_left hδ2 (by positivity : (0:ℝ) ≤ (n : ℝ) ^ 2)
          rwa [mul_one_div_cancel (by positivity)] at this
        nlinarith
      have hx02 : x₀ ^ 2 ≤ x ^ 2 := by
        rw [hx₀, mul_pow, neg_sq]
        nlinarith [sq_nonneg x]
      have : (0 : ℝ) ^ 2 + 0 ^ 2 + (x₀ ^ 2 + x ^ 2) ≤ 2 * (n : ℝ) ^ 2 / A ^ 2 := by
        have : 2 * (n : ℝ) ^ 2 / A ^ 2 = (n : ℝ) ^ 2 / A ^ 2 + (n : ℝ) ^ 2 / A ^ 2 := by ring
        rw [this]; nlinarith
      linarith
    · -- `S = {Боб}`
      have hg : ∀ g, some g ∉ S := fun g hg2 => hg ⟨g, hg2⟩
      have hSeq : S = {none} := by
        ext x; constructor
        · intro hx; cases x with
          | none => simp
          | some g => exact absurd hx (hg g)
        · intro hx; rw [Finset.mem_singleton] at hx; rw [hx]; exact hb
      have h0 : (0 : ℕ) < K + 1 := Nat.succ_pos K
      -- точка `t = −e₀/A`: невязка Боба `1 − ⟨B,t⟩ = 0`
      set t : Fin (K + 1) → ℝ := Fin.cons (α := fun _ => ℝ) (-1 / A) (fun _ => 0) with ht
      have hdh : dotp (lbDir h) t = -1 / A := by
        simp only [dotp, Fin.sum_univ_succ, lbDir, ht, Fin.cons_zero, Fin.cons_succ]; simp
      have hsum : ∑ l, t l ^ 2 = 1 / A ^ 2 := by
        simp only [Fin.sum_univ_succ, ht, Fin.cons_zero, Fin.cons_succ]; simp; ring
      have hW := hwd t
      rw [lb_phi A h S t, hSeq, Finset.sum_singleton, hsum, dotp_lbB_none, hdh] at hW
      have h1 : (-(A * (-1 / A)) - lbm (none : Option (Fin K → Fin n))) ^ 2 = 0 := by
        have : -(A * (-1 / A)) = 1 := by field_simp
        rw [this]; simp [lbm]
      rw [h1, zero_add] at hW
      have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      rw [hSeq]
      calc objLO lbm lbd (lbB A h) (opI (Fin (K + 1))) {none} w ≤ 1 / A ^ 2 := hW
        _ ≤ 2 * (n : ℝ) ^ 2 / A ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity); linarith
  · -- без Боба все `m_i = 0`: в точке `t = 0` двойственная функция равна нулю
    have hphi := lb_phi A h S 0
    have hz : ∀ i ∈ S, (dotp (lbB A h i) 0 - lbm i) ^ 2 = 0 := by
      intro i hi
      cases i with
      | none => exact absurd hi hb
      | some g => simp [dotp, lbm]
    rw [Finset.sum_eq_zero hz] at hphi
    have hW := hwd 0
    rw [hphi] at hW
    simp at hW
    linarith

/-- **Каждый `(1 − ε)`-хороший кандидат содержит `h`.** -/
theorem lb_mem_of_good (hn : 0 < n) {A ε : ℝ} (hA : 0 < A)
    (hAn : 4 * (n : ℝ) ^ 2 < (1 - ε) * A ^ 2) (h : Fin K → Fin n)
    {S : Finset (Option (Fin K → Fin n))} (hS : S.card ≤ 2) (w : Option (Fin K → Fin n) → ℝ)
    (hgood : (1 - ε) * objLO lbm lbd (lbB A h) (opI (Fin (K + 1))) {some h, none} (fun _ => 1 / 2)
      ≤ objLO lbm lbd (lbB A h) (opI (Fin (K + 1))) S w) :
    some h ∈ S := by
  by_contra hh
  have h1 := lb_obj_le hn hA h hS hh w
  rw [lb_pair_obj] at hgood
  have hA2 : 0 < A ^ 2 := by positivity
  have : 2 * (n : ℝ) ^ 2 / A ^ 2 < (1 - ε) * (1 / 2) := by
    rw [div_lt_iff₀ hA2]; nlinarith
  linarith

/-- **Нижняя оценка для схем в один проход.** `keep` — активы Алисы, которые схема хранит после
их прочтения (одно и то же множество при любом активе Боба, пришедшем потом); `out h` — кандидаты,
выданные после актива Боба `h`, все — из хранимых активов Алисы и актива Боба. Если для каждого
`h` среди кандидатов есть носитель с не более чем двумя именами и весами, чья цель не меньше
`1 − ε` от цели пары `{h, Боб}` (в частности, `(1 − ε)`-оптимальный, long-only или long-short),
то схема хранит **все** `n^K` активов Алисы. -/
theorem onepass_lower (hn : 0 < n) {A ε : ℝ} (hA : 0 < A)
    (hAn : 4 * (n : ℝ) ^ 2 < (1 - ε) * A ^ 2)
    (keep : Finset (Fin K → Fin n))
    (out : (Fin K → Fin n) → Finset (Finset (Option (Fin K → Fin n))))
    (hout : ∀ h, ∀ S ∈ out h, ∀ g, some g ∈ S → g ∈ keep)
    (hgood : ∀ h, ∃ S ∈ out h, S.card ≤ 2 ∧ ∃ w : Option (Fin K → Fin n) → ℝ,
      (1 - ε) * objLO lbm lbd (lbB A h) (opI (Fin (K + 1))) {some h, none} (fun _ => 1 / 2)
        ≤ objLO lbm lbd (lbB A h) (opI (Fin (K + 1))) S w) :
    keep = Finset.univ ∧ keep.card = n ^ K := by
  have hall : ∀ h, h ∈ keep := by
    intro h
    obtain ⟨S, hSo, hS, w, hw⟩ := hgood h
    exact hout h S hSo h (lb_mem_of_good hn hA hAn h hS w hw)
  have heq : keep = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
  refine ⟨heq, ?_⟩
  rw [heq, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- Плечи примера: `ω = B'Σ_fB/d ≤ (K + 1)A²` у каждого актива. -/
theorem lb_leverage_le (A : ℝ) (h : Fin K → Fin n) (i : Option (Fin K → Fin n)) :
    ∑ j, ∑ j', lbB A h i j * (opI (Fin (K + 1)) j j' * lbB A h i j') / lbd i
      ≤ (K + 1) * A ^ 2 := by
  have hdir : ∀ g : Fin K → Fin n, ∀ l, lbDir g l ^ 2 ≤ 1 := by
    intro g l
    refine Fin.cases ?_ (fun l' => ?_) l
    · simp [lbDir]
    · simp only [lbDir, Fin.cons_succ]
      by_cases hn : n = 0
      · subst hn; simp
      have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have h0 : (0 : ℝ) ≤ ((g l' : ℕ) : ℝ) / (n : ℝ) := by positivity
      have h1 : ((g l' : ℕ) : ℝ) / (n : ℝ) ≤ 1 := by
        rw [div_le_one hnR]; exact_mod_cast (g l').isLt.le
      nlinarith
  have hsum : ∀ g : Fin K → Fin n, ∑ l, (A * lbDir g l) ^ 2 ≤ (K + 1) * A ^ 2 := by
    intro g
    calc ∑ l, (A * lbDir g l) ^ 2 = ∑ l, A ^ 2 * lbDir g l ^ 2 :=
          Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ ∑ _l : Fin (K + 1), A ^ 2 * 1 :=
          Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hdir g l) (sq_nonneg A)
      _ = (K + 1) * A ^ 2 := by simp [Finset.sum_const, Finset.card_univ]
  have hlbd : lbd i = 1 := rfl
  simp only [hlbd, div_one]
  rw [sum_opI_mul]
  cases i with
  | none =>
    calc ∑ j, lbB A h none j * lbB A h none j = ∑ j, (A * lbDir h j) ^ 2 :=
          Finset.sum_congr rfl fun _ _ => by simp only [lbB]; ring
      _ ≤ _ := hsum h
  | some g =>
    calc ∑ j, lbB A h (some g) j * lbB A h (some g) j = ∑ j, (A * lbDir g j) ^ 2 :=
          Finset.sum_congr rfl fun _ _ => by simp only [lbB]; ring
      _ ≤ _ := hsum g

/-- **Гипотезы `onepass_lower` выполнимы.** Схема, хранящая всех Алисиных и выдающая пару
`{h, Боб}`, удовлетворяет `hout` и `hgood`; например, при `K = 1`, `n = 2`, `A = 6`, `ε = 1/2`
выполнено и `4n² < (1 − ε)A²`. -/
theorem onepass_instance :
    4 * ((2 : ℕ) : ℝ) ^ 2 < (1 - 1 / 2) * (6 : ℝ) ^ 2 ∧
    (∀ h : Fin 1 → Fin 2, ∀ S ∈ ({{some h, none}} : Finset (Finset (Option (Fin 1 → Fin 2)))),
      ∀ g, some g ∈ S → g ∈ (Finset.univ : Finset (Fin 1 → Fin 2))) ∧
    (∀ h : Fin 1 → Fin 2, ∃ S ∈ ({{some h, none}} : Finset (Finset (Option (Fin 1 → Fin 2)))),
      S.card ≤ 2 ∧ ∃ w : Option (Fin 1 → Fin 2) → ℝ,
        (1 - 1 / 2) * objLO lbm lbd (lbB 6 h) (opI (Fin (1 + 1))) {some h, none} (fun _ => 1 / 2)
          ≤ objLO lbm lbd (lbB 6 h) (opI (Fin (1 + 1))) S w) := by
  refine ⟨by norm_num, fun _ _ _ _ _ => Finset.mem_univ _, fun h => ?_⟩
  refine ⟨{some h, none}, Finset.mem_singleton_self _, ?_, fun _ => 1 / 2, ?_⟩
  · rw [Finset.card_pair (Option.some_ne_none h)]
  · rw [lb_pair_obj]; norm_num


/-- **Подсчёт.** При `A² = 8n²/(1 − ε)`, `ε < 1`, у каждого актива примера
`((1 − ε)·ω_i/(8(K + 1)))^{K/2} ≤ n^K`: схема хранит не меньше этой величины активов
(в статье `K + 1` факторов здесь — это `K`). -/
theorem lb_count {A ε : ℝ} (hε : ε < 1) (hA2 : A ^ 2 = 8 * (n : ℝ) ^ 2 / (1 - ε))
    (h : Fin K → Fin n) (i : Option (Fin K → Fin n)) :
    ((1 - ε) * (∑ j, ∑ j', lbB A h i j * (opI (Fin (K + 1)) j j' * lbB A h i j') / lbd i)
      / (8 * (K + 1))) ^ ((K : ℝ) / 2) ≤ (n : ℝ) ^ K := by
  have hom := lb_leverage_le A h i
  set ω := ∑ j, ∑ j', lbB A h i j * (opI (Fin (K + 1)) j j' * lbB A h i j') / lbd i with hω
  have hω0 : 0 ≤ ω := by
    have e : ω = ∑ j, lbB A h i j * lbB A h i j := by
      rw [hω]; simp only [lbd, div_one]; exact sum_opI_mul _ _
    rw [e]; exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have h1ε : 0 < 1 - ε := by linarith
  have hK : (0 : ℝ) < 8 * (K + 1) := by positivity
  have hx : (1 - ε) * ω / (8 * (K + 1)) ≤ (n : ℝ) ^ 2 := by
    rw [div_le_iff₀ hK]
    have h2 : ω ≤ (K + 1) * (8 * (n : ℝ) ^ 2 / (1 - ε)) := by rw [← hA2]; exact hom
    calc (1 - ε) * ω ≤ (1 - ε) * ((K + 1) * (8 * (n : ℝ) ^ 2 / (1 - ε))) :=
          mul_le_mul_of_nonneg_left h2 h1ε.le
      _ = (n : ℝ) ^ 2 * (8 * (K + 1)) := by field_simp
  have hx0 : 0 ≤ (1 - ε) * ω / (8 * (K + 1)) := by positivity
  calc ((1 - ε) * ω / (8 * (K + 1))) ^ ((K : ℝ) / 2)
      ≤ ((n : ℝ) ^ 2) ^ ((K : ℝ) / 2) := Real.rpow_le_rpow hx0 hx (by positivity)
    _ = (n : ℝ) ^ K := by
      rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_mul (by positivity)]
      rw [show ((2 : ℕ) : ℝ) * ((K : ℝ) / 2) = (K : ℝ) by push_cast; ring]
      exact Real.rpow_natCast _ K

end OnePassLower

end SparseSharpe.Factor
