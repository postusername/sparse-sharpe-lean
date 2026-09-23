import SparseSharpe.Factor.Clipped
import SparseSharpe.Factor.MaxVolume

set_option linter.style.header false

/-!
# Потеря от зажатия в узле максимально-объёмной сетки

Это недостающее звено между зажатой задачей (`Factor/Clipped.lean`) и сеткой
Теоремы H (`Factor/MaxVolume.lean`, `Factor/GridK.lean`).

Ситуация. `A*` — носитель оптимального long-only портфеля; в точке `t̂ = t*` все его
невязки неотрицательны, поэтому `ψ_{Ā*}(t̂) = φ_{Ā*}(t̂) = OPT_LO`. В узле `t`
некоторые строки `A*` могут стать неактивными (`r_i(t) < 0`), и тогда зажатое `Q`,
которое считает динамика, меньше незажатого `φ_{Ā*}(t)`.

Утверждение `phi_sub_psiC_le_at_node`: эта разница не больше `|S|·K·gramK(t−t̂)`.
Иначе говоря, при `gramK(t−t̂) ≤ εF/C` (что и обеспечивает сетка) потеря не
превосходит `|S|K·εF/C`, то есть имеет тот же порядок `εF`, что и сам зазор узла.
Существенно, что **никакой зависимости от `‖a_i‖` тут нет**: правило Крамера
(`sq_dotp_le_card_mul_gramK`) даёт поточечную оценку `⟨a_i, t−t̂⟩² ≤ K·gramK(t−t̂)`.

Это закрывает «количественную» часть зазора (i) из `theory_note_v5.md`, §7.2:
вклад выпавших строк в `Q` контролируется. Нерешённым остаётся их вклад в форму
Грама (`Σ ⟨a_i,v⟩²` по выпавшим строкам), где такой оценки нет.
-/

namespace SparseSharpe.Factor

open Finset Matrix

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {cl : ι → Bool} {S : Finset ι} {T : κ → ι}
variable {t th : κ → ℝ}

/-- Невязка, сменившая знак между `t̂` и узлом `t`, по модулю не больше приращения. -/
lemma sq_res_le_sq_dotp {i : ι} (hth : 0 ≤ y i - dotp (a i) th)
    (ht : y i - dotp (a i) t < 0) :
    (y i - dotp (a i) t) ^ 2 ≤ (dotp (a i) (t - th)) ^ 2 := by
  have hsub : dotp (a i) (t - th) = dotp (a i) t - dotp (a i) th := dotp_sub _ _ _
  rw [hsub]
  nlinarith

/-- **Потеря от зажатия в узле.**

`φ_S(t) − ψ_S(t) ≤ |S| · K · gramK(t − t̂)` — при условии, что каждая зажатая строка,
ставшая в узле неактивной, была активна в `t̂`. Величина `gramK(t − t̂)` — это ровно
то, что ограничивает сетка Теоремы H. -/
theorem phi_sub_psiC_le_at_node (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0)
    (hres : ∀ i ∈ S, cl i → y i - dotp (a i) t < 0 → 0 ≤ y i - dotp (a i) th) :
    phi a y S t - psiC a y cl S t
      ≤ S.card * ((Fintype.card κ : ℝ) * gramK a T (t - th)) := by
  refine phi_sub_psiC_le ?_ ?_
  · exact mul_nonneg (Nat.cast_nonneg _) (gramK_nonneg a T (t - th))
  · intro i hi hc hlt
    calc (y i - dotp (a i) t) ^ 2
        ≤ (dotp (a i) (t - th)) ^ 2 := sq_res_le_sq_dotp (hres i hi hc hlt) hlt
      _ ≤ (Fintype.card κ : ℝ) * gramK a T (t - th) :=
          sq_dotp_le_card_mul_gramK hmax hdet hi _

/-- Версия с явной сеточной оценкой: `gramK(t−t̂) ≤ εF/C` даёт потерю `≤ |S|K·εF/C`. -/
theorem phi_sub_psiC_le_of_grid (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0)
    (hres : ∀ i ∈ S, cl i → y i - dotp (a i) t < 0 → 0 ≤ y i - dotp (a i) th)
    {ε F C : ℝ} (hC : 0 < C) (hε : 0 ≤ ε) (hF : 0 ≤ F)
    (hh : gramK a T (t - th) ≤ ε * F / C) :
    phi a y S t - psiC a y cl S t ≤ S.card * ((Fintype.card κ : ℝ) * (ε * F / C)) := by
  refine le_trans (phi_sub_psiC_le_at_node hmax hdet hres) ?_
  have hK : (0 : ℝ) ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh hK) (Nat.cast_nonneg _)

/-! ### Теорема O: ближайший узел (`theory_note_v5.md`, §10)

Если узел — ближайший к `t*` (смещение по каждой координате `K`-ки не больше `h`)
и у всех активов `A*` невязка в `t*` не меньше `ρ + σ`, где
`σ² = |Ā*|·K²·h²` — оценка сверху на `gram_{Ā*}(t−t*)`, то

  (a) весь `A*` допущен в узле: `r_i(t) ≥ ρ`;
  (b) `gram_{Ā*}(t−t*) ≤ σ²`.

Из (b) следует `Q_t(A*) − F(Ā*) ≤ σ²`: вытеснивший `A*` из корзины набор `R`
имеет тот же зазор, значит при `σ ≤ ρ` проходит сертификат Теоремы L, и по
`psiC_min_le_of_bucket_of_certificate` его long-only значение не меньше.
Численно: `code/check_lo_theoremO.py` — (a) и (b) верны в 100 % случаев при
выполненной гипотезе, и алгоритм там точен. -/

/-- Ближайший узел: `gramK_T(v) ≤ K·h²`, если каждая координата смещена на `≤ h`. -/
theorem gramK_le_of_coords (hb : ∀ l, |dotp (a (T l)) v| ≤ h) :
    gramK a T v ≤ (Fintype.card κ : ℝ) * h ^ 2 := by
  have hterm : ∀ l : κ, (dotp (a (T l)) v) ^ 2 ≤ h ^ 2 := by
    intro l
    have := hb l
    nlinarith [abs_nonneg (dotp (a (T l)) v), sq_abs (dotp (a (T l)) v)]
  calc gramK a T v = ∑ l, (dotp (a (T l)) v) ^ 2 := rfl
    _ ≤ ∑ _l : κ, h ^ 2 := Finset.sum_le_sum fun l _ => hterm l
    _ = (Fintype.card κ : ℝ) * h ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]; rfl

/-- **Теорема O(b).** `gram_{S}(v) ≤ |S|·K²·h²` для ближайшего узла. -/
theorem gram_le_of_nearest_node (hmax : MaxVol a S T) (hdet : (rowMat a T).det ≠ 0)
    (hb : ∀ l, |dotp (a (T l)) v| ≤ h) :
    gram a S v ≤ (S.card : ℝ) * (Fintype.card κ : ℝ) ^ 2 * h ^ 2 := by
  have h1 := gram_le_card_mul_gramK hmax hdet v
  have h2 := gramK_le_of_coords (a := a) (T := T) (v := v) (h := h) hb
  have hc : (0:ℝ) ≤ (S.card * Fintype.card κ : ℝ) := by positivity
  calc gram a S v ≤ (S.card * Fintype.card κ : ℝ) * gramK a T v := h1
    _ ≤ (S.card * Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) * h ^ 2) :=
        mul_le_mul_of_nonneg_left h2 hc
    _ = (S.card : ℝ) * (Fintype.card κ : ℝ) ^ 2 * h ^ 2 := by push_cast; ring

/-- **Теорема O(a).** Запас `ρ + σ` в `t*` переживает переход в узел с
`gram_S(t − t̂) ≤ σ²`: невязка в узле остаётся не меньше `ρ`. -/
theorem res_ge_of_gram_le {i : ι} (hi : i ∈ S) {ρ σ : ℝ} (hσ : 0 ≤ σ)
    (hgram : gram a S (t - th) ≤ σ ^ 2)
    (hmargin : ρ + σ ≤ y i - dotp (a i) th) :
    ρ ≤ y i - dotp (a i) t := by
  have hsingle : (dotp (a i) (t - th)) ^ 2 ≤ gram a S (t - th) := sq_dotp_le_gram hi _
  have hle : (dotp (a i) (t - th)) ^ 2 ≤ σ ^ 2 := le_trans hsingle hgram
  have hbnd : dotp (a i) (t - th) ≤ σ := by nlinarith
  have hsub : dotp (a i) (t - th) = dotp (a i) t - dotp (a i) th := dotp_sub _ _ _
  rw [hsub] at hbnd
  linarith

/-! ### Непустота гипотез

Гипотезы `phi_sub_psiC_le_at_node` — это `MaxVol a S T`, `det (rowMat a T) ≠ 0`
и `hres`. Ниже: (а) конкретные `a, S, T`, для которых первые две выполнены
**одновременно**; (б) достаточное условие для `hres`. -/

/-- (а) Одна строка `a = (1)`, `S = univ`, `T` — она же: `MaxVol` и `det ≠ 0`. -/
example :
    MaxVol (ι := Fin 1) (κ := Fin 1) (fun _ _ => 1) Finset.univ (fun _ => 0)
    ∧ (rowMat (ι := Fin 1) (κ := Fin 1) (fun _ _ => 1) (fun _ => 0)).det ≠ 0 := by
  refine ⟨⟨fun l => Finset.mem_univ _, fun T' _ => ?_⟩, ?_⟩
  · have hT : T' = (fun _ => (0 : Fin 1)) := by funext l; exact Subsingleton.elim _ _
    rw [hT]
  · simp [rowMat, Matrix.det_fin_one]

/-- (б) `hres` выполняется, когда в `t̂` неотрицательны **все** зажатые невязки —
именно этот случай возникает для носителя `A*` оптимального long-only портфеля
(`Factor/LongOnlyK.lean`, `wclip_eq_of_kkt`). -/
example (h : ∀ i ∈ S, cl i → 0 ≤ y i - dotp (a i) th) :
    ∀ i ∈ S, cl i → y i - dotp (a i) t < 0 → 0 ≤ y i - dotp (a i) th :=
  fun i hi hc _ => h i hi hc

end SparseSharpe.Factor
