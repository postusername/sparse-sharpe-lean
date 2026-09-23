import SparseSharpe.Factor.Clipped

set_option linter.style.header false

/-!
# Теорема U: фильтр по знаку в неподвижной точке снимает вытеснение

Вся линия §§10–13 заметки `theory_note_v5.md` строила фильтр динамики по **узлу**:
актив допускается, если `r_i(t) ≥ ρ`. Два контрпримера пережали эту линию с двух
сторон: `Ex125` (§13.3) — узел рядом с `t̂` не допускает весь оптимум, `Ex135`
(§13.5) — в далёком узле вытеснение из корзины может стоить почти всего значения.

Здесь — выход: фильтровать надо **не по узлу, а по знаку невязки в неподвижной
точке**, и тогда никакого запаса `ρ` не нужно вовсе.

Ключевое наблюдение в одну строку: **у точных соседей по корзине одна и та же
неподвижная точка**. Если `mom_R(t,·) = mom_S(t,·)` и `gram_R = gram_S`, то
`φ_R − φ_S` — константа (`phi_eq_add_const`), поэтому `mom_R(u,·) = mom_S(u,·)`
при **любом** `u`, и в частности `t̂_S` удовлетворяет нормальным уравнениям и
для `R`. Значит, если динамика допускает только активы с `r_i(t̂_S) ≥ 0`, то
всякий сосед по корзине **самосогласован по построению**:

    F_LO(R) = F(R̄) = F(S̄) + (Q_t(R) − Q_t(S))  ≥  F_LO(S) .

Ни зажатия, ни сертификата Теоремы L, ни порога `ρ` — ничего этого не нужно.
Цена: точка `t̂_S` неизвестна и её приходится угадывать по сетке; `Ex135` при
этом перестаёт быть контрпримером (в нём нарушитель имеет `r(t̂) < 0`, то есть
фильтр его не пропустит), а `Ex125` — тоже (там все невязки в `t̂` положительны,
и запас не требуется).

**Что остаётся открытым** после этой теоремы, сказано в `theory_note_v6.md`,
§§4.3–4.4. Теорема U требует, чтобы фильтр стоял ровно в неподвижной точке `t̂`,
а алгоритм может поставить его только в узле сетки `τ ≈ t̂` (и ключ динамики к
тому же округлён). Поэтому нарушители всё-таки возникают, но неглубокие:
`|r_i(t̂_R)| ≤ √(h_i·зазор)` (`Factor/Leverage.lean`, `sq_dotp_le_lev_mul_gram`),
а цена выбрасывания — `r²/(1−h_i)` (`phi_erase_cost_le_of_lev`). Нелипкие строки
(`h_i ≤ 1−θ`) стоят `≤ зазор/θ` каждая и поглощаются калибровкой; липких по
бюджету плеч меньше `K/(1−θ)` (`card_sticky_le`), и **для них цена достигается**
— §4.4 заметки строит явный инстанс. Это и есть весь остаток.
-/

namespace SparseSharpe.Factor

open Finset

variable {ι κ : Type*} [Fintype κ]
variable {a : ι → κ → ℝ} {y : ι → ℝ} {cl : ι → Bool} {S R : Finset ι} {t th : κ → ℝ}

/-- **Первый момент соседей по корзине совпадает в любой точке, а не только в узле.**

Из `phi_eq_add_const`: `φ_R − φ_S` не зависит от точки, поэтому у разложений
`phi_shift` в произвольной точке `u` совпадают и линейные члены. -/
theorem mom_eq_of_bucket (hMom : ∀ v, mom a y R t v = mom a y S t v)
    (hK : ∀ v, gram a R v = gram a S v) (u v : κ → ℝ) :
    mom a y R u v = mom a y S u v := by
  have hR := phi_shift a y R u v
  have hS := phi_shift a y S u v
  have c1 := phi_eq_add_const hMom hK (u + v)
  have c2 := phi_eq_add_const hMom hK u
  have hKv := hK v
  linarith [hR, hS, c1, c2, hKv]

/-- **У соседей по корзине одна и та же неподвижная точка.** -/
theorem isNormal_of_bucket (hMom : ∀ v, mom a y R t v = mom a y S t v)
    (hK : ∀ v, gram a R v = gram a S v) (hnormS : IsNormal a y S th) :
    IsNormal a y R th := fun v => by
  rw [mom_eq_of_bucket hMom hK th v]; exact hnormS v

/-- Прибавка к значению равна прибавке к `Q` в узле: `F(R̄) − F(S̄) = Q_t(R) − Q_t(S)`. -/
theorem phi_normal_sub_eq (hMom : ∀ v, mom a y R t v = mom a y S t v)
    (hK : ∀ v, gram a R v = gram a S v) :
    phi a y R th - phi a y S th = phi a y R t - phi a y S t := by
  have := phi_eq_add_const hMom hK th
  linarith

/-- **Теорема U.** Пусть

* `t̂` — неподвижная точка набора `S`, и `S` самосогласован в ней;
* `R` — точный сосед `S` по корзине в узле `t` (те же `mom` и `gram`) с не меньшим `Q`;
* **все активы `R` имеют неотрицательную невязку в `t̂`** (фильтр по знаку — без запаса).

Тогда `F_LO(S)` и `F_LO(R)` — это в точности `φ_S(t̂)` и `φ_R(t̂)`, и
`F_LO(S) ≤ F_LO(R)`. Вытеснение из корзины безвредно.

Фильтр по знаку существен: без него заключение неверно — см. `example` ниже
и `Factor/Ex135.lean`. -/
theorem psiC_min_le_of_active_bucket
    (hQ : phi a y S t ≤ phi a y R t)
    (hMom : ∀ v, mom a y R t v = mom a y S t v)
    (hK : ∀ v, gram a R v = gram a S v)
    (hnormS : IsNormal a y S th)
    (hselfS : ∀ i ∈ S, cl i → 0 ≤ y i - dotp (a i) th)
    (hactR : ∀ i ∈ R, cl i → 0 ≤ y i - dotp (a i) th) :
    IsLeast {z : ℝ | ∃ t', z = psiC a y cl S t'} (phi a y S th)
    ∧ IsLeast {z : ℝ | ∃ t', z = psiC a y cl R t'} (phi a y R th)
    ∧ phi a y S th ≤ phi a y R th := by
  refine ⟨isLeast_psiC_of_selfconsistent hnormS hselfS,
    isLeast_psiC_of_selfconsistent (isNormal_of_bucket hMom hK hnormS) hactR, ?_⟩
  have := phi_normal_sub_eq (a := a) (y := y) (t := t) (th := th) hMom hK
  linarith

/-! ### Непустота гипотез и существенность фильтра

Первый `example` — гипотезы выполнимы (берём `R = S`, одна строка `a = (1)`,
`y = 1`, `t̂ = 1`). Второй показывает, что гипотеза `hactR` **не автоматична**:
у строк `a₁ = a₂ = 1`, `y = (0, 2)` точка `t̂ = 1` удовлетворяет нормальным
уравнениям, но `r₁(t̂) = −1 < 0`. Что при нарушении `hactR` ломается и само
заключение, показывает `Factor/Ex135.lean`: там `F_LO(R) = 25/17` строго меньше
`F_LO(A) ≥ 60/13`, хотя все прочие гипотезы Теоремы U выполнены. -/

/-- (а) Гипотезы выполнимы: `S = R`, одна строка `a = (1)`, `y = 1`, `t̂ = 1`. -/
example :
    IsNormal (ι := Fin 1) (κ := Fin 1) (fun _ _ => 1) (fun _ => 1) Finset.univ
        (fun _ => 1)
    ∧ (∀ i ∈ (Finset.univ : Finset (Fin 1)), (fun _ : Fin 1 => true) i →
        0 ≤ (fun _ : Fin 1 => (1:ℝ)) i
          - dotp ((fun _ _ => (1:ℝ)) i : Fin 1 → ℝ) (fun _ => (1:ℝ))) := by
  constructor
  · intro v; simp [mom, dotp]
  · intro i _ _; simp [dotp]

/-- (б) Фильтр по знаку существен: у строк `a₁ = a₂ = 1`, `y = (0,2)` точка
`t̂ = 1` удовлетворяет нормальным уравнениям, но невязка первой строки в ней
отрицательна — гипотеза `hactR` нарушена, и `R` не самосогласован. -/
example :
    IsNormal (ι := Fin 2) (κ := Fin 1) (fun _ _ => 1)
        (fun i => if i = 0 then (0:ℝ) else 2) Finset.univ (fun _ => 1)
    ∧ ¬ (∀ i ∈ (Finset.univ : Finset (Fin 2)), (fun _ : Fin 2 => true) i →
        0 ≤ (fun i => if i = 0 then (0:ℝ) else 2) i
          - dotp ((fun _ _ => (1:ℝ)) i : Fin 1 → ℝ) (fun _ => (1:ℝ))) := by
  constructor
  · intro v; simp [mom, dotp, Fin.sum_univ_two]; ring
  · intro hcon
    have h := hcon 0 (Finset.mem_univ 0) rfl
    simp [dotp] at h
    linarith

end SparseSharpe.Factor
