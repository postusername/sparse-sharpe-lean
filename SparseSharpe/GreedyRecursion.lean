import Mathlib

set_option linter.style.header false

/-!
# Рекурсия Das–Kempe: от пошаговой оценки к `(1 − e^{−γ})`

Теорема A опирается на Theorem 6 Das–Kempe: жадный алгоритм с отношением
субмодулярности `γ` даёт `f(S_k) ≥ (1 − e^{−γ})·f(S*)`. Содержательная часть
(оценка `γ ≥ λ_min(R; 2k)` через ККТ и две оценки прироста) формализована
в `Greedy.lean`. Здесь — оставшееся звено: чистая индукция, переводящая
пошаговое неравенство

    f(S*) − f(S_{j+1}) ≤ (1 − γ/k)·(f(S*) − f(S_j))

в итоговую гарантию. Ничего специфичного для задачи здесь нет.
-/

namespace SparseSharpe

/-- Геометрическое убывание невязки. -/
theorem gap_geometric {g : ℕ → ℝ} {V q : ℝ} (hq : 0 ≤ q)
    (hstep : ∀ j, V - g (j + 1) ≤ q * (V - g j)) (k : ℕ) :
    V - g k ≤ q ^ k * (V - g 0) := by
  induction k with
  | zero => simp
  | succ n ih =>
    calc V - g (n + 1) ≤ q * (V - g n) := hstep n
      _ ≤ q * (q ^ n * (V - g 0)) := by
          exact mul_le_mul_of_nonneg_left ih hq
      _ = q ^ (n + 1) * (V - g 0) := by ring

/-- `(1 − γ/k)^k ≤ e^{−γ}` при `0 ≤ γ ≤ k`. -/
theorem one_sub_div_pow_le_exp_neg {γ : ℝ} {k : ℕ} (hk : 0 < k) (_hγ : 0 ≤ γ)
    (hγk : γ ≤ k) : (1 - γ / k) ^ k ≤ Real.exp (-γ) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hbase : (0:ℝ) ≤ 1 - γ / k := by
    have : γ / k ≤ 1 := (div_le_one hk').mpr hγk
    linarith
  have hle : 1 - γ / k ≤ Real.exp (-(γ / k)) := by
    have := Real.add_one_le_exp (-(γ / k))
    linarith
  calc (1 - γ / k) ^ k ≤ (Real.exp (-(γ / k))) ^ k := by
        exact pow_le_pow_left₀ hbase hle k
    _ = Real.exp (-(γ / k) * k) := by
        rw [← Real.exp_nat_mul]; ring_nf
    _ = Real.exp (-γ) := by
        congr 1
        field_simp

/-- **Рекурсия Das–Kempe.** Если `f(S_0) = 0`, `f(S*) = V ≥ 0` и на каждом шаге
невязка сжимается в `(1 − γ/k)` раз, то `f(S_k) ≥ (1 − e^{−γ})·V`. -/
theorem greedy_guarantee {g : ℕ → ℝ} {V γ : ℝ} {k : ℕ} (hk : 0 < k)
    (hγ : 0 ≤ γ) (hγk : γ ≤ k) (hV : 0 ≤ V) (h0 : g 0 = 0)
    (hstep : ∀ j, V - g (j + 1) ≤ (1 - γ / k) * (V - g j)) :
    (1 - Real.exp (-γ)) * V ≤ g k := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hbase : (0:ℝ) ≤ 1 - γ / k := by
    have : γ / k ≤ 1 := (div_le_one hk').mpr hγk
    linarith
  have hgeo := gap_geometric (g := g) (V := V) (q := 1 - γ / k) hbase hstep k
  rw [h0, sub_zero] at hgeo
  have hexp : (1 - γ / k) ^ k ≤ Real.exp (-γ) := one_sub_div_pow_le_exp_neg hk hγ hγk
  have : (1 - γ / k) ^ k * V ≤ Real.exp (-γ) * V :=
    mul_le_mul_of_nonneg_right hexp hV
  linarith


/-! ### Сборка: от свойств жадного шага к пошаговому сжатию -/

variable {ι : Type*} [DecidableEq ι]

/-- **Шаг жадного алгоритма сжимает невязку.** Гипотезы:
* `hgreedy` — шаг жадного не хуже любого одиночного добавления;
* `hmono` — значение вдоль жадной последовательности не убывает;
* `hratio` — определение отношения субмодулярности `γ` (Das–Kempe, Def. 2)
  вместе с монотонностью `f`;
* `hcard` — `|S*| ≤ k`.

Вывод — ровно гипотеза `hstep` теоремы `greedy_guarantee`. -/
theorem greedy_step {f : Finset ι → ℝ} {k : ℕ} (hk : 0 < k) {Sstar : Finset ι}
    (hcard : Sstar.card ≤ k) {γ : ℝ} {S : ℕ → Finset ι}
    (hgreedy : ∀ j, ∀ i : ι, f (insert i (S j)) - f (S j) ≤ f (S (j + 1)) - f (S j))
    (hmono : ∀ j, f (S j) ≤ f (S (j + 1)))
    (hratio : ∀ j, γ * (f Sstar - f (S j))
      ≤ ∑ i ∈ Sstar, (f (insert i (S j)) - f (S j))) (j : ℕ) :
    f Sstar - f (S (j + 1)) ≤ (1 - γ / k) * (f Sstar - f (S j)) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hgain : 0 ≤ f (S (j + 1)) - f (S j) := by linarith [hmono j]
  have hsum : ∑ i ∈ Sstar, (f (insert i (S j)) - f (S j))
      ≤ (Sstar.card : ℝ) * (f (S (j + 1)) - f (S j)) := by
    calc ∑ i ∈ Sstar, (f (insert i (S j)) - f (S j))
        ≤ ∑ _i ∈ Sstar, (f (S (j + 1)) - f (S j)) :=
          Finset.sum_le_sum fun i _ => hgreedy j i
      _ = (Sstar.card : ℝ) * (f (S (j + 1)) - f (S j)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard' : (Sstar.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hcard
  have hk_bound : (Sstar.card : ℝ) * (f (S (j + 1)) - f (S j))
      ≤ (k : ℝ) * (f (S (j + 1)) - f (S j)) :=
    mul_le_mul_of_nonneg_right hcard' hgain
  have hkey : γ * (f Sstar - f (S j)) ≤ (k : ℝ) * (f (S (j + 1)) - f (S j)) := by
    linarith [hratio j, hsum, hk_bound]
  have hdiv : (γ / k) * (f Sstar - f (S j)) ≤ f (S (j + 1)) - f (S j) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hk']
    linarith [hkey]
  nlinarith [hdiv]

/-- **Теорема 6 Das–Kempe (абстрактная форма).** Жадный алгоритм с отношением
субмодулярности `γ` даёт `f(S_k) ≥ (1 − e^{−γ})·f(S*)`. -/
theorem greedy_theorem {f : Finset ι → ℝ} {k : ℕ} (hk : 0 < k) {Sstar : Finset ι}
    (hcard : Sstar.card ≤ k) {γ : ℝ} (hγ : 0 ≤ γ) (hγk : γ ≤ k)
    (hV : 0 ≤ f Sstar) {S : ℕ → Finset ι} (h0 : f (S 0) = 0)
    (hgreedy : ∀ j, ∀ i : ι, f (insert i (S j)) - f (S j) ≤ f (S (j + 1)) - f (S j))
    (hmono : ∀ j, f (S j) ≤ f (S (j + 1)))
    (hratio : ∀ j, γ * (f Sstar - f (S j))
      ≤ ∑ i ∈ Sstar, (f (insert i (S j)) - f (S j))) :
    (1 - Real.exp (-γ)) * f Sstar ≤ f (S k) :=
  greedy_guarantee (g := fun j => f (S j)) (V := f Sstar) hk hγ hγk hV h0
    (greedy_step hk hcard hgreedy hmono hratio)

end SparseSharpe
