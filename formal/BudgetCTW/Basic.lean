/-
Кодовая длина и общие соглашения формализации.

Постановка П4 меряет всё в битах: `L = −log₂ P`. В Lean удобнее доказывать
мультипликативные неравенства на вероятностях, а в логарифмы переходить один
раз в конце — поэтому здесь только определение `L` и переходные леммы.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace BudgetCTW

/-- Кодовая длина в битах: `L p = −log₂ p`. -/
noncomputable def L (p : ℝ) : ℝ := -Real.logb 2 p

@[simp] lemma L_one : L 1 = 0 := by simp [L]

/-- Бо́льшая вероятность — более короткий код. -/
lemma L_antitone {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) : L q ≤ L p := by
  have h : Real.logb 2 p ≤ Real.logb 2 q :=
    Real.logb_le_logb_of_le (by norm_num) hp hpq
  simp only [L]
  linarith

/-- Произведение вероятностей — сумма кодовых длин. -/
lemma L_mul {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) : L (p * q) = L p + L q := by
  simp only [L, Real.logb_mul hp hq]
  ring

/-- Множитель `2 ^ n` стоит ровно `n` бит. -/
lemma L_two_pow (n : ℕ) : L ((2 : ℝ) ^ n) = -(n : ℝ) := by
  simp only [L, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  ring

lemma L_two_pow_mul {p : ℝ} (hp : 0 < p) (n : ℕ) :
    L ((2 : ℝ) ^ n * p) = -(n : ℝ) + L p := by
  rw [L_mul (by positivity) (ne_of_gt hp), L_two_pow]

end BudgetCTW
