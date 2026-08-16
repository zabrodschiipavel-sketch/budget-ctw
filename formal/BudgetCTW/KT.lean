/-
Оценщик Кричевского–Трофимова (1981).

Определяется замкнутой формой (а не последовательным произведением), потому
что тогда обе формулы обновления и — главное — тождество согласованности
`kt (a+1) b + kt a (b+1) = kt a b` доказываются одним `Finset.prod_range_succ`.

Тождество согласованности есть в точности инвариант `Σ_x P(x) = 1` на уровне
одного узла: то самое свойство, нарушение которого на этапе 4 выглядело как
«сжатие» 0.204 bpc (notes/stage4-results.md). В коде оно проверяется флагом
`--verify-sum`; здесь оно доказано.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace BudgetCTW

open Finset

/-- `ktUp n = ∏_{i<n} (2i+1)` — нечётный двойной факториал `(2n−1)!!`. -/
noncomputable def ktUp (n : ℕ) : ℝ := ∏ i ∈ range n, (2 * (i : ℝ) + 1)

/-- `ktDown n = ∏_{i<n} (2i+2) = 2ⁿ·n!`. -/
noncomputable def ktDown (n : ℕ) : ℝ := ∏ i ∈ range n, (2 * (i : ℝ) + 2)

/-- Вероятность KT для любой двоичной строки с `a` нулями и `b` единицами
(оценщик обменный, поэтому от порядка символов не зависит). -/
noncomputable def kt (a b : ℕ) : ℝ := ktUp a * ktUp b / ktDown (a + b)

lemma ktUp_pos (n : ℕ) : 0 < ktUp n := by
  unfold ktUp
  refine Finset.prod_pos ?_
  intro i _
  positivity

lemma ktDown_pos (n : ℕ) : 0 < ktDown n := by
  unfold ktDown
  refine Finset.prod_pos ?_
  intro i _
  positivity

lemma kt_pos (a b : ℕ) : 0 < kt a b :=
  div_pos (mul_pos (ktUp_pos a) (ktUp_pos b)) (ktDown_pos (a + b))

lemma ktUp_succ (n : ℕ) : ktUp (n + 1) = ktUp n * (2 * (n : ℝ) + 1) :=
  Finset.prod_range_succ _ _

lemma ktDown_succ (n : ℕ) : ktDown (n + 1) = ktDown n * (2 * (n : ℝ) + 2) :=
  Finset.prod_range_succ _ _

@[simp] lemma ktUp_zero : ktUp 0 = 1 := by simp [ktUp]

@[simp] lemma ktDown_zero : ktDown 0 = 1 := by simp [ktDown]

@[simp] lemma kt_zero_zero : kt 0 0 = 1 := by simp [kt]

/-- Сверка с ручным счётом: KT-вероятность строки «01» равна 1/8. -/
example : kt 1 1 = 1 / 8 := by
  norm_num [kt, ktUp, ktDown, Finset.prod_range_succ]

/-- Обновление при появлении нуля. -/
lemma kt_succ_left (a b : ℕ) :
    kt (a + 1) b = kt a b * ((2 * (a : ℝ) + 1) / (2 * ((a : ℝ) + (b : ℝ)) + 2)) := by
  have hd : ktDown (a + b) ≠ 0 := ne_of_gt (ktDown_pos _)
  have hne : 2 * ((a : ℝ) + (b : ℝ)) + 2 ≠ 0 := by positivity
  have hab : a + 1 + b = a + b + 1 := by omega
  have hcast : ((a + b : ℕ) : ℝ) = (a : ℝ) + (b : ℝ) := by push_cast; ring
  unfold kt
  rw [hab, ktUp_succ, ktDown_succ, hcast]
  field_simp
  try ring

/-- Обновление при появлении единицы. -/
lemma kt_succ_right (a b : ℕ) :
    kt a (b + 1) = kt a b * ((2 * (b : ℝ) + 1) / (2 * ((a : ℝ) + (b : ℝ)) + 2)) := by
  have hd : ktDown (a + b) ≠ 0 := ne_of_gt (ktDown_pos _)
  have hne : 2 * ((a : ℝ) + (b : ℝ)) + 2 ≠ 0 := by positivity
  have hab : a + (b + 1) = a + b + 1 := by omega
  have hcast : ((a + b : ℕ) : ℝ) = (a : ℝ) + (b : ℝ) := by push_cast; ring
  unfold kt
  rw [hab, ktUp_succ, ktDown_succ, hcast]
  field_simp
  try ring

/-- **Согласованность KT.** Ненормированная сумма по продолжению на один символ
равна вероятности исходной строки: это инвариант `Σ_x P(x) = 1` для одного
узла. -/
theorem kt_consistent (a b : ℕ) : kt (a + 1) b + kt a (b + 1) = kt a b := by
  have hne : (2 * ((a : ℝ) + (b : ℝ)) + 2) ≠ 0 := by positivity
  rw [kt_succ_left, kt_succ_right]
  field_simp
  try ring

/-- Отсюда сразу: условные вероятности, которыми пользуется алгоритм,
суммируются в единицу. -/
theorem kt_predict_sums_to_one (a b : ℕ) :
    kt (a + 1) b / kt a b + kt a (b + 1) / kt a b = 1 := by
  have h := kt_consistent a b
  have hne : kt a b ≠ 0 := ne_of_gt (kt_pos a b)
  field_simp
  linarith

/-- KT — вероятностная мера: `kt a b ≤ 1`. -/
theorem kt_le_one (a b : ℕ) : kt a b ≤ 1 := by
  induction a generalizing b with
  | zero =>
    induction b with
    | zero => simp
    | succ b ihb =>
      have h := kt_consistent 0 b
      have hpos := kt_pos (0 + 1) b
      linarith
  | succ a iha =>
    have h := kt_consistent a b
    have hpos := kt_pos a (b + 1)
    have hprev := iha b
    linarith

end BudgetCTW
