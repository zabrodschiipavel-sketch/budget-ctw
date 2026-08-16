/-
Инвариант `Σ_x P(x) = 1` для УСЕЧЁННОГО дерева.

В коде это флаг `--verify-sum`. Цена ошибки здесь измерена: на этапе 4
нарушение инварианта выглядело как «сжатие» 0.204 bpc, то есть как улучшение
целевой метрики (notes/stage4-results.md).

Содержательное место — усечение. Обрыв спуска меняет форму взвешивания в
зависимости от арены, и априори неочевидно, что масса сохраняется. Теорема
ниже говорит: сохраняется при ЛЮБОЙ арене. Значит нормировку вытеснение
сломать не может — сломать оно может только счётчики.

Формулировка абстрактная. `Pe`, `Pe0`, `Pe1` — оценки узлов до шага и после
прихода символа 0 / 1; `P` — предикат «узел лежит на текущем пути
обновления». Требуется четыре свойства, все дешёвые: у узла на пути ровно
один ребёнок на пути; ниже узла вне пути пути нет; на пути оценки
складываются (для KT это `KT.kt_consistent`); вне пути не меняются.
-/
import BudgetCTW.Mixture

namespace BudgetCTW

noncomputable section

/-- Вне пути обновления взвешивание не меняется. -/
lemma PwB_off (Pe Pe' : List Bool → ℝ) (A : Arena) (P : List Bool → Prop)
    (hdown : ∀ u c, ¬ P u → ¬ P (u ++ [c]))
    (hOff : ∀ u, ¬ P u → Pe' u = Pe u) :
    ∀ (d : ℕ) (u : List Bool), ¬ P u → PwB Pe' A d u = PwB Pe A d u := by
  intro d
  induction d with
  | zero => intro u hu; simp [hOff u hu]
  | succ d ih =>
    intro u hu
    rw [PwB_succ, PwB_succ, hOff u hu, ih _ (hdown u false hu), ih _ (hdown u true hu)]

/-- **Сохранение массы под бюджетом.**

Если листовые оценки согласованы на пути обновления и не тронуты вне его, то
взвешенная вероятность тоже согласована — при ЛЮБОЙ арене `A`. Усечение
дерева нормировку не ломает. -/
theorem PwB_consistent (Pe Pe0 Pe1 : List Bool → ℝ) (A : Arena) (P : List Bool → Prop)
    (hsplit : ∀ u, P u → (P (u ++ [false]) ∧ ¬ P (u ++ [true])) ∨
        (P (u ++ [true]) ∧ ¬ P (u ++ [false])))
    (hdown : ∀ u c, ¬ P u → ¬ P (u ++ [c]))
    (hOn : ∀ u, P u → Pe0 u + Pe1 u = Pe u)
    (hOff0 : ∀ u, ¬ P u → Pe0 u = Pe u)
    (hOff1 : ∀ u, ¬ P u → Pe1 u = Pe u) :
    ∀ (d : ℕ) (u : List Bool), P u →
      PwB Pe0 A d u + PwB Pe1 A d u = PwB Pe A d u := by
  intro d
  induction d with
  | zero =>
    intro u hu
    simpa using hOn u hu
  | succ d ih =>
    intro u hu
    have hpe := hOn u hu
    rw [PwB_succ, PwB_succ, PwB_succ]
    by_cases hA : (A (u ++ [false]) && A (u ++ [true])) = true
    · rw [if_pos hA, if_pos hA, if_pos hA]
      rcases hsplit u hu with ⟨hc, hnc⟩ | ⟨hc, hnc⟩
      · -- на пути левый ребёнок, правый вне пути
        have hIH := ih (u ++ [false]) hc
        have ho0 := PwB_off Pe Pe0 A P hdown hOff0 d (u ++ [true]) hnc
        have ho1 := PwB_off Pe Pe1 A P hdown hOff1 d (u ++ [true]) hnc
        rw [ho0, ho1]
        linear_combination hpe / 2 + (PwB Pe A d (u ++ [true]) / 2) * hIH
      · -- на пути правый ребёнок, левый вне пути
        have hIH := ih (u ++ [true]) hc
        have ho0 := PwB_off Pe Pe0 A P hdown hOff0 d (u ++ [false]) hnc
        have ho1 := PwB_off Pe Pe1 A P hdown hOff1 d (u ++ [false]) hnc
        rw [ho0, ho1]
        linear_combination hpe / 2 + (PwB Pe A d (u ++ [false]) / 2) * hIH
    · rw [if_neg hA, if_neg hA, if_neg hA]
      exact hpe

end

end BudgetCTW
