/-
Инвариант `Σ_x P(x) = 1` для УСЕЧЁННОГО дерева.

В коде это флаг `--verify-sum`. Цена ошибки здесь измерена: на этапе 4
нарушение инварианта выглядело как «сжатие» 0.204 bpc, то есть как улучшение
целевой метрики (notes/stage4-results.md).

Содержательное место — усечение. Обрыв спуска меняет форму взвешивания в
зависимости от арены, и априори неочевидно, что масса сохраняется. Теорема
ниже говорит: сохраняется при ЛЮБОЙ арене. Значит нормировку вытеснение
сломать не может — сломать оно может только счётчики.

Формулировка абстрактная: `Pe`, `Pe0`, `Pe1` — оценки узлов до шага и после
прихода символа 0 / 1. Требуется ровно два свойства: на пути обновления
оценки складываются (для KT это `KT.kt_consistent`), вне пути — не меняются.
-/
import BudgetCTW.Mixture

namespace BudgetCTW

noncomputable section

/-- Ровно один из двух детей узла на пути остаётся на пути. -/
lemma prefix_split (u w : List Bool) (hu : u <+: w) (hlt : u.length < w.length) :
    ((u ++ [false]) <+: w ∧ ¬ ((u ++ [true]) <+: w)) ∨
      ((u ++ [true]) <+: w ∧ ¬ ((u ++ [false]) <+: w)) := by
  obtain ⟨t, ht⟩ := hu
  cases t with
  | nil =>
    rw [List.append_nil] at ht
    subst ht
    exact absurd hlt (lt_irrefl _)
  | cons c t' =>
    have hpre : (u ++ [c]) <+: w := ⟨t', by rw [List.append_assoc]; simpa using ht⟩
    have hno : ¬ ((u ++ [!c]) <+: w) := by
      rintro ⟨s, hs⟩
      rw [List.append_assoc, ← ht] at hs
      have h := List.append_cancel_left hs
      cases c <;> simp at h
    cases c with
    | false => exact Or.inl ⟨hpre, by simpa using hno⟩
    | true => exact Or.inr ⟨hpre, by simpa using hno⟩

/-- Вне пути обновления взвешивание не меняется. -/
lemma PwB_off (Pe Pe' : List Bool → ℝ) (A : Arena) (w : List Bool)
    (hOff : ∀ u, ¬ (u <+: w) → Pe' u = Pe u) :
    ∀ (d : ℕ) (u : List Bool), ¬ (u <+: w) → PwB Pe' A d u = PwB Pe A d u := by
  intro d
  induction d with
  | zero => intro u hu; simp [hOff u hu]
  | succ d ih =>
    intro u hu
    have h0 : ¬ ((u ++ [false]) <+: w) := fun h =>
      hu ((List.prefix_append u [false]).trans h)
    have h1 : ¬ ((u ++ [true]) <+: w) := fun h =>
      hu ((List.prefix_append u [true]).trans h)
    rw [PwB_succ, PwB_succ, hOff u hu, ih _ h0, ih _ h1]

/-- **Сохранение массы под бюджетом.**

Если листовые оценки согласованы на пути обновления и не тронуты вне его, то
взвешенная вероятность тоже согласована — при ЛЮБОЙ арене `A`. Усечение
дерева нормировку не ломает. -/
theorem PwB_consistent (Pe Pe0 Pe1 : List Bool → ℝ) (A : Arena) (w : List Bool)
    (hOn : ∀ u, u <+: w → Pe0 u + Pe1 u = Pe u)
    (hOff0 : ∀ u, ¬ (u <+: w) → Pe0 u = Pe u)
    (hOff1 : ∀ u, ¬ (u <+: w) → Pe1 u = Pe u) :
    ∀ (d : ℕ) (u : List Bool), u.length + d = w.length → u <+: w →
      PwB Pe0 A d u + PwB Pe1 A d u = PwB Pe A d u := by
  intro d
  induction d with
  | zero =>
    intro u _ hu
    simpa using hOn u hu
  | succ d ih =>
    intro u hlen hu
    have hlt : u.length < w.length := by omega
    have hpe := hOn u hu
    rw [PwB_succ, PwB_succ, PwB_succ]
    by_cases hA : (A (u ++ [false]) && A (u ++ [true])) = true
    · rw [if_pos hA, if_pos hA, if_pos hA]
      rcases prefix_split u w hu hlt with ⟨hc, hnc⟩ | ⟨hc, hnc⟩
      · -- на пути левый ребёнок
        have hlen' : (u ++ [false]).length + d = w.length := by
          simp only [List.length_append, List.length_singleton]; omega
        have hIH := ih (u ++ [false]) hlen' hc
        have ho0 := PwB_off Pe Pe0 A w hOff0 d (u ++ [true]) hnc
        have ho1 := PwB_off Pe Pe1 A w hOff1 d (u ++ [true]) hnc
        rw [ho0, ho1]
        linear_combination hpe / 2 + (PwB Pe A d (u ++ [true]) / 2) * hIH
      · -- на пути правый ребёнок
        have hlen' : (u ++ [true]).length + d = w.length := by
          simp only [List.length_append, List.length_singleton]; omega
        have hIH := ih (u ++ [true]) hlen' hc
        have ho0 := PwB_off Pe Pe0 A w hOff0 d (u ++ [false]) hnc
        have ho1 := PwB_off Pe Pe1 A w hOff1 d (u ++ [false]) hnc
        rw [ho0, ho1]
        linear_combination hpe / 2 + (PwB Pe A d (u ++ [false]) / 2) * hIH
    · rw [if_neg hA, if_neg hA, if_neg hA]
      exact hpe

/-- Тот же результат в корне дерева: суммарная вероятность двух продолжений
равна вероятности уже прочитанного. Это и есть `--verify-sum`. -/
theorem PwB_sums_to_one (Pe Pe0 Pe1 : List Bool → ℝ) (A : Arena) (w : List Bool)
    (hOn : ∀ u, u <+: w → Pe0 u + Pe1 u = Pe u)
    (hOff0 : ∀ u, ¬ (u <+: w) → Pe0 u = Pe u)
    (hOff1 : ∀ u, ¬ (u <+: w) → Pe1 u = Pe u) :
    PwB Pe0 A w.length [] + PwB Pe1 A w.length [] = PwB Pe A w.length [] :=
  PwB_consistent Pe Pe0 Pe1 A w hOn hOff0 hOff1 w.length [] (by simp) List.nil_prefix

end

end BudgetCTW
