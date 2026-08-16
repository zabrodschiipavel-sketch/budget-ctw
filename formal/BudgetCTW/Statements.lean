/-
Постановка П4 в Lean: что доказано и что осталось.

Файл держит ГРАНИЦУ между доказанным и недоказанным явно. Всё, что помечено
`sorry`, в препринт как теорема не идёт. Это прямая реакция на то, чем
кончился stage7: абстракт заявлял теоремы, которых не было
(notes/gap-to-100.md §4).

Соответствие пунктам постановки problems/P04-budget-ctw.md:
  (2) верхняя граница — `point2_static_kt` ДОКАЗАН для статической арены;
                        динамическая (с вытеснением) — открыта, см. §«Осталось»;
  (3) нижняя граница  — открыта в Lean; бумажный вариант в
                        notes/stage11-lower-bound.md.
-/
import BudgetCTW.Basic
import BudgetCTW.Tree
import BudgetCTW.KT
import BudgetCTW.Mixture
import BudgetCTW.Consistency
import BudgetCTW.Counts

namespace BudgetCTW

open CTree

noncomputable section

/-! ## Пункт (2) при статической арене — доказано -/

/-- **Верхняя граница пункта (2) для статической арены.**

Для любого дерева сравнения `S`, помещающегося в арену, кодовая длина
бюджетного CTW не превосходит `Γ_D(S) + Σ_листья L(KT)`. Ни одного `sorry`
ниже по цепочке: `Mixture.budget_mixture` → `Mixture.budget_codelength`. -/
theorem point2_static_kt (x : ℕ → Bool) (T D : ℕ) (A : Arena) (S : CTree)
    (hd : S.depth ≤ D) (hfit : Fits A S []) :
    L (PwB (PeKT x T) A D []) ≤
      (S.gamma D : ℝ) + leafSum (fun v => L (PeKT x T v)) S [] :=
  budget_codelength (PeKT x T) (PeKT_pos x T) A S D hd [] hfit

/-- Структурная часть границы — та самая «структурная компонента O(M) бит»
из постановки: `Γ_D(S) ≤ 2M − 1` для всякого `S ∈ T_M`. -/
theorem point2_structural_cost (S : CTree) (D M : ℕ) (hS : TM D M S) :
    S.gamma D + 1 ≤ 2 * M := by
  have h := CTree.gamma_le S D
  have hM := hS.2
  omega

/-- **Сожаление при статической арене ≤ 2M − 1 бит.**

`leafSum (L ∘ PeKT)` есть в точности `L_S(x)` из постановки: кодовая длина
последовательности деревом `S` при KT-оценщиках в листьях (оценщик обменный,
поэтому зависит только от финальных счётчиков). Это то же самое, что считает
компаратор с `--cost kt`.

Итог в форме пункта (2) постановки — `R_T ≤ CTW-компонента + штраф
вытеснения` — при статической арене: CTW-компонента равна `2M − 1` бит на
весь корпус, штраф вытеснения равен нулю ТОЧНО (усечение не добавляет
мультипликативной потери), и квантор — по деревьям `S ∈ T_M`, помещающимся в
арену. Динамика арены сюда не входит, см. §«Осталось». -/
theorem point2_static_regret (x : ℕ → Bool) (T D M : ℕ) (A : Arena) (S : CTree)
    (hS : TM D M S) (hfit : Fits A S []) :
    L (PwB (PeKT x T) A D []) - leafSum (fun v => L (PeKT x T v)) S []
      ≤ 2 * (M : ℝ) - 1 := by
  have h1 := point2_static_kt x T D A S hS.1 hfit
  have h2 : (S.gamma D : ℝ) + 1 ≤ 2 * (M : ℝ) := by
    exact_mod_cast point2_structural_cost S D M hS
  linarith

/-! ## Инвариант Σ P(x) = 1 на настоящих счётчиках -/

/-- **`--verify-sum` как теорема.**

Две ветви продолжения последовательности на один символ дают в сумме ровно
вероятность уже прочитанного — при любой арене, любой глубине и любом
усечении. Собирается из двух доказанных частей: `KT.kt_consistent` (оценщик в
узле) и `Consistency.PwB_consistent` (перенос на усечённое дерево). -/
theorem ctw_consistent (x : ℕ → Bool) (T D : ℕ) (A : Arena) :
    PwB (PeKT (Function.update x T false) (T + 1)) A D [] +
        PwB (PeKT (Function.update x T true) (T + 1)) A D [] =
      PwB (PeKT x T) A D [] :=
  PwB_consistent (PeKT x T)
    (PeKT (Function.update x T false) (T + 1))
    (PeKT (Function.update x T true) (T + 1))
    A (OnPath x T)
    (onPath_split x T) (onPath_down x T)
    (fun u hu => PeKT_on x T u hu)
    (fun u hu => PeKT_off x T u false hu)
    (fun u hu => PeKT_off x T u true hu)
    D [] (by simp [OnPath, ctx])

/-! ## Осталось доказать

Динамическая арена (пункт (2) в полном виде) в Lean не формулируется: для
этого нужна модель алгоритма как системы переходов (состояние =
префикс-замкнутое множество контекстов + счётчики), а её бумажная версия ещё
не устоялась — см. notes/gap-to-100.md §2 (2b). Формулировать в Lean раньше
бумаги — прямой путь получить удобную для доказательства и бесполезную для
препринта лемму (риск §6 в notes/stage8-lean-plan.md).

Не формализована и избыточность KT (`L(kt a b) ≤ n·H + ½log n + 1`) —
единственная тяжёлая аналитическая лемма трека, веха M2 плана этапа 8. Без
неё граница `point2_static_regret` формулируется относительно KT-стоимости
дерева (как в определении `L_S` постановки), но не относительно
идеализированного энтропийного компаратора.
-/

end

end BudgetCTW

/- Контроль: доказанные утверждения не должны зависеть от `sorryAx`.
Ожидаемый вывод — только `propext`, `Classical.choice`, `Quot.sound`. -/
#print axioms BudgetCTW.point2_static_kt
#print axioms BudgetCTW.point2_static_regret
#print axioms BudgetCTW.point2_structural_cost
#print axioms BudgetCTW.budget_mixture
#print axioms BudgetCTW.budget_codelength
#print axioms BudgetCTW.ctw_consistent
#print axioms BudgetCTW.PwB_consistent
#print axioms BudgetCTW.kt_consistent
