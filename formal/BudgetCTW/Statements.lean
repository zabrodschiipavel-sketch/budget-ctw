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

namespace BudgetCTW

open CTree

noncomputable section

/-! ## Последовательность, контексты, счётчики -/

/-- Контекст глубины `d` в момент `t`: последние `d` символов, свежий первым.
Позиции до начала последовательности заполняются нулём — как спуск в
src/ctw.rs. -/
def ctx (x : ℕ → Bool) (t d : ℕ) : List Bool :=
  (List.range d).map (fun i => if i < t then x (t - 1 - i) else false)

lemma ctx_length (x : ℕ → Bool) (t d : ℕ) : (ctx x t d).length = d := by
  simp [ctx]

/-- Сколько раз на первых `T` символах контекст `u` встретился и следующим
символом был `b`. -/
def counts (x : ℕ → Bool) (T : ℕ) (u : List Bool) (b : Bool) : ℕ :=
  ((Finset.range T).filter (fun t => ctx x t u.length = u ∧ x t = b)).card

/-- Листовая оценка алгоритма: KT по накопленным счётчикам. -/
def PeKT (x : ℕ → Bool) (T : ℕ) (u : List Bool) : ℝ :=
  kt (counts x T u false) (counts x T u true)

lemma PeKT_pos (x : ℕ → Bool) (T : ℕ) (u : List Bool) : 0 < PeKT x T u := kt_pos _ _

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

/-! ## Осталось доказать

Ниже — единственное место в проекте, где `sorry` допустим: это список
открытых обязательств, а не результат.

`ctw_consistent` — инвариант `Σ_x P(x) = 1` для взвешенного дерева (в коде
флаг `--verify-sum`). Содержательная часть уже доказана дважды и без `sorry`:
`KT.kt_consistent` (согласованность оценщика в одном узле) и
`Consistency.PwB_consistent` (перенос согласованности на усечённое дерево при
любой арене). Остался технический мост между ними — аддитивность счётчиков
по детям, `counts u b = counts (u++[false]) b + counts (u++[true]) b`, и
проверка того, что приход символа меняет счётчики только на пути `ctx x T D`.
Это работа с `Finset.filter`, не с вероятностями.

Динамическая арена (пункт (2) в полном виде) в Lean пока не формулируется:
для этого нужна модель алгоритма как системы переходов (состояние =
префикс-замкнутое множество контекстов + счётчики), а её бумажная версия ещё
не устоялась — см. notes/gap-to-100.md §2 (2b). Формулировать в Lean раньше
бумаги — прямой путь получить удобную для доказательства и бесполезную для
препринта лемму (риск §6 в notes/stage8-lean-plan.md).
-/

/-- Инвариант `Σ_x P(x) = 1` для взвешенного дерева. ОТКРЫТО. -/
theorem ctw_consistent (x : ℕ → Bool) (T D : ℕ) (A : Arena) :
    PwB (PeKT (Function.update x T false) (T + 1)) A D [] +
        PwB (PeKT (Function.update x T true) (T + 1)) A D [] =
      PwB (PeKT x T) A D [] := by
  sorry

end

end BudgetCTW

/- Контроль: доказанные утверждения не должны зависеть от `sorryAx`.
Ожидаемый вывод — только `propext`, `Classical.choice`, `Quot.sound`. -/
#print axioms BudgetCTW.point2_static_kt
#print axioms BudgetCTW.point2_structural_cost
#print axioms BudgetCTW.budget_mixture
#print axioms BudgetCTW.budget_codelength
#print axioms BudgetCTW.PwB_consistent
#print axioms BudgetCTW.kt_consistent
