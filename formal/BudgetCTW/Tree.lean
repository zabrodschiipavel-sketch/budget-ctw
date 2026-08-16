/-
Класс сравнения T_M из постановки П4.

Это главный страховочный модуль. Репозиторий уже один раз потерял недели на
том, что пять независимых реализаций компаратора минимизировали по строгому
ПОДКЛАССУ T_M (обрыв дерева на первом унарном узле), и ошибка ловилась только
сравнением реализации с самой собой — см. notes/stage5b-comparator-audit.md.
Здесь класс задаётся один раз, и все утверждения квантифицируются по нему.

Соглашение о путях: узел дерева адресуется списком `List Bool` — путь от
корня, где голова списка есть ПОСЛЕДНИЙ (самый свежий) символ контекста.
Спуск на уровень вниз приписывает символ в конец: `u ++ [b]`. Это ровно то,
что делает спуск в src/ctw.rs.
-/
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Common

namespace BudgetCTW

/-- Двоичное контекстное дерево класса сравнения: лист либо внутренний узел с
двумя поддеревьями. Полное (не унарное) ветвление — это и есть класс из
постановки: «дерево контекстов с ≤ M листьями». -/
inductive CTree where
  | leaf : CTree
  | node : CTree → CTree → CTree
  deriving DecidableEq, Repr

namespace CTree

/-- Число листьев. -/
def leafCount : CTree → ℕ
  | leaf => 1
  | node l r => leafCount l + leafCount r

/-- Глубина. -/
def depth : CTree → ℕ
  | leaf => 0
  | node l r => max (depth l) (depth r) + 1

/-- Структурная стоимость Γ_d(S) в битах при запасе глубины `d`: каждый
внутренний узел стоит один бит («расщепиться»), и каждый лист, стоящий строго
выше уровня `d`, — тоже один бит («остановиться»). Это вес дерева в смеси CTW.
Случай `node`/`d = 0` недостижим при `depth S ≤ d` и оставлен мусорным. -/
def gamma : CTree → ℕ → ℕ
  | leaf, 0 => 0
  | leaf, _ + 1 => 1
  | node _ _, 0 => 0
  | node l r, d + 1 => gamma l d + gamma r d + 1

@[simp] lemma leafCount_leaf : leafCount leaf = 1 := rfl

@[simp] lemma leafCount_node (l r : CTree) :
    leafCount (node l r) = leafCount l + leafCount r := rfl

@[simp] lemma depth_leaf : depth leaf = 0 := rfl

@[simp] lemma depth_node (l r : CTree) :
    depth (node l r) = max (depth l) (depth r) + 1 := rfl

@[simp] lemma gamma_leaf_zero : gamma leaf 0 = 0 := rfl

@[simp] lemma gamma_leaf_succ (d : ℕ) : gamma leaf (d + 1) = 1 := rfl

@[simp] lemma gamma_node_zero (l r : CTree) : gamma (node l r) 0 = 0 := rfl

@[simp] lemma gamma_node_succ (l r : CTree) (d : ℕ) :
    gamma (node l r) (d + 1) = gamma l d + gamma r d + 1 := rfl

lemma one_le_leafCount (S : CTree) : 1 ≤ S.leafCount := by
  induction S with
  | leaf => simp
  | node l r ihl ihr => simp; omega

/-- Структурная компонента ограничена числом листьев: `Γ_d(S) ≤ 2·M − 1`
(записано без вычитания в ℕ). Это первое слагаемое требуемой в пункте (2)
границы — «структурная компонента O(M) бит» из постановки. -/
theorem gamma_le (S : CTree) (d : ℕ) : S.gamma d + 1 ≤ 2 * S.leafCount := by
  induction S generalizing d with
  | leaf =>
    cases d with
    | zero => simp
    | succ d => simp
  | node l r ihl ihr =>
    cases d with
    | zero =>
      have hl := one_le_leafCount l
      have hr := one_le_leafCount r
      simp only [gamma_node_zero, leafCount_node]
      omega
    | succ d =>
      have hl := ihl d
      have hr := ihr d
      simp only [gamma_node_succ, leafCount_node]
      omega

end CTree

/-- Класс сравнения из постановки: деревья с не более чем `M` листьями и
глубиной не более `D`. -/
def TM (D M : ℕ) (S : CTree) : Prop := S.depth ≤ D ∧ S.leafCount ≤ M

end BudgetCTW
