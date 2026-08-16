/-
Смесевое неравенство CTW — и его версия для УСЕЧЁННОГО (бюджетного) дерева.

Это содержательная часть пункта (2а) из notes/gap-to-100.md: «доказательство,
что смесевое неравенство CTW переживает усечённое дерево — то есть второй член
разложения действительно нулевой, а не примерно нулевой».

Ключевое наблюдение, делающее это доказуемым без всякого анализа: неравенство
`2^(−Γ(S))·∏_листья Pe ≤ P_w` — чисто алгебраическое. Оно не использует ни
аддитивность счётчиков, ни свойства KT, ни нормировку: достаточно `Pe ≥ 0`.
Поэтому оно доказывается структурной индукцией по дереву и переносится на
бюджетный случай дословно, с одной новой гипотезой — дерево должно помещаться
в арену.

`Pe` здесь — произвольная неотрицательная оценка в узле; KT подставляется
позже (BudgetCTW.Statements).
-/
import BudgetCTW.Basic
import BudgetCTW.Tree

namespace BudgetCTW

open CTree

noncomputable section

/-- Произведение оценок по листьям дерева `S`, посаженного в узел `u`. -/
def leafProd (w : List Bool → ℝ) : CTree → List Bool → ℝ
  | .leaf, u => w u
  | .node l r, u => leafProd w l (u ++ [false]) * leafProd w r (u ++ [true])

/-- Сумма кодовых длин по листьям — логарифмический двойник `leafProd`. -/
def leafSum (f : List Bool → ℝ) : CTree → List Bool → ℝ
  | .leaf, u => f u
  | .node l r, u => leafSum f l (u ++ [false]) + leafSum f r (u ++ [true])

@[simp] lemma leafProd_leaf (w : List Bool → ℝ) (u : List Bool) :
    leafProd w .leaf u = w u := rfl

@[simp] lemma leafProd_node (w : List Bool → ℝ) (l r : CTree) (u : List Bool) :
    leafProd w (.node l r) u = leafProd w l (u ++ [false]) * leafProd w r (u ++ [true]) := rfl

@[simp] lemma leafSum_leaf (f : List Bool → ℝ) (u : List Bool) :
    leafSum f .leaf u = f u := rfl

@[simp] lemma leafSum_node (f : List Bool → ℝ) (l r : CTree) (u : List Bool) :
    leafSum f (.node l r) u = leafSum f l (u ++ [false]) + leafSum f r (u ++ [true]) := rfl

/-- Арена: множество контекстов, которые алгоритм действительно материализовал.
Задаётся булевым предикатом, чтобы не тащить инстансы разрешимости. -/
abbrev Arena := List Bool → Bool

/-- Взвешенная вероятность под бюджетом: узел, у которого не оба ребёнка лежат
в арене, трактуется как ЛИСТ (`P_w := P_e`). Это ровно то, что делает
src/ctw.rs при усечении спуска. -/
def PwB (Pe : List Bool → ℝ) (A : Arena) : ℕ → List Bool → ℝ
  | 0, u => Pe u
  | d + 1, u =>
      if A (u ++ [false]) && A (u ++ [true]) then
        (Pe u + PwB Pe A d (u ++ [false]) * PwB Pe A d (u ++ [true])) / 2
      else
        Pe u

/-- Полное CTW-взвешивание — частный случай бюджетного при неограниченной арене. -/
def Pw (Pe : List Bool → ℝ) : ℕ → List Bool → ℝ := PwB Pe (fun _ => true)

@[simp] lemma PwB_zero (Pe : List Bool → ℝ) (A : Arena) (u : List Bool) :
    PwB Pe A 0 u = Pe u := rfl

lemma PwB_succ (Pe : List Bool → ℝ) (A : Arena) (d : ℕ) (u : List Bool) :
    PwB Pe A (d + 1) u =
      if A (u ++ [false]) && A (u ++ [true]) then
        (Pe u + PwB Pe A d (u ++ [false]) * PwB Pe A d (u ++ [true])) / 2
      else
        Pe u := rfl

/-- Дерево `S`, посаженное в узел `u`, помещается в арену `A`: всякое
расщепление, которое `S` делает, алгоритму доступно. -/
def Fits (A : Arena) : CTree → List Bool → Prop
  | .leaf, _ => True
  | .node l r, u =>
      A (u ++ [false]) = true ∧ A (u ++ [true]) = true ∧
      Fits A l (u ++ [false]) ∧ Fits A r (u ++ [true])

lemma PwB_nonneg (Pe : List Bool → ℝ) (hPe : ∀ u, 0 ≤ Pe u) (A : Arena) :
    ∀ (d : ℕ) (u : List Bool), 0 ≤ PwB Pe A d u := by
  intro d
  induction d with
  | zero => intro u; simpa using hPe u
  | succ d ih =>
    intro u
    rw [PwB_succ]
    split
    · have h0 := ih (u ++ [false])
      have h1 := ih (u ++ [true])
      have hm : 0 ≤ PwB Pe A d (u ++ [false]) * PwB Pe A d (u ++ [true]) := mul_nonneg h0 h1
      have := hPe u
      linarith
    · exact hPe u

lemma PwB_pos (Pe : List Bool → ℝ) (hPe : ∀ u, 0 < Pe u) (A : Arena) :
    ∀ (d : ℕ) (u : List Bool), 0 < PwB Pe A d u := by
  intro d
  induction d with
  | zero => intro u; simpa using hPe u
  | succ d ih =>
    intro u
    rw [PwB_succ]
    split
    · have h0 := ih (u ++ [false])
      have h1 := ih (u ++ [true])
      have hm : 0 < PwB Pe A d (u ++ [false]) * PwB Pe A d (u ++ [true]) := mul_pos h0 h1
      have := hPe u
      linarith
    · exact hPe u

lemma leafProd_nonneg (Pe : List Bool → ℝ) (hPe : ∀ u, 0 ≤ Pe u) (S : CTree) (u : List Bool) :
    0 ≤ leafProd Pe S u := by
  induction S generalizing u with
  | leaf => simpa using hPe u
  | node l r ihl ihr =>
    simp only [leafProd_node]
    exact mul_nonneg (ihl _) (ihr _)

lemma leafProd_pos (Pe : List Bool → ℝ) (hPe : ∀ u, 0 < Pe u) (S : CTree) (u : List Bool) :
    0 < leafProd Pe S u := by
  induction S generalizing u with
  | leaf => simpa using hPe u
  | node l r ihl ihr =>
    simp only [leafProd_node]
    exact mul_pos (ihl _) (ihr _)

/-- **Смесевое неравенство CTW под бюджетом.**

Для любого дерева `S`, помещающегося в арену `A`, взвешенная вероятность
бюджетного алгоритма не меньше вклада `S`, взятого с классическим структурным
весом `2^(−Γ_d(S))`. Иначе говоря: усечение арены НЕ портит смесевую оценку —
оно лишь сужает множество деревьев, по которым берётся минимум.

Это и есть пункт (2а): второй член разложения сожаления равен нулю точно, а не
приближённо. -/
theorem budget_mixture (Pe : List Bool → ℝ) (hPe : ∀ u, 0 ≤ Pe u) (A : Arena) :
    ∀ (S : CTree) (d : ℕ), S.depth ≤ d → ∀ u : List Bool, Fits A S u →
      leafProd Pe S u ≤ 2 ^ (S.gamma d) * PwB Pe A d u := by
  intro S
  induction S with
  | leaf =>
    intro d _ u _
    cases d with
    | zero => simp
    | succ d =>
      have hu := hPe u
      rw [PwB_succ]
      simp only [gamma_leaf_succ, leafProd_leaf, pow_one]
      split
      · have h0 := PwB_nonneg Pe hPe A d (u ++ [false])
        have h1 := PwB_nonneg Pe hPe A d (u ++ [true])
        have hm : 0 ≤ PwB Pe A d (u ++ [false]) * PwB Pe A d (u ++ [true]) := mul_nonneg h0 h1
        linarith
      · linarith
  | node l r ihl ihr =>
    intro d hd u hfit
    cases d with
    | zero =>
      simp only [depth_node] at hd
      omega
    | succ d =>
      obtain ⟨hA0, hA1, hfl, hfr⟩ := hfit
      simp only [depth_node] at hd
      have hmax : max l.depth r.depth ≤ d := by omega
      have hdl : l.depth ≤ d := le_trans (le_max_left _ _) hmax
      have hdr : r.depth ≤ d := le_trans (le_max_right _ _) hmax
      have Hl := ihl d hdl (u ++ [false]) hfl
      have Hr := ihr d hdr (u ++ [true]) hfr
      have hr0 := leafProd_nonneg Pe hPe r (u ++ [true])
      have hpw0 := PwB_nonneg Pe hPe A d (u ++ [false])
      have hb : (0 : ℝ) ≤ 2 ^ (l.gamma d) * PwB Pe A d (u ++ [false]) :=
        mul_nonneg (by positivity) hpw0
      have hcond : (A (u ++ [false]) && A (u ++ [true])) = true := by
        rw [hA0, hA1]; rfl
      rw [PwB_succ, if_pos hcond]
      simp only [gamma_node_succ, leafProd_node]
      calc leafProd Pe l (u ++ [false]) * leafProd Pe r (u ++ [true])
          ≤ (2 ^ (l.gamma d) * PwB Pe A d (u ++ [false])) *
            (2 ^ (r.gamma d) * PwB Pe A d (u ++ [true])) := mul_le_mul Hl Hr hr0 hb
        _ = (2 ^ (l.gamma d) * 2 ^ (r.gamma d)) *
            (PwB Pe A d (u ++ [false]) * PwB Pe A d (u ++ [true])) := by ring
        _ ≤ (2 ^ (l.gamma d) * 2 ^ (r.gamma d)) *
            (Pe u + PwB Pe A d (u ++ [false]) * PwB Pe A d (u ++ [true])) := by
              have hp : (0 : ℝ) ≤ 2 ^ (l.gamma d) * 2 ^ (r.gamma d) := by positivity
              have := hPe u
              nlinarith
        _ = 2 ^ (l.gamma d + r.gamma d + 1) *
            ((Pe u + PwB Pe A d (u ++ [false]) * PwB Pe A d (u ++ [true])) / 2) := by
              rw [pow_add, pow_add]; ring

/-- Полная арена вмещает любое дерево. -/
lemma fits_full (S : CTree) (u : List Bool) : Fits (fun _ => true) S u := by
  induction S generalizing u with
  | leaf => trivial
  | node l r ihl ihr => exact ⟨rfl, rfl, ihl _, ihr _⟩

/-- Классическое смесевое неравенство CTW — частный случай при полной арене. -/
theorem ctw_mixture (Pe : List Bool → ℝ) (hPe : ∀ u, 0 ≤ Pe u) (S : CTree) (d : ℕ)
    (hd : S.depth ≤ d) (u : List Bool) :
    leafProd Pe S u ≤ 2 ^ (S.gamma d) * Pw Pe d u :=
  budget_mixture Pe hPe (fun _ => true) S d hd u (fits_full S u)

/-- Кодовая длина произведения по листьям есть сумма кодовых длин. -/
lemma L_leafProd (Pe : List Bool → ℝ) (hPe : ∀ u, 0 < Pe u) (S : CTree) (u : List Bool) :
    L (leafProd Pe S u) = leafSum (fun v => L (Pe v)) S u := by
  induction S generalizing u with
  | leaf => simp
  | node l r ihl ihr =>
    simp only [leafProd_node, leafSum_node]
    rw [L_mul (ne_of_gt (leafProd_pos Pe hPe l _)) (ne_of_gt (leafProd_pos Pe hPe r _)),
      ihl, ihr]

/-- **Верхняя граница на кодовую длину бюджетного взвешивания.**

Для КАЖДОГО дерева `S`, помещающегося в арену, кодовая длина бюджетного
алгоритма не превосходит структурной цены `Γ_d(S)` плюс суммы кодовых длин
листовых оценок. Вместе с `CTree.gamma_le` (`Γ ≤ 2M−1`) это первые две строки
разложения из notes/gap-to-100.md §2 — теперь доказанные. -/
theorem budget_codelength (Pe : List Bool → ℝ) (hPe : ∀ u, 0 < Pe u) (A : Arena)
    (S : CTree) (d : ℕ) (hd : S.depth ≤ d) (u : List Bool) (hfit : Fits A S u) :
    L (PwB Pe A d u) ≤ (S.gamma d : ℝ) + leafSum (fun v => L (Pe v)) S u := by
  have hnn : ∀ v, 0 ≤ Pe v := fun v => le_of_lt (hPe v)
  have hmix := budget_mixture Pe hnn A S d hd u hfit
  have hlp : 0 < leafProd Pe S u := leafProd_pos Pe hPe S u
  have hpw : 0 < PwB Pe A d u := PwB_pos Pe hPe A d u
  have hL := L_antitone hlp hmix
  rw [L_two_pow_mul hpw (S.gamma d)] at hL
  rw [← L_leafProd Pe hPe S u]
  linarith

end

end BudgetCTW
