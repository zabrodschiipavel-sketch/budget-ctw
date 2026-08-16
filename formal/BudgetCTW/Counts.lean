/-
Контексты и счётчики: мост от абстрактной согласованности к реальным KT-счётчикам.

Здесь нет вероятностей — только `List` и `Finset.filter`. Содержание: приход
одного символа меняет счётчики ровно вдоль текущего контекста, и у узла на
этом пути ровно один ребёнок тоже на нём.
-/
import BudgetCTW.KT
import BudgetCTW.Consistency

namespace BudgetCTW

/-- Символ, приписываемый при спуске на уровень `d` в момент `t`: это `x` в
позиции на `d+1` назад. Позиции до начала последовательности читаются нулём —
как спуск в src/ctw.rs. -/
def bitAt (x : ℕ → Bool) (t d : ℕ) : Bool := if d < t then x (t - 1 - d) else false

/-- Контекст глубины `d` в момент `t`: последние `d` символов, свежий первым. -/
def ctx (x : ℕ → Bool) (t d : ℕ) : List Bool := (List.range d).map (bitAt x t)

@[simp] lemma ctx_length (x : ℕ → Bool) (t d : ℕ) : (ctx x t d).length = d := by
  simp [ctx]

lemma ctx_succ (x : ℕ → Bool) (t d : ℕ) :
    ctx x t (d + 1) = ctx x t d ++ [bitAt x t d] := by
  simp [ctx, List.range_succ]

/-- Спуск на один уровень: контекст глубины `|u|+1` равен `u ++ [c]` ровно
тогда, когда контекст глубины `|u|` равен `u`, а очередной символ равен `c`. -/
lemma ctx_append_iff (x : ℕ → Bool) (t : ℕ) (u : List Bool) (c : Bool) :
    ctx x t (u ++ [c]).length = u ++ [c] ↔
      (ctx x t u.length = u ∧ bitAt x t u.length = c) := by
  simp only [List.length_append, List.length_singleton]
  constructor
  · intro h
    rw [ctx_succ] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩
    rw [ctx_succ, h1, h2]

/-- Узел лежит на пути обновления в момент `T`. -/
def OnPath (x : ℕ → Bool) (T : ℕ) (u : List Bool) : Prop := ctx x T u.length = u

instance decOnPath (x : ℕ → Bool) (T : ℕ) (u : List Bool) : Decidable (OnPath x T u) :=
  inferInstanceAs (Decidable (ctx x T u.length = u))

/-- У узла на пути ровно один ребёнок на пути. -/
lemma onPath_split (x : ℕ → Bool) (T : ℕ) (u : List Bool) (hu : OnPath x T u) :
    (OnPath x T (u ++ [false]) ∧ ¬ OnPath x T (u ++ [true])) ∨
      (OnPath x T (u ++ [true]) ∧ ¬ OnPath x T (u ++ [false])) := by
  unfold OnPath at *
  rcases hc : bitAt x T u.length with _ | _
  · left
    constructor
    · exact (ctx_append_iff x T u false).2 ⟨hu, hc⟩
    · intro h
      have := ((ctx_append_iff x T u true).1 h).2
      rw [hc] at this
      exact Bool.noConfusion this
  · right
    constructor
    · exact (ctx_append_iff x T u true).2 ⟨hu, hc⟩
    · intro h
      have := ((ctx_append_iff x T u false).1 h).2
      rw [hc] at this
      exact Bool.noConfusion this

/-- Ниже узла вне пути пути нет. -/
lemma onPath_down (x : ℕ → Bool) (T : ℕ) (u : List Bool) (c : Bool)
    (hu : ¬ OnPath x T u) : ¬ OnPath x T (u ++ [c]) := by
  unfold OnPath at *
  intro h
  exact hu ((ctx_append_iff x T u c).1 h).1

/-- Сколько раз на первых `T` символах контекст `u` встретился и следующим
символом был `b`. -/
def counts (x : ℕ → Bool) (T : ℕ) (u : List Bool) (b : Bool) : ℕ :=
  ((Finset.range T).filter (fun t => ctx x t u.length = u ∧ x t = b)).card

/-- Изменение символа в позиции `T` не влияет на контексты моментов `t ≤ T`. -/
lemma ctx_update (x : ℕ → Bool) (T t d : ℕ) (c : Bool) (ht : t ≤ T) :
    ctx (Function.update x T c) t d = ctx x t d := by
  unfold ctx
  apply List.map_congr_left
  intro i _
  unfold bitAt
  by_cases h : i < t
  · rw [if_pos h, if_pos h, Function.update_of_ne]
    omega
  · rw [if_neg h, if_neg h]

/-- Приход символа `c` в позиции `T` увеличивает на единицу ровно один
счётчик и ровно в узлах текущего пути. -/
lemma counts_update (x : ℕ → Bool) (T : ℕ) (u : List Bool) (b c : Bool) :
    counts (Function.update x T c) (T + 1) u b =
      counts x T u b + (if OnPath x T u ∧ c = b then 1 else 0) := by
  classical
  unfold counts
  rw [Finset.range_add_one, Finset.filter_insert]
  have hbody : ((Finset.range T).filter
      (fun t => ctx (Function.update x T c) t u.length = u ∧ (Function.update x T c) t = b))
      = (Finset.range T).filter (fun t => ctx x t u.length = u ∧ x t = b) := by
    apply Finset.filter_congr
    intro t htmem
    have htT : t < T := Finset.mem_range.1 htmem
    rw [ctx_update x T t u.length c (le_of_lt htT), Function.update_of_ne (by omega)]
  have hhead : (ctx (Function.update x T c) T u.length = u ∧ (Function.update x T c) T = b)
      ↔ (OnPath x T u ∧ c = b) := by
    unfold OnPath
    rw [ctx_update x T T u.length c (le_refl T), Function.update_self]
  by_cases hp : OnPath x T u ∧ c = b
  · rw [if_pos (hhead.2 hp), if_pos hp, hbody, Finset.card_insert_of_notMem]
    all_goals simp
  · rw [if_neg (fun h => hp (hhead.1 h)), if_neg hp, hbody]
    all_goals simp

/-- Листовая оценка алгоритма: KT по накопленным счётчикам. -/
noncomputable def PeKT (x : ℕ → Bool) (T : ℕ) (u : List Bool) : ℝ :=
  kt (counts x T u false) (counts x T u true)

lemma PeKT_pos (x : ℕ → Bool) (T : ℕ) (u : List Bool) : 0 < PeKT x T u := kt_pos _ _

/-- На пути обновления KT-оценки двух продолжений складываются. -/
lemma PeKT_on (x : ℕ → Bool) (T : ℕ) (u : List Bool) (hu : OnPath x T u) :
    PeKT (Function.update x T false) (T + 1) u + PeKT (Function.update x T true) (T + 1) u
      = PeKT x T u := by
  unfold PeKT
  rw [counts_update, counts_update, counts_update, counts_update]
  have e1 : (if OnPath x T u ∧ false = false then 1 else 0) = 1 := by simp [hu]
  have e2 : (if OnPath x T u ∧ false = true then 1 else 0) = 0 := by simp
  have e3 : (if OnPath x T u ∧ true = false then 1 else 0) = 0 := by simp
  have e4 : (if OnPath x T u ∧ true = true then 1 else 0) = 1 := by simp [hu]
  rw [e1, e2, e3, e4]
  simp only [Nat.add_zero]
  exact kt_consistent _ _

/-- Вне пути обновления счётчики не меняются. -/
lemma PeKT_off (x : ℕ → Bool) (T : ℕ) (u : List Bool) (c : Bool) (hu : ¬ OnPath x T u) :
    PeKT (Function.update x T c) (T + 1) u = PeKT x T u := by
  unfold PeKT
  rw [counts_update, counts_update]
  simp [hu]

end BudgetCTW
