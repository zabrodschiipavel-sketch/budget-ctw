"""Точная лагранжева развёртка: жадное отщипывание слабейшего звена
(Breiman cost-complexity pruning) — этап 5б.

Даёт точки нижней выпуклой оболочки (листья, стоимость) за
O(узлы · log узлы) вместо сетки по λ. Проверяется против точного DP:

1. Ни одна точка оболочки не лучше точного DP при том же бюджете
   (оболочка — верхняя граница: C_оболочки(L) ≥ DP(≤L)).
2. На точках, где оболочка совпадает с DP — лагранжево приближение точно.
3. Измеряется максимальный разрыв оболочки от DP по всем M — это цена
   лагранжева приближения в невыпуклых областях, которую спека требует
   зафиксировать в препринте.

Инвариант алгоритма: после отщипывания узел становится листом и больше
никогда не кандидат (иначе устаревшие записи кучи «отщипывают» его
повторно, не меняя числа листьев, — баг, дававший мусорные точки).

Дерево честное (класс T_M постановки П4): внутренний узел — любой с ≥1
встреченным ребёнком; отсутствующий брат — виртуальный лист (нулевые
счётчики, нулевая стоимость), который нигде не материализуется как объект,
а входит в R(u)/leaves(u) символически, парой (0.0, 1).
"""
import heapq
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")
sys.path.insert(0, "tools")
from comparator_ref import build_tree, ExactDP, cost_leaf


def weakest_link_frontier(nodes, cost: str = "entropy"):
    n = len(nodes)
    ch0 = [nd["ch"][0] for nd in nodes]
    ch1 = [nd["ch"][1] for nd in nodes]
    par = [0] * n
    for u in range(n):
        for c in (ch0[u], ch1[u]):
            if c:
                par[c] = u
    R = [0.0] * n
    leaves = [0] * n
    alive = [True] * n
    # Стоимость узла как листа считается один раз: для cost="kt" это три
    # lgamma на узел, а α пересчитывается на каждом предке при каждом
    # отщипывании.
    leafc = [cost_leaf(nodes, u, cost) for u in range(n)]

    def rval(c):
        return R[c] if c else 0.0

    def lval(c):
        return leaves[c] if c else 1

    def kill_subtree(u):
        """Пометить РЕАЛЬНОЕ поддерево u как мёртвое (виртуальные листья
        нигде не хранятся — хоронить нечего)."""
        stack = [u]
        while stack:
            w = stack.pop()
            alive[w] = False
            if ch0[w]:
                stack.append(ch0[w])
            if ch1[w]:
                stack.append(ch1[w])

    # Стартовое дерево = оптимум при λ=0 (штрафа за лист нет).
    #
    # Для entropy это в точности T_max: вогнутость энтропии даёт
    # R(дети) ≤ c(u) всегда, условие ниже никогда не срабатывает, и поведение
    # бит-в-бит прежнее (в т.ч. на унарных цепочках, где R(дети) == c(u) и
    # расщепление сохраняется как кандидат с α=0).
    #
    # Для kt расщепление ПЛАТНОЕ (каждый новый лист несёт свою ½log₂n
    # избыточности), поэтому R(дети) может быть > c(u), и такие узлы обязаны
    # схлопнуться ДО развёртки. Иначе ломается сама теорема Бреймана: её
    # доказательство нестингa опирается на α ≥ 0, а при отрицательных α
    # жадное отщипывание перестаёт давать лагранжев оптимум — измерено:
    # 170 точек хребта из 4308 оказывались хуже точного DP при своём же
    # числе листьев. После предредукции c(u) ≥ R(u) во всех узлах, и все
    # последующие α ≥ 0 (отщипывание только удорожает).
    for u in range(n - 1, -1, -1):
        if ch0[u] or ch1[u]:
            rs = rval(ch0[u]) + rval(ch1[u])
            if rs <= leafc[u]:
                R[u] = rs
                leaves[u] = lval(ch0[u]) + lval(ch1[u])
                continue
        R[u] = leafc[u]
        leaves[u] = 1
    # Узлы под схлопнувшимися больше не в дереве. Обход сверху за O(n) —
    # дешевле, чем kill_subtree на каждом схлопывании (там O(n²) на цепочке).
    if any(leaves[u] == 1 and (ch0[u] or ch1[u]) for u in range(n)):
        for u in range(n):
            alive[u] = False
        stack = [0]
        while stack:
            w = stack.pop()
            alive[w] = True
            if leaves[w] == 1:
                continue
            if ch0[w]:
                stack.append(ch0[w])
            if ch1[w]:
                stack.append(ch1[w])
    pts = [(leaves[0], R[0])]

    alpha = {}

    def push(u):
        if alive[u] and (ch0[u] or ch1[u]) and leaves[u] > 1:
            a = (leafc[u] - R[u]) / (leaves[u] - 1)
            alpha[u] = a
            heapq.heappush(h, (a, u))

    h = []
    for u in range(n):
        push(u)
    while h:
        a, u = heapq.heappop(h)
        if not alive[u] or leaves[u] <= 1:
            continue
        if alpha.get(u) != a:
            continue  # устаревшая запись: α пересчитан после отщипывания ниже
        # отщипываем u: узел становится листом; всё его (реальное) поддерево
        # выбывает из кандидатов (вклад потомков уже учтён в листе u)
        kill_subtree(u)
        R[u] = leafc[u]
        leaves[u] = 1
        # пересчёт предков: от родителя u вверх до корня включительно.
        # Сам u не пересчитываем — он только что стал листом (для корня
        # par[0] == 0, поэтому цикл просто не выполняется).
        v = par[u]
        while v != u:
            R[v] = rval(ch0[v]) + rval(ch1[v])
            leaves[v] = lval(ch0[v]) + lval(ch1[v])
            if leaves[v] == 1:
                break
            alpha[v] = (leafc[v] - R[v]) / (leaves[v] - 1)
            heapq.heappush(h, (alpha[v], v))
            if v == 0:
                break
            v = par[v]
        pts.append((leaves[0], R[0]))
        if leaves[0] == 1:
            break
    return pts


CASES = [
    (b"abababababababab", 8),
    (b"the quick brown fox jumps over the lazy dog the quick brown fox", 8),
    (b"the quick brown fox jumps over the lazy dog", 12),
    (bytes((i * 37 + 11) % 256 for i in range(64)), 10),
    (b"hello world hello world hello world", 12),
    (b"\x00" * 32, 8),
    (b"a", 4),
]


def self_check():
    fail = 0
    for cost in ("entropy", "kt"):
        print(f"--- модель стоимости: {cost} ---")
        fail += _check_model(cost)
    print("ПРОВАЛЕНО" if fail else "все проверки пройдены (обе модели)")
    return fail


def _check_model(cost):
    fail = 0
    for data, depth in CASES:
        nodes = build_tree(data, depth)
        max_m = min(24, len(nodes))
        dp = ExactDP(nodes, max_m, cost).frontier(max_m)
        pts = weakest_link_frontier(nodes, cost)
        ok = True
        worst_gap = 0.0
        worst_m = None
        n_exact = 0
        for m in range(1, max_m + 1):
            cand = [C for L, C in pts if L <= m]
            if not cand:
                continue
            b = min(cand)
            d = dp[m - 1]
            if b < d - 1e-9:
                print(f"  НАРУШЕНИЕ: M={m} оболочка={b:.4f} < DP={d:.4f}")
                ok = False
            gap = (b - d) / max(d, 1e-9)
            if gap > worst_gap:
                worst_gap, worst_m = gap, m
            if abs(b - d) < 1e-6:
                n_exact += 1
        print(
            ("OK  " if ok else "FAIL"),
            f"D={depth} узлов={len(nodes)} точек={len(pts)} "
            f"листья {pts[0][0]}->{pts[-1][0]} | совпало с DP: {n_exact}/{max_m} "
            f"| макс.разрыв {worst_gap*100:.2f}% при M={worst_m}",
        )
        if not ok:
            fail += 1
    return fail


if __name__ == "__main__":
    sys.exit(self_check())
