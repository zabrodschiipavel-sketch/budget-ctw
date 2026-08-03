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

Дерево полное (см. comparator_ref.build_tree): у каждого внутреннего узла
два ребёнка, виртуальные листья имеют нулевые счётчики и стоимость 0.
"""
import heapq
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")
sys.path.insert(0, "tools")
from comparator_ref import build_tree, ExactDP, cost_leaf


def weakest_link_frontier(nodes):
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

    def kill_subtree(u):
        """Пометить поддерево u как не входящее в дерево (мёртвое)."""
        stack = [u]
        while stack:
            w = stack.pop()
            alive[w] = False
            if ch0[w]:
                stack.append(ch0[w])
            if ch1[w]:
                stack.append(ch1[w])

    for u in range(n - 1, -1, -1):
        if ch0[u] and ch1[u]:
            R[u] = R[ch0[u]] + R[ch1[u]]
            leaves[u] = leaves[ch0[u]] + leaves[ch1[u]]
        else:
            # узел с ≤1 ребёнком: лист. Его поддерево (если есть) в полное
            # дерево не входит: c(u) = 0, спуск не может дать меньше.
            R[u] = cost_leaf(nodes, u)
            leaves[u] = 1
            if ch0[u]:
                kill_subtree(ch0[u])
            if ch1[u]:
                kill_subtree(ch1[u])
    pts = [(leaves[0], R[0])]

    alpha = {}

    def push(u):
        if alive[u] and ch0[u] and ch1[u] and leaves[u] > 1:
            a = (cost_leaf(nodes, u) - R[u]) / (leaves[u] - 1)
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
        # отщипываем u: узел становится листом; всё его поддерево выбывает
        # из кандидатов (вклад потомков уже учтён в листе u)
        stack = [u]
        while stack:
            w = stack.pop()
            alive[w] = False
            if ch0[w]:
                stack.append(ch0[w])
            if ch1[w]:
                stack.append(ch1[w])
        R[u] = cost_leaf(nodes, u)
        leaves[u] = 1
        # пересчёт предков: от родителя u вверх до корня включительно.
        # Сам u не пересчитываем — он только что стал листом (для корня
        # par[0] == 0, поэтому цикл просто не выполняется).
        v = par[u]
        while v != u:
            R[v] = R[ch0[v]] + R[ch1[v]]
            leaves[v] = leaves[ch0[v]] + leaves[ch1[v]]
            if leaves[v] == 1:
                break
            alpha[v] = (cost_leaf(nodes, v) - R[v]) / (leaves[v] - 1)
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
    for data, depth in CASES:
        nodes = build_tree(data, depth)
        max_m = min(24, len(nodes))
        dp = ExactDP(nodes, max_m).frontier(max_m)
        pts = weakest_link_frontier(nodes)
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
    print("ПРОВАЛЕНО" if fail else "все проверки пройдены")
    return fail


if __name__ == "__main__":
    sys.exit(self_check())
