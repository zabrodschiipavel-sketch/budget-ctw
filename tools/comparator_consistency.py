"""Согласованность двух реализаций лагранжевой развёртки: жадное
отщипывание (weakest link) и сетка по λ (bfos).

Сравниваются БЮДЖЕТНЫЕ ФУНКЦИИ — то, что реально идёт в компаратор:

    best(M) = min{ стоимость : число листьев ≤ M }

Обе реализации обязаны давать одинаковую best(M) с точностью до
дискретизации сетки λ (сетка может лишь чуть завысить — верхняя граница).
Множества точек могут отличаться на плоских участках (узлы с нулевым
выигрышем: эквивалентные деревья с разным числом листьев и той же
стоимостью) — это не ошибка.
"""
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")
sys.path.insert(0, "tools")
from comparator_ref import build_tree, bfos
from comparator_wl import weakest_link_frontier

CASES = [
    (b"abababababababab", 8),
    (b"the quick brown fox jumps over the lazy dog the quick brown fox", 8),
    (b"the quick brown fox jumps over the lazy dog", 12),
    (bytes((i * 37 + 11) % 256 for i in range(64)), 10),
    (b"hello world hello world hello world", 12),
    (b"\x00" * 32, 8),
]


def budget_fn(points, max_m):
    """best[M] = min стоимость среди точек с листьями ≤ M."""
    best = [float("inf")] * (max_m + 1)
    cur = float("inf")
    # точки в порядке убывания листьев → возрастания M
    for L, C in sorted(points, reverse=True):
        pass
    pts = sorted(points)
    j = 0
    for m in range(1, max_m + 1):
        while j < len(pts) and pts[j][0] <= m:
            cur = min(cur, pts[j][1])
            j += 1
        best[m] = cur
    return best


fail = 0
for data, depth in CASES:
    nodes = build_tree(data, depth)
    wl = weakest_link_frontier(nodes)
    lam = 2.0 ** 16
    bf = []
    while lam >= 0:
        c, l = bfos(nodes, lam)
        bf.append((l, c))
        if lam == 0:
            break
        lam /= 2.0
    max_m = min(24, max(l for l, _ in wl))
    bw = budget_fn(wl, max_m)
    bb = budget_fn(bf, max_m)
    ok = True
    worst = 0.0
    for m in range(1, max_m + 1):
        if bw[m] == float("inf") or bb[m] == float("inf"):
            continue
        # WL — точная оболочка, BFOS-сетка не может быть лучше WL
        if bb[m] < bw[m] - 1e-6:
            print(f"  НАРУШЕНИЕ: M={m} BFOS={bb[m]:.4f} < WL={bw[m]:.4f}")
            ok = False
        # сетка может лишь чуть завысить
        gap = (bb[m] - bw[m]) / max(bw[m], 1e-9)
        worst = max(worst, gap)
    print(
        ("OK  " if ok else "FAIL"),
        f"D={depth} узлов={len(nodes)} WL={len(wl)} BFOS={len(bf)} "
        f"макс.завышение BFOS {worst*100:.2f}%",
    )
    if not ok:
        fail += 1
print("ПРОВАЛЕНО" if fail else "все проверки пройдены")
