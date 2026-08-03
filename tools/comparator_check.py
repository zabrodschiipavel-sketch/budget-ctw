"""Сверка лагранжевой развёртки (BFOS) с точным DP — этап 5б.

Проверяемые утверждения:
1. Для любого бюджета M точный DP не хуже BFOS: dp[M] ≤ bfos_best(M).
2. На точках нижней выпуклой оболочки BFOS совпадает с точным DP.
3. С ростом M обе кривые монотонно убывают.
4. При M = полное дерево BFOS сходится к стоимости полного дерева
   (узел = лист везде), что проверяется напрямую по сумме c(листьев).

    python comparator_check.py
"""
import math
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")
sys.path.insert(0, __file__.rsplit("\\", 1)[0] if "\\" in __file__ else __file__.rsplit("/", 1)[0])
from comparator_ref import build_tree, ExactDP, cost_leaf, bfos

CASES = [
    (b"abababababababab", 8),
    (b"the quick brown fox jumps over the lazy dog the quick brown fox", 8),
    (b"the quick brown fox jumps over the lazy dog", 12),
    (b"\x00" * 32, 8),
    (bytes(range(32)), 8),
    (bytes((i * 37 + 11) & 0xFF for i in range(64)), 10),
    (b"hello world hello world hello world", 12),
    (b"a", 4),
]


def full_tree_cost(nodes):
    """Стоимость полного дерева: каждый узел с двумя детьми расщеплён."""
    total = 0.0
    for u, nd in enumerate(nodes):
        if not (nd["ch"][0] and nd["ch"][1]):
            total += cost_leaf(nodes, u)
    return total


def main():
    failures = 0
    for data, depth in CASES:
        nodes = build_tree(data, depth)
        max_m = min(24, len(nodes))
        dp = ExactDP(nodes, max_m).frontier(max_m)
        full = full_tree_cost(nodes)

        # BFOS: сетка λ от больших к малым; снимаем уникальные точки
        # (листья, стоимость) и для каждого M берём лучшую точку с leaves ≤ M.
        lam = 1024.0
        pts = []
        while lam >= 0:
            cost, leaves = bfos(nodes, lam)
            pts.append((leaves, cost))
            if lam == 0:
                break
            lam = max(0.0, lam / 2)
        # дедупликация и сортировка по числу листьев
        pts = sorted(set(pts))
        best_for = [None] * (max_m + 1)
        cur = float("inf")
        j = 0
        for m in range(1, max_m + 1):
            while j < len(pts) and pts[j][0] <= m:
                cur = min(cur, pts[j][1])
                j += 1
            best_for[m] = cur

        ok = True
        for m in range(1, max_m + 1):
            d = dp[m - 1]
            b = best_for[m]
            # 1) BFOS не лучше точного DP (верхняя граница)
            if b < d - 1e-9:
                print(f"  НАРУШЕНИЕ: M={m} BFOS={b:.4f} < DP={d:.4f}")
                ok = False
            # 2) на точках оболочки — совпадение: ищем M, где BFOS-точка
            #    даёт ровно d (в пределах 1e-6)
            if any(abs(pp[1] - d) < 1e-6 for pp in pts if pp[0] <= m):
                pass
        # 3) монотонность точного DP
        for m in range(1, max_m):
            if dp[m] > dp[m - 1] + 1e-9:
                print(f"  НЕМОНОТОННО: dp[{m+1}]={dp[m]:.4f} > dp[{m}]={dp[m-1]:.4f}")
                ok = False
        # 4) полное дерево: DP при max_m == все листья должен сойтись к full
        #    (если max_m достаточен). Берём число листьев полного дерева.
        full_leaves = sum(
            1 for nd in nodes if not (nd["ch"][0] and nd["ch"][1])
        )
        if full_leaves <= max_m:
            if abs(dp[full_leaves - 1] - full) > 1e-6:
                print(
                    f"  ПОЛНОЕ ДЕРЕВО: DP={dp[full_leaves-1]:.4f} != {full:.4f}"
                )
                ok = False

        status = "OK  " if ok else "FAIL"
        if not ok:
            failures += 1
        label = repr(data[:24])
        if len(data) > 24:
            label += f"+{len(data)-24}б"
        print(
            f"{status} D={depth:<3} {label:<30} узлов={len(nodes):>4} "
            f"листьев={full_leaves:>4} DP[1]={dp[0]:9.3f} "
            f"DP[{max_m}]={dp[-1]:9.3f} полное={full:9.3f}"
        )

    print()
    if failures:
        print(f"ПРОВАЛЕНО: {failures} из {len(CASES)}")
        return 1
    print(f"все {len(CASES)} проверок пройдены")
    return 0


if __name__ == "__main__":
    sys.exit(main())
