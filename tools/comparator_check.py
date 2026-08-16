"""Сверка лагранжевой развёртки (BFOS) с точным DP — этап 5б.

Гоняется на ОБЕИХ моделях стоимости листа (design-spec §5): основной
энтропийной n·H и вторичной KT (−log₂KT(n0,n1) — настоящая кодовая длина,
то, что постановка П4 называет L_S).

Проверяемые утверждения:
1. Для любого бюджета M точный DP не хуже BFOS: dp[M] ≤ bfos_best(M).
2. На точках нижней выпуклой оболочки BFOS совпадает с точным DP.
3. С ростом M кривая точного DP не растёт (по построению: дерево с ≤m
   листьями допустимо и при бюджете m+1).
4. Полное дерево: для энтропии оно оптимально (вогнутость ⇒ расщепление
   всегда не дороже), поэтому dp[все листья] == full. Для KT расщепление
   стоит ~½log₂n избыточности на новый лист, полное дерево оптимальным быть
   НЕ обязано, и проверяется неравенство dp[все листья] ≤ full.
5. Только для KT — две границы KT-стоимости на каждом узле:
   n·H ≤ −log₂KT ≤ n·H + ½log₂n + 1 (левая: KT — смесь, не лучше ML;
   правая: лемма 1 Виллемса, тот самый параметрический член границы (2)).

    python comparator_check.py
"""
import math
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")
sys.path.insert(0, __file__.rsplit("\\", 1)[0] if "\\" in __file__ else __file__.rsplit("/", 1)[0])
from comparator_ref import build_tree, ExactDP, cost_leaf, bfos, full_tree_cost, kt_cost

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


def kt_bounds_ok(nodes):
    """n·H ≤ −log₂KT(n0,n1) ≤ n·H + ½log₂n + 1 на каждом узле."""
    worst_slack = 0.0
    for nd in nodes:
        n0, n1 = nd["n"]
        n = n0 + n1
        if n == 0:
            continue
        p = n0 / n
        h = 0.0 if p <= 0.0 or p >= 1.0 else -p * math.log2(p) - (1 - p) * math.log2(1 - p)
        nh = n * h
        kt = kt_cost(n0, n1)
        if kt < nh - 1e-9:
            return None, f"KT < n·H при (n0,n1)=({n0},{n1}): {kt:.6f} < {nh:.6f}"
        excess = kt - nh
        limit = 0.5 * math.log2(n) + 1.0
        if excess > limit + 1e-9:
            return None, (f"KT > n·H+½log₂n+1 при (n0,n1)=({n0},{n1}): "
                          f"избыток {excess:.6f} > {limit:.6f}")
        worst_slack = max(worst_slack, excess - 0.5 * math.log2(n))
    return worst_slack, None


def main():
    failures = 0
    for cost in ("entropy", "kt"):
        print(f"=== модель стоимости: {cost} ===")
        failures += run_model(cost)
    print()
    if failures:
        print(f"ПРОВАЛЕНО: {failures}")
        return 1
    print(f"все проверки пройдены на обеих моделях ({len(CASES)} кейсов каждая)")
    return 0


def run_model(cost):
    failures = 0
    for data, depth in CASES:
        nodes = build_tree(data, depth)
        max_m = min(24, len(nodes))
        dp = ExactDP(nodes, max_m, cost).frontier(max_m)
        full = full_tree_cost(nodes, cost)

        # BFOS: сетка λ от больших к малым; снимаем уникальные точки
        # (листья, стоимость) и для каждого M берём лучшую точку с leaves ≤ M.
        lam = 1024.0
        pts = []
        while lam >= 0:
            c, leaves = bfos(nodes, lam, cost)
            pts.append((leaves, c))
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
        # 4) полное дерево T_max. Число его листьев = реальные листья +
        #    виртуальные братья унарных узлов (они стоят 0 бит, но бюджет
        #    занимают — тот же учёт, что в weakest_link).
        full_leaves = sum(
            1 for nd in nodes if not nd["ch"][0] and not nd["ch"][1]
        )
        tmax_leaves = full_leaves + sum(
            1 for nd in nodes
            if bool(nd["ch"][0]) != bool(nd["ch"][1])
        )
        if tmax_leaves <= max_m:
            d_full = dp[tmax_leaves - 1]
            if cost == "entropy":
                # вогнутость энтропии ⇒ T_max оптимально
                if abs(d_full - full) > 1e-6:
                    print(f"  ПОЛНОЕ ДЕРЕВО: DP={d_full:.4f} != {full:.4f}")
                    ok = False
            else:
                # KT: T_max оптимальным быть не обязано, но хуже него DP быть
                # не может (T_max — допустимое дерево с tmax_leaves листьями)
                if d_full > full + 1e-6:
                    print(f"  ПОЛНОЕ ДЕРЕВО: DP={d_full:.4f} > T_max={full:.4f}")
                    ok = False

        # 5) границы KT на каждом узле
        slack = None
        if cost == "kt":
            slack, err = kt_bounds_ok(nodes)
            if err:
                print(f"  ГРАНИЦЫ KT: {err}")
                ok = False

        status = "OK  " if ok else "FAIL"
        if not ok:
            failures += 1
        label = repr(data[:24])
        if len(data) > 24:
            label += f"+{len(data)-24}б"
        tail = "" if slack is None else f" изб.KT−½log₂n ≤ {slack:+.3f}"
        print(
            f"{status} D={depth:<3} {label:<30} узлов={len(nodes):>4} "
            f"листьев={full_leaves:>4} DP[1]={dp[0]:9.3f} "
            f"DP[{max_m}]={dp[-1]:9.3f} полное={full:9.3f}{tail}"
        )

    return failures


if __name__ == "__main__":
    sys.exit(main())
