"""Сверка sa_prod.py (продакшн-пайплайн) против comparator_sa_ref.py (эталон,
уже сверенный с explicit) и explicit напрямую — этап 5б, после исправления
класса 2026-08-10.

Прогоняет полный пайплайн sa_prod.py (generate → merge_all →
build_tree_from_file → weakest_link_arrays) на малых/средних корпусах и
сравнивает: (а) стоимость и лист-счёт T_max; (б) полную последовательность
точек хребта — с comparator_sa_ref (тот же алгоритм, но O(depth) обход вместо
O(1) XOR-перепрыжка) и с explicit (comparator_ref.build_tree +
comparator_wl.weakest_link_frontier).

    python tools/sa_prod_check.py
"""
import random
import sys
from pathlib import Path

sys.path.insert(0, "tools")
sys.stdout.reconfigure(encoding="utf-8", errors="replace")

from comparator_ref import build_tree
from comparator_wl import weakest_link_frontier
from comparator_sa_ref import build_sa_tree, weakest_link_frontier_sa
from sa_prod import generate, merge_all, build_tree_from_file, weakest_link_arrays

random.seed(20260810)

CASES = [
    (b"abababababab", 8),
    (b"the quick brown fox jumps over the lazy dog", 12),
    (bytes(range(256)) * 4, 12),
    (b"\x00" * 40 + b"\x01" + b"\x00" * 40 + b"\x02", 32),
    (b"a" * 60 + b"b" + b"a" * 60 + b"c" + b"a" * 20, 48),
    (bytes([0, 0, 0, 1]) * 30, 40),
]
# несколько случайных корпусов на разных глубинах — стресс сжатия
for _ in range(6):
    n = random.randint(200, 2000)
    data = bytes(random.getrandbits(8) for _ in range(n))
    depth = random.choice([8, 16, 24, 32, 48])
    CASES.append((data, depth))


def run_sa_prod(data: bytes, depth: int, tmp: Path):
    created = []
    tmp.mkdir(parents=True, exist_ok=True)
    import time

    start = time.perf_counter()
    files, _n = generate(data, depth, tmp, created, start)
    final = merge_all(files, tmp, created, start, way=4)
    tr, n, pref_path = build_tree_from_file(final, depth, start)
    created.append(pref_path)
    pts = weakest_link_arrays(tr)
    for p in created:
        try:
            if p.exists():
                p.unlink()
        except PermissionError:
            pass
    try:
        tmp.rmdir()
    except OSError:
        pass
    return tr, pts


def main():
    fail = 0
    for i, (data, depth) in enumerate(CASES):
        e_nodes = build_tree(data, depth)
        e_pts = weakest_link_frontier(e_nodes)

        s_nodes, s_fo = build_sa_tree(data, depth)
        s_pts = weakest_link_frontier_sa(s_nodes, s_fo)

        tmp = Path(f"tools/.sa_check_tmp_{i}")
        tr, p_pts = run_sa_prod(data, depth, tmp)

        ok = True
        if len(e_pts) != len(s_pts) or len(e_pts) != len(p_pts):
            ok = False
            print(f"  ДЛИНА: explicit={len(e_pts)} sa_ref={len(s_pts)} sa_prod={len(p_pts)}")
        else:
            for (le, ce), (ls, cs), (lp, cp) in zip(e_pts, s_pts, p_pts):
                if le != ls or le != lp or abs(ce - cs) > 1e-6 or abs(ce - cp) > 1e-6:
                    ok = False
                    print(f"  ТОЧКА: explicit=({le},{ce:.4f}) sa_ref=({ls},{cs:.4f}) sa_prod=({lp},{cp:.4f})")
                    break

        status = "OK  " if ok else "FAIL"
        if not ok:
            fail += 1
        label = repr(data[:20])
        if len(data) > 20:
            label += f"+{len(data) - 20}б"
        print(
            f"{status} depth={depth:<3} {label:<28} узлов explicit={len(e_nodes):>6} "
            f"sa_ref={len(s_nodes):>5} sa_prod={len(tr):>5}  точек={len(e_pts):>4}"
        )

    print()
    if fail:
        print(f"ПРОВАЛЕНО: {fail} из {len(CASES)}")
        return 1
    print(f"все {len(CASES)} проверок пройдены")
    return 0


if __name__ == "__main__":
    sys.exit(main())
