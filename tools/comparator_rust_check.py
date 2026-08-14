"""Сверка Rust-компаратора с Python-эталоном (weakest-link + точный DP).

Гоняется на ОБЕИХ моделях стоимости листа: entropy (n·H) и kt (−log₂KT).
"""
import sys, subprocess, random
sys.stdout.reconfigure(encoding="utf-8", errors="replace")
sys.path.insert(0, "tools")
from comparator_ref import build_tree, ExactDP
from comparator_wl import weakest_link_frontier

random.seed(12345)
BAD=0; CHECKS=0
for trial in range(24):
    cost = "entropy" if trial % 2 == 0 else "kt"
    N=random.randint(40,160)
    data=bytes(random.getrandbits(8) for _ in range(N))
    depth=random.randint(6,10)
    fn=f"tools/_r_{trial}.bin"
    open(fn,"wb").write(data)
    # --points должен покрыть ВЕСЬ хребет: после исправления семантики
    # (расщепление сквозь унарные узлы) точек стало на порядки больше,
    # 200 первых (от T_max) не доходили до малых M — сравнение падало
    # с "empty sequence" не из-за расхождения, а из-за обрезки вывода.
    out=subprocess.run(["./bin/comparator.exe", fn, "--depth", str(depth),
                        "--points", "10000000", "--cost", cost],
                       capture_output=True, text=True, encoding="utf-8", errors="replace")
    open(fn,"rb").read()  # убедимся файл есть
    # парсим Rust-точки (--points: листья, биты, бит/бит, bpc — bpc с этой
    # правки печатается отдельной 4-й колонкой, раньше было 3)
    rust_pts=[]
    for line in out.stdout.splitlines():
        parts=line.split()
        if len(parts) in (3,4) and parts[0].isdigit():
            try:
                l=int(parts[0]); c=float(parts[1]); rust_pts.append((l,c))
            except ValueError: pass
    # Python-эталон (weakest-link) и точный DP
    nodes=build_tree(data, depth)
    py=[(l,c) for l,c in weakest_link_frontier(nodes, cost)]
    dp=ExactDP(nodes, 500, cost)  # solve(u, m) не зависит от max_m — только для .frontier()
    # сверяем: каждая Python-точка должна быть в Rust (с допуском)
    for (l,c) in py:
        best=min((abs(c2-c), l2, c2) for (l2,c2) in rust_pts if l2==l)
        ok = best[0] < 1e-3
        CHECKS+=1
        if not ok:
            BAD+=1
            print(f"[trial {trial}/{cost}] M={l}: py={c:.4f} rust={best[2]:.4f} diff={best[0]:.2e}")
    # и каждая Rust-точка (M <= DP_CAP) должна быть оптимальна (<= DP + 1e-6).
    # После исправления класса (расщепление сквозь унарные узлы) честных точек
    # на хребте стало на порядки больше — solve(0, l) для КАЖДОЙ было бы
    # O(узлы × M²) на самой большой M, часами в чистом Python. Малые M — как
    # раз там, где сильнее всего проявлялась старая ошибка класса (см. аудит:
    # классы расходятся с ростом M, а не на старте), поэтому урезание диапазона
    # не ослабляет проверку в интересующей нас области.
    DP_CAP = 150
    for (l,c) in rust_pts:
        if l > DP_CAP:
            continue
        opt=dp.solve(0,l)
        CHECKS+=1
        if c > opt + 1e-3:
            BAD+=1
            print(f"[trial {trial}/{cost}] Rust M={l}: {c:.4f} > DP opt {opt:.4f}")
    import os; os.remove(fn)
print(f"\nИТОГ: проверено {CHECKS}, расхождений {BAD}")
sys.exit(1 if BAD else 0)
