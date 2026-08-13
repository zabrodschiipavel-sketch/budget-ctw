"""Сверка bin/sa_frontier.exe (Rust-порт build+frontier) с Python-эталонами.

Rust-порт нужен потому, что честное дерево D=48/100 МБ в Python не влезает
(~30 ГБ, см. notes/stage5b-comparator-results.md). Здесь он проверяется на
размерах, где Python ещё считает: строит тот же отсортированный .npy через
sa_prod.generate + merge_all, затем сравнивает

  Rust sa_frontier   vs   sa_prod.weakest_link_arrays (Python SA)
                     vs   comparator_wl.weakest_link_frontier (explicit)

по числу листьев T_max, стоимости T_max и ответам на бюджеты.

    python tools/sa_frontier_check.py
"""
import random
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, "tools")
sys.stdout.reconfigure(encoding="utf-8", errors="replace")

from comparator_ref import build_tree
from comparator_wl import weakest_link_frontier
from sa_prod import generate, merge_all, build_tree_from_file, weakest_link_arrays

EXE = Path("bin/sa_frontier.exe")
BUDGETS = [10, 100, 1000, 10000]

random.seed(20260811)
CASES = [
    (b"the quick brown fox jumps over the lazy dog the quick brown fox", 8),
    (bytes(range(256)) * 4, 12),
    (b"\x00" * 40 + b"\x01" + b"\x00" * 40 + b"\x02", 32),
    (b"a" * 60 + b"b" + b"a" * 60 + b"c" + b"a" * 20, 48),
]
for _ in range(5):
    n = random.randint(500, 4000)
    CASES.append((bytes(random.getrandbits(8) for _ in range(n)),
                  random.choice([8, 16, 24, 32, 48])))
# реальный текст
enwik = Path(r"C:\Users\pavel\budget-ctw\data\enwik8")
if enwik.exists():
    raw = enwik.read_bytes()[:60000]
    CASES.append((raw[:20000], 24))
    CASES.append((raw, 48))


def best_for(pts, m):
    """Лучшая (минимальная) стоимость среди точек с листьями ≤ m."""
    cand = [c for l, c in pts if l <= m]
    return min(cand) if cand else float("inf")


def main() -> int:
    if not EXE.exists():
        print(f"нет {EXE} — собери: rustc -O --edition 2021 -o {EXE} tools/sa_frontier.rs")
        return 2
    fails = 0
    for idx, (data, depth) in enumerate(CASES):
        tmp = Path(f"tools/.sa_fr_{idx}")
        tmp.mkdir(parents=True, exist_ok=True)
        created: list[Path] = []
        start = time.perf_counter()
        files, _n = generate(data, depth, tmp, created, start)
        merged = merge_all(files, tmp, created, start, way=4)

        # Rust
        out = subprocess.run(
            [str(EXE), str(merged), "--depth", str(depth),
             "--budgets", ",".join(str(b) for b in BUDGETS)],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
        )
        if out.returncode != 0:
            print(f"FAIL depth={depth} len={len(data)}: sa_frontier вернул {out.returncode}\n{out.stderr}")
            fails += 1
            continue
        rust = {}
        rust_budgets = {}
        for line in out.stdout.splitlines():
            p = line.split()
            if line.startswith("листья (полное дерево)"):
                rust["leaves"] = int(p[-1])
            elif line.startswith("стоимость полного дерева"):
                rust["cost"] = float(p[3])
            elif len(p) == 4 and p[0].isdigit():
                rust_budgets[int(p[0])] = float(p[1])

        # Python SA (тот же алгоритм) и explicit
        tr, _N, pref = build_tree_from_file(merged, depth, start)
        created.append(pref)
        py_pts = weakest_link_arrays(tr)
        ex_pts = weakest_link_frontier(build_tree(data, depth))

        ok = True
        if rust.get("leaves") != py_pts[0][0] or py_pts[0][0] != ex_pts[0][0]:
            ok = False
            print(f"  ЛИСТЬЯ: rust={rust.get('leaves')} py={py_pts[0][0]} explicit={ex_pts[0][0]}")
        if abs(rust.get("cost", -1) - py_pts[0][1]) > 1e-3 or abs(py_pts[0][1] - ex_pts[0][1]) > 1e-6:
            ok = False
            print(f"  СТОИМОСТЬ: rust={rust.get('cost')} py={py_pts[0][1]} explicit={ex_pts[0][1]}")
        for m in BUDGETS:
            pb, eb = best_for(py_pts, m), best_for(ex_pts, m)
            rb = rust_budgets.get(m, float("inf"))
            if abs(pb - eb) > 1e-6 or (rb != float("inf") or pb != float("inf")) and abs(rb - pb) > 1e-3:
                ok = False
                print(f"  БЮДЖЕТ M={m}: rust={rb} py={pb} explicit={eb}")

        print(f"{'OK  ' if ok else 'FAIL'} depth={depth:<3} len={len(data):<6} "
              f"листьев={py_pts[0][0]:<9} точек={len(py_pts):<7} узлов={len(tr)}")
        if not ok:
            fails += 1

        del tr
        import gc
        gc.collect()
        for p in created:
            try:
                if p.exists():
                    p.unlink()
            except (PermissionError, FileNotFoundError):
                pass
        try:
            tmp.rmdir()
        except OSError:
            pass

    print()
    if fails:
        print(f"ПРОВАЛЕНО: {fails} из {len(CASES)}")
        return 1
    print(f"все {len(CASES)} проверок пройдены")
    return 0


if __name__ == "__main__":
    sys.exit(main())
