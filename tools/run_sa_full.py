"""Полный прогон SA-компаратора: внешняя сортировка + fast build + frontier.

Использование: python tools/run_sa_full.py <корпус> [--depth 48] [--budgets ...]

Этапы:
  1. generate — векторная генерация записей (key, pos, label) чанками;
  2. merge_all — потоковое k-way слияние;
  3. build_tree_fast — блочный build (RAM-блоки, mem-поиск только верхние уровни);
  4. weakest_link_arrays — frontier с тай-брейком (alpha, first_occ, dep);
  5. печать полного дерева и бюджетной таблицы.
"""
from __future__ import annotations

import argparse
import math
import os
import sys
import time
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sa_prod import generate, merge_all, weakest_link_arrays, log  # noqa: E402
from sa_prod_fast import build_tree_fast  # noqa: E402


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("file")
    ap.add_argument("--depth", type=int, default=48)
    ap.add_argument("--budgets", default="")
    ap.add_argument("--points", type=int, default=0)
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--merge-way", type=int, default=8)
    ap.add_argument("--tmp", default=None)
    args = ap.parse_args()

    start = time.perf_counter()
    infile = Path(args.file)
    data = infile.read_bytes()
    nbits = len(data) * 8
    if nbits == 0:
        raise SystemExit("empty input")
    tmpdir = Path(args.tmp) if args.tmp else infile.parent / ".sa_tmp"
    tmp_existed = tmpdir.exists()
    tmpdir.mkdir(parents=True, exist_ok=True)
    created: list[Path] = []

    try:
        log(f"данные: {len(data)} байт = {nbits} бит", start)
        files, _ = generate(data, args.depth, tmpdir, created, start)
        log(f"генерация: {len(files)} чанков", start)
        final = merge_all(files, tmpdir, created, start, max(2, args.merge_way))
        log(f"слияние готово: {final}", start)
        tr, N, pref_path = build_tree_fast(final, args.depth, start)
        created.append(pref_path)
        pts = weakest_link_arrays(tr)
        log(f"frontier: {len(pts)} точек", start)

        # bpc = бит/БАЙТ (как в ядре и src/comparator.rs); бит/бит = bpc/8.
        nbytes = len(data)
        full_leaves, full_cost = pts[0]
        print()
        print(f"узлов в контрактированном дереве   {len(tr)}")
        print(f"точек на оболочке                  {len(pts)}")
        print(f"листья (полное дерево)             {full_leaves}")
        print(f"стоимость полного дерева {full_cost:.3f} бит "
              f"({full_cost / nbits:.6f} бит/бит, {full_cost / nbytes:.4f} bpc)")
        print()

        if args.points > 0:
            print(f"первые {args.points} точек оболочки (листья, биты, бит/бит, bpc):")
            for l, c in pts[: args.points]:
                print(f"  {l:>12}  {c:>16.3f}  {c / nbits:>10.6f}  {c / nbytes:>10.6f}")
            print()
        if args.budgets:
            budgets = [int(x) for x in args.budgets.split(",") if x]
            print("бюджет M (листья)  стоимость (бит)   бит/бит      bpc")
            for m in budgets:
                best = min((c for l, c in pts if l <= m), default=float("inf"))
                if math.isinf(best):
                    print(f"{m:>16}  — нет дерева с ≤M листьями")
                else:
                    print(f"{m:>16}  {best:>16.3f}  {best / nbits:>10.4f}  {best / nbytes:>10.4f}")
        log("готово", start)
    finally:
        if not args.keep:
            import gc
            gc.collect()
            for p in created:
                try:
                    if p.exists():
                        p.unlink()
                except PermissionError:
                    log(f"warning: не удалось удалить {p}", start)
            if not tmp_existed:
                try:
                    tmpdir.rmdir()
                except OSError:
                    pass


if __name__ == "__main__":
    main()
