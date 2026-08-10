"""Восстановительный build: только build_tree_fast + frontier по готовому
отсортированному .npy-файлу (этапы generate/merge уже выполнены).

Использование:
    python tools/sa_build_only.py <merged.npy> --depth 48 \
        --budgets 1000,10000,56000,100000,466021,500000,857401 --points 3

Входной файл НЕ удаляется. Если run_sa_full.py падает в build-фазе, но
merged-файл (sa_run_mrg_*.npy) успели скопировать — запускать этот скрипт.
"""
from __future__ import annotations

import argparse
import math
import os
import sys
import time
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sa_prod import weakest_link_arrays, log  # noqa: E402
from sa_prod_fast import build_tree_fast  # noqa: E402


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("npy")
    ap.add_argument("--depth", type=int, default=48)
    ap.add_argument("--budgets", default="")
    ap.add_argument("--points", type=int, default=0)
    args = ap.parse_args()

    start = time.perf_counter()
    final = Path(args.npy)
    if not final.exists():
        raise SystemExit(f"нет файла: {final}")
    # размер в битах: 800M записей по 8 бит = 6.4 млрд? нет: записей = бит в корпусе
    # каждая запись = один бит (ключ контекста + следующий бит). Бит корпуса = число записей.
    import numpy as np
    nbits = int(np.load(final, mmap_mode="r").shape[0])
    log(f"записей (=бит корпуса): {nbits}", start)

    tr, N, pref_path = build_tree_fast(final, args.depth, start)
    pts = weakest_link_arrays(tr)
    log(f"frontier: {len(pts)} точек", start)

    # nbits — число записей = число бит корпуса (см. комментарий выше);
    # bpc = бит/БАЙТ (как в ядре и src/comparator.rs), нужно делить на 8 раз
    # больше — bpc = бит/бит / 8 = (стоимость/nbits)/8 = стоимость/(nbits*8).
    nbytes = nbits / 8
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
    # входной файл и pref НЕ удаляем — это сохранённая точка восстановления


if __name__ == "__main__":
    main()
