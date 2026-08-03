"""Замер масштабируемости компаратора на растущих префиксах enwik8.

    python comparator_scale.py <enwik8> [--max-mb 64]
"""
import os
import sys
import time

sys.stdout.reconfigure(encoding="utf-8", errors="replace")
sys.path.insert(0, "tools")
from comparator_ref import build_tree
from comparator_wl import weakest_link_frontier

corpus = sys.argv[1]
max_mb = 64
if len(sys.argv) > 2:
    max_mb = int(sys.argv[2])
depth = 20

with open(corpus, "rb") as f:
    data = f.read()

for mb in (1, 2, 4, 8, 16, 32, max_mb):
    chunk = data[: mb * 1024 * 1024]
    t0 = time.monotonic()
    nodes = build_tree(chunk, depth)
    t1 = time.monotonic()
    pts = weakest_link_frontier(nodes)
    t2 = time.monotonic()
    leaves0 = pts[0][0]
    # бюджетная функция: для M в логарифмической сетке
    print(
        f"{mb:>3} МБ: узлов={len(nodes):>8} листьев={leaves0:>8} "
        f"точек_оболочки={len(pts):>6} построение={t1-t0:5.1f}с "
        f"оболочка={t2-t1:5.1f}с"
    )
    sys.stdout.flush()
    if t1 - t0 > 120:
        print("  (дальше слишком медленно)")
        break
