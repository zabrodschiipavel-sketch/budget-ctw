"""Кривая утечки качества от вытеснения (этап 5).

Меряет то, ради чего задача и поставлена: насколько budget-CTW отстаёт от полного
CTW при заданном бюджете памяти — и что происходит на глубинах, где полный CTW
не помещается в память вовсе.

    python leak_curve.py <корпус> [--depths 16,20,24] [--deep 32,48]
                         [--budgets 65536,262144,1048576,4194304] [--limit N]

Глубины из --depths прогоняются и полным, и бюджетным вариантом (нужен базлайн).
Глубины из --deep — только бюджетным: там полное дерево не помещается, и это
самостоятельный результат, а не пропуск.
"""
import argparse
import os
import re
import subprocess
import sys
import time

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

NODE_BYTES = 40


def run(binary, corpus, depth, budget=None, limit=None, **kw):
    cmd = [binary, corpus, "--depth", str(depth)]
    if budget is not None:
        cmd += ["--budget", str(budget)]
    if limit is not None:
        cmd += ["--limit", str(limit)]
    for k, v in kw.items():
        cmd += ["--" + k.replace("_", "-"), str(v)]
    t0 = time.monotonic()
    out = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8")
    dt = time.monotonic() - t0
    if out.returncode != 0:
        return None
    g = lambda f: re.search(rf"^{f}\s+(\S+)", out.stdout, re.M).group(1)
    return dict(bpc=float(g("bpc")), nodes=int(g("узлов")), mem=int(g("память")),
                ev=int(g("вытеснено")), sec=dt)


def ceiling_nodes(depth, nbits):
    """Верхняя оценка размера полного дерева: Σ_d min(2^d, T)."""
    return sum(min(1 << d, nbits) for d in range(depth + 1))


def main():
    ap = argparse.ArgumentParser()
    here = os.path.dirname(os.path.abspath(__file__))
    ap.add_argument("corpus")
    ap.add_argument("--bin", default=os.path.join(here, "..", "bin", "ctw.exe"))
    ap.add_argument("--depths", default="16,20,24")
    ap.add_argument("--deep", default="32,48")
    ap.add_argument("--budgets", default="65536,262144,1048576,4194304")
    ap.add_argument("--limit", type=int, default=None)
    args = ap.parse_args()

    size = os.path.getsize(args.corpus)
    if args.limit:
        size = min(size, args.limit)
    nbits = size * 8
    depths = [int(d) for d in args.depths.split(",") if d]
    deep = [int(d) for d in args.deep.split(",") if d]
    budgets = [int(b) for b in args.budgets.split(",") if b]

    print(f"корпус {size} байт ({nbits} бит), узел {NODE_BYTES} байт\n")

    print("Оценка полного дерева (Σ_d min(2^d, T)) — что вообще посчитаемо:")
    for d in sorted(set(depths + deep)):
        c = ceiling_nodes(d, nbits)
        print(f"  D={d:<3} ≤ {c:>15,} узлов ≈ {c*NODE_BYTES/2**30:>10.2f} ГБ")
    print()

    full = {}
    for d in depths:
        r = run(args.bin, args.corpus, d, limit=args.limit)
        if r is None:
            print(f"D={d}: полный CTW не отработал (вероятно, памяти не хватило)")
            continue
        full[d] = r
        print(f"полный CTW D={d}: {r['bpc']:.4f} bpc, {r['nodes']:,} узлов, "
              f"{r['mem']/2**20:.0f} МБ, {r['sec']:.0f} с")
    print()

    print("бюджетный CTW (victim=lfu, birth=cold):")
    print(f"{'D':>3} {'бюджет':>10} {'память':>10} {'bpc':>8} {'утечка':>8} "
          f"{'вытесн/бит':>11} {'сек':>6}")
    for d in depths + deep:
        for b in budgets:
            r = run(args.bin, args.corpus, d, budget=b, limit=args.limit)
            if r is None:
                print(f"{d:>3} {b:>10,} — прогон не удался")
                continue
            leak = f"{r['bpc'] - full[d]['bpc']:+8.4f}" if d in full else "     n/a"
            print(f"{d:>3} {b:>10,} {r['mem']/2**20:>9.0f}М {r['bpc']:>8.4f} {leak} "
                  f"{r['ev']/nbits:>11.2f} {r['sec']:>6.0f}")
        print()

    if deep:
        print("Глубины из --deep базлайна не имеют по построению: полное дерево там")
        print("не помещается в память. Это и есть содержательный результат — на таких")
        print("глубинах бюджетный вариант не «дешевле» полного, а единственно возможный.")


if __name__ == "__main__":
    sys.exit(main() or 0)
