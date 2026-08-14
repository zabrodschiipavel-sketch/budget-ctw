"""Насколько удержанное ядром дерево совпадает с оптимальным того же размера.

Вход:
  * дамп ядра — `ctw --dump-tree ФАЙЛ`: по строке на КАЖДЫЙ удержанный узел,
    контекст цепочкой битов от самого свежего;
  * дамп оптимума — `comparator --dump-optimal ФАЙЛ --dump-at M`: по строке на
    ЛИСТ оптимального дерева при ≤M листьях, формат `<контекст> <n0> <n1>`.

Зачем. Замер [stage10 §6](../notes/stage10-upper-bound.md) показал, что
сожаление budget-CTW целиком структурное: параметрическая часть отрицательна,
весь положительный остаток даёт структура, которую удержал бюджет. Значит
доказывать в пункте (2) надо утверждение «LFU удерживает почти оптимальное
дерево», и первый вопрос к нему — а насколько почти? Здесь это меряется
напрямую: какая доля листьев оптимума (и какая доля обращений) вообще
присутствует в арене ядра.

Различаются три вещи, и путать их нельзя:
  * лист оптимума НАБЛЮДАЛСЯ (n0+n1 > 0) — ядро в принципе могло его удержать;
  * лист оптимума ВИРТУАЛЬНЫЙ (0 0) — контекст ни разу не встретился, ядро
    такой узел не создаёт никогда, и стоит он 0 бит; в покрытие не входит;
  * узел ядра БЕСПОЛЕЗЕН, если он не лист оптимума и не предок его листа.

    python tools/structure_overlap.py <дамп_ядра> <дамп_оптимума>
"""
import bisect
import sys
from collections import defaultdict

sys.stdout.reconfigure(encoding="utf-8", errors="replace")


def read_kernel(path):
    out = []
    with open(path, encoding="utf-8", errors="replace") as f:
        for line in f:
            s = line.strip()
            if s:
                out.append(s)
    return out


def read_optimal(path):
    leaves = {}
    with open(path, encoding="utf-8", errors="replace") as f:
        for line in f:
            p = line.split()
            if len(p) != 3:
                continue
            ctx = "" if p[0] == "-" else p[0]
            leaves[ctx] = int(p[1]) + int(p[2])
    return leaves


def main() -> int:
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    kernel = read_kernel(sys.argv[1])
    opt = read_optimal(sys.argv[2])
    kset = set(kernel)

    observed = {c: m for c, m in opt.items() if m > 0}
    virtual = len(opt) - len(observed)
    total_mass = sum(observed.values())

    hit = [c for c in observed if c in kset]
    hit_mass = sum(observed[c] for c in hit)

    print(f"листьев оптимума        {len(opt)}")
    print(f"  наблюдённых           {len(observed)}")
    print(f"  виртуальных (0 бит)   {virtual}")
    print(f"узлов ядра              {len(kernel)}")
    print()
    print(f"покрытие по листьям     {len(hit)}/{len(observed)} = "
          f"{100.0 * len(hit) / max(len(observed), 1):.2f}%")
    print(f"покрытие по обращениям  {hit_mass}/{total_mass} = "
          f"{100.0 * hit_mass / max(total_mass, 1):.4f}%")
    print()

    # Промахи: где именно ядро не удержало лист оптимума.
    miss_by_depth = defaultdict(lambda: [0, 0])   # глубина → [штук, масса]
    for c, m in observed.items():
        if c not in kset:
            e = miss_by_depth[len(c)]
            e[0] += 1
            e[1] += m
    if miss_by_depth:
        print("промахи по глубине (штук, обращений, среднее обращений на лист):")
        for d in sorted(miss_by_depth):
            k, m = miss_by_depth[d]
            print(f"  d={d:<3} {k:>9}  {m:>12}  {m / k:>8.1f}")
        print()

    # Бесполезные узлы ядра: не лист оптимума и не предок его листа.
    # Проверка префиксности через сортированный список листьев: строка u —
    # префикс какого-то листа тогда и только тогда, когда лист, следующий за u
    # в лексикографическом порядке, начинается с u.
    srt = sorted(opt)
    useless = 0
    for u in kernel:
        i = bisect.bisect_left(srt, u)
        if i < len(srt) and srt[i].startswith(u):
            continue
        useless += 1
    print(f"узлов ядра вне оптимума {useless}/{len(kernel)} = "
          f"{100.0 * useless / max(len(kernel), 1):.2f}%")
    print("  (не лист оптимума и не предок его листа — потраченная ёмкость)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
