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

    # Классификация узлов ядра относительно оптимального дерева. Листья
    # оптимума задают ПОЛНОЕ разбиение контекстов, поэтому любая строка
    # сравнима ровно с одним листом: она либо его предок, либо он сам, либо
    # его продолжение. Третьей категории («вообще не в дереве») быть не может,
    # и весь перерасход — это спуск глубже, чем оптимуму нужно.
    #
    # Префиксность через сортированный список листьев: u — предок листа тогда
    # и только тогда, когда следующий за u лист начинается с u.
    srt = sorted(opt)
    deeper = 0
    deeper_by_extra = defaultdict(int)   # на сколько уровней глубже листа
    for u in kernel:
        i = bisect.bisect_left(srt, u)
        if i < len(srt) and srt[i].startswith(u):
            continue                      # предок листа или сам лист
        # иначе u — продолжение какого-то листа; найдём его длину
        j = i - 1
        extra = None
        while j >= 0 and len(srt[j]) > 0:
            if u.startswith(srt[j]):
                extra = len(u) - len(srt[j])
                break
            j -= 1
        deeper += 1
        deeper_by_extra[extra if extra is not None else -1] += 1
    print(f"узлов ядра глубже оптимума {deeper}/{len(kernel)} = "
          f"{100.0 * deeper / max(len(kernel), 1):.2f}%")
    print("  (строгие потомки листьев оптимума — ёмкость на расщепления,")
    print("   которые оптимальному дереву не окупаются)")
    if deeper_by_extra:
        print("  на сколько уровней глубже листа:")
        for e in sorted(deeper_by_extra):
            label = "?" if e < 0 else f"+{e}"
            print(f"    {label:>4}  {deeper_by_extra[e]:>9}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
