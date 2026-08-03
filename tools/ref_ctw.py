"""Точный эталон CTW для проверки целочисленного ядра (этап 3).

Считает кодовую длину ПО ОПРЕДЕЛЕНИЮ, а не по β-рекурсии:

    P_e(s)  — KT-оценка из финальных счётчиков узла (точная дробь),
    P_w(s)  = P_e(s),                             если глубина s = D,
    P_w(s)  = ½·P_e(s) + ½·P_w(0s)·P_w(1s),       иначе,
    L       = −log₂ P_w(корень).

Это независимый путь вычисления: ядро на Rust получает то же число, поднимаясь
инкрементно по log β, а здесь оно собирается из счётчиков одним проходом по дереву.
Совпадение результатов проверяет саму рекурсию, а не только арифметику.

Арифметика точная (Fraction), поэтому пригодно только для коротких входов.

    python ref_ctw.py <файл> --depth D [--limit N]
"""
import argparse
import math
import sys
from fractions import Fraction

sys.stdout.reconfigure(encoding="utf-8", errors="replace")  # консоль Windows не UTF-8


def kt_prob(a, b):
    """KT-оценка вероятности последовательности из a нулей и b единиц.

    P_e(a,b) = [∏_{i=1..a}(i−½)·∏_{j=1..b}(j−½)] / (a+b)!
    """
    num = Fraction(1)
    for i in range(1, a + 1):
        num *= Fraction(2 * i - 1, 2)
    for j in range(1, b + 1):
        num *= Fraction(2 * j - 1, 2)
    den = math.factorial(a + b)
    return num / den


def build_counts(bits, depth, lazy=0):
    """Симуляция эволюции дерева тем же правилом, что и в ядре.

    Соглашения совпадают с ядром на Rust: история стартует с нулей, узел на
    глубине d — это последние d бит, самый свежий бит первый, счётчики
    инкрементируются на всём ПРОЙДЕННОМ пути. Ключ узла — кортеж бит контекста
    (пустой кортеж = корень).

    При lazy > 0 ребёнок создаётся, только когда родитель посещён не менее lazy
    раз, поэтому спуск обрывается выше предельной глубины и дерево получается
    неравноглубоким.

    Возвращает финальные счётчики и снимок счётчиков каждого узла на момент,
    когда у него появился первый ребёнок (то есть когда он перестал быть листом).
    Снимок берётся ДО инкремента текущим символом: символ, на котором ребёнок
    создан, относится уже к внутренней фазе — так же, как в ядре.
    """
    counts = {(): [0, 0]}
    became_internal = {}
    hist = 0
    for x in bits:
        path = [()]
        ctx = ()
        for d in range(depth):
            child = ctx + (((hist >> d) & 1),)
            if child not in counts:
                if counts[ctx][0] + counts[ctx][1] < lazy:
                    break
                counts[child] = [0, 0]
                if ctx not in became_internal:
                    became_internal[ctx] = list(counts[ctx])
            ctx = child
            path.append(ctx)
        for c in path:
            counts[c][x] += 1
        hist = (hist << 1) | x
    return counts, became_internal


def weighted_prob(counts, became_internal, ctx, depth):
    """P_w(ctx) по определению. Непосещённый узел даёт P_w = 1 (пустая история).

    Узел, у которого так и не появилось детей (предельная глубина или ленивый
    порог), — лист: P_w = P_e по всем его данным.

    У остальных данные разбиты на две фазы. До появления первого ребёнка узел
    был листом и кодировал сам, поэтому его вклад — P_e(лист-фаза). После
    появления ребёнка начинается смешивание, но только по последующим данным:

        P_w(s) = P_e(лист) · ½·[ P_e(всё)/P_e(лист) + P_w(0s)·P_w(1s) ]

    Отношение P_e(всё)/P_e(лист) — это ровно произведение условных KT за
    внутреннюю фазу: счётчики KT продолжаются, а не сбрасываются при переходе.

    Такое разбиение — не вольность, а единственный вариант, оставляющий модель
    распределением. Считать смесь по ВСЕМ данным узла нельзя: свежие дети тогда
    получают вероятность 1 за данные, которых не видели, и Σ_x P(x) > 1.
    """
    node = counts.get(ctx)
    if node is None:
        return Fraction(1)
    pe_all = kt_prob(node[0], node[1])
    if ctx not in became_internal:
        return pe_all
    snap = became_internal[ctx]
    pe_leaf = kt_prob(snap[0], snap[1])
    p0 = weighted_prob(counts, became_internal, ctx + (0,), depth)
    p1 = weighted_prob(counts, became_internal, ctx + (1,), depth)
    return pe_leaf * (pe_all / pe_leaf + p0 * p1) / 2


def log2_fraction(fr):
    """log₂ точной дроби без переполнения float."""

    def log2_int(n):
        b = n.bit_length()
        shift = max(0, b - 53)
        return math.log2(n >> shift) + shift

    return log2_int(fr.numerator) - log2_int(fr.denominator)


def code_length(data, depth, lazy=0):
    """Кодовая длина в битах для последовательности байт."""
    bits = [(byte >> k) & 1 for byte in data for k in range(7, -1, -1)]
    counts, became = build_counts(bits, depth, lazy)
    pw = weighted_prob(counts, became, (), depth)
    return -log2_fraction(pw), len(counts)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("file")
    ap.add_argument("--depth", type=int, default=8)
    ap.add_argument("--limit", type=int, default=None)
    args = ap.parse_args()

    data = open(args.file, "rb").read()
    if args.limit is not None:
        data = data[: args.limit]

    sys.setrecursionlimit(10000 + args.depth * 100)
    bits, nodes = code_length(data, args.depth)
    print(f"байт            {len(data)}")
    print(f"глубина         {args.depth} бит")
    print(f"узлов           {nodes}")
    print(f"кодовая длина   {bits:.6f} бит")
    if data:
        print(f"bpc             {bits / len(data):.6f}")


if __name__ == "__main__":
    main()
