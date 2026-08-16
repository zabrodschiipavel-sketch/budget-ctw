"""Показатель ципфовости распределения частот контекстов по глубинам.

Вход — вывод `bin/comparator.exe <корпус> --depth D --hist`, строки
`hist <глубина> <лог2-бакет k> <контекстов с частотой в [2^k, 2^(k+1))>`.

Зачем: пункт (2) постановки П4 требует «охарактеризовать классы
последовательностей (стационарность, ципфовость распределения контекстов), при
которых штраф есть O(M log T) или хотя бы o(T)». Пока ципфовость в заметках
проекта — согласующееся объяснение, а не измеренный факт
(notes/stage5-results.md сам это оговаривает). Здесь она измеряется.

Что считается. Для ранг-частотного закона f(r) ∝ r^(−α) число контекстов с
частотой не меньше c ведёт себя как N(≥c) ∝ c^(−1/α), поэтому наклон
log₂N(≥c) по log₂c равен −1/α. Фит — обычный МНК по бакетам, где ещё есть
статистика (N ≥ MIN_N) и куда не попадает вырожденная верхушка.

Дополнительно печатается доля контекстов, несущих 90% всех обращений: именно
она, а не сам показатель, отвечает на вопрос «есть ли что вытеснять без
потерь». Масса бакета оценивается по геометрической середине 2^k·√2 —
приближение в пределах ±20% на бакет, для доли этого достаточно.

    bin/comparator.exe data/enwik8 --depth 24 --hist > hist.txt
    python tools/zipf_fit.py hist.txt
"""
import math
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

MIN_N = 8       # бакеты с меньшим числом контекстов в фит не берём
MIN_POINTS = 4  # меньше — фит не имеет смысла


def read_hist(path):
    per_depth = {}
    src = open(path, encoding="utf-8", errors="replace") if path != "-" else sys.stdin
    with src as f:
        for line in f:
            if not line.startswith("hist "):
                continue
            _, d, k, c = line.split()
            per_depth.setdefault(int(d), {})[int(k)] = int(c)
    return per_depth


def fit_depth(buckets):
    """(α, R², число точек фита, всего контекстов, макс. бакет, доля 90% массы)."""
    kmax = max(buckets)
    total = sum(buckets.values())
    # CCDF: N(≥2^k) — суффиксная сумма
    ccdf = {}
    acc = 0
    for k in range(kmax, -1, -1):
        acc += buckets.get(k, 0)
        ccdf[k] = acc

    xs, ys = [], []
    for k in range(0, kmax + 1):
        n = ccdf[k]
        if n >= MIN_N:
            xs.append(float(k))            # log₂ c
            ys.append(math.log2(n))        # log₂ N(≥c)
    if len(xs) < MIN_POINTS:
        return None

    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    slope = sxy / sxx
    inter = my - slope * mx
    ss_tot = sum((y - my) ** 2 for y in ys)
    ss_res = sum((y - (slope * x + inter)) ** 2 for x, y in zip(xs, ys))
    r2 = 1.0 - ss_res / ss_tot if ss_tot > 0 else float("nan")
    alpha = float("inf") if slope == 0 else -1.0 / slope

    # доля контекстов, несущих 90% массы (от самых частых вниз)
    mass = {k: c * (2 ** k) * math.sqrt(2) for k, c in buckets.items()}
    total_mass = sum(mass.values())
    acc_mass, acc_ctx = 0.0, 0
    for k in sorted(buckets, reverse=True):
        acc_mass += mass[k]
        acc_ctx += buckets[k]
        if acc_mass >= 0.9 * total_mass:
            break
    return alpha, r2, n, total, kmax, acc_ctx / total


def main() -> int:
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    per_depth = read_hist(sys.argv[1])
    if not per_depth:
        print("нет строк hist — подан не тот файл?")
        return 2

    print(f"{'глубина':>7} {'контекстов':>12} {'макс.частота':>13} {'α':>7} {'R²':>7} "
          f"{'точек':>6} {'контекстов на 90% массы':>24}")
    for d in sorted(per_depth):
        res = fit_depth(per_depth[d])
        if res is None:
            print(f"{d:>7} {sum(per_depth[d].values()):>12}   — мало бакетов для фита")
            continue
        alpha, r2, npts, total, kmax, share90 = res
        print(f"{d:>7} {total:>12} {'2^' + str(kmax):>13} {alpha:>7.3f} {r2:>7.4f} "
              f"{npts:>6} {share90 * 100:>23.2f}%")
    print()
    print("α — показатель ранг-частотного закона f(r) ∝ r^(−α), фит по CCDF;")
    print("R² близкое к 1 означает, что степенной закон описывает хвост, а не")
    print("подогнан к произвольной кривой. Последний столбец — доля контекстов,")
    print("на которые приходится 90% всех обращений (оценка по бакетам).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
