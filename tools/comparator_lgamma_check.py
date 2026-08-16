"""Проверка вычисления −log₂KT(n0,n1) в компараторе.

Две части.

**1. Против точного эталона** (запускается всегда). Для малых счётчиков KT
считается точной рациональной дробью (`fractions.Fraction`), логарифм берётся
`Decimal` с 60 знаками — это ground truth, не зависящий ни от lgamma, ни от
асимптотик. Для средних счётчиков эталон — прямая сумма
Σlog₂(k+1) − Σlog₂(i+½) − Σlog₂(j+½) через `math.fsum` (точно округлённая
сумма).

**2. Rust ≡ Python** (если на stdin подан дамп). В std Rust нет lgamma, там
приближение Ланцоша плюс те же спецветки; сверяем реализации между собой на
сетке до n = 4·10⁸.

Почему это отдельная проверка: в −log₂KT = [lnΓ(n+1) + lnπ − lnΓ(n0+½) −
lnΓ(n1+½)]/ln2 при перекошенных счётчиках вычитаются почти равные огромные
числа. При (4·10⁸, 0) каждое lnΓ ≈ 1.4·10¹⁰, ответ ≈ 15 бит — прямая формула
теряет ~10 порядков и даёт ошибку 6.8·10⁻⁷ бита. Именно такие листья
(детерминированное продолжение контекста) в дереве enwik8 самые массовые,
поэтому для них есть отдельная точная ветка, и она проверяется здесь.

    python tools/comparator_lgamma_check.py                       # часть 1
    bin/comparator.exe --kt-selftest | python tools/comparator_lgamma_check.py
"""
import math
import sys
from decimal import Decimal, getcontext
from fractions import Fraction

sys.stdout.reconfigure(encoding="utf-8", errors="replace")
sys.path.insert(0, __file__.rsplit("\\", 1)[0] if "\\" in __file__ else __file__.rsplit("/", 1)[0])
from comparator_ref import kt_cost

getcontext().prec = 60

# Допуск в БИТАХ на лист. Стоимости суммируются по листьям (до 5.5·10⁸ штук
# при D=48), поэтому осмысленный критерий — абсолютная ошибка, а не
# относительная: 10⁻⁹ бита на лист даёт < 1 бита на всё дерево при полной
# корреляции ошибок, против ~1.5·10⁸ бит итоговой стоимости.
TOL_BITS = 1e-9


def tol_for(n0: float, n1: float) -> float:
    """Допуск с поправкой на разрядность.

    При min(n0,n1) ≤ 64 работает точная ветка — там держим TOL_BITS. При
    обоих больших счётчиках обе реализации идут через lnΓ, где промежуточные
    члены имеют порядок n·log₂n (при n=8·10⁸ это 2.4·10¹⁰), и double просто не
    хранит больше ~15 значащих цифр: физический предел ошибки ≈ 10⁻¹⁵·n·log₂n,
    а не TOL_BITS. Узлов с такими счётчиками единицы (на уровне их не больше
    T/n), поэтому вклад в сумму по дереву — доли бита.
    """
    n = n0 + n1
    if min(n0, n1) <= 64 or n <= 0:
        return TOL_BITS
    return max(TOL_BITS, 4e-15 * n * max(math.log2(n), 1.0))


def kt_exact(a: int, b: int) -> float:
    """Точное −log₂KT(a,b) через рациональную дробь и Decimal.ln()."""
    p = Fraction(1)
    for i in range(a):                       # сначала a нулей
        p *= Fraction(2 * i + 1, 2 * i + 2)
    for j in range(b):                       # затем b единиц
        p *= Fraction(2 * j + 1, 2 * (a + j) + 2)
    d = Decimal(p.numerator) / Decimal(p.denominator)
    return float(-d.ln() / Decimal(2).ln())


def kt_fsum(a: int, b: int) -> float:
    """Эталон для средних счётчиков: точно округлённые суммы логарифмов."""
    n = a + b
    if n == 0:
        return 0.0
    s_fact = math.fsum(math.log2(k + 1.0) for k in range(n))
    s_a = math.fsum(math.log2(i + 0.5) for i in range(a))
    s_b = math.fsum(math.log2(j + 0.5) for j in range(b))
    return s_fact - s_a - s_b


def part1() -> int:
    bad = 0
    worst = (0.0, None)

    small = [(0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (2, 3), (5, 5), (7, 1),
             (10, 0), (13, 2), (32, 0), (63, 1), (64, 64), (100, 7), (127, 0),
             (128, 0), (129, 1), (200, 200), (255, 3), (300, 64), (301, 65)]
    for a, b in small:
        want = kt_exact(a, b)
        got = kt_cost(a, b)
        err = abs(got - want)
        if err > worst[0]:
            worst = (err, (a, b, want, got))
        if err > TOL_BITS:
            bad += 1
            print(f"  ТОЧНЫЙ ЭТАЛОН (n0,n1)=({a},{b}): kt_cost={got!r} exact={want!r} Δ={err:.3e} бит")
    print(f"часть 1а — точная дробь, {len(small)} пар: "
          f"худшая ошибка {worst[0]:.3e} бита при (n0,n1)={worst[1][:2]}")

    worst = (0.0, None)
    # Последние две пары специально в режиме «оба счётчика велики» — там обе
    # реализации идут через lnΓ, и fsum-эталон показывает настоящую ошибку
    # этой ветки, а не только расхождение Rust с Python.
    mid = [(1000, 0), (5000, 1), (20000, 64), (20000, 65), (50000, 3),
           (100000, 0), (100000, 100), (65536, 65536), (12345, 6789),
           (500000, 500000), (900000, 100000)]
    for a, b in mid:
        want = kt_fsum(a, b)
        got = kt_cost(a, b)
        err = abs(got - want)
        if err > worst[0]:
            worst = (err, (a, b, want, got))
        # средние счётчики: у самого fsum-эталона ошибка ~n·2⁻⁵³ бит
        tol = max(tol_for(a, b), (a + b) * 1e-13)
        if err > tol:
            bad += 1
            print(f"  FSUM-ЭТАЛОН (n0,n1)=({a},{b}): kt_cost={got!r} fsum={want!r} Δ={err:.3e} бит")
    print(f"часть 1б — fsum-эталон, {len(mid)} пар: "
          f"худшая ошибка {worst[0]:.3e} бита при (n0,n1)={worst[1][:2]}")

    # Стык веток mn ≤ 64 / lgamma и m < 128 / асимптотика должен быть гладким.
    for a in (100000, 4 * 10 ** 8):
        j1, j2 = kt_cost(a, 64), kt_cost(a, 65)
        step = j2 - j1
        want = math.log2((a + 65.0) / 64.5)   # 65-й символ по формуле KT
        if abs(step - want) > 1e-6:
            bad += 1
            print(f"  СТЫК ВЕТОК при n0={a}: шаг 64→65 равен {step:.9f}, ожидалось {want:.9f}")
    print("часть 1в — стык веток mn=64/65 гладкий")
    return bad


def part2(lines) -> int:
    rows = 0
    bad = 0
    worst = (0.0, None)
    for line in lines:
        parts = line.split()
        if len(parts) != 3:
            continue
        n0, n1, got = float(parts[0]), float(parts[1]), float(parts[2])
        rows += 1
        want = kt_cost(int(n0), int(n1))
        err = abs(got - want)
        if err > worst[0]:
            worst = (err, (n0, n1, want, got))
        if err > tol_for(n0, n1):
            bad += 1
            print(f"  RUST≠PYTHON n=({n0:.0f},{n1:.0f}): rust={got!r} python={want!r} Δ={err:.3e} бит")
    if rows:
        n0, n1, want, got = worst[1]
        print(f"часть 2 — Rust ≡ Python, {rows} точек сетки: худшая ошибка "
              f"{worst[0]:.3e} бита при (n0,n1)=({n0:.0f},{n1:.0f}), значение {want:.6f} бит")
    return bad


def main() -> int:
    bad = part1()
    if not sys.stdin.isatty():
        bad += part2(sys.stdin)
    else:
        print("часть 2 пропущена (нет дампа на stdin): "
              "bin/comparator.exe --kt-selftest | python tools/comparator_lgamma_check.py")
    print()
    print(f"ПРОВАЛЕНО: {bad}" if bad else "все проверки пройдены")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
