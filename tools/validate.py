"""Сверка целочисленного ядра (Rust) с точным эталоном (Python), этап 3.

Проверяется двойное совпадение на каждом тесте:
  * кодовая длина — в пределах бюджета ошибки округления фиксированной точки;
  * число созданных узлов — точно, это проверяет спуск по контексту.

    python validate.py [--bin ../bin/ctw.exe]
"""
import argparse
import os
import re
import subprocess
import sys
import tempfile

sys.stdout.reconfigure(encoding="utf-8", errors="replace")  # консоль Windows не UTF-8

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ref_ctw

# Погрешность одного обращения к таблице ≈ 2⁻²⁵ (design-spec §2); на бит
# приходится ≤ 4·D таких обращений. Тройной запас на накопление.
PER_LOOKUP = 3.0e-8
MARGIN = 3.0


def run_rust(binary, path, depth, limit=None, lazy=0):
    # --verify-sum держит инвариант Σ_x P(x) = 1 на каждом бите: без него
    # ошибки учёта символа выглядят как улучшение сжатия.
    cmd = [binary, path, "--depth", str(depth), "--lazy", str(lazy), "--verify-sum"]
    if limit is not None:
        cmd += ["--limit", str(limit)]
    out = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8")
    if out.returncode != 0:
        raise RuntimeError(f"ядро упало: {out.stderr.strip()}")
    bits = re.search(r"кодовая длина\s+(-?[\d.]+)", out.stdout)
    nodes = re.search(r"узлов\s+(\d+)", out.stdout)
    if not bits or not nodes:
        raise RuntimeError(f"не разобран вывод ядра:\n{out.stdout}")
    return float(bits.group(1)), int(nodes.group(1))


CASES = [
    # (данные, глубина, ленивый порог)
    (b"a", 4, 0),
    (b"a", 8, 0),
    (b"aaaaaaaa", 4, 0),
    (b"aaaaaaaa", 12, 0),
    (b"\x00" * 16, 8, 0),
    (b"\xff" * 16, 8, 0),
    (b"hello world", 2, 0),
    (b"hello world", 8, 0),
    (b"hello world", 16, 0),
    (bytes(range(32)), 8, 0),
    (b"abababababababab", 6, 0),
    (b"abababababababab", 16, 0),
    (bytes((i * 37 + 11) & 0xFF for i in range(48)), 10, 0),
    (b"the quick brown fox jumps over the lazy dog", 12, 0),
    # Неравноглубокое дерево: ленивый порог обрывает спуск, узлы переходят из
    # листьев во внутренние по ходу. Именно эта семантика была сломана и
    # проявлялась как «слишком хорошее» сжатие.
    (b"the quick brown fox jumps over the lazy dog", 12, 2),
    (b"the quick brown fox jumps over the lazy dog", 12, 8),
    (b"abababababababab", 16, 4),
    (b"\x00" * 16, 8, 3),
    (bytes(range(32)), 8, 5),
    (bytes((i * 37 + 11) & 0xFF for i in range(48)), 10, 16),
    (b"hello world hello world hello", 16, 6),
]


def main():
    ap = argparse.ArgumentParser()
    here = os.path.dirname(os.path.abspath(__file__))
    default_bin = os.path.join(here, "..", "bin", "ctw.exe")
    ap.add_argument("--bin", default=default_bin)
    args = ap.parse_args()

    if not os.path.exists(args.bin):
        print(f"нет бинарника {args.bin} — сначала соберите ядро")
        return 1

    failures = 0
    for data, depth, lazy in CASES:
        with tempfile.NamedTemporaryFile(delete=False, suffix=".bin") as f:
            f.write(data)
            path = f.name
        try:
            got_bits, got_nodes = run_rust(args.bin, path, depth, lazy=lazy)
            exp_bits, exp_nodes = ref_ctw.code_length(data, depth, lazy)
        finally:
            os.unlink(path)

        nbits = len(data) * 8
        tol = MARGIN * PER_LOOKUP * 4 * depth * nbits + 1e-4
        diff = abs(got_bits - exp_bits)
        ok_bits = diff <= tol
        ok_nodes = got_nodes == exp_nodes
        status = "OK  " if (ok_bits and ok_nodes) else "FAIL"
        if not (ok_bits and ok_nodes):
            failures += 1
        label = repr(data[:20])
        if len(data) > 20:
            label += f"+{len(data)-20}б"
        print(
            f"{status} D={depth:<3} lazy={lazy:<3} {label:<28} "
            f"ядро={got_bits:.6f} эталон={exp_bits:.6f} "
            f"Δ={diff:.2e} (допуск {tol:.1e}) узлы {got_nodes}/{exp_nodes}"
        )

    print()
    if failures:
        print(f"ПРОВАЛЕНО тестов: {failures} из {len(CASES)}")
        return 1
    print(f"все {len(CASES)} тестов пройдены")
    return 0


if __name__ == "__main__":
    sys.exit(main())
