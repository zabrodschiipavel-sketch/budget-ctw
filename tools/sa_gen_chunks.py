"""Генерация отсортированных чанков для bin/sa_frontier.exe (без слияния).

Слияние делает сам sa_frontier (k-way на лету, прямо в построение дерева),
поэтому Python-фаза merge_all не нужна: на полном корпусе она прогоняла
~2.4 млрд записей через heapq (часы) и требовала ещё 13.6 ГБ под
промежуточный файл.

    python tools/sa_gen_chunks.py <корпус> <глубина> <папка> [--limit N]

Печатает список созданных чанков; они НЕ удаляются — их и надо передать в
sa_frontier:

    bin/sa_frontier.exe <папка>/sa_run_rec_*.npy --depth 48 --budgets ...
"""
import argparse
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.stdout.reconfigure(encoding="utf-8", errors="replace")

from sa_prod import generate, CHUNK


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("corpus")
    ap.add_argument("depth", type=int)
    ap.add_argument("outdir")
    ap.add_argument("--limit", type=int, default=None)
    args = ap.parse_args()

    out = Path(args.outdir)
    out.mkdir(parents=True, exist_ok=True)
    data = Path(args.corpus).read_bytes()
    if args.limit:
        data = data[: args.limit]

    start = time.perf_counter()
    print(f"корпус {len(data)} байт = {len(data) * 8} бит, глубина {args.depth}, "
          f"чанк {CHUNK} записей (env SA_CHUNK)", flush=True)
    created: list[Path] = []
    files, n = generate(data, args.depth, out, created, start)
    total_gb = sum(f.stat().st_size for f in files) / 1e9
    print(f"\nготово за {time.perf_counter() - start:.1f} с: {len(files)} чанков, "
          f"{n} записей, {total_gb:.2f} ГБ", flush=True)
    print(f"\nдальше:\n  bin/sa_frontier.exe {out}/sa_run_rec_*.npy "
          f"--depth {args.depth} --budgets ...", flush=True)


if __name__ == "__main__":
    main()
