"""Продакшн SA-компаратор для enwik8 D=48 с внешней сортировкой.

Исправленная версия после code review 2026-08-04:
- searchsorted только с np.uint64(T), без float64-копии и потери точности;
- k-way потоковое слияние sorted chunks, без concatenate всего датасета;
- узлы и frontier — компактные numpy/list-массивы, без Python dict на узел;
- heap weakest-link с cap+перестройкой, как в Rust comparator.rs;
- UTF-8 stdout, безопасная чистка только файлов текущего run.

**Исправлено 2026-08-10** (класс сравнения — та же ошибка, что была в
explicit-компараторе, но на уровне построения дерева: `build()` останавливал
спуск на первом унарном узле, выбрасывая структуру под ним). Семантика теперь
совпадает с tools/comparator_sa_ref.py (эталон, сверено численно): дерево
СЖАТОЕ (Patricia-подобное) — узел материализуется только на настоящем
ветвлении или обрыве (глубина D / 1 запись в диапазоне), а число пропущенных
унарных уровней хранится как `k` и учитывается в leaves(u) = k(u)+база(u).
Разбор — docstring comparator_sa_ref.weakest_link_frontier_sa и
notes/stage5b-comparator-audit.md. Tie-break weakest-link при равных alpha —
(first_occ, dep), без изменений.
"""
from __future__ import annotations

import argparse
import heapq
import math
import os
import shutil
import sys
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Iterable

import numpy as np

try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass

DEFAULT_DEPTH = 48
CHUNK = int(os.environ.get("SA_CHUNK", "8000000"))
MERGE_BLOCK = int(os.environ.get("SA_MERGE_BLOCK", "1048576"))
RUN_PREFIX = "sa_run_"
DTYPE = np.dtype([("key", "<u8"), ("pos", "<u8"), ("label", "u1")])  # 17 B packed


@dataclass
class TreeArrays:
    n0: list[int]
    n1: list[int]
    ch0: list[int]
    ch1: list[int]
    dep: list[int]
    first_occ: list[int]
    k: list[int]

    def __len__(self) -> int:
        return len(self.n0)


def now() -> float:
    return time.perf_counter()


def log(msg: str, start: float) -> None:
    print(f"[{time.perf_counter() - start:7.1f}s] {msg}", flush=True)


def cost_leaf(n0: int, n1: int) -> float:
    n = n0 + n1
    if n <= 0:
        return 0.0
    p = n0 / n
    if p <= 0.0 or p >= 1.0:
        return 0.0
    return n * (-p * math.log2(p) - (1.0 - p) * math.log2(1.0 - p))


def tracked(path: Path, created: list[Path]) -> str:
    created.append(path)
    return str(path)


def generate(data: bytes, depth: int, tmpdir: Path, created: list[Path], start: float) -> tuple[list[Path], int]:
    """Generate sorted chunk files of (key:uint64, pos:uint64, label:uint8)."""
    if depth < 0 or depth > 63:
        raise ValueError("--depth must be in [0, 63] for uint64 keys")
    bits = np.unpackbits(np.frombuffer(data, np.uint8))
    N = int(bits.shape[0])
    if N == 0:
        raise ValueError("empty input is not supported")
    pad = np.zeros(depth, np.uint8)
    arr = np.concatenate([pad, bits])
    files: list[Path] = []
    cs = 0
    ci = 0
    while cs < N:
        L = min(CHUNK, N - cs)
        win = arr[cs : cs + L + depth]
        acc = np.zeros(L, np.uint64)
        for k in range(depth):
            acc |= win[k : k + L].astype(np.uint64) << np.uint64(k)
        rec = np.empty(L, dtype=DTYPE)
        rec["key"] = acc
        rec["pos"] = np.arange(cs, cs + L, dtype=np.uint64)
        rec["label"] = win[depth : depth + L]
        rec.sort(order="key")
        f = tmpdir / f"{RUN_PREFIX}rec_{ci:04d}.npy"
        np.save(tracked(f, created), rec)
        files.append(f)
        cs += L
        ci += 1
        if ci % 10 == 0 or cs == N:
            log(f"генерация: {ci} чанков, {cs / 1e6:.1f}M/{N / 1e6:.1f}M записей", start)
    return files, N


class BlockReader:
    def __init__(self, path: Path, block: int = MERGE_BLOCK):
        self.path = path
        self.arr = np.load(path, mmap_mode="r")
        self.block = block
        self.n = len(self.arr)
        self.pos = 0
        self.buf = None
        self.i = 0
        self._load()

    def _load(self) -> None:
        if self.pos >= self.n:
            self.buf = None
            self.i = 0
            return
        end = min(self.pos + self.block, self.n)
        self.buf = self.arr[self.pos : end]
        self.pos = end
        self.i = 0

    def pop(self):
        if self.buf is None:
            return None
        r = self.buf[self.i]
        self.i += 1
        if self.i >= len(self.buf):
            self._load()
        return r


def merge_stream(group: list[Path], out: Path, created: list[Path], start: float) -> None:
    """K-way merge sorted chunk files into out, streaming blocks only."""
    readers = [BlockReader(p) for p in group]
    h = []
    for i, rd in enumerate(readers):
        r = rd.pop()
        if r is not None:
            heapq.heappush(h, (int(r["key"]), int(r["pos"]), int(r["label"]), i))
    total = sum(rd.n for rd in readers)
    out_arr = np.lib.format.open_memmap(tracked(out, created), mode="w+", dtype=DTYPE, shape=(total,))
    w = 0
    while h:
        key, pos, label, i = heapq.heappop(h)
        out_arr[w] = (key, pos, label)
        w += 1
        r = readers[i].pop()
        if r is not None:
            heapq.heappush(h, (int(r["key"]), int(r["pos"]), int(r["label"]), i))
        if w % 50_000_000 == 0:
            log(f"слияние {out.name}: {w / 1e6:.0f}M/{total / 1e6:.0f}M", start)
    out_arr.flush()
    del out_arr
    # release mmaps before deleting inputs on Windows
    for rd in readers:
        del rd.arr
    if w != total:
        raise RuntimeError(f"merge wrote {w}, expected {total}")


def merge_all(files: list[Path], tmpdir: Path, created: list[Path], start: float, way: int) -> Path:
    if not files:
        raise ValueError("no chunk files to merge")
    level = 0
    while len(files) > 1:
        nxt: list[Path] = []
        for i in range(0, len(files), way):
            group = files[i : i + way]
            if len(group) == 1:
                nxt.append(group[0])
                continue
            out = tmpdir / f"{RUN_PREFIX}mrg_{level}_{len(nxt):04d}.npy"
            merge_stream(group, out, created, start)
            nxt.append(out)
            # delete consumed files from THIS run only
            for p in group:
                if p in created and p.exists():
                    try:
                        p.unlink()
                        created.remove(p)
                    except PermissionError:
                        log(f"warning: не удалось удалить {p}", start)
        log(f"слияние уровень {level}: {len(files)} -> {len(nxt)} файлов", start)
        files = nxt
        level += 1
    return files[0]


def build_tree_from_file(path: Path, depth: int, start: float) -> tuple[TreeArrays, int, Path]:
    mm = np.load(path, mmap_mode="r")
    keys = mm["key"]
    labels = mm["label"]
    poss = mm["pos"]
    N = int(len(mm))
    if N == 0:
        raise ValueError("empty sorted file")
    log(f"записей: {N} ({N / 1e6:.1f}M), itemsize={mm.dtype.itemsize} B", start)

    pref_path = Path(str(path) + ".pref")
    pref = np.memmap(pref_path, dtype=np.uint64, mode="w+", shape=(N + 1,))
    pref[0] = 0
    acc = 0
    for i in range(0, N, MERGE_BLOCK):
        seg = labels[i : i + MERGE_BLOCK]
        c = np.cumsum(seg.astype(np.uint64))
        if len(c):
            pref[i + 1 : i + 1 + len(seg)] = acc + c
            acc += int(c[-1])
    pref.flush()
    log(f"префиксные суммы готовы (sum label = {acc})", start)

    tr = TreeArrays([], [], [], [], [], [], [])

    def emit(lo: int, hi: int, d: int, k: int) -> int:
        u = len(tr.n0)
        s = int(pref[hi]) - int(pref[lo])
        tr.n0.append(hi - lo - s)
        tr.n1.append(s)
        tr.ch0.append(0)
        tr.ch1.append(0)
        tr.dep.append(d)
        tr.k.append(k)
        tr.first_occ.append(0)
        return u

    def build(lo: int, hi: int, d: int) -> int:
        # Сжатие ребра: находим глубину первого возможного расхождения ЗА
        # ОДИН шаг через XOR граничных ключей отсортированного диапазона —
        # если keys[lo] и keys[hi-1] совпадают до глубины X, совпадают и
        # ВСЕ ключи между ними (иначе нарушился бы порядок сортировки).
        # Заменяет обход по уровню (O(depth) searchsorted) на O(1) + один
        # searchsorted для настоящего ветвления — важно на 800M записей.
        if hi - lo <= 1:
            k = depth - d
            d = depth
        else:
            diff = int(keys[lo]) ^ int(keys[hi - 1])
            if diff == 0:
                k = depth - d
                d = depth
            else:
                dd = depth - 1 - (diff.bit_length() - 1)
                k = dd - d
                d = dd
        if d < depth:
            # d здесь гарантированно точка настоящего ветвления (см. вывод
            # выше: старший несовпадающий бит границ ⇒ keys[lo] даёт 0,
            # keys[hi-1] даёт 1 на этом бите ⇒ has0 и has1 оба истинны).
            p0 = int(keys[lo]) >> (depth - d)
            T = np.uint64((2 * p0 + 1) << (depth - 1 - d))
            mid = int(np.searchsorted(keys, T, side="left"))
            if mid < lo:
                mid = lo
            elif mid > hi:
                mid = hi
            u = emit(lo, hi, d, k)
            l0 = build(lo, mid, d + 1)
            l1 = build(mid, hi, d + 1)
            tr.ch0[u] = l0
            tr.ch1[u] = l1
            tr.first_occ[u] = min(tr.first_occ[l0], tr.first_occ[l1])
            return u
        u = emit(lo, hi, d, k)
        tr.first_occ[u] = int(np.min(poss[lo:hi]))
        return u

    build(0, N, 0)
    internal = sum(1 for c in tr.ch0 if c)
    log(f"дерево: {len(tr)} узлов, {internal} внутренних", start)
    # release mmaps explicitly enough for Windows cleanup after caller drops refs
    del mm, keys, labels, poss
    pref.flush()
    del pref
    return tr, N, pref_path


def weakest_link_arrays(tr: TreeArrays, heap_cap: int = 8_000_000) -> list[tuple[int, float]]:
    """leaves(u) = k(u) + база(u): k(u) — СВОЁ сжатое ребро узла u (число
    унарных уровней, поглощённых build() над этим узлом), база — 1 для
    листа, leaves(ch0)+leaves(ch1) для ветвления (k детей уже учтён в их
    собственных leaves рекурсивно). Лист с k>0 — тоже кандидат кучи: его
    α = (c(u)-R(u))/(leaves(u)-1) = 0/k = 0 тождественно (R листа всегда
    равен его cost_leaf), то есть отщипывание накопленной цепочки НИКОГДА
    не меняет стоимость, только сокращает число листьев. Подробный вывод —
    docstring comparator_sa_ref.weakest_link_frontier_sa (эталон, с которым
    сверено численно).
    """
    n = len(tr)
    ch0, ch1, k = tr.ch0, tr.ch1, tr.k
    par = [0] * n
    for u in range(n):
        c0, c1 = ch0[u], ch1[u]
        if c0:
            par[c0] = u
        if c1:
            par[c1] = u
    R = [0.0] * n
    leaves = [0] * n

    def kill(u: int) -> None:
        st = [u]
        while st:
            w = st.pop()
            leaves[w] = 0
            if ch0[w]:
                st.append(ch0[w])
            if ch1[w]:
                st.append(ch1[w])

    for u in range(n - 1, -1, -1):
        if ch0[u] and ch1[u]:
            R[u] = R[ch0[u]] + R[ch1[u]]
            leaves[u] = k[u] + leaves[ch0[u]] + leaves[ch1[u]]
        else:
            R[u] = cost_leaf(tr.n0[u], tr.n1[u])
            leaves[u] = k[u] + 1

    pts = [(leaves[0], R[0])]
    alpha = [math.nan] * n
    heap: list[tuple[float, int, int, int]] = []

    def push(u: int) -> None:
        # Кандидат — любой узел с leaves>1: ветвление ИЛИ лист со сжатым
        # ребром k>0 (гарантированно α=0, см. docstring функции).
        if leaves[u] > 1:
            a = (cost_leaf(tr.n0[u], tr.n1[u]) - R[u]) / (leaves[u] - 1)
            alpha[u] = a
            heapq.heappush(heap, (a, tr.first_occ[u], tr.dep[u], u))

    for u in range(n):
        push(u)
    cap = min(max(2 * n, 16), heap_cap)

    while heap:
        a, _fo, _d, u = heapq.heappop(heap)
        if leaves[u] <= 1:
            continue
        if alpha[u] != a:
            continue
        st = [u]
        while st:
            w = st.pop()
            leaves[w] = 0
            if ch0[w]:
                st.append(ch0[w])
            if ch1[w]:
                st.append(ch1[w])
        R[u] = cost_leaf(tr.n0[u], tr.n1[u])
        leaves[u] = 1
        v = par[u]
        while v != u:
            R[v] = R[ch0[v]] + R[ch1[v]]
            leaves[v] = k[v] + leaves[ch0[v]] + leaves[ch1[v]]
            if leaves[v] == 1:
                break
            alpha[v] = (cost_leaf(tr.n0[v], tr.n1[v]) - R[v]) / (leaves[v] - 1)
            heapq.heappush(heap, (alpha[v], tr.first_occ[v], tr.dep[v], v))
            if v == 0:
                break
            v = par[v]
        pts.append((leaves[0], R[0]))
        if leaves[0] == 1:
            break
        if len(heap) > cap:
            heap.clear()
            for u2 in range(n):
                if leaves[u2] > 1:
                    heapq.heappush(heap, (alpha[u2], tr.first_occ[u2], tr.dep[u2], u2))
    return pts


def cleanup(paths: Iterable[Path], tmpdir: Path, remove_tmpdir: bool, start: float) -> None:
    for p in list(paths):
        try:
            if p.exists():
                p.unlink()
        except PermissionError:
            log(f"warning: не удалось удалить {p}", start)
    if remove_tmpdir:
        try:
            tmpdir.rmdir()
        except OSError:
            pass


def acquire_lock(tmpdir: Path) -> Path:
    """Создаёт lock-файл. Блокирует параллельные запуски."""
    lock_path = tmpdir / ".lock"
    if lock_path.exists():
        try:
            pid = int(lock_path.read_text().strip())
            # Проверка: жив ли процесс
            try:
                import ctypes
                kernel32 = ctypes.windll.kernel32
                handle = kernel32.OpenProcess(0x1000, False, pid)
                if handle:
                    kernel32.CloseHandle(handle)
                    raise SystemExit(
                        f"ERROR: другой процесс (PID {pid}) уже использует {tmpdir}\n"
                        f"Дождись завершения или удали {lock_path} вручную"
                    )
            except (OSError, AttributeError):
                pass  # не Windows или не удалось проверить — считаем stale
        except ValueError:
            pass  # corrupt lock
        lock_path.unlink(missing_ok=True)
    lock_path.write_text(str(os.getpid()))
    return lock_path


def create_run_dir(base_tmpdir: Path) -> Path:
    """Создаёт уникальную подпапку для run'а: run_<timestamp>_<pid>."""
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    run_dir = base_tmpdir / f"run_{ts}_{os.getpid()}"
    run_dir.mkdir(parents=True, exist_ok=True)
    return run_dir


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("file")
    ap.add_argument("--depth", type=int, default=DEFAULT_DEPTH)
    ap.add_argument("--tmp", default=None)
    ap.add_argument("--budgets", default="")
    ap.add_argument("--points", type=int, default=0)
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--merge-way", type=int, default=8)
    args = ap.parse_args()

    start = now()
    infile = Path(args.file)
    data = infile.read_bytes()
    nbits = len(data) * 8
    if nbits == 0:
        raise SystemExit("empty input")
    tmpdir = Path(args.tmp) if args.tmp else infile.parent / ".sa_tmp"
    tmp_existed = tmpdir.exists()
    tmpdir.mkdir(parents=True, exist_ok=True)
    
    # Lock для запрета параллельных запусков
    lock_path = acquire_lock(tmpdir)
    # Run-ID изоляция: каждый запуск в свою подпапку
    run_dir = create_run_dir(tmpdir)
    
    log(f"run dir: {run_dir.name}", start)
    
    created: list[Path] = []

    try:
        log(f"данные: {len(data)} байт = {nbits} бит", start)
        files, _N = generate(data, args.depth, run_dir, created, start)
        log(f"генерация: {len(files)} чанков", start)
        final = merge_all(files, run_dir, created, start, max(2, args.merge_way))
        log(f"слияние готово: {final}", start)
        tr, N, pref_path = build_tree_from_file(final, args.depth, start)
        created.append(pref_path)
        pts = weakest_link_arrays(tr)
        log(f"frontier: {len(pts)} точек", start)

        # bpc = bits per character, бит/БАЙТ (как в ядре ctw.rs и src/comparator.rs
        # после правки 2026-08-10); бит/бит = bpc/8, отдельная нормированная
        # величина. Раньше здесь под именем "bpc" печаталось бит/бит — 8-кратный
        # разнобой с остальным проектом.
        nbytes = len(data)
        full_leaves, full_cost = pts[0]
        print()
        print(f"узлов в контрактированном дереве   {len(tr)}")
        print(f"точек на оболочке                  {len(pts)}")
        print(f"листья (полное дерево)             {full_leaves}")
        print(f"стоимость полного дерева {full_cost:.3f} бит "
              f"({full_cost / nbits:.4f} бит/бит, {full_cost / nbytes:.4f} bpc)")
        print()

        if args.points > 0:
            print(f"первые {args.points} точек оболочки (листья, биты, бит/бит, bpc):")
            for l, c in pts[: args.points]:
                print(f"  {l:>12}  {c:>16.3f}  {c / nbits:>10.6f}  {c / nbytes:>10.6f}")
            print()
        if args.budgets:
            budgets = [int(x) for x in args.budgets.split(",") if x]
            print("бюджет M (листья)  стоимость (бит)   бит/бит      bpc")
            # pts идут от больших листьев к меньшим; для M ищем min c при l<=M
            for m in budgets:
                best = min((c for l, c in pts if l <= m), default=float("inf"))
                if math.isinf(best):
                    print(f"{m:>16}  — нет дерева с ≤M листьями")
                else:
                    print(f"{m:>16}  {best:>16.3f}  {best / nbits:>10.4f}  {best / nbytes:>10.4f}")
        log("готово", start)
    finally:
        if not args.keep:
            cleanup(created, run_dir, remove_tmpdir=True, start=start)
        # Освобождаем lock
        try:
            lock_path.unlink(missing_ok=True)
        except Exception:
            pass


if __name__ == "__main__":
    main()
