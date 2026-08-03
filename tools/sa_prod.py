"""Продакшн SA-компаратор для полного enwik8 D=48 — внешняя сортировка.

Пайплайн:
  1. Генерация записей (key=48-бит контекст, pos, label) векторно через numpy,
     чанками по CHUNK записей; каждая запись 16 Б (key u64, pos u32, label u8).
  2. Сортировка каждого чанка по key (np.sort), затем внешнее слияние
     группами по 4 через np.concatenate + np.sort (пик ~2 ГБ, page file).
  3. Построение контрактированного дерева из отсортированного массива
     (np.memmap): рекурсия build(lo,hi,d), партиционирование бинарным поиском
     по порогу T = (2·P0+1) << (depth−1−d); счётчики через префиксные суммы
     меток; first_occ = min pos диапазона (листья — скан, внутренние — min детей).
  4. Weakest-link frontier с тай-брейком (α, first_occ, dep) — идентичен
     explicit-дереву (доказано: 15/15 + 40/40 кейсов в comparator_sa_ref.py).

Конвенция ключа: key = Σ_k bit(i−depth+k) << k — LSB = самый старый бит
контекста, MSB = самый свежий; совпадает с _records в comparator_sa_ref.py
и с (hist>>d)&1 в ядре ctw.rs.

Запуск: python sa_prod.py <файл> [--depth D] [--tmp DIR] [--budgets M1,M2,...]
                 [--points N] [--keep]
"""
import os
import sys
import time
import heapq
import argparse

import numpy as np

DEFAULT_DEPTH = 48
CHUNK = 8_000_000
MERGE_WAY = 4
MERGE_CHUNK = 1_000_000


def t0():
    return time.perf_counter()


def log(msg, start):
    print(f"[{time.perf_counter() - start:7.1f}s] {msg}", flush=True)


def generate(data: bytes, depth: int, tmpdir: str):
    """Записи (key, pos, label) чанками, каждый отсортирован по key."""
    bits = np.unpackbits(np.frombuffer(data, np.uint8))
    N = bits.shape[0]
    pad = np.zeros(depth, np.uint8)
    arr = np.concatenate([pad, bits])  # arr[i] = бит (i - depth)
    files = []
    cs = 0
    ci = 0
    while cs < N:
        L = min(CHUNK, N - cs)
        win = arr[cs: cs + L + depth]  # win[m] = бит (cs + m - depth)
        acc = np.zeros(L, np.uint64)
        for k in range(depth):
            acc |= win[k: k + L].astype(np.uint64) << k
        rec = np.empty(L, dtype=[('key', '<u8'), ('pos', '<u4'), ('label', 'u1')])
        rec['key'] = acc
        rec['pos'] = np.arange(cs, cs + L, dtype=np.uint32)
        rec['label'] = win[depth: depth + L]
        rec.sort(order='key')
        f = os.path.join(tmpdir, f"rec_{ci:04d}.npy")
        np.save(f, rec)
        files.append(f)
        cs += L
        ci += 1
    return files, N


def merge_all(files, tmpdir, start):
    """Внешнее слияние групп по MERGE_WAY; возвращает один отсортированный файл."""
    level = 0
    while len(files) > 1:
        nxt = []
        for i in range(0, len(files), MERGE_WAY):
            group = files[i: i + MERGE_WAY]
            if len(group) == 1:
                nxt.append(group[0])
                continue
            parts = [np.load(f) for f in group]
            merged = np.concatenate(parts)
            merged.sort(order='key')
            f = os.path.join(tmpdir, f"mrg_{level}_{len(nxt):04d}.npy")
            np.save(f, merged)
            nxt.append(f)
            del parts, merged
        log(f"слияние уровень {level}: {len(files)} -> {len(nxt)} файлов", start)
        files = nxt
        level += 1
    return files[0]


def build_tree_from_file(f, depth, start):
    """Контрактированное дерево из отсортированного файла.

    Возвращает (nodes, first_occ) как в comparator_sa_ref.build_sa_tree.
    nodes — списки numpy-массивов (n0,n1,ch0,ch1,dep) для компактности.
    """
    mm = np.load(f, mmap_mode='r')
    keys = mm['key']
    labels = mm['label']
    poss = mm['pos']
    N = len(mm)
    log(f"записей: {N} ({N / 1e6:.1f}M), ключей в файле", start)

    # префиксные суммы меток (memmap на диск)
    pref_path = f + ".pref"
    pref = np.memmap(pref_path, dtype=np.uint64, mode='w+', shape=(N + 1,))
    acc = 0
    for i in range(0, N, MERGE_CHUNK):
        seg = labels[i: i + MERGE_CHUNK]
        c = np.cumsum(seg.astype(np.uint64))
        pref[i + 1: i + 1 + len(seg)] = acc + c
        acc += int(c[-1]) if len(c) else 0
    pref.flush()
    log(f"префиксные суммы готовы (Σ label = {acc})", start)

    n0 = []
    n1 = []
    ch0 = []
    ch1 = []
    dep = []
    focc = []  # first_occ по индексу узла

    def build(lo, hi, d):
        u = len(n0)
        s = int(pref[hi]) - int(pref[lo])
        n0.append(hi - lo - s)
        n1.append(s)
        ch0.append(0)
        ch1.append(0)
        dep.append(d)
        focc.append(0)  # placeholder: заполним до возврата
        if d >= depth or hi - lo <= 1:
            # лист: first_occ = min pos диапазона (скан)
            focc[u] = int(np.min(poss[lo:hi])) if lo < hi else 0
            return u
        # партиционирование по биту d: порог T = (2·P0+1) << (depth-1-d)
        P0 = int(keys[lo]) >> (depth - d)
        T = (2 * P0 + 1) << (depth - 1 - d)
        mid = int(np.searchsorted(keys, T, side='left'))
        if mid < lo:
            mid = lo
        if mid > hi:
            mid = hi
        has0 = mid > lo
        has1 = mid < hi
        if has0 and has1:
            l0 = build(lo, mid, d + 1)
            l1 = build(mid, hi, d + 1)
            ch0[u] = l0
            ch1[u] = l1
            focc[u] = min(focc[l0], focc[l1])
        else:
            # унарный: лист, поддерево поглощено
            focc[u] = int(np.min(poss[lo:hi])) if lo < hi else 0
        return u

    build(0, N, 0)
    log(f"дерево: {len(n0)} узлов, {sum(1 for c in ch0 if c)} внутренних", start)

    # упакуем в dict-подобный формат для frontier
    nodes = []
    for i in range(len(n0)):
        nodes.append({'n': [n0[i], n1[i]], 'ch': [ch0[i], ch1[i]], 'dep': dep[i]})
    first_occ = {i: focc[i] for i in range(len(focc))}
    return nodes, first_occ, N


def frontier_sa(nodes, first_occ):
    """Weakest-link с тай-брейком (α, first_occ, dep) — из comparator_sa_ref."""
    from comparator_sa_ref import weakest_link_frontier_sa
    return weakest_link_frontier_sa(nodes, first_occ)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("file")
    ap.add_argument("--depth", type=int, default=DEFAULT_DEPTH)
    ap.add_argument("--tmp", default=None)
    ap.add_argument("--budgets", default="")
    ap.add_argument("--points", type=int, default=0)
    ap.add_argument("--keep", action="store_true")
    args = ap.parse_args()

    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    start = t0()
    tmpdir = args.tmp or os.path.join(os.path.dirname(args.file), ".sa_tmp")
    os.makedirs(tmpdir, exist_ok=True)

    data = open(args.file, 'rb').read()
    nbits = len(data) * 8
    log(f"данные: {len(data)} байт = {nbits} бит", start)

    files, _ = generate(data, args.depth, tmpdir)
    log(f"генерация: {len(files)} чанков", start)

    final = merge_all(files, tmpdir, start)
    log(f"слияние готово: {final}", start)

    nodes, first_occ, N = build_tree_from_file(final, args.depth, start)

    pts = frontier_sa(nodes, first_occ)
    log(f"frontier: {len(pts)} точек", start)

    full_cost = pts[0][1]
    full_leaves = pts[0][0]
    print()
    print(f"узлов в контрактированном дереве   {len(nodes)}")
    print(f"точек на оболочке                  {len(pts)}")
    print(f"листья (полное дерево)             {full_leaves}")
    print(f"стоимость полного дерева {full_cost:.3f} бит ({full_cost / nbits:.4f} bpc)")
    print()

    if args.points > 0:
        print(f"первые {args.points} точек оболочки (листья, биты, bpc):")
        for l, c in pts[:args.points]:
            print(f"  {l:>12}  {c:>16.3f}  {c / nbits:>10.6f}")
        print()

    if args.budgets:
        budgets = [int(x) for x in args.budgets.split(',') if x]
        print("бюджет M (листья)  стоимость (бит)      bpc")
        for m in budgets:
            best = min((c for l, c in pts if l <= m), default=float('inf'))
            if best == float('inf'):
                print(f"{m:>16}  — нет дерева с ≤M листьями")
            else:
                print(f"{m:>16}  {best:>16.3f}  {best / nbits:>10.4f}")

    if not args.keep:
        import shutil
        shutil.rmtree(tmpdir, ignore_errors=True)
    log("готово", start)


if __name__ == "__main__":
    main()
