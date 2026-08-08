"""Fallback build для sa_prod.py — блочный, без thrashing.

Проблема исходного build_tree_from_file: np.searchsorted по memmap-массиву
13.6 ГБ на КАЖДЫЙ внутренний узел. При свободной RAM ~0.3 ГБ (llama-серверы
держат 13 ГБ) каждый бинарный поиск читает случайные страницы, вытесняемые
между вызовами, — сотни тысяч обращений к диску, build тянется сутками.

Решение: двухуровневый build.
  - Диапазоны > RAM_BLOCK записей (верхние ~9 уровней, ~500 узлов) ходят по
    memmap ручным бинарным поиском, локализованным в [lo, hi).
  - Диапазоны <= RAM_BLOCK: блок (structured: key/pos/label, ~32 МБ) целиком
    читается в RAM, и весь под-дерево блока строится по RAM-массивам
    (np.searchsorted по RAM — наносекунды; счётчики — cumsum labels блока;
    first_occ — np.min по RAM-куску poss).
  - Итог: memmap читается ПОСЛЕДОВАТЕЛЬНО, 200 блоков × 32 МБ = 6.4 ГБ один
    раз; случайных обращений к диску нет. Ожидание: 3-8 мин вместо 20+ ч.

Интерфейс совпадает с build_tree_from_file: (TreeArrays, N, pref_path).
Семантика (контракция унарного узла, тай-брейк first_occ) — та же, что в
comparator_sa_ref.py; сверяется с explicit на малых данных.
"""
from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np

from sa_prod import TreeArrays, log, MERGE_BLOCK  # reuse logger + dataclass

RAM_BLOCK = int(__import__("os").environ.get("SA_RAM_BLOCK", "4000000"))


def _mem_binsearch(keys, lo: int, hi: int, T) -> int:
    """Первый индекс в [lo, hi) с keys[idx] >= T; ручной, по memmap."""
    L, R = lo, hi
    while L < R:
        m = (L + R) >> 1
        if int(keys[m]) < int(T):
            L = m + 1
        else:
            R = m
    return L


def _min_pos(poss, lo: int, hi: int) -> int:
    """min poss[lo:hi] — для больших листьев (редко); np.min с memmap."""
    if lo >= hi:
        return 0
    return int(np.min(poss[lo:hi]))


def build_tree_fast(path: Path, depth: int, start: float) -> tuple[TreeArrays, int, Path]:
    mm = np.load(path, mmap_mode="r")
    keys = mm["key"]
    labels = mm["label"]
    poss = mm["pos"]
    N = int(len(mm))
    if N == 0:
        raise ValueError("empty sorted file")
    log(f"[fast] записей: {N} ({N / 1e6:.1f}M), itemsize={mm.dtype.itemsize} B, RAM_BLOCK={RAM_BLOCK}", start)

    # префиксные суммы labels — memmap (нужны только большим узлам)
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
    log(f"[fast] префиксные суммы готовы (sum label = {acc})", start)

    tr = TreeArrays([], [], [], [], [], [])
    n_blocks = 0
    _node_log = [0]

    def node_progress(start):
        _node_log[0] += 1
        if _node_log[0] % 20000 == 0:
            log(f"[fast] узлов построено: {_node_log[0]}", start)

    def emit(lo: int, hi: int, d: int) -> int:
        """Создать узел; счётчики из pref (memmap, 2 чтения на узел)."""
        u = len(tr.n0)
        s = int(pref[hi]) - int(pref[lo])
        tr.n0.append(hi - lo - s)
        tr.n1.append(s)
        tr.ch0.append(0)
        tr.ch1.append(0)
        tr.dep.append(d)
        tr.first_occ.append(0)
        return u

    def build_ram(blk, d: int, u0: int, lo0: int, hi0: int) -> None:
        """Построить под-дерево узла u0 (диапазон [lo0, hi0) в блочных координатах)
        целиком по RAM-массивам. Возвращает first_occ узла.

        ВАЖНО: поля structured-массива — view с шагом 17 байт; np.searchsorted
        по такому массиву делает КОПИЮ O(n) на каждый вызов (16 мс против
        2.4 мкс на contiguous!). Поэтому поля копируются в contiguous-массивы.
        """
        bkeys = np.array(blk["key"], copy=True)   # contiguous uint64
        bposs = np.array(blk["pos"], copy=True)   # contiguous uint64
        blabels = np.array(blk["label"], copy=True)
        # cumsum labels блока — один раз на блок
        bc = np.cumsum(blabels.astype(np.uint64))
        pref1 = np.concatenate(([0], bc))  # pref1[i] = sum label[0:i]

        def counts(a: int, b: int) -> tuple[int, int]:
            n1 = int(pref1[b]) - int(pref1[a])
            return (b - a - n1, n1)

        def rec(a: int, b: int, dd: int, u: int) -> int:
            node_progress(start)
            n0c, n1c = counts(a, b)
            tr.n0[u] = n0c
            tr.n1[u] = n1c
            if dd >= depth or b - a <= 1:
                fo = int(np.min(bposs[a:b])) if a < b else 0
                tr.first_occ[u] = fo
                return fo
            p0 = int(bkeys[a]) >> (depth - dd)
            T = np.uint64((2 * p0 + 1) << (depth - 1 - dd))
            mid = int(np.searchsorted(bkeys, T, side="left"))  # уже в координатах блока
            if mid < a:
                mid = a
            elif mid > b:
                mid = b
            has0 = mid > a
            has1 = mid < b
            if has0 and has1:
                c0 = len(tr.n0)
                for _ in range(2):
                    tr.n0.append(0); tr.n1.append(0)
                    tr.ch0.append(0); tr.ch1.append(0)
                    tr.dep.append(dd + 1); tr.first_occ.append(0)
                tr.ch0[u] = c0
                tr.ch1[u] = c0 + 1
                f0 = rec(a, mid, dd + 1, c0)
                f1 = rec(mid, b, dd + 1, c0 + 1)
                fo = min(f0, f1)
                tr.first_occ[u] = fo
                return fo
            fo = int(np.min(bposs[a:b])) if a < b else 0
            tr.first_occ[u] = fo
            return fo

        rec(lo0, hi0, d, u0)

    # BFS по уровням для больших узлов; level: (lo, hi, d, u, parent)
    u0 = emit(0, N, 0)
    level = [(0, N, 0, u0, -1)]
    lvl = 0
    while level:
        nxt = []
        for lo, hi, d, u, parent in level:
            if hi - lo <= RAM_BLOCK:
                blk = np.array(mm[lo:hi])  # ЯВНАЯ копия в RAM (не view на mmap!)
                build_ram(blk, d, u, 0, hi - lo)  # перезапишет счётчики и создаст детей
                n_blocks += 1
                if n_blocks % 20 == 0:
                    log(f"[fast] блоков обработано: {n_blocks}, узлов: {len(tr.n0)}", start)
            elif d >= depth or hi - lo <= 1:
                tr.first_occ[u] = _min_pos(poss, lo, hi)
            else:
                p0 = int(keys[lo]) >> (depth - d)
                T = np.uint64((2 * p0 + 1) << (depth - 1 - d))
                mid = _mem_binsearch(keys, lo, hi, T)
                has0 = mid > lo
                has1 = mid < hi
                if has0 and has1:
                    c0 = emit(lo, mid, d + 1)   # дети создаются СРАЗУ со счётчиками
                    c1 = emit(mid, hi, d + 1)
                    tr.ch0[u] = c0
                    tr.ch1[u] = c1
                    nxt.append((lo, mid, d + 1, c0, u))
                    nxt.append((mid, hi, d + 1, c1, u))
                else:
                    tr.first_occ[u] = _min_pos(poss, lo, hi)
        # first_occ внутренних mem-узлов = min по детям (build_ram уже сделал для блоков)
        for lo, hi, d, u, parent in level:
            if parent >= 0 and tr.ch0[parent]:
                tr.first_occ[parent] = min(tr.first_occ[parent], tr.first_occ[u])
        log(f"[fast] уровень {lvl}: {len(level)} узлов -> {len(nxt)}", start)
        level = nxt
        lvl += 1

    internal = sum(1 for c in tr.ch0 if c)
    log(f"[fast] дерево: {len(tr)} узлов, {internal} внутренних, блоков {n_blocks}", start)
    del mm, keys, labels, poss
    pref.flush()
    del pref
    return tr, N, pref_path


if __name__ == "__main__":
    # самопроверка против explicit на малых данных
    sys.path.insert(0, "tools")
    from comparator_ref import build_tree
    from comparator_wl import weakest_link_frontier
    from sa_prod import generate, merge_all

    start = float("nan")
    import time
    start = time.perf_counter()

    data = open("tools/_t2k.bin", "rb").read()
    for depth in (4, 8, 12):
        tmp = Path("tools/.sa_tmp_fast")
        tmp.mkdir(parents=True, exist_ok=True)
        created = []
        files, _ = generate(data, depth, tmp, created, start)
        final = merge_all(files, tmp, created, start, way=4)
        tr, N, prefp = build_tree_fast(final, depth, start)
        # frontier
        from sa_prod import weakest_link_arrays
        pts = weakest_link_arrays(tr)
        e = build_tree(data, depth)
        ref = weakest_link_frontier(e)
        assert len(pts) == len(ref), (len(pts), len(ref), depth)
        for (l1, c1), (l2, c2) in zip(pts, ref):
            assert l1 == l2 and abs(c1 - c2) < 1e-6, (l1, c1, l2, c2, depth)
        print(f"[fast] depth={depth}: OK, узлов {len(tr)}, точек {len(pts)}")
        import gc
        gc.collect()  # освободить mmap-хендлы до unlink
        for p in created:
            try:
                if p.exists():
                    p.unlink()
            except PermissionError:
                pass
        try:
            (tmp / (final.name + ".pref")).unlink(missing_ok=True)
        except PermissionError:
            pass
        try:
            tmp.rmdir()
        except OSError:
            pass
    print("FAST BUILD: OK")
