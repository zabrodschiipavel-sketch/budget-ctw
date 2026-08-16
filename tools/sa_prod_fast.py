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

**Исправлено 2026-08-10** (класс сравнения — см. sa_prod.py и
notes/stage5b-comparator-audit.md): дерево СЖАТОЕ (Patricia-подобное), узел
материализуется только на настоящем ветвлении/обрыве, число пропущенных
унарных уровней — `k`. Оба пути (memmap для больших диапазонов через
`advance()`, RAM-блок через `rec()`) находят точку сжатия ЗА ОДИН шаг —
XOR граничных ключей диапазона вместо обхода по уровню (тот же приём, что в
sa_prod.build_tree_from_file.build — см. вывод там). Тай-брейк first_occ — без
изменений. Сверяется с comparator_sa_ref.py и explicit на малых данных
(см. __main__ внизу) и с sa_prod.py на средних (tools/sa_prod_check.py).
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

    tr = TreeArrays([], [], [], [], [], [], [])
    n_blocks = 0
    _node_log = [0]

    def node_progress(start):
        _node_log[0] += 1
        if _node_log[0] % 20000 == 0:
            log(f"[fast] узлов построено: {_node_log[0]}", start)

    def emit(lo: int, hi: int, d: int) -> int:
        """Создать узел; счётчики из pref (memmap, 2 чтения на узел).

        k=0 — заглушка: узел либо выставлен в очередь BFS (`level`) для
        обработки в advance() ниже, либо будет сразу передан в rec()
        (внутри build_ram) — в обоих случаях сжатие определит настоящие
        глубину/k и перезапишет tr.dep[u]/tr.k[u] до использования.
        """
        u = len(tr.n0)
        s = int(pref[hi]) - int(pref[lo])
        tr.n0.append(hi - lo - s)
        tr.n1.append(s)
        tr.ch0.append(0)
        tr.ch1.append(0)
        tr.dep.append(d)
        tr.k.append(0)
        tr.first_occ.append(0)
        return u

    def advance(lo: int, hi: int, d: int) -> tuple[int, int]:
        """Сжатие ребра через memmap: O(1) переход к глубине первого
        возможного расхождения (см. sa_prod.build_tree_from_file.build) —
        два скалярных чтения из memmap + XOR вместо обхода по уровню."""
        if hi - lo <= 1:
            return depth, depth - d
        diff = int(keys[lo]) ^ int(keys[hi - 1])
        if diff == 0:
            return depth, depth - d
        dd = depth - 1 - (diff.bit_length() - 1)
        return dd, dd - d

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
            """u уже выделен (либо снаружи как u0, либо парой ниже) с
            заглушками dep/k — эта функция определяет настоящие dep/k через
            сжатие (те же 2 чтения+XOR, что advance(), но по RAM-массивам
            блока) и перезаписывает их вместе со счётчиками.
            """
            node_progress(start)
            n0c, n1c = counts(a, b)
            tr.n0[u] = n0c
            tr.n1[u] = n1c
            if b - a <= 1:
                k = depth - dd
                dd = depth
            else:
                diff = int(bkeys[a]) ^ int(bkeys[b - 1])
                if diff == 0:
                    k = depth - dd
                    dd = depth
                else:
                    ddx = depth - 1 - (diff.bit_length() - 1)
                    k = ddx - dd
                    dd = ddx
            tr.dep[u] = dd
            tr.k[u] = k
            if dd >= depth:
                fo = int(np.min(bposs[a:b])) if a < b else 0
                tr.first_occ[u] = fo
                return fo
            # dd здесь гарантированно точка настоящего ветвления (см. вывод
            # в comparator_sa_ref.build_sa_tree)
            p0 = int(bkeys[a]) >> (depth - dd)
            T = np.uint64((2 * p0 + 1) << (depth - 1 - dd))
            mid = int(np.searchsorted(bkeys, T, side="left"))  # уже в координатах блока
            if mid < a:
                mid = a
            elif mid > b:
                mid = b
            c0 = len(tr.n0)
            for _ in range(2):
                tr.n0.append(0); tr.n1.append(0)
                tr.ch0.append(0); tr.ch1.append(0)
                tr.dep.append(dd + 1); tr.k.append(0); tr.first_occ.append(0)
            tr.ch0[u] = c0
            tr.ch1[u] = c0 + 1
            f0 = rec(a, mid, dd + 1, c0)
            f1 = rec(mid, b, dd + 1, c0 + 1)
            fo = min(f0, f1)
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
                build_ram(blk, d, u, 0, hi - lo)  # перезапишет счётчики/dep/k и создаст детей
                n_blocks += 1
                if n_blocks % 20 == 0:
                    log(f"[fast] блоков обработано: {n_blocks}, узлов: {len(tr.n0)}", start)
            else:
                # hi-lo не меняется сжатием (см. вывод в comparator_sa_ref),
                # поэтому решение RAM_BLOCK выше не зависит от порядка.
                d2, k = advance(lo, hi, d)
                tr.dep[u] = d2
                tr.k[u] = k
                if d2 >= depth:
                    tr.first_occ[u] = _min_pos(poss, lo, hi)
                else:
                    # d2 здесь гарантированно точка настоящего ветвления
                    p0 = int(keys[lo]) >> (depth - d2)
                    T = np.uint64((2 * p0 + 1) << (depth - 1 - d2))
                    mid = _mem_binsearch(keys, lo, hi, T)
                    c0 = emit(lo, mid, d2 + 1)   # дети создаются СРАЗУ со счётчиками
                    c1 = emit(mid, hi, d2 + 1)
                    tr.ch0[u] = c0
                    tr.ch1[u] = c1
                    nxt.append((lo, mid, d2 + 1, c0, u))
                    nxt.append((mid, hi, d2 + 1, c1, u))
        log(f"[fast] уровень {lvl}: {len(level)} узлов -> {len(nxt)}", start)
        level = nxt
        lvl += 1

    # first_occ ветвлений memmap-пути = min по детям. Один проход по убыванию
    # индекса, а не «один уровень BFS за раз, как раньше»: дети ВСЕГДА
    # созданы позже родителя (и в memmap-BFS, и в rec()), поэтому убывающий
    # индекс — корректный снизу-вверх обход за один проход. Прежний
    # одноуровневый fixup был багом: если ребёнок САМ оказывался ветвлением
    # (его first_occ ещё не разрешён — ждёт СВОЕГО fixup на следующей
    # итерации), родитель получал placeholder 0 вместо истинного минимума.
    # build_ram уже проставляет first_occ корректно внутри себя (рекурсия
    # rec() строго сверху вниз в один вызов), этот проход их не портит: для
    # уже готовых узлов min(x, x)==x.
    for u in range(len(tr.n0) - 1, -1, -1):
        c0, c1 = tr.ch0[u], tr.ch1[u]
        if c0 or c1:
            fo = tr.first_occ[c0] if c0 else tr.first_occ[c1]
            if c1:
                fo = min(fo, tr.first_occ[c1])
            tr.first_occ[u] = fo

    internal = sum(1 for c in tr.ch0 if c)
    log(f"[fast] дерево: {len(tr)} узлов, {internal} внутренних, блоков {n_blocks}", start)
    del mm, keys, labels, poss
    pref.flush()
    del pref
    return tr, N, pref_path


if __name__ == "__main__":
    # самопроверка против explicit на малых данных, с генерируемыми (не
    # захардкоженными в отсутствующий файл) корпусами; RAM_BLOCK занижен,
    # чтобы даже маленькие тесты реально прогоняли ОБА пути (memmap для
    # диапазонов > RAM_BLOCK, RAM-блок для остальных).
    import random
    import time

    sys.path.insert(0, "tools")
    from comparator_ref import build_tree
    from comparator_wl import weakest_link_frontier
    from sa_prod import generate, merge_all, weakest_link_arrays

    # ВАЖНО: обычное переприсваивание, не через отдельный import — при запуске
    # как `python sa_prod_fast.py` этот файл выполняется как __main__, и
    # `import sa_prod_fast` загрузил бы ВТОРОЙ, независимый экземпляр модуля
    # (RAM_BLOCK поменялся бы не у того build_tree_fast, что реально вызывается
    # ниже, — memmap-путь тогда молча не проверялся бы вовсе).
    RAM_BLOCK = 40  # форсирует переключение memmap<->RAM на малых данных

    random.seed(20260810)
    CASES = [
        (b"the quick brown fox jumps over the lazy dog the quick brown fox", 8),
        (bytes(range(256)) * 4, 12),
        (b"\x00" * 40 + b"\x01" + b"\x00" * 40 + b"\x02", 32),
        (b"a" * 60 + b"b" + b"a" * 60 + b"c" + b"a" * 20, 48),
    ]
    for _ in range(4):
        n = random.randint(300, 1500)
        data = bytes(random.getrandbits(8) for _ in range(n))
        depth = random.choice([8, 16, 24, 32, 48])
        CASES.append((data, depth))

    start = time.perf_counter()
    fail = 0
    for data, depth in CASES:
        tmp = Path("tools/.sa_tmp_fast")
        tmp.mkdir(parents=True, exist_ok=True)
        created = []
        files, _ = generate(data, depth, tmp, created, start)
        final = merge_all(files, tmp, created, start, way=4)
        tr, N, prefp = build_tree_fast(final, depth, start)
        pts = weakest_link_arrays(tr)
        e = build_tree(data, depth)
        ref = weakest_link_frontier(e)
        ok = len(pts) == len(ref) and all(
            l1 == l2 and abs(c1 - c2) < 1e-6 for (l1, c1), (l2, c2) in zip(pts, ref)
        )
        status = "OK  " if ok else "FAIL"
        if not ok:
            fail += 1
        print(f"{status} depth={depth:<3} len={len(data):<5} узлов {len(tr):>6} точек {len(pts):>5}")
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
    print()
    if fail:
        print(f"ПРОВАЛЕНО: {fail} из {len(CASES)}")
        sys.exit(1)
    print(f"[fast] все {len(CASES)} проверок пройдены")
