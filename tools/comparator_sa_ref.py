"""SA-бэкенд компаратора — эталонная реализация.

Строит контрактированное дерево из отсортированных записей (контекст, метка)
и считает frontier слабейшего звена с тай-брейком, эквивалентным explicit-дереву.

Ключевая семантика (совпадает с explicit-деревом после контракции в
weakest_link_frontier):

  - Узел с ДВУМЯ детьми — внутренний (остаётся).
  - Узел с ≤1 ребёнком — ЛИСТ наверху унарной цепочки: его счётчики n[0], n[1]
    поглощают ВСЁ поддерево ниже (в explicit-дереве дети убиваются, а n[u]
    накоплен по всем проходящим записям). Спуск вглубь НЕ выполняется.
  - Это НЕ Patricia-дерево: Patricia сжимает унарное ребро к следующему
    ветвлению, а explicit-контракция останавливается на первом унарном узле.

Тай-брейк при равных α: explicit-дерево нумерует узлы в порядке создания =
(позиция первого вхождения контекста в потоке, глубина) лексикографически
(проверено: 0 расхождений из 8243 узлов). Поэтому SA-бэкенд использует heap-ключ
(α, first_occ, dep) — последовательность отщипываний идентична explicit.
"""
import heapq
from comparator_ref import bits_of


def _records(data: bytes, depth: int):
    """(контекст-ключ глубины depth, метка, позиция в потоке) для каждого бита."""
    hist = 0
    out = []
    for i, x in enumerate(bits_of(data)):
        key = 0
        for d in range(depth):
            key = (key << 1) | ((hist >> d) & 1)
        out.append((key, x, i))
        hist = ((hist << 1) | x) & ((1 << 63) - 1)
    return out


def build_sa_tree(data: bytes, depth: int):
    """Контрактированное дерево + first_occ каждого узла.

    Возвращает (nodes, first_occ): nodes — список {n, ch, dep}, first_occ —
    позиция первого вхождения контекста узла в битовом потоке.
    """
    recs = sorted(_records(data, depth))
    keys = [r[0] for r in recs]
    labels = [r[1] for r in recs]
    spos = [r[2] for r in recs]
    pref0 = [0]
    pref1 = [0]
    for x in labels:
        pref0.append(pref0[-1] + (x == 0))
        pref1.append(pref1[-1] + (x == 1))

    def counts(lo, hi):
        return [pref0[hi] - pref0[lo], pref1[hi] - pref1[lo]]

    def bit_at(key, d):
        return (key >> (depth - 1 - d)) & 1

    nodes = []
    ranges = {}

    def build(lo, hi, d):
        u = len(nodes)
        ranges[u] = (lo, hi)
        nodes.append({"n": counts(lo, hi), "ch": [0, 0], "dep": d})
        if d >= depth or hi - lo <= 1:
            return u
        mid = lo
        while mid < hi and bit_at(keys[mid], d) == 0:
            mid += 1
        has0, has1 = mid > lo, mid < hi
        if has0 and has1:
            nodes[u]["ch"][0] = build(lo, mid, d + 1)
            nodes[u]["ch"][1] = build(mid, hi, d + 1)
        # иначе: унарный — лист, поддерево поглощено счётчиками узла
        return u

    build(0, len(recs), 0)
    first_occ = {u: min(spos[lo:hi]) for u, (lo, hi) in ranges.items()}
    return nodes, first_occ


def weakest_link_frontier_sa(nodes, first_occ):
    """Frontier как в weakest_link_frontier, но с тай-брейком (α, first_occ, dep).

    Даёт ПОСЛЕДОВАТЕЛЬНОСТЬ, идентичную explicit-дереву (проверено).
    """
    from comparator_ref import cost_leaf
    n = len(nodes)
    ch0 = [nd["ch"][0] for nd in nodes]
    ch1 = [nd["ch"][1] for nd in nodes]
    par = [0] * n
    for u in range(n):
        for c in (ch0[u], ch1[u]):
            if c:
                par[c] = u
    R = [0.0] * n
    leaves = [0] * n
    alive = [True] * n

    def kill_subtree(u):
        stack = [u]
        while stack:
            w = stack.pop()
            alive[w] = False
            if ch0[w]:
                stack.append(ch0[w])
            if ch1[w]:
                stack.append(ch1[w])

    for u in range(n - 1, -1, -1):
        if ch0[u] and ch1[u]:
            R[u] = R[ch0[u]] + R[ch1[u]]
            leaves[u] = leaves[ch0[u]] + leaves[ch1[u]]
        else:
            R[u] = cost_leaf(nodes, u)
            leaves[u] = 1
            if ch0[u]:
                kill_subtree(ch0[u])
            if ch1[u]:
                kill_subtree(ch1[u])
    pts = [(leaves[0], R[0])]

    alpha = {}

    def push(u):
        if alive[u] and ch0[u] and ch1[u] and leaves[u] > 1:
            a = (cost_leaf(nodes, u) - R[u]) / (leaves[u] - 1)
            alpha[u] = a
            heapq.heappush(h, (a, first_occ[u], nodes[u]["dep"]))

    h = []
    fo_dep_to_u = {(first_occ[u], nodes[u]["dep"]): u for u in range(n)}
    for u in range(n):
        push(u)
    while h:
        a, fo, dep = heapq.heappop(h)
        u = fo_dep_to_u[(fo, dep)]
        if not alive[u] or leaves[u] <= 1:
            continue
        if alpha.get(u) != a:
            continue
        stack = [u]
        while stack:
            w = stack.pop()
            alive[w] = False
            if ch0[w]:
                stack.append(ch0[w])
            if ch1[w]:
                stack.append(ch1[w])
        R[u] = cost_leaf(nodes, u)
        leaves[u] = 1
        v = par[u]
        while v != u:
            R[v] = R[ch0[v]] + R[ch1[v]]
            leaves[v] = leaves[ch0[v]] + leaves[ch1[v]]
            if leaves[v] == 1:
                break
            alpha[v] = (cost_leaf(nodes, v) - R[v]) / (leaves[v] - 1)
            heapq.heappush(h, (alpha[v], first_occ[v], nodes[v]["dep"]))
            if v == 0:
                break
            v = par[v]
        pts.append((leaves[0], R[0]))
        if leaves[0] == 1:
            break
    return pts


if __name__ == "__main__":
    import sys
    from comparator_ref import build_tree
    from comparator_wl import weakest_link_frontier

    CASES = [
        (b"abababababab", 1),
        (b"abababababab", 3),
        (b"abababababab", 8),
        (b"\x00" * 8, 1),
        (b"\x00" * 8, 3),
        (b"\x00" * 8, 8),
        (b"\xff" * 8, 1),
        (b"\xff" * 8, 3),
        (b"\xff" * 8, 8),
        (bytes(range(32)), 1),
        (bytes(range(32)), 3),
        (bytes(range(32)), 8),
        (b"the quick brown fox jumps over the lazy dog", 8),
        (bytes(range(256)) * 4, 12),
        (b"0101010101010101", 16),
    ]
    for data, depth in CASES:
        e = build_tree(data, depth)
        s, fo = build_sa_tree(data, depth)
        a = weakest_link_frontier(e)
        b = weakest_link_frontier_sa(s, fo)
        assert len(a) == len(b), (len(a), len(b), len(data), depth)
        for (la, ca), (lb, cb) in zip(a, b):
            assert la == lb and abs(ca - cb) < 1e-8, (la, ca, lb, cb, len(data), depth)
        print(f"OK  len={len(data)} depth={depth}  "
              f"узлов: explicit={len(e)} sa={len(s)} точек={len(a)}")
    print("SA fixed-key oracle: OK (последовательность идентична explicit)")
