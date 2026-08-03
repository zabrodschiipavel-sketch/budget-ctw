"""Проверка гипотезы: поштучное отщипывание при связях α даёт разные
(иногда неоптимальные) последовательности. Классика Бреймана требует
отщипывать ВСЕ слабые звенья с минимальным α одновременно.

Сравниваются три варианта на точном DP:
  A. поштучно, меньший индекс первым (текущий Python)
  B. поштучно, больший индекс первым (текущий Rust)
  C. все слабые звенья с α_min одновременно
"""
import heapq
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")
sys.path.insert(0, "tools")
from comparator_ref import build_tree, ExactDP, cost_leaf


def weakest_link_variant(nodes, mode):
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

    def kill(u):
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
                kill(ch0[u])
            if ch1[u]:
                kill(ch1[u])

    pts = [(leaves[0], R[0])]
    alpha = {}

    def push(u):
        if alive[u] and ch0[u] and ch1[u] and leaves[u] > 1:
            a = (cost_leaf(nodes, u) - R[u]) / (leaves[u] - 1)
            alpha[u] = a
            heapq.heappush(h, (a, u))

    def refresh_ancestors(u):
        v = par[u]
        while v != u:
            R[v] = R[ch0[v]] + R[ch1[v]]
            leaves[v] = leaves[ch0[v]] + leaves[ch1[v]]
            if leaves[v] == 1:
                break
            alpha[v] = (cost_leaf(nodes, v) - R[v]) / (leaves[v] - 1)
            heapq.heappush(h, (alpha[v], v))
            if v == 0:
                break
            v = par[v]

    h = []
    for u in range(n):
        push(u)
    while h:
        a, u = heapq.heappop(h)
        if not alive[u] or leaves[u] <= 1:
            continue
        if alpha.get(u) != a:
            continue
        if mode == "C":
            # собрать все живые узлы с тем же α (в пределах эпсилон)
            batch = [u]
            rest = []
            while h:
                a2, u2 = heapq.heappop(h)
                if (
                    alive[u2]
                    and leaves[u2] > 1
                    and alpha.get(u2) == a2
                    and abs(a2 - a) < 1e-12
                ):
                    batch.append(u2)
                else:
                    rest.append((a2, u2))
            for it in rest:
                heapq.heappush(h, it)
            for uu in batch:
                if not alive[uu] or leaves[uu] <= 1:
                    continue
                stack = [uu]
                while stack:
                    w = stack.pop()
                    alive[w] = False
                    if ch0[w]:
                        stack.append(ch0[w])
                    if ch1[w]:
                        stack.append(ch1[w])
                R[uu] = cost_leaf(nodes, uu)
                leaves[uu] = 1
                refresh_ancestors(uu)
        else:
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
            refresh_ancestors(u)
        pts.append((leaves[0], R[0]))
        if leaves[0] == 1:
            break
    return pts


CASES = [
    (b"abababababababab", 8),
    (b"the quick brown fox jumps over the lazy dog the quick brown fox", 8),
    (b"the quick brown fox jumps over the lazy dog", 12),
    (bytes((i * 37 + 11) % 256 for i in range(64)), 10),
    (b"hello world hello world hello world", 12),
    (b"\x00" * 32, 8),
]

for data, depth in CASES:
    nodes = build_tree(data, depth)
    max_m = min(24, len(nodes))
    dp = ExactDP(nodes, max_m).frontier(max_m)
    print(f"D={depth} узлов={len(nodes)}")
    for mode in ("A", "B", "C"):
        pts = weakest_link_variant(nodes, mode)
        bad = 0
        worst = 0.0
        for m in range(1, max_m + 1):
            cand = [c for l, c in pts if l <= m]
            if not cand:
                continue
            b = min(cand)
            d = dp[m - 1]
            if b < d - 1e-9:
                bad += 1
            worst = max(worst, (b - d) / max(d, 1e-9))
        n_opt = sum(1 for l, c in pts if l <= max_m and any(abs(c - dp[l - 1]) < 1e-6 for _ in [0]))
        # сколько точек совпадают с DP точно
        exact = sum(1 for l, c in pts if l <= max_m and abs(c - dp[l - 1]) < 1e-6)
        print(f"  {mode}: точек={len(pts)} нарушений={bad} совпало_с_DP={exact}/{len(pts)} макс_разрыв={worst*100:.2f}%")
