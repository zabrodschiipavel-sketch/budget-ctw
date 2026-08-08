import sys, subprocess, random
sys.stdout.reconfigure(encoding="utf-8", errors="replace")
sys.path.insert(0, "tools")
from comparator_ref import build_tree, ExactDP
from comparator_wl import weakest_link_frontier

random.seed(12345)
BAD=0; CHECKS=0
for trial in range(12):
    N=random.randint(40,160)
    data=bytes(random.getrandbits(8) for _ in range(N))
    depth=random.randint(6,10)
    fn=f"tools/_r_{trial}.bin"
    open(fn,"wb").write(data)
    out=subprocess.run(["./bin/comparator.exe", fn, "--depth", str(depth), "--points", "200"],
                       capture_output=True, text=True)
    open(fn,"rb").read()  # убедимся файл есть
    # парсим Rust-точки
    rust_pts=[]
    for line in out.stdout.splitlines():
        parts=line.split()
        if len(parts)==3 and parts[0].isdigit():
            try:
                l=int(parts[0]); c=float(parts[1]); rust_pts.append((l,c))
            except: pass
    # Python-эталон (weakest-link) и точный DP
    nodes=build_tree(data, depth)
    py=[(l,c) for l,c in weakest_link_frontier(nodes)]
    dp=ExactDP(nodes, max(leaves_count(nodes), 1)) if False else ExactDP(nodes, 500)
    # сверяем: каждая Python-точка должна быть в Rust (с допуском)
    for (l,c) in py:
        best=min((abs(c2-c), l2, c2) for (l2,c2) in rust_pts if l2==l)
        ok = best[0] < 1e-3
        CHECKS+=1
        if not ok:
            BAD+=1
            print(f"[trial {trial}] M={l}: py={c:.4f} rust={best[2]:.4f} diff={best[0]:.2e}")
    # и каждая Rust-точка должна быть оптимальна (<= DP + 1e-6)
    for (l,c) in rust_pts:
        opt=dp.solve(0,l)
        if c > opt + 1e-3:
            BAD+=1; CHECKS+=1
            print(f"[trial {trial}] Rust M={l}: {c:.4f} > DP opt {opt:.4f}")
    import os; os.remove(fn)
print(f"\nИТОГ: проверено {CHECKS}, расхождений {BAD}")
sys.exit(1 if BAD else 0)

def leaves_count(nodes):
    return max(1, sum(1 for nd in nodes if nd["ch"][0]==0 and nd["ch"][1]==0))
