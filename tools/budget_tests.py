"""Инварианты бюджетного слоя (этап 4).

Проверяется то, что нельзя проверить сверкой с эталоном: сам бюджет, целостность
дерева под вытеснением, воспроизводимость и то, что бюджетный слой не меняет
поведение, пока вытеснение не начало срабатывать.

    python budget_tests.py [--bin ../bin/ctw.exe]
"""
import argparse
import glob
import os
import re
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

FIELDS = (
    "узлов", "создано", "вытеснено", "масса вытесн.",
    "обрыв бюджет", "обрыв ленивый", "кодовая длина", "bpc",
)


def run(binary, path, **kw):
    """Запустить ядро и вернуть разобранный вывод."""
    # --verify-sum держит под контролем главный инвариант предсказателя:
    # Σ_x P(x) = 1. Без него ошибки учёта символа выглядят как улучшение сжатия.
    cmd = [binary, path, "--check", "--verify-sum"]
    for k, v in kw.items():
        flag = "--" + k.replace("_", "-")
        if v is True:
            cmd.append(flag)
        elif v is not None:
            cmd += [flag, str(v)]
    out = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8")
    if out.returncode != 0:
        raise RuntimeError(f"код {out.returncode}: {out.stdout}\n{out.stderr}")
    res = {}
    for line in out.stdout.splitlines():
        m = re.match(r"(.+?)\s{2,}(.+)", line)
        if m:
            res[m.group(1).strip()] = m.group(2).strip()
    for f in FIELDS:
        if f not in res:
            raise RuntimeError(f"нет поля «{f}» в выводе:\n{out.stdout}")
    return res


def num(res, field):
    return float(res[field].split()[0])


def make_corpus(dest):
    """Реальный текст, если он есть рядом; иначе синтетика с похожей структурой."""
    docs = sorted(glob.glob(
        os.path.join(os.path.dirname(dest), "..", "..",
                     "cpu-neural-foundations", "docs", "*.txt")))
    blob = b""
    for d in docs:
        blob += open(d, "rb").read()
    if len(blob) < 4096:
        words = [b"the", b"quick", b"brown", b"fox", b"context", b"tree", b"weighting"]
        blob = b" ".join(words[(i * 7 + i // 3) % len(words)] for i in range(20000))
    open(dest, "wb").write(blob)
    return len(blob)


def main():
    ap = argparse.ArgumentParser()
    here = os.path.dirname(os.path.abspath(__file__))
    ap.add_argument("--bin", default=os.path.join(here, "..", "bin", "ctw.exe"))
    args = ap.parse_args()
    if not os.path.exists(args.bin):
        print(f"нет бинарника {args.bin}")
        return 1

    corpus = os.path.join(here, "..", "bin", "_test_corpus.bin")
    size = make_corpus(corpus)
    limit = min(size, 60000)
    depth = 16
    fails = []

    def check(name, ok, detail=""):
        print(f"{'OK  ' if ok else 'FAIL'} {name}{(' — ' + detail) if detail else ''}")
        if not ok:
            fails.append(name)

    print(f"корпус {limit} байт, глубина {depth}\n")

    # 1. Бюджет не превышается никогда, инварианты дерева целы.
    #    (--check уже отработал внутри ядра; здесь сверяем и число узлов.)
    base = run(args.bin, corpus, depth=depth, limit=limit)
    full_nodes = int(num(base, "узлов"))
    print(f"без бюджета: {full_nodes} узлов, bpc {base['bpc']}\n")

    for b in (64, 256, 1024, 4096, 16384, 65536):
        r = run(args.bin, corpus, depth=depth, limit=limit, budget=b)
        n = int(num(r, "узлов"))
        check(f"бюджет {b}: узлов {n} ≤ {b}", n <= b,
              f"вытеснений {int(num(r,'вытеснено'))}, bpc {r['bpc']}")

    # 2. Бюджет с запасом обязан давать в точности безбюджетный результат:
    #    вытеснение не срабатывает, значит и расхождений быть не может.
    roomy = run(args.bin, corpus, depth=depth, limit=limit, budget=full_nodes + 10)
    check("запас бюджета ≡ без бюджета",
          roomy["кодовая длина"] == base["кодовая длина"]
          and int(num(roomy, "вытеснено")) == 0,
          f"{roomy['кодовая длина']} против {base['кодовая длина']}")

    # 3. Воспроизводимость: тот же вход и те же параметры — тот же вывод,
    #    несмотря на случайную выборку кандидатов.
    a = run(args.bin, corpus, depth=depth, limit=limit, budget=2048)
    b2 = run(args.bin, corpus, depth=depth, limit=limit, budget=2048)
    check("детерминизм при одном зерне", a == b2)

    c = run(args.bin, corpus, depth=depth, limit=limit, budget=2048, seed=12345)
    check("другое зерно — другой ход вытеснения",
          c["кодовая длина"] != a["кодовая длина"],
          "иначе выборка не влияет и тест бессмыслен")

    # 4. Все политики работают и не рушат инварианты.
    for victim in ("lfu", "ss", "random"):
        for birth in ("cold", "spacesaving", "parent"):
            r = run(args.bin, corpus, depth=depth, limit=limit, budget=1024,
                    victim=victim, birth=birth)
            n = int(num(r, "узлов"))
            check(f"политика {victim}/{birth}", n <= 1024, f"bpc {r['bpc']}")

    # 5. Ленивое создание сокращает число созданных узлов.
    lazy0 = run(args.bin, corpus, depth=depth, limit=limit, budget=1024, lazy=0)
    lazy4 = run(args.bin, corpus, depth=depth, limit=limit, budget=1024, lazy=4)
    check("ленивое создание снижает отток",
          num(lazy4, "создано") < num(lazy0, "создано"),
          f"создано {int(num(lazy4,'создано'))} против {int(num(lazy0,'создано'))}")

    # 5б. Отложенное расщепление детерминированных узлов: сокращает число
    #     созданных узлов и не ломает инвариант Σ_x P(x)=1 (run() гоняет с
    #     --verify-sum, то есть проверка идёт на каждом бите). Обрыв спуска —
    #     исторически самое опасное место ядра, см. design-spec §2а.
    det = run(args.bin, corpus, depth=depth, limit=limit, budget=1024,
              defer_det=16)
    check("отложенное расщепление детерминированных снижает отток",
          num(det, "создано") < num(lazy0, "создано") and num(det, "обрыв детерм.") > 0,
          f"создано {int(num(det,'создано'))} против {int(num(lazy0,'создано'))}, "
          f"обрывов {int(num(det,'обрыв детерм.'))}")

    # 6. Качество монотонно не ухудшается с ростом бюджета (с допуском на шум
    #    выборки): грубая проверка того, что бюджет вообще работает как ресурс.
    bpcs = [(b, num(run(args.bin, corpus, depth=depth, limit=limit, budget=b), "bpc"))
            for b in (128, 512, 2048, 8192, 32768)]
    mono = all(bpcs[i][1] >= bpcs[i + 1][1] - 0.02 for i in range(len(bpcs) - 1))
    check("bpc не растёт с бюджетом", mono,
          " ".join(f"{b}:{v:.3f}" for b, v in bpcs))

    os.unlink(corpus)
    print()
    if fails:
        print(f"ПРОВАЛЕНО: {len(fails)} — {', '.join(fails)}")
        return 1
    print("все инварианты бюджетного слоя выполнены")
    return 0


if __name__ == "__main__":
    sys.exit(main())
