"""Adversarial-последовательность для нижней границы (пункт (3) П4).

Конструкция блоками. Блок = [адрес: D бит][полезный бит: 1 бит]. Адрес
выбирается равномерно из фиксированного множества G, |G| = K; полезный бит
равен метке ℓ(адрес) — фиксированной случайной функции G → {0,1}.

Смысл: в позиции полезного бита контекст глубины D — это в точности адрес,
поэтому древесный источник с листьями на адресах G предсказывает полезные
биты БЕЗ ОШИБКИ. Предсказателю же, чтобы делать то же самое, надо помнить K
меток; если памяти меньше, он обязан ошибаться — и ошибаться в каждом раунде
заново, потому что метки не меняются, а память не растёт. Отсюда линейный по T
штраф. Формулировка и доказательство — notes/stage11-lower-bound.md.

Адресные биты одинаково доступны обеим сторонам и в сожалении почти
сокращаются: их энтропия log₂K на блок, и её платят оба.

    python tools/adversary.py OUT.bin --depth 16 --keys 256 --blocks 200000

Проверить, что конструкция делает обещанное:
    bin/ctw.exe OUT.bin --depth 16 --budget МАЛО
    bin/comparator.exe OUT.bin --depth 16 --cost kt --budgets ...
"""
import argparse
import random
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--depth", type=int, default=16, help="длина адреса D в битах")
    ap.add_argument("--keys", type=int, default=256, help="сколько адресов K в G")
    ap.add_argument("--blocks", type=int, default=200000)
    ap.add_argument("--seed", type=int, default=20260816)
    ap.add_argument("--order", choices=("cycle", "random"), default="cycle",
                    help="cycle — каждый адрес ровно раз за раунд (режим теоремы); "
                         "random — равномерный выбор (без побочного канала фазы)")
    args = ap.parse_args()

    if args.keys > 1 << args.depth:
        print(f"K={args.keys} больше 2^D={1 << args.depth}")
        return 2

    rng = random.Random(args.seed)
    # G — случайные различные адреса; ℓ — случайные метки
    g = rng.sample(range(1 << args.depth), args.keys)
    label = [rng.getrandbits(1) for _ in g]

    bits = bytearray()
    for i in range(args.blocks):
        j = i % args.keys if args.order == "cycle" else rng.randrange(args.keys)
        a = g[j]
        for k in range(args.depth - 1, -1, -1):   # адрес, старший бит первым
            bits.append((a >> k) & 1)
        bits.append(label[j])

    # упаковка в байты, старший бит первым — как читает ядро
    pad = (-len(bits)) % 8
    bits.extend([0] * pad)
    out = bytearray()
    for i in range(0, len(bits), 8):
        b = 0
        for k in range(8):
            b = (b << 1) | bits[i + k]
        out.append(b)
    with open(args.out, "wb") as f:
        f.write(out)

    nbits = args.blocks * (args.depth + 1)
    print(f"{args.out}: {len(out)} байт, {nbits} бит, блоков {args.blocks}, "
          f"D={args.depth}, K={args.keys}")
    print(f"порядок {args.order}; каждый адрес повторяется "
          f"{'ровно' if args.order == 'cycle' else '~'}{args.blocks // args.keys} раз")
    print(f"полезных бит {args.blocks} ({100.0 * args.blocks / nbits:.1f}% потока); "
          f"их энтропия для незнающего метки — {args.blocks} бит, для знающего — 0")
    print(f"адресных бит {args.blocks * args.depth}, их энтропия "
          f"{args.blocks} × log₂{args.keys} = {args.blocks * (args.keys.bit_length() - 1)} бит "
          f"(платят обе стороны)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
