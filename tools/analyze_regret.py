#!/usr/bin/env python3
"""⚠️ НЕ СЧИТАЕТ СОЖАЛЕНИЕ. Не использовать до переписывания.

Скрипт читает ТОЛЬКО вывод компаратора и выдаёт cost(M) − cost(полное дерево),
то есть разницу компаратора с самим собой. Кодовая длина алгоритма в неё не
входит вообще, а сожаление из постановки П4 — это R_T = L_алг − min_{S∈T_M} L_S.
Разбор ошибки — notes/stage5b-comparator-audit.md (пункт 4 раздела «что чинить»).

Правильный расчёт сейчас делается вручную и записан в
notes/stage5b-comparator-results.md: кодовая длина ядра из stage5-results.md
минус кодовая длина компаратора при согласованном бюджете (M = узлы/c), и
обязательно с `--cost kt` — модель стоимости листа меняет пол на 0.03 bpc при
D=24 и на 0.6 bpc при D=48.

Чтобы переписать, скрипту нужны ДВА входа: таблица bpc ядра и таблица
компаратора, плюс явный коэффициент c.
"""
import sys, re

def parse_comparator_output(text: str):
    """Парсит вывод comparator.exe:
    узлов в полном дереве   N
    точек на оболочке       K
    листья (полное дерево)  L
    стоимость полного дерева C бит (X.XXXX bpc)
    ...
    M1    C1    bpc1
    M2    C2    bpc2
    """
    lines = text.strip().split('\n')
    result = {'full_tree_nodes': 0, 'full_tree_leaves': 0, 'full_tree_cost': 0.0, 'bpc': 0.0, 'points': []}
    
    for line in lines:
        m = re.match(r'узлов в полном дереве\s+(\d+)', line)
        if m: result['full_tree_nodes'] = int(m.group(1)); continue
        m = re.match(r'листья \(полное дерево\)\s+(\d+)', line)
        if m: result['full_tree_leaves'] = int(m.group(1)); continue
        # "X бит (Y бит/бит, Z bpc)" — comparator.rs печатает обе единицы;
        # regex ниже разбирает и старый двухзначный, и новый трёхзначный
        # формат (bpc — последнее число в скобках в обоих случаях).
        m = re.match(
            r'стоимость полного дерева\s+([\d.]+)\s+бит\s+\(([\d.]+)(?:\s+бит/бит,\s+([\d.]+))?\s+bpc\)',
            line,
        )
        if m:
            result['full_tree_cost'] = float(m.group(1))
            result['bpc'] = float(m.group(3) if m.group(3) is not None else m.group(2))
            continue
        # строки точек оболочки (--points, 3 или 4 токена: листья, биты,
        # [бит/бит,] bpc) — bpc всегда последний токен.
        parts = line.split()
        if len(parts) in (3, 4):
            try:
                M = int(parts[0])
                cost = float(parts[1])
                bpc = float(parts[-1])
                result['points'].append((M, cost, bpc))
            except ValueError:
                pass
    return result

def main():
    if len(sys.argv) < 2:
        print("Usage: python analyze_regret.py <comparator_output.txt>")
        sys.exit(1)
    
    with open(sys.argv[1], 'r', encoding='utf-8') as f:
        text = f.read()
    
    data = parse_comparator_output(text)
    
    print(f"Полное дерево: {data['full_tree_nodes']} узлов, {data['full_tree_leaves']} листьев")
    print(f"Стоимость полного дерева: {data['full_tree_cost']:.4f} бит ({data['bpc']:.4f} bpc)")
    print(f"Точек на оболочке: {len(data['points'])}")
    print()
    
    # L_full = стоимость полного дерева (нет бюджета)
    L_full = data['full_tree_cost']
    
    # Из stage5: budget-CTW D=48 (32 MB) = 2.5341 bpc
    # Полный CTW D=24 (268 MB) = 2.7239 bpc
    # На D=48 полное дерево не влезало, но компаратор считает точное L_full для D=48 на enwik8
    
    print(f"{'M':>8}  {'cost':>12}  {'bpc':>8}  {'regret(cost)':>12}  {'regret(bpc)':>10}")
    for M, cost, bpc in data['points']:
        regret_cost = cost - L_full
        regret_bpc = bpc - data['bpc']
        print(f"{M:>8}  {cost:>12.4f}  {bpc:>8.4f}  {regret_cost:>12.4f}  {regret_bpc:>10.4f}")
    
    # Важное замечание по спеке:
    print()
    print("=== ВАЖНО (спека §5) ===")
    print("Лагранжева развёртка (слабейшее звено) даёт НИЖНЮЮ ВЫПУКЛУЮ ОБОЛОЧКУ.")
    print("Regret, измеренный через эти точки — НИЖНЯЯ ОЦЕНКА истинного regret.")
    print("На невыпуклых участках бюджета истинный regret может быть больше.")

if __name__ == '__main__':
    main()