//! Аудит класса сравнения компаратора (этап 5б).
//!
//! Считает на одних и тех же данных и в той же битовой модели, что `src/ctw.rs`
//! и `src/comparator.rs`, две стоимости полного дерева:
//!
//!   A — «контрактированная»: узел с ≤1 ребёнком становится листом, и всё
//!       поддерево под ним выбрасывается. Это семантика `src/comparator.rs`,
//!       `tools/comparator_ref.py`, `tools/sa_prod*.py`.
//!   B — честная: узел с ≥1 ребёнком внутренний, отсутствующий брат — законный
//!       лист нулевой массы и нулевой стоимости; платят только узлы совсем без
//!       детей. Это класс T_M из постановки П4 («деревья контекстов с ≤ M
//!       листьями, глубина ≤ D»).
//!
//! A ≥ B всегда: класс A — строгий подкласс. Разность и есть систематическое
//! завышение min_{S∈T_M} L_S(x), из-за которого измеренное сожаление занижено
//! (и на enwik8 уходит в минус, см. notes/stage5b-comparator-audit.md).
//!
//! Сборка: rustc -O --edition 2021 -o bin/class_audit.exe tools/comparator_class_audit.rs
//! Запуск: class_audit <файл> <глубина> [лимит_байт]

use std::env;
use std::fs;

#[derive(Clone, Copy)]
struct Node {
    n: [u32; 2],
    child: [u32; 2],
}

/// c(u) = n_u · H(эмпирическое распределение следующего бита), биты.
fn cost_leaf(nd: &Node) -> f64 {
    let n0 = nd.n[0] as f64;
    let n1 = nd.n[1] as f64;
    let n = n0 + n1;
    if n <= 0.0 {
        return 0.0;
    }
    let p = n0 / n;
    if p <= 0.0 || p >= 1.0 {
        return 0.0;
    }
    n * (-p * p.log2() - (1.0 - p) * (1.0 - p).log2())
}

/// Полное дерево встреченных контекстов — тот же обход, что в build_tree
/// компаратора: байт → 8 бит MSB-first, бит глубины d = (hist>>d)&1.
fn build_tree(data: &[u8], depth: usize) -> Vec<Node> {
    let mut nodes = vec![Node { n: [0, 0], child: [0, 0] }];
    let mut hist: u64 = 0;
    for &byte in data {
        for s in (0..8).rev() {
            let x = ((byte >> s) & 1) as usize;
            let mut cur = 0usize;
            nodes[cur].n[x] += 1;
            for d in 0..depth {
                let b = ((hist >> d) & 1) as usize;
                let c = nodes[cur].child[b];
                if c == 0 {
                    let idx = nodes.len() as u32;
                    nodes.push(Node { n: [0, 0], child: [0, 0] });
                    nodes[cur].child[b] = idx;
                    cur = idx as usize;
                } else {
                    cur = c as usize;
                }
                nodes[cur].n[x] += 1;
            }
            hist = (hist << 1) | x as u64;
        }
    }
    nodes
}

fn main() {
    let a: Vec<String> = env::args().collect();
    if a.len() < 3 {
        eprintln!("использование: class_audit <файл> <глубина> [лимит_байт]");
        std::process::exit(2);
    }
    let depth: usize = a[2].parse().expect("глубина");
    let mut data = fs::read(&a[1]).expect("файл не читается");
    if a.len() > 3 {
        data.truncate(a[3].parse().expect("лимит"));
    }
    let nodes = build_tree(&data, depth);

    // A: контрактированная семантика проекта
    let mut contracted = 0.0f64;
    let mut contracted_leaves: u64 = 0;
    let mut unary_cuts: u64 = 0;
    let mut unary_mass: u64 = 0;
    let mut stack = vec![0u32];
    while let Some(u) = stack.pop() {
        let nd = nodes[u as usize];
        let (c0, c1) = (nd.child[0], nd.child[1]);
        if c0 != 0 && c1 != 0 {
            stack.push(c0);
            stack.push(c1);
        } else {
            contracted += cost_leaf(&nd);
            contracted_leaves += 1;
            if c0 != 0 || c1 != 0 {
                unary_cuts += 1;
                unary_mass += nd.n[0] as u64 + nd.n[1] as u64;
            }
        }
    }

    // B: честный класс T_M (отсутствующий брат — лист нулевой стоимости)
    let mut honest = 0.0f64;
    let mut honest_leaves: u64 = 0;
    let mut stack = vec![0u32];
    while let Some(u) = stack.pop() {
        let nd = nodes[u as usize];
        let (c0, c1) = (nd.child[0], nd.child[1]);
        if c0 != 0 || c1 != 0 {
            if c0 != 0 { stack.push(c0); } else { honest_leaves += 1; }
            if c1 != 0 { stack.push(c1); } else { honest_leaves += 1; }
        } else {
            honest += cost_leaf(&nd);
            honest_leaves += 1;
        }
    }

    let nbits = (data.len() * 8) as f64;
    let nbytes = data.len() as f64;
    println!("байт {}  глубина {}  узлов {}", data.len(), depth, nodes.len());
    println!("A контрактированное (проект) {:>18.3} бит  {:.6} бит/бит  {:.4} бит/байт  листьев {}",
             contracted, contracted / nbits, contracted / nbytes, contracted_leaves);
    println!("B честное полное дерево      {:>18.3} бит  {:.6} бит/бит  {:.4} бит/байт  листьев {}",
             honest, honest / nbits, honest / nbytes, honest_leaves);
    println!("завышение A−B                {:>18.3} бит  {:.4} бит/байт  {:.2}% от B",
             contracted - honest, (contracted - honest) / nbytes,
             100.0 * (contracted - honest) / honest);
    println!("унарных обрывов {}  битов истории под ними {}", unary_cuts, unary_mass);
}
