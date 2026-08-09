//! Честная нижняя оболочка min_{S∈T_M} L_S(x) — класс T_M из постановки П4.
//!
//! От `src/comparator.rs` отличается ровно одним: узел с одним встреченным
//! ребёнком МОЖНО расщепить, отсутствующий брат становится листом нулевой
//! массы (и стоит только λ в лагранжевой развёртке). `src/comparator.rs`
//! вместо этого превращает такой узел в лист и выбрасывает всё поддерево.
//!
//! Метод — лагранжева развёртка (BFOS): при штрафе λ за лист
//! F_λ(u) = min( c(u) + λ, F_λ(u0) + F_λ(u1) ), сетка λ сверху вниз даёт точки
//! нижней выпуклой оболочки (листья, биты). Оговорка спеки §5 в силе: для
//! бюджета вне оболочки точка — верхняя граница истинного минимума.
//!
//! Сборка: rustc -O --edition 2021 -o bin/honest_frontier.exe tools/comparator_honest_frontier.rs
//! Запуск: honest_frontier <файл> <глубина> [лимит_байт] [шаг_сетки_λ]

use std::env;
use std::fs;

#[derive(Clone, Copy)]
struct Node {
    n: [u32; 2],
    child: [u32; 2],
}

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

/// Один проход развёртки: возвращает (стоимость без штрафа, число листьев).
/// Узлы создаются «родитель раньше детей», поэтому обход с конца — пост-порядок.
fn sweep(nodes: &[Node], c: &[f64], lam: f64, f: &mut [f64], l: &mut [u64]) -> (f64, u64) {
    for u in (0..nodes.len()).rev() {
        let (c0, c1) = (nodes[u].child[0], nodes[u].child[1]);
        let as_leaf = c[u] + lam;
        if c0 != 0 || c1 != 0 {
            // отсутствующий ребёнок — пустой лист: стоимость 0, штраф λ, 1 лист
            let (f0, l0) = if c0 != 0 { (f[c0 as usize], l[c0 as usize]) } else { (lam, 1) };
            let (f1, l1) = if c1 != 0 { (f[c1 as usize], l[c1 as usize]) } else { (lam, 1) };
            if f0 + f1 < as_leaf {
                f[u] = f0 + f1;
                l[u] = l0 + l1;
                continue;
            }
        }
        f[u] = as_leaf;
        l[u] = 1;
    }
    (f[0] - lam * l[0] as f64, l[0])
}

fn main() {
    let a: Vec<String> = env::args().collect();
    if a.len() < 3 {
        eprintln!("использование: honest_frontier <файл> <глубина> [лимит_байт] [шаг_λ]");
        std::process::exit(2);
    }
    let depth: usize = a[2].parse().expect("глубина");
    let mut data = fs::read(&a[1]).expect("файл не читается");
    if a.len() > 3 {
        data.truncate(a[3].parse().expect("лимит"));
    }
    // Шаг геометрической сетки λ: мельче шаг — плотнее точки оболочки.
    let step: f64 = if a.len() > 4 { a[4].parse().expect("шаг_λ") } else { 1.05 };
    assert!(step > 1.0, "шаг сетки λ должен быть > 1");

    let mut nodes = vec![Node { n: [0, 0], child: [0, 0] }];
    let mut hist: u64 = 0;
    for &byte in &data {
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
    eprintln!("узлов {}", nodes.len());

    let c: Vec<f64> = nodes.iter().map(cost_leaf).collect();
    let mut f = vec![0.0f64; nodes.len()];
    let mut l = vec![0u64; nodes.len()];

    let mut pts: Vec<(u64, f64)> = Vec::new();
    let mut lam = 4096.0f64;
    while lam > 1e-7 {
        pts.push({
            let (cost, leaves) = sweep(&nodes, &c, lam, &mut f, &mut l);
            (leaves, cost)
        });
        lam /= step;
    }
    let (cost, leaves) = sweep(&nodes, &c, 0.0, &mut f, &mut l); // полное дерево
    pts.push((leaves, cost));
    pts.sort_by(|x, y| x.0.cmp(&y.0));
    pts.dedup();

    let nbits = (data.len() * 8) as f64;
    println!("листья            биты        бит/бит   бит/байт");
    for &(lv, cst) in &pts {
        println!("{:>10}  {:>16.3}  {:.6}  {:.4}",
                 lv, cst, cst / nbits, cst / data.len() as f64);
    }
}
