//! Честный компаратор min_{S∈T_M} L_S(x) на SA-бэкенде — Rust-порт
//! build+frontier из `tools/sa_prod.py` / `tools/sa_prod_fast.py`.
//!
//! Зачем: после исправления класса сравнения (2026-08-10, см.
//! notes/stage5b-comparator-audit.md) честное дерево на D=48/100 МБ — это
//! ~200M узлов. В Python (семь списков int'ов, 151.7 Б/узел — замерено
//! tracemalloc) это ~30 ГБ и не влезает. Здесь те же массивы в компактных
//! типах: 42 Б/узел ⇒ ~8 ГБ, что помещается на 16-ГБ стенде.
//!
//! Вход — отсортированный .npy от `sa_prod.generate` + `sa_prod.merge_all`
//! (записи `(key: u64, pos: u64, label: u8)`, 17 Б, упорядочены по key).
//! Генерация и внешняя сортировка остаются в Python — они не были узким
//! местом по памяти и уже проверены.
//!
//! **Построение за один последовательный проход.** Терминалы честного дерева
//! — это ровно РАЗЛИЧНЫЕ ключи (каждая группа равных ключей = один терминал
//! на глубине depth), а ветвления сидят на LCP соседних различных ключей,
//! то есть дерево — классический Patricia-trie отсортированных ключей.
//! Поэтому достаточно LCP-стека вдоль правого края: ни бинарного поиска, ни
//! mmap, ни массива префиксных сумм (в Python он занимал ещё 6.4 ГБ на диске).
//! Счётчики и first_occ накапливаются по ходу группы.
//!
//! Семантика pruning идентична Python-эталону (`comparator_sa_ref.py`):
//! leaves(u) = k(u) + база(u), где k(u) = dep(u) − dep(par(u)) − 1 — длина
//! сжатого ребра НАД u (для корня k = dep(корня)); узел представляет ВЕРХ
//! своего сжатого ребра, поэтому после отщипывания leaves(u) = 1.
//!
//! Сборка: rustc -O --edition 2021 -o bin/sa_frontier.exe tools/sa_frontier.rs
//! Запуск: sa_frontier <merged.npy> --depth D [--budgets "M1,M2"] [--points N]

use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::env;
use std::fs::File;
use std::io::{BufReader, Read, Seek, SeekFrom};
use std::process;

const REC: usize = 17; // (key u64, pos u64, label u8), packed
const NONE: u32 = u32::MAX;

// ---------------------------------------------------------------------------
// Чтение .npy
// ---------------------------------------------------------------------------

/// Возвращает (смещение данных, число записей). Проверяет, что dtype — тот
/// самый упакованный кортеж из sa_prod.DTYPE.
fn npy_open(path: &str) -> (File, u64, u64) {
    let mut f = match File::open(path) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("не читается {}: {}", path, e);
            process::exit(1);
        }
    };
    let mut magic = [0u8; 10];
    if f.read_exact(&mut magic).is_err() || &magic[..6] != b"\x93NUMPY" {
        eprintln!("{}: не .npy", path);
        process::exit(2);
    }
    // v1.0: 2 байта длины заголовка; v2.0+: 4 байта
    let (hlen, hstart) = if magic[6] == 1 {
        (u16::from_le_bytes([magic[8], magic[9]]) as u64, 10u64)
    } else {
        let mut ext = [0u8; 2];
        f.read_exact(&mut ext).expect("npy v2 header");
        (
            u32::from_le_bytes([magic[8], magic[9], ext[0], ext[1]]) as u64,
            12u64,
        )
    };
    let mut header = vec![0u8; hlen as usize];
    f.read_exact(&mut header).expect("npy header");
    let header = String::from_utf8_lossy(&header).to_string();
    if !header.contains("'key'") || !header.contains("'pos'") || !header.contains("'label'") {
        eprintln!("{}: неожиданный dtype: {}", path, header.trim());
        process::exit(2);
    }
    if header.contains("'fortran_order': True") {
        eprintln!("{}: fortran_order не поддержан", path);
        process::exit(2);
    }
    let offset = hstart + hlen;
    let total = f.metadata().expect("metadata").len();
    let n = (total - offset) / REC as u64;
    if (total - offset) % REC as u64 != 0 {
        eprintln!("{}: размер данных не кратен {} Б", path, REC);
        process::exit(2);
    }
    (f, offset, n)
}

// ---------------------------------------------------------------------------
// Дерево
// ---------------------------------------------------------------------------

struct Tree {
    n0: Vec<u32>,
    n1: Vec<u32>,
    ch0: Vec<u32>,
    ch1: Vec<u32>,
    par: Vec<u32>,
    dep: Vec<u8>,
    fo: Vec<u32>,
}

impl Tree {
    fn new() -> Tree {
        Tree { n0: Vec::new(), n1: Vec::new(), ch0: Vec::new(), ch1: Vec::new(),
               par: Vec::new(), dep: Vec::new(), fo: Vec::new() }
    }
    fn len(&self) -> usize { self.n0.len() }

    fn push(&mut self, dep: u8, n0: u32, n1: u32, fo: u32, ch0: u32, ch1: u32) -> u32 {
        let u = self.n0.len() as u32;
        self.n0.push(n0);
        self.n1.push(n1);
        self.ch0.push(ch0);
        self.ch1.push(ch1);
        self.par.push(NONE);
        self.dep.push(dep);
        self.fo.push(fo);
        u
    }

    /// c(u) = n_u · H(эмпирическое распределение следующего бита), биты.
    fn cost_leaf(&self, u: usize) -> f64 {
        let a = self.n0[u] as f64;
        let b = self.n1[u] as f64;
        let n = a + b;
        if n <= 0.0 { return 0.0; }
        let p = a / n;
        if p <= 0.0 || p >= 1.0 { return 0.0; }
        n * (-p * p.log2() - (1.0 - p) * (1.0 - p).log2())
    }

    /// Длина сжатого ребра НАД узлом: k(u) = dep(u) − dep(par(u)) − 1;
    /// для корня — dep(корня) (в Python: build(0,N,0) даёт k = dd − 0).
    fn k(&self, u: usize) -> u64 {
        let p = self.par[u];
        if p == NONE { self.dep[u] as u64 } else { (self.dep[u] - self.dep[p as usize] - 1) as u64 }
    }
}

/// Глубина расхождения двух ключей в порядке расщепления (0 = самый свежий
/// бит контекста). Совпадает с `advance`/`bit_at` в sa_prod*: бит глубины d
/// — это (key >> (depth−1−d)) & 1.
#[inline]
fn lcp_depth(a: u64, b: u64, depth: usize) -> usize {
    let diff = a ^ b;
    if diff == 0 { depth } else { depth - 1 - (63 - diff.leading_zeros()) as usize }
}

/// Строит сжатое дерево за один последовательный проход по отсортированным
/// записям (LCP-стек вдоль правого края). Возвращает (дерево, индекс корня):
/// корень — это ДНО стека, а не последний созданный узел (последним всегда
/// создаётся ветвление для последней группы, оно сидит глубоко).
fn build(mut f: File, offset: u64, n: u64, depth: usize) -> (Tree, u32) {
    f.seek(SeekFrom::Start(offset)).expect("seek");
    let mut rdr = BufReader::with_capacity(1 << 22, f);

    let mut tr = Tree::new();
    let mut stack: Vec<u32> = Vec::with_capacity(depth + 2);

    // текущая группа равных ключей = будущий терминал
    let mut cur_key: u64 = 0;
    let mut cur_n0: u32 = 0;
    let mut cur_n1: u32 = 0;
    let mut cur_fo: u32 = u32::MAX;
    let mut have_group = false;
    let mut prev_key: u64 = 0;

    // Замыкание не годится (нужен &mut tr и &mut stack одновременно), поэтому
    // терминал закрывается инлайн-макросом-подобным блоком ниже.
    let close_group = |tr: &mut Tree, stack: &mut Vec<u32>,
                           key: u64, n0: u32, n1: u32, fo: u32, prev: u64, first: bool| {
        let t = tr.push(depth as u8, n0, n1, fo, NONE, NONE);
        if first {
            stack.push(t);
            return;
        }
        let l = lcp_depth(prev, key, depth);
        // отщипываем всё, что глубже точки ветвления: последний снятый —
        // корень уже завершённого левого поддерева
        let mut left = NONE;
        while let Some(&top) = stack.last() {
            if tr.dep[top as usize] as usize > l {
                stack.pop();
                left = top;
            } else {
                break;
            }
        }
        debug_assert!(left != NONE, "LCP-стек: нечего вешать слева");
        debug_assert!(
            stack.last().map_or(true, |&t| (tr.dep[t as usize] as usize) < l),
            "ветвление на глубине {} уже существует — ключи не отсортированы?", l
        );
        // Уцелевшие на стеке — предки нового терминала; их поддеревья
        // расширились на него, поэтому счётчики и first_occ надо дополнить.
        // (Само ветвление b ниже получает счётчики сразу и в этот цикл не
        // входит, иначе терминал был бы учтён дважды.)
        for &anc in stack.iter() {
            let a = anc as usize;
            tr.n0[a] += n0;
            tr.n1[a] += n1;
            if fo < tr.fo[a] { tr.fo[a] = fo; }
        }
        let n0b = tr.n0[left as usize] + n0;
        let n1b = tr.n1[left as usize] + n1;
        let fob = tr.fo[left as usize].min(fo);
        // Новое ветвление ВСТАЁТ НА МЕСТО left у её прежнего родителя —
        // без этого left оказывается ребёнком двух узлов сразу, а её
        // поддерево отваливается от дерева (получался лес, а не дерево).
        let old_par = tr.par[left as usize];
        let b = tr.push(l as u8, n0b, n1b, fob, left, t);
        tr.par[left as usize] = b;
        tr.par[t as usize] = b;
        if old_par != NONE {
            let p = old_par as usize;
            if tr.ch1[p] == left {
                tr.ch1[p] = b;
            } else {
                debug_assert_eq!(tr.ch0[p], left, "left не ребёнок своего родителя");
                tr.ch0[p] = b;
            }
            tr.par[b as usize] = old_par;
        }
        stack.push(b);
        stack.push(t);
    };

    let block = 1_000_000usize;
    let mut buf = vec![0u8; REC * block];
    let mut left = n;
    let mut first_group = true;
    while left > 0 {
        let take = block.min(left as usize);
        let bytes = REC * take;
        rdr.read_exact(&mut buf[..bytes]).expect("чтение записей");
        for i in 0..take {
            let o = i * REC;
            let key = u64::from_le_bytes(buf[o..o + 8].try_into().unwrap());
            let pos = u64::from_le_bytes(buf[o + 8..o + 16].try_into().unwrap()) as u32;
            let label = buf[o + 16];
            if have_group && key == cur_key {
                if label == 0 { cur_n0 += 1 } else { cur_n1 += 1 }
                if pos < cur_fo { cur_fo = pos }
                continue;
            }
            if have_group {
                close_group(&mut tr, &mut stack, cur_key, cur_n0, cur_n1, cur_fo, prev_key, first_group);
                first_group = false;
                prev_key = cur_key;
            }
            cur_key = key;
            cur_n0 = if label == 0 { 1 } else { 0 };
            cur_n1 = if label == 0 { 0 } else { 1 };
            cur_fo = pos;
            have_group = true;
        }
        left -= take as u64;
    }
    if have_group {
        close_group(&mut tr, &mut stack, cur_key, cur_n0, cur_n1, cur_fo, prev_key, first_group);
    }
    if stack.is_empty() {
        eprintln!("пустой вход: ни одной записи");
        process::exit(2);
    }
    let root = stack[0];
    (tr, root)
}

// ---------------------------------------------------------------------------
// Weakest link
// ---------------------------------------------------------------------------

/// Запись кучи. BinaryHeap — max-heap, поэтому сравнение инвертировано:
/// порядок (α, first_occ, dep, idx) по возрастанию, как heapq в Python.
#[derive(Clone, Copy)]
struct Entry { alpha: f64, fo: u32, dep: u8, idx: u32 }

impl PartialEq for Entry {
    fn eq(&self, o: &Self) -> bool { self.cmp(o) == Ordering::Equal }
}
impl Eq for Entry {}
impl Ord for Entry {
    fn cmp(&self, o: &Self) -> Ordering {
        o.alpha
            .total_cmp(&self.alpha)
            .then_with(|| o.fo.cmp(&self.fo))
            .then_with(|| o.dep.cmp(&self.dep))
            .then_with(|| o.idx.cmp(&self.idx))
    }
}
impl PartialOrd for Entry {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> { Some(self.cmp(o)) }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("использование: sa_frontier <merged.npy> [--depth D]");
        eprintln!("  [--budgets \"M1,M2,...\"] [--points N] [--heap-cap N]");
        process::exit(2);
    }
    let mut depth = 48usize;
    let mut budgets: Vec<u64> = Vec::new();
    let mut npoints = 0usize;
    let mut heap_cap = 16_000_000usize;
    let mut i = 2;
    while i < args.len() {
        let need = |i: usize| -> String {
            if i + 1 >= args.len() { eprintln!("{}: нужен аргумент", args[i]); process::exit(2); }
            args[i + 1].clone()
        };
        match args[i].as_str() {
            "--depth" => { depth = need(i).parse().expect("--depth"); i += 2; }
            "--points" => { npoints = need(i).parse().expect("--points"); i += 2; }
            "--heap-cap" => { heap_cap = need(i).parse().expect("--heap-cap"); i += 2; }
            "--budgets" => {
                budgets = need(i).split(',').filter(|s| !s.is_empty())
                    .map(|s| s.parse().expect("--budgets")).collect();
                i += 2;
            }
            other => { eprintln!("неизвестный аргумент: {}", other); process::exit(2); }
        }
    }
    if depth == 0 || depth > 63 {
        eprintln!("--depth должен быть в [1, 63]");
        process::exit(2);
    }

    let t0 = std::time::Instant::now();
    let (f, offset, nrec) = npy_open(&args[1]);
    eprintln!("[{:6.1}s] записей {} ({:.1}M)", t0.elapsed().as_secs_f64(), nrec, nrec as f64 / 1e6);

    let (tr, root_idx) = build(f, offset, nrec, depth);
    let n = tr.len();
    let internal = tr.ch0.iter().filter(|&&c| c != NONE).count();
    eprintln!("[{:6.1}s] дерево: {} узлов, {} внутренних", t0.elapsed().as_secs_f64(), n, internal);

    // --- инициализация T_max ---
    // Порядок по индексу НЕ годится: при вставке ветвления над уже связанным
    // узлом (см. close_group) у родителя появляется ребёнок с бо́льшим
    // индексом. Идём пост-обходом от корня; глубина дерева ≤ depth+1, потому
    // что вдоль любого пути глубина строго растёт, — стек остаётся крошечным.
    let mut r = vec![0.0f64; n];
    let mut leaves = vec![0u64; n];
    let k: Vec<u8> = (0..n).map(|u| tr.k(u) as u8).collect();
    let root = root_idx as usize;
    {
        let mut st: Vec<(u32, u8)> = Vec::with_capacity(3 * (depth + 2));
        st.push((root_idx, 0));
        while let Some((u, phase)) = st.pop() {
            let ui = u as usize;
            if tr.ch0[ui] == NONE {
                r[ui] = tr.cost_leaf(ui);
                leaves[ui] = k[ui] as u64 + 1;
            } else if phase == 0 {
                st.push((u, 1));
                st.push((tr.ch0[ui], 0));
                st.push((tr.ch1[ui], 0));
            } else {
                let (a, b) = (tr.ch0[ui] as usize, tr.ch1[ui] as usize);
                r[ui] = r[a] + r[b];
                leaves[ui] = k[ui] as u64 + leaves[a] + leaves[b];
            }
        }
    }
    debug_assert_eq!(tr.par[root], NONE, "у корня не должно быть родителя");
    let full_leaves = leaves[root];
    let full_cost = r[root];
    eprintln!("[{:6.1}s] T_max: {} листьев, {:.3} бит",
              t0.elapsed().as_secs_f64(), full_leaves, full_cost);

    // --- отщипывание слабейшего звена ---
    let alpha_of = |u: usize, r: &Vec<f64>, leaves: &Vec<u64>, tr: &Tree| -> f64 {
        (tr.cost_leaf(u) - r[u]) / (leaves[u] - 1) as f64
    };
    let mut heap: BinaryHeap<Entry> = BinaryHeap::new();
    for u in 0..n {
        if leaves[u] > 1 {
            heap.push(Entry { alpha: alpha_of(u, &r, &leaves, &tr), fo: tr.fo[u], dep: tr.dep[u], idx: u as u32 });
        }
    }

    // Для каждого бюджета — стоимость первой точки с листьями ≤ M (точки идут
    // по убыванию листьев и возрастанию стоимости, поэтому первая и есть
    // лучшая). Все точки не храним: их ~столько же, сколько ветвлений.
    let mut best: Vec<f64> = vec![f64::INFINITY; budgets.len()];
    let mut points_shown = 0usize;
    let mut npts: u64 = 1;
    let update = |leaves0: u64, cost0: f64, best: &mut Vec<f64>| {
        for (bi, &m) in budgets.iter().enumerate() {
            if leaves0 <= m && !best[bi].is_finite() {
                best[bi] = cost0;
            }
        }
    };
    update(leaves[root], r[root], &mut best);
    if npoints > 0 {
        println!("первые {} точек оболочки (листья, биты):", npoints);
        println!("  {:>12}  {:>18.3}", leaves[root], r[root]);
        points_shown = 1;
    }

    let mut stack: Vec<u32> = Vec::new();
    while let Some(e) = heap.pop() {
        let u = e.idx as usize;
        if leaves[u] <= 1 { continue; }
        if alpha_of(u, &r, &leaves, &tr) != e.alpha { continue; } // устаревшая запись
        // отщипываем u: поддерево выбывает, u становится листом (узел
        // представляет ВЕРХ сжатого ребра, поэтому ровно 1, без k)
        stack.push(e.idx);
        while let Some(w) = stack.pop() {
            let w = w as usize;
            leaves[w] = 0;
            if tr.ch0[w] != NONE { stack.push(tr.ch0[w]); stack.push(tr.ch1[w]); }
        }
        r[u] = tr.cost_leaf(u);
        leaves[u] = 1;
        // пересчёт предков до корня
        let mut v = tr.par[u];
        while v != NONE {
            let vi = v as usize;
            let (a, b) = (tr.ch0[vi] as usize, tr.ch1[vi] as usize);
            r[vi] = r[a] + r[b];
            leaves[vi] = k[vi] as u64 + leaves[a] + leaves[b];
            if leaves[vi] == 1 { break; }
            heap.push(Entry { alpha: alpha_of(vi, &r, &leaves, &tr), fo: tr.fo[vi], dep: tr.dep[vi], idx: v });
            v = tr.par[vi];
        }
        npts += 1;
        update(leaves[root], r[root], &mut best);
        if npoints > 0 && points_shown < npoints {
            println!("  {:>12}  {:>18.3}", leaves[root], r[root]);
            points_shown += 1;
        }
        if leaves[root] == 1 { break; }
        if heap.len() > heap_cap {
            heap.clear();
            for u2 in 0..n {
                if leaves[u2] > 1 {
                    heap.push(Entry { alpha: alpha_of(u2, &r, &leaves, &tr), fo: tr.fo[u2], dep: tr.dep[u2], idx: u2 as u32 });
                }
            }
        }
    }
    eprintln!("[{:6.1}s] frontier: {} точек", t0.elapsed().as_secs_f64(), npts);

    // --- вывод ---
    // bpc = бит/БАЙТ (как в ядре и src/comparator.rs); записей = бит корпуса.
    let nbits = nrec as f64;
    let nbytes = nrec as f64 / 8.0;
    println!();
    println!("узлов в сжатом дереве   {}", n);
    println!("точек на оболочке       {}", npts);
    println!("листья (полное дерево)  {}", full_leaves);
    println!("стоимость полного дерева {:.3} бит ({:.6} бит/бит, {:.4} bpc)",
             full_cost, full_cost / nbits, full_cost / nbytes);
    if !budgets.is_empty() {
        println!();
        println!("бюджет M (листья)  стоимость (бит)   бит/бит      bpc");
        for (bi, &m) in budgets.iter().enumerate() {
            if best[bi].is_finite() {
                println!("{:>16}  {:>16.3}  {:>8.4}  {:>8.4}",
                         m, best[bi], best[bi] / nbits, best[bi] / nbytes);
            } else {
                println!("{:>16}  — дерево с ≤M листьев не встретилось", m);
            }
        }
    }
}
