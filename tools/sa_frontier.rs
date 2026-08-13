//! Честный компаратор min_{S∈T_M} L_S(x) на SA-бэкенде — Rust-порт
//! build+frontier из `tools/sa_prod.py` / `tools/sa_prod_fast.py`.
//!
//! Зачем: после исправления класса сравнения (2026-08-10, см.
//! notes/stage5b-comparator-audit.md) честное дерево на D=48/100 МБ — это
//! ~200M узлов. В Python (семь списков int'ов, 151.7 Б/узел — замерено
//! tracemalloc) это ~30 ГБ и не влезает. Здесь те же массивы в компактных
//! типах: 42 Б/узел ⇒ ~8 ГБ, что помещается на 16-ГБ стенде.
//!
//! Вход — .npy-файлы от `sa_prod.generate` (записи `(key: u64, pos: u64,
//! label: u8)`, 17 Б, каждый файл отсортирован по key). Файлов можно передать
//! несколько: они сливаются k-way на лету, прямо в построение дерева. Это
//! снимает самую долгую фазу пайплайна — `sa_prod.merge_all` на 800M записей
//! в Python прогоняет ~2.4 млрд записей через heapq (часы) и требует ещё
//! 13.6 ГБ под промежуточный файл. Генерация чанков остаётся в Python:
//! она векторная и по памяти узким местом не была.
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
    /// `cap` — стартовая ёмкость: без неё семь Vec'ов удваиваются по ходу
    /// построения, и на пике это лишние гигабайты (перевыделение копирует
    /// массив целиком, то есть держит старый и новый одновременно).
    fn with_capacity(cap: usize) -> Tree {
        Tree {
            n0: Vec::with_capacity(cap), n1: Vec::with_capacity(cap),
            ch0: Vec::with_capacity(cap), ch1: Vec::with_capacity(cap),
            par: Vec::with_capacity(cap), dep: Vec::with_capacity(cap),
            fo: Vec::with_capacity(cap),
        }
    }
    fn len(&self) -> usize { self.n0.len() }

    /// Отдать обратно неиспользованный хвост ёмкости перед тем, как рядом
    /// встанут массивы frontier (R/leaves/k).
    fn shrink(&mut self) {
        self.n0.shrink_to_fit(); self.n1.shrink_to_fit();
        self.ch0.shrink_to_fit(); self.ch1.shrink_to_fit();
        self.par.shrink_to_fit(); self.dep.shrink_to_fit(); self.fo.shrink_to_fit();
    }

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

/// Один входной чанк: буферизованное чтение записей по возрастанию key.
struct Chunk {
    rdr: BufReader<File>,
    left: u64,
    head: Option<(u64, u64, u8)>, // (key, pos, label)
}

impl Chunk {
    fn open(f: File, offset: u64, n: u64) -> Chunk {
        let mut f = f;
        f.seek(SeekFrom::Start(offset)).expect("seek");
        let mut c = Chunk { rdr: BufReader::with_capacity(1 << 20, f), left: n, head: None };
        c.advance();
        c
    }
    fn advance(&mut self) {
        if self.left == 0 {
            self.head = None;
            return;
        }
        let mut b = [0u8; REC];
        self.rdr.read_exact(&mut b).expect("чтение записи");
        self.left -= 1;
        self.head = Some((
            u64::from_le_bytes(b[0..8].try_into().unwrap()),
            u64::from_le_bytes(b[8..16].try_into().unwrap()),
            b[16],
        ));
    }
}

/// Строит сжатое дерево за один последовательный проход по отсортированным
/// записям (LCP-стек вдоль правого края); входные чанки сливаются k-way на
/// лету. Возвращает (дерево, индекс корня): корень — это ДНО стека, а не
/// последний созданный узел (последним всегда создаётся ветвление для
/// последней группы, оно сидит глубоко).
fn build(inputs: Vec<(File, u64, u64)>, depth: usize, nodes_hint: Option<usize>) -> (Tree, u32) {
    // Узлов будет 2·(различных ключей) − 1, и доля различных падает с ростом
    // корпуса: замерено при D=48 на enwik8 — 457 911 узлов на 0.41M записей,
    // 8 943 657 на 16.8M, 28 105 213 на 83.9M, то есть рост ≈N^0.71, а
    // отношение узлы/запись 1.12 → 0.53 → 0.335. Промахнуться вверх дорого:
    // ёмкость сразу занимает память (при 800M записей «total/3» — это 267M
    // слотов ≈ 6.7 ГБ при реальных ~140M узлов), промахнуться вниз — тоже
    // (перевыделение копирует массив, держа старый и новый одновременно).
    // total/5 попадает чуть выше ожидаемого на полном корпусе; точное число
    // можно задать флагом --nodes-hint.
    let total: u64 = inputs.iter().map(|&(_, _, n)| n).sum();
    let cap = nodes_hint.unwrap_or_else(|| (total / 5).max(1024) as usize);
    let mut chunks: Vec<Chunk> = inputs.into_iter().map(|(f, off, n)| Chunk::open(f, off, n)).collect();
    // Порядок среди РАВНЫХ ключей не важен: счётчики складываются, а
    // first_occ берётся минимумом — обе операции коммутативны.
    let mut order: BinaryHeap<(std::cmp::Reverse<u64>, usize)> = BinaryHeap::new();
    for (i, c) in chunks.iter().enumerate() {
        if let Some((k, _, _)) = c.head {
            order.push((std::cmp::Reverse(k), i));
        }
    }

    let mut tr = Tree::with_capacity(cap);
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

    let mut first_group = true;
    while let Some((std::cmp::Reverse(_), ci)) = order.pop() {
        let (key, pos64, label) = chunks[ci].head.expect("голова чанка");
        let pos = pos64 as u32;
        chunks[ci].advance();
        if let Some((k2, _, _)) = chunks[ci].head {
            order.push((std::cmp::Reverse(k2), ci));
        }
        if have_group && key == cur_key {
            if label == 0 { cur_n0 += 1 } else { cur_n1 += 1 }
            if pos < cur_fo { cur_fo = pos }
            continue;
        }
        if have_group {
            debug_assert!(key > cur_key, "вход не отсортирован по key");
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

/// Ключ упорядочивания: (α, first_occ, dep, idx) по возрастанию — тот же
/// тай-брейк, что у heapq в Python-эталоне.
#[derive(Clone, Copy, PartialEq)]
struct Key { alpha: f64, fo: u32, dep: u8, idx: u32 }

impl Key {
    #[inline]
    fn lt(&self, o: &Key) -> bool {
        match self.alpha.total_cmp(&o.alpha) {
            Ordering::Less => true,
            Ordering::Greater => false,
            Ordering::Equal => (self.fo, self.dep, self.idx) < (o.fo, o.dep, o.idx),
        }
    }
}

/// Индексированная двоичная min-куча: у каждого узла НЕ БОЛЕЕ ОДНОЙ записи,
/// ключ можно менять на месте (sift), запись можно удалить по индексу узла.
///
/// Ленивая куча (запись на каждое изменение + отбраковка устаревших) здесь
/// не работает: кандидатов сразу ~2·(число терминалов) — на 10 МБ это 28M
/// записей, — и любая фиксированная граница чистки оказывается НИЖЕ числа
/// живых записей, отчего чистка запускается на каждом шаге. Замерено: 946 с
/// CPU меньше чем на 5M точек из 14M. Здесь чисток нет вовсе, а память —
/// 8 Б/узел (heap + pos) вместо 24 Б на каждую устаревшую запись.
struct IdxHeap {
    heap: Vec<u32>,
    pos: Vec<u32>, // pos[node] = место в heap, либо NONE
}

impl IdxHeap {
    fn new(n: usize) -> IdxHeap {
        IdxHeap { heap: Vec::with_capacity(n), pos: vec![NONE; n] }
    }

    #[inline]
    fn sift_up<F: Fn(u32) -> Key>(&mut self, mut i: usize, key: &F) {
        let v = self.heap[i];
        let kv = key(v);
        while i > 0 {
            let p = (i - 1) / 2;
            let hp = self.heap[p];
            if kv.lt(&key(hp)) {
                self.heap[i] = hp;
                self.pos[hp as usize] = i as u32;
                i = p;
            } else {
                break;
            }
        }
        self.heap[i] = v;
        self.pos[v as usize] = i as u32;
    }

    #[inline]
    fn sift_down<F: Fn(u32) -> Key>(&mut self, mut i: usize, key: &F) {
        let n = self.heap.len();
        let v = self.heap[i];
        let kv = key(v);
        loop {
            let l = 2 * i + 1;
            if l >= n { break; }
            let r = l + 1;
            let c = if r < n && key(self.heap[r]).lt(&key(self.heap[l])) { r } else { l };
            let hc = self.heap[c];
            if key(hc).lt(&kv) {
                self.heap[i] = hc;
                self.pos[hc as usize] = i as u32;
                i = c;
            } else {
                break;
            }
        }
        self.heap[i] = v;
        self.pos[v as usize] = i as u32;
    }

    /// Вставить узел или пересортировать уже вставленный после смены ключа.
    fn upsert<F: Fn(u32) -> Key>(&mut self, u: u32, key: &F) {
        let p = self.pos[u as usize];
        if p == NONE {
            self.heap.push(u);
            let i = self.heap.len() - 1;
            self.pos[u as usize] = i as u32;
            self.sift_up(i, key);
        } else {
            // ключ мог как вырасти, так и упасть — пробуем оба направления
            let i = p as usize;
            self.sift_up(i, key);
            let i2 = self.pos[u as usize] as usize;
            if i2 == i { self.sift_down(i, key); }
        }
    }

    fn remove<F: Fn(u32) -> Key>(&mut self, u: u32, key: &F) {
        let p = self.pos[u as usize];
        if p == NONE { return; }
        let i = p as usize;
        self.pos[u as usize] = NONE;
        let last = self.heap.pop().expect("непустая куча");
        if i < self.heap.len() {
            self.heap[i] = last;
            self.pos[last as usize] = i as u32;
            self.sift_up(i, key);
            let i2 = self.pos[last as usize] as usize;
            if i2 == i { self.sift_down(i, key); }
        }
    }

    fn pop_min<F: Fn(u32) -> Key>(&mut self, key: &F) -> Option<u32> {
        if self.heap.is_empty() { return None; }
        let top = self.heap[0];
        self.remove(top, key);
        Some(top)
    }

    fn len(&self) -> usize { self.heap.len() }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("использование: sa_frontier <chunk1.npy> [chunk2.npy ...] [--depth D]");
        eprintln!("  [--budgets \"M1,M2,...\"] [--points N] [--nodes-hint N]");
        eprintln!("несколько файлов сливаются k-way на лету (каждый должен быть");
        eprintln!("отсортирован по key) — merge_all в Python не нужен");
        process::exit(2);
    }
    let mut depth = 48usize;
    let mut budgets: Vec<u64> = Vec::new();
    let mut npoints = 0usize;
    let mut nodes_hint: Option<usize> = None;
    // позиционные аргументы до первого флага — входные .npy
    let mut inputs: Vec<String> = Vec::new();
    let mut i = 1;
    while i < args.len() && !args[i].starts_with("--") {
        inputs.push(args[i].clone());
        i += 1;
    }
    if inputs.is_empty() {
        eprintln!("не задан ни один входной .npy");
        process::exit(2);
    }
    while i < args.len() {
        let need = |i: usize| -> String {
            if i + 1 >= args.len() { eprintln!("{}: нужен аргумент", args[i]); process::exit(2); }
            args[i + 1].clone()
        };
        match args[i].as_str() {
            "--depth" => { depth = need(i).parse().expect("--depth"); i += 2; }
            "--points" => { npoints = need(i).parse().expect("--points"); i += 2; }
            "--nodes-hint" => { nodes_hint = Some(need(i).parse().expect("--nodes-hint")); i += 2; }
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
    let mut opened: Vec<(File, u64, u64)> = Vec::with_capacity(inputs.len());
    let mut nrec: u64 = 0;
    for p in &inputs {
        let (f, offset, n) = npy_open(p);
        nrec += n;
        opened.push((f, offset, n));
    }
    eprintln!("[{:6.1}s] входов {}, записей {} ({:.1}M)",
              t0.elapsed().as_secs_f64(), opened.len(), nrec, nrec as f64 / 1e6);

    let (mut tr, root_idx) = build(opened, depth, nodes_hint);
    tr.shrink(); // вернуть хвост ёмкости до выделения R/leaves/k
    let tr = tr;
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
    // α кешируется в массиве и пересчитывается ТОЛЬКО когда у узламенялись
    // r/leaves. Считать его внутри сравнения нельзя: cost_leaf зовёт log2()
    // дважды, а просеивание кучи делает десятки сравнений на операцию —
    // замерено, что так frontier не доходил и до 1M точек из 14M за 30+ с.
    let mut alpha = vec![f64::INFINITY; n];
    let recalc = |alpha: &mut Vec<f64>, r: &Vec<f64>, leaves: &Vec<u64>, u: usize| {
        alpha[u] = if leaves[u] > 1 {
            (tr.cost_leaf(u) - r[u]) / (leaves[u] - 1) as f64
        } else {
            f64::INFINITY
        };
    };
    for u in 0..n {
        recalc(&mut alpha, &r, &leaves, u);
    }
    macro_rules! keyf {
        ($alpha:expr) => {
            |u: u32| -> Key {
                let ui = u as usize;
                Key { alpha: $alpha[ui], fo: tr.fo[ui], dep: tr.dep[ui], idx: u }
            }
        };
    }
    let mut heap = IdxHeap::new(n);
    {
        let kf = keyf!(alpha);
        for u in 0..n {
            if leaves[u] > 1 {
                heap.upsert(u as u32, &kf);
            }
        }
    }
    eprintln!("[{:6.1}s] кандидатов в куче: {}", t0.elapsed().as_secs_f64(), heap.len());

    // Для каждого бюджета — стоимость первой точки с листьями ≤ M (точки идут
    // по убыванию листьев и возрастанию стоимости, поэтому первая и есть
    // лучшая). Все точки не храним: их ~столько же, сколько ветвлений.
    let mut best: Vec<f64> = vec![f64::INFINITY; budgets.len()];
    let mut points_shown = 0usize;
    let mut npts: u64 = 1;
    for (bi, &m) in budgets.iter().enumerate() {
        if leaves[root] <= m && !best[bi].is_finite() { best[bi] = r[root]; }
    }
    if npoints > 0 {
        println!("первые {} точек оболочки (листья, биты):", npoints);
        println!("  {:>12}  {:>18.3}", leaves[root], r[root]);
        points_shown = 1;
    }

    let mut stack: Vec<u32> = Vec::new();
    loop {
        let umin = { let kf = keyf!(alpha); match heap.pop_min(&kf) { Some(u) => u, None => break } };
        let u = umin as usize;
        debug_assert!(leaves[u] > 1, "в куче не должно быть узлов с leaves<=1");

        // отщипываем u: поддерево выбывает, u становится листом (узел
        // представляет ВЕРХ сжатого ребра, поэтому ровно 1, без k)
        stack.push(umin);
        while let Some(w) = stack.pop() {
            let wi = w as usize;
            if w != umin {
                // потомки выбывают из рассмотрения — убираем их из кучи,
                // иначе их ключ считался бы от leaves == 0
                { let kf = keyf!(alpha); heap.remove(w, &kf); }
                leaves[wi] = 0;
                alpha[wi] = f64::INFINITY;
            }
            if tr.ch0[wi] != NONE { stack.push(tr.ch0[wi]); stack.push(tr.ch1[wi]); }
        }
        r[u] = tr.cost_leaf(u);
        leaves[u] = 1;
        alpha[u] = f64::INFINITY;

        // пересчёт предков до корня
        let mut v = tr.par[u];
        while v != NONE {
            let vi = v as usize;
            let (a, b) = (tr.ch0[vi] as usize, tr.ch1[vi] as usize);
            r[vi] = r[a] + r[b];
            leaves[vi] = k[vi] as u64 + leaves[a] + leaves[b];
            recalc(&mut alpha, &r, &leaves, vi);
            if leaves[vi] <= 1 {
                { let kf = keyf!(alpha); heap.remove(v, &kf); }
                break;
            }
            { let kf = keyf!(alpha); heap.upsert(v, &kf); }
            v = tr.par[vi];
        }
        npts += 1;
        for (bi, &m) in budgets.iter().enumerate() {
            if leaves[root] <= m && !best[bi].is_finite() { best[bi] = r[root]; }
        }
        if npoints > 0 && points_shown < npoints {
            println!("  {:>12}  {:>18.3}", leaves[root], r[root]);
            points_shown += 1;
        }
        if leaves[root] == 1 { break; }
        if npts % 1_000_000 == 0 {
            eprintln!("[{:6.1}s] точек {}, листьев {}, куча {}",
                      t0.elapsed().as_secs_f64(), npts, leaves[root], heap.len());
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
