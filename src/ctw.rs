//! budget-CTW: Context Tree Weighting с жёстким бюджетом узлов и вытеснением.
//!
//! Один файл содержит и полный CTW, и бюджетный: без `--budget` арена не
//! ограничена и вытеснение не срабатывает ни разу, то есть базлайн «полный CTW»
//! проходит по тому же коду и той же арифметике, что и бюджетный вариант.
//! Сравнение мерит потерю от вытеснения, а не разницу двух реализаций.
//!
//! Плавающей точки нет нигде, включая построение таблиц: f64 не встречается в файле.
//! Обоснование решений — notes/design-spec.md.
//!
//! Сборка:  rustc -O --edition 2021 -o bin/ctw.exe src/ctw.rs
//! Запуск:  ctw <файл> [--depth D] [--limit N] [--budget УЗЛОВ]
//!               [--victim lfu|random] [--birth cold|spacesaving|parent]
//!               [--sample S] [--lazy K] [--gamma G] [--beta-reset] [--seed S]

use std::env;
use std::fs;
use std::process;

// ---------------------------------------------------------------------------
// Формат с фиксированной точкой
// ---------------------------------------------------------------------------

/// Дробных битов в логарифмическом домене. Все величины log₂ — i64 в Q24.
const Q: u32 = 24;
const ONE: i64 = 1 << Q;

/// Табличных битов: таблицы по 2^12 отсчётов + линейная интерполяция.
/// Погрешность обеих таблиц ≈ 2⁻²⁶ (оценка — см. design-spec §2).
const TB: u32 = 12;
const TN: usize = 1 << TB;

/// За этим порогом log₂(1 + 2^−d) < 2⁻²⁵ и в Q24 неотличим от нуля.
const SATURATE: i64 = 25 << Q;

// ---------------------------------------------------------------------------
// Целочисленное построение таблиц
// ---------------------------------------------------------------------------

/// Целочисленный квадратный корень (Ньютон). Нужен для констант 2^(−2^−i).
fn isqrt(n: u128) -> u128 {
    if n == 0 {
        return 0;
    }
    let bits = 128 - n.leading_zeros();
    let mut x = 1u128 << ((bits + 1) / 2);
    loop {
        let y = (x + n / x) >> 1;
        if y >= x {
            return x;
        }
        x = y;
    }
}

/// log₂(m) для m ∈ [1, 2), заданного в Q32, результат в Q24.
///
/// Классический алгоритм последовательного возведения в квадрат: на каждом шаге
/// m² либо переваливает за 2 (тогда очередной бит результата — единица, и m²
/// делится пополам), либо нет. Q итераций дают Q дробных битов. Только целые.
fn log2_mantissa(mut m: u64) -> i64 {
    let mut res: i64 = 0;
    for _ in 0..Q {
        let sq = ((m as u128) * (m as u128)) >> 32; // Q32, в [2³², 2³⁴)
        let mut m2 = sq as u64;
        res <<= 1;
        if m2 >= 1u64 << 33 {
            m2 >>= 1;
            res |= 1;
        }
        m = m2;
    }
    res
}

/// Таблицы логарифма и экспоненты. Строятся один раз при старте, целочисленно.
struct Tables {
    /// log₂(1 + j/2^TB) в Q24, j = 0..=TN.
    log1p: Vec<i64>,
    /// 2^(−j/2^TB) в Q32, j = 0..=TN. Убывает от 2³² до 2³¹.
    exp2neg: Vec<u64>,
}

impl Tables {
    fn new() -> Tables {
        let mut log1p = Vec::with_capacity(TN + 1);
        for j in 0..=TN {
            let m = (1u64 << 32) + ((j as u64) << (32 - TB)); // 1 + j/2^TB в Q32
            log1p.push(if j == TN { ONE } else { log2_mantissa(m) });
        }

        // Константы s[i] = 2^(−2^−i) в Q32, i = 1..=TB, через повторный корень:
        // s[1] = √(2⁻¹), s[i+1] = √(s[i]).
        let mut s = vec![0u64; TB as usize + 1];
        let mut cur = 1u64 << 31; // 2⁻¹ в Q32
        for i in 1..=TB as usize {
            cur = isqrt((cur as u128) << 32) as u64;
            s[i] = cur;
        }

        let mut exp2neg = Vec::with_capacity(TN + 1);
        for j in 0..=TN {
            if j == TN {
                // φ = 1 не раскладывается по TB битам — задаём явно: 2⁻¹.
                // Без этого отсчёта таблица теряет монотонность на последнем
                // интервале, и вычитание a−b в exp2_neg уходит в переполнение.
                exp2neg.push(1u64 << 31);
                continue;
            }
            // φ = j/2^TB = Σ b_i·2^−i  ⇒  2^−φ = Π s[i]^{b_i}
            let mut acc = 1u128 << 32;
            for i in 1..=TB as usize {
                if (j >> (TB as usize - i)) & 1 == 1 {
                    acc = (acc * s[i] as u128) >> 32;
                }
            }
            exp2neg.push(acc as u64);
        }

        Tables { log1p, exp2neg }
    }

    /// log₂(1 + x) для x ∈ [0, 1), заданного в Q32. Результат в Q24.
    fn log2_1p(&self, x: u64) -> i64 {
        debug_assert!(x < (1u64 << 32), "log2_1p вне области: x={:#x}", x);
        let idx = (x >> (32 - TB)) as usize;
        let frac = (x & ((1u64 << (32 - TB)) - 1)) as i64;
        let a = self.log1p[idx];
        let b = self.log1p[idx + 1];
        a + (((b - a) * frac) >> (32 - TB))
    }

    /// 2^(−φ) для φ ∈ [0, 1) в Q24. Результат в Q32.
    fn exp2_neg(&self, phi: i64) -> u64 {
        let idx = (phi >> (Q - TB)) as usize;
        let frac = (phi & ((1 << (Q - TB)) - 1)) as u64;
        let a = self.exp2neg[idx];
        let b = self.exp2neg[idx + 1]; // a ≥ b: функция убывает
        a - (((a - b) * frac) >> (Q - TB))
    }

    /// log₂(v) для целого v ≥ 1. Результат в Q24.
    fn log2_int(&self, v: u64) -> i64 {
        debug_assert!(v >= 1, "log2_int(0)");
        let k = 63 - v.leading_zeros(); // позиция старшего бита
        let m = if k <= 32 { v << (32 - k) } else { v >> (k - 32) };
        ((k as i64) << Q) + self.log2_1p(m - (1u64 << 32))
    }

    /// log₂(1 + 2^y) — якобиан-логарифм, y в Q24, результат в Q24.
    ///
    /// Тождество: log₂(1 + 2^y) = max(y, 0) + log₂(1 + 2^−|y|). Второе слагаемое
    /// раскладывается как 2^−|y| = 2^−k · 2^−φ, где k = ⌊|y|⌋, φ — дробная часть;
    /// поэтому хватает двух таблиц вместо отдельной таблицы якобиана.
    fn log2_1p_exp2(&self, y: i64) -> i64 {
        let base = if y > 0 { y } else { 0 };
        let d = if y < 0 { -y } else { y };
        if d >= SATURATE {
            return base; // добавка ниже разрешения Q24
        }
        let k = (d >> Q) as u32;
        let phi = d & (ONE - 1);
        let e = self.exp2_neg(phi); // Q32, в [2³¹, 2³²]
        if k == 0 && e >= 1u64 << 32 {
            return base + ONE; // ровно 2⁰: log₂(1+1) = 1
        }
        base + self.log2_1p(e >> k)
    }
}

// ---------------------------------------------------------------------------
// Политики бюджетного слоя
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq)]
enum Victim {
    /// Выборочный LFU: сэмплируем S листьев, вытесняем наименее посещаемый.
    Lfu,
    /// Space-Saving на отдельном приоритете: вытесняем минимальный, новый узел
    /// получает c_min + 1. Счётчики KT при этом остаются холодными.
    ///
    /// Разделение ролей здесь и есть суть: счётчик узла в CTW обслуживает две
    /// разные задачи — «как часто встречался контекст» (структура, ею и ведает
    /// Space-Saving) и «каково распределение следующего символа» (параметр,
    /// им ведает KT). Наследование массы полезно первой и портит вторую.
    Ss,
    /// Случайный лист — слабый базлайн для сравнения.
    Random,
}

#[derive(Clone, Copy, PartialEq)]
enum Birth {
    /// E1: новый узел стартует с нулей.
    Cold,
    /// Приём Space-Saving: новый узел наследует массу вытесненного (c_min),
    /// распределённую в пропорции родителя. Именно это наследование даёт
    /// алгоритму его гарантию ошибки счётчика (design-spec §4).
    SpaceSaving,
    /// E2: тёплый старт от родителя со скидкой γ.
    Parent,
}

const NONE: u32 = u32::MAX;

// ---------------------------------------------------------------------------
// Узел и дерево
// ---------------------------------------------------------------------------

/// 32 байта, два узла на строку кэша. Индексы вместо указателей (design-spec §3).
/// `parent` нужен, чтобы отцепить вытесняемый лист; номер слота выводится
/// сравнением, отдельного поля не требует. `leaf_pos` — позиция в массиве
/// листьев, даёт удаление за O(1).
#[derive(Clone, Copy)]
struct Node {
    n: [u32; 2],
    child: [u32; 2],
    parent: u32,
    leaf_pos: u32,
    /// Приоритет Space-Saving: частота контекста, отдельная от счётчиков KT.
    /// Присутствует при любой политике, чтобы размер узла не зависел от неё и
    /// сравнение политик шло при равном числе узлов и равной памяти.
    prio: u32,
    logbeta: i64,
}

impl Node {
    /// Свежий узел: log β = 0, поскольку у пустого узла P_e = 1 и у обоих
    /// (отсутствующих) детей P_w = 1, то есть β = 1.
    fn fresh(parent: u32, n0: u32, n1: u32, prio: u32) -> Node {
        Node { n: [n0, n1], child: [0, 0], parent, leaf_pos: NONE, prio, logbeta: 0 }
    }
}

struct Stats {
    evictions: u64,
    creations: u64,
    /// Масса счётчиков, ушедшая вместе с вытесненными узлами.
    evicted_mass: u64,
    /// Символы, где спуск оборвался из-за бюджета / из-за ленивого создания.
    trunc_budget: u64,
    trunc_lazy: u64,
    peak_nodes: usize,
}

struct Ctw {
    nodes: Vec<Node>,
    free: Vec<u32>,
    /// Индексы узлов без детей — единственные кандидаты на вытеснение.
    leaves: Vec<u32>,
    depth: usize,
    cap: usize,
    hist: u64,
    /// Накопленная кодовая длина в битах, Q24.
    codelen: i64,
    victim: Victim,
    birth: Birth,
    sample: usize,
    lazy_k: u64,
    gamma: u32,
    beta_reset: bool,
    verify_sum: bool,
    /// Приоритет последнего вытесненного узла — c_min для политики Space-Saving.
    last_evicted_prio: u32,
    rng: u64,
    stats: Stats,
    tab: Tables,
}

impl Ctw {
    fn new(depth: usize, cap: usize) -> Ctw {
        assert!(depth <= 63, "глубина ограничена разрядностью истории (u64)");
        assert!(cap >= depth + 2, "бюджета не хватит даже на один полный путь");
        Ctw {
            nodes: vec![Node::fresh(NONE, 0, 0, 0)], // корень — индекс 0
            free: Vec::new(),
            leaves: Vec::new(), // корень в список листьев не входит: невытесняем
            depth,
            cap,
            hist: 0,
            codelen: 0,
            victim: Victim::Lfu,
            birth: Birth::Cold,
            sample: 8,
            lazy_k: 0,
            gamma: 2,
            beta_reset: false,
            verify_sum: false,
            last_evicted_prio: 0,
            rng: 0x2545F4914F6CDD1D,
            stats: Stats {
                evictions: 0,
                creations: 0,
                evicted_mass: 0,
                trunc_budget: 0,
                trunc_lazy: 0,
                peak_nodes: 1,
            },
            tab: Tables::new(),
        }
    }

    fn rng_next(&mut self) -> u64 {
        // xorshift64*: детерминирован при фиксированном зерне — это проверяется
        // тестом на воспроизводимость.
        let mut x = self.rng;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.rng = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }

    // --- учёт листьев ---

    fn leaf_add(&mut self, v: u32) {
        if v == 0 || self.nodes[v as usize].leaf_pos != NONE {
            return; // корень невытесняем, повторное добавление игнорируем
        }
        self.nodes[v as usize].leaf_pos = self.leaves.len() as u32;
        self.leaves.push(v);
    }

    fn leaf_remove(&mut self, v: u32) {
        let pos = self.nodes[v as usize].leaf_pos;
        if pos == NONE {
            return;
        }
        let last = *self.leaves.last().unwrap();
        self.leaves.swap_remove(pos as usize);
        if last != v {
            self.nodes[last as usize].leaf_pos = pos;
        }
        self.nodes[v as usize].leaf_pos = NONE;
    }

    /// Вытеснить один лист. `protect` — узел, которому мы прямо сейчас создаём
    /// ребёнка: он единственный на пути может оказаться листом, все прочие узлы
    /// пути имеют ребёнка на этом же пути и в списке листьев не значатся.
    ///
    /// Возвращает индекс освобождённого узла и массу его счётчиков (c_min для
    /// политики Space-Saving).
    fn evict(&mut self, protect: u32) -> Option<(u32, u64)> {
        if self.leaves.is_empty() {
            return None;
        }
        let mut best: Option<(u32, u64)> = None;
        for _ in 0..self.sample {
            let j = (self.rng_next() % self.leaves.len() as u64) as usize;
            let cand = self.leaves[j];
            if cand == protect {
                continue;
            }
            let nd = &self.nodes[cand as usize];
            let key = match self.victim {
                Victim::Lfu => nd.n[0] as u64 + nd.n[1] as u64,
                Victim::Ss => nd.prio as u64,
                Victim::Random => 0, // первый же годный кандидат
            };
            match best {
                Some((_, bk)) if bk <= key => {}
                _ => best = Some((cand, key)),
            }
            if self.victim == Victim::Random {
                break;
            }
        }
        // Масса берётся из самого узла, а не из ключа отбора: у политики Random
        // ключ тождественно нулевой, и использование его как массы обнуляло бы
        // и статистику, и наследование c_min в политике рождения Space-Saving.
        let (v, _key) = best?;
        let mass = self.nodes[v as usize].n[0] as u64 + self.nodes[v as usize].n[1] as u64;
        self.last_evicted_prio = self.nodes[v as usize].prio;

        // отцепить от родителя
        let p = self.nodes[v as usize].parent;
        let pn = &mut self.nodes[p as usize];
        if pn.child[0] == v {
            pn.child[0] = 0;
        } else {
            pn.child[1] = 0;
        }
        if self.beta_reset {
            pn.logbeta = 0;
        }
        let parent_now_leaf = pn.child[0] == 0 && pn.child[1] == 0;
        if parent_now_leaf {
            self.leaf_add(p);
        }
        self.leaf_remove(v);

        self.stats.evictions += 1;
        self.stats.evicted_mass += mass;
        Some((v, mass))
    }

    /// Выделить узел под ребёнка `slot` узла `parent`. None — бюджет исчерпан и
    /// вытеснять нечего, спуск придётся оборвать.
    fn alloc(&mut self, parent: u32, slot: usize) -> Option<u32> {
        let mut cmin: Option<u64> = None;
        self.last_evicted_prio = 0;
        let idx = if let Some(f) = self.free.pop() {
            f
        } else if self.nodes.len() < self.cap {
            self.nodes.push(Node::fresh(parent, 0, 0, 0));
            (self.nodes.len() - 1) as u32
        } else {
            let (v, mass) = self.evict(parent)?;
            cmin = Some(mass);
            v
        };
        // Приём Space-Saving: пришедший на место выбывшего стартует с c_min + 1,
        // иначе свежий узел с нулевым приоритетом был бы вытеснен немедленно.
        let prio = self.last_evicted_prio + 1;

        // Начальные счётчики по политике рождения.
        let (n0, n1) = match self.birth {
            Birth::Cold => (0, 0),
            Birth::SpaceSaving => match cmin {
                // Наследование массы имеет смысл только когда узел РОДИЛСЯ ИЗ
                // вытеснения — так же, как в Space-Saving, где c_min берётся у
                // выбывшего элемента. При свободном месте старт холодный.
                Some(mass) => split_by_ratio(mass, &self.nodes[parent as usize]),
                None => (0, 0),
            },
            Birth::Parent => {
                let p = &self.nodes[parent as usize];
                (p.n[0] / self.gamma, p.n[1] / self.gamma)
            }
        };

        self.nodes[idx as usize] = Node::fresh(parent, n0, n1, prio);
        self.leaf_remove(parent); // родитель перестал быть листом
        self.leaf_add(idx);
        self.nodes[parent as usize].child[slot] = idx;
        self.stats.creations += 1;
        if self.nodes.len() > self.stats.peak_nodes {
            self.stats.peak_nodes = self.nodes.len();
        }
        Some(idx)
    }

    /// log₂ условной вероятности KT для символа x в узле i:
    /// (2·n_x + 1) / (2·n + 2). Два целочисленных логарифма, никакого деления.
    fn kt_log_cond(&self, i: usize, x: usize) -> i64 {
        let nd = &self.nodes[i];
        let num = 2 * nd.n[x] as u64 + 1;
        let den = 2 * (nd.n[0] as u64 + nd.n[1] as u64) + 2;
        self.tab.log2_int(num) - self.tab.log2_int(den)
    }

    /// Подъём по пути: множитель обновления r = P_w^root(после)/P_w^root(до)
    /// в log₂. При `commit` записывает новые log β, иначе только считает.
    ///
    /// **Глубочайший узел пути всегда трактуется как лист** (P_w = P_e, r = q),
    /// независимо от того, дошли мы до предельной глубины или спуск оборвался
    /// по бюджету либо ленивому порогу. Это не деталь, а условие корректности:
    /// символ обязан быть учтён ровно один раз, в самом глубоком доступном узле.
    /// Если вместо этого считать оборванный узел внутренним с отсутствующими
    /// детьми (P_w = 1), то гипотеза «дети» получает вероятность 1 за данные,
    /// которых не моделировала: Σ_x r(x) = (β+2)/(β+1) > 1, модель перестаёт
    /// быть распределением, а кодовая длина занижается тем сильнее, чем чаще
    /// обрывается спуск. Инвариант Σ_x r(x) = 1 проверяется `--verify-sum`.
    fn walk(&mut self, path: &[u32], x: usize, commit: bool) -> i64 {
        let k = path.len() - 1;
        let mut logr = self.kt_log_cond(path[k] as usize, x);
        let mut d = k as isize - 1;
        while d >= 0 {
            let i = path[d as usize] as usize;
            let lq = self.kt_log_cond(i, x);
            let lb = self.nodes[i].logbeta;
            // β' = β · q / r  (в логарифмах — сложение)
            let lb_new = lb + lq - logr;
            // r_d = r_{d+1} · (1 + β') / (1 + β)
            logr += self.tab.log2_1p_exp2(lb_new) - self.tab.log2_1p_exp2(lb);
            if commit {
                self.nodes[i].logbeta = lb_new;
            }
            d -= 1;
        }
        logr
    }

    /// Проверка, что предсказатель выдаёт распределение: r(0) + r(1) = 1.
    /// Ловит именно тот класс ошибок, который даёт «слишком хорошее» сжатие.
    fn check_sums_to_one(&mut self, path: &[u32]) {
        let r0 = self.walk(path, 0, false);
        let r1 = self.walk(path, 1, false);
        let (hi, lo) = if r0 >= r1 { (r0, r1) } else { (r1, r0) };
        let total = hi + self.tab.log2_1p_exp2(lo - hi); // log₂(2^r0 + 2^r1)
        // Допуск — накопленное округление таблиц на пути длиной ≤ D.
        let tol = (path.len() as i64 + 2) * 64;
        if total.abs() > tol {
            panic!(
                "Σ_x P(x) ≠ 1: log₂ суммы = {} (допуск {}), длина пути {}",
                total,
                tol,
                path.len()
            );
        }
    }

    /// Обработать один бит: посчитать его кодовую длину и обновить модель.
    fn update(&mut self, x: usize, path: &mut Vec<u32>) {
        // --- спуск по контексту ---
        // Индекс 0 — корень, поэтому 0 годится как признак «ребёнка нет»:
        // корень ничьим ребёнком не бывает.
        path.clear();
        path.push(0);
        let mut cur = 0u32;
        for d in 0..self.depth {
            let b = ((self.hist >> d) & 1) as usize;
            let mut c = self.nodes[cur as usize].child[b];
            if c == 0 {
                let visits = self.nodes[cur as usize].n[0] as u64
                    + self.nodes[cur as usize].n[1] as u64;
                if visits < self.lazy_k {
                    self.stats.trunc_lazy += 1;
                    break;
                }
                match self.alloc(cur, b) {
                    Some(idx) => c = idx,
                    None => {
                        self.stats.trunc_budget += 1;
                        break;
                    }
                }
            }
            cur = c;
            path.push(cur);
            let _ = d;
        }

        // --- подъём по пути ---
        if self.verify_sum {
            self.check_sums_to_one(path);
        }
        let logr = self.walk(path, x, true);

        // Кодовая длина бита = −log₂ (P_w^root после / P_w^root до).
        self.codelen -= logr;

        // --- обновление счётчиков на всём пройденном пути ---
        // n — параметр модели (KT), prio — частота контекста (Space-Saving).
        // Растут вместе, но используются раздельно: n предсказывает, prio решает,
        // кого вытеснить.
        for &i in path.iter() {
            self.nodes[i as usize].n[x] += 1;
            self.nodes[i as usize].prio += 1;
        }
        self.hist = (self.hist << 1) | x as u64;
    }

    /// Проверка инвариантов структуры — вызывается тестами, не горячим путём.
    fn check_invariants(&self) -> Result<(), String> {
        if self.nodes.len() > self.cap {
            return Err(format!("бюджет превышен: {} > {}", self.nodes.len(), self.cap));
        }
        let live: usize = self.nodes.len() - self.free.len();
        let mut counted_leaves = 0usize;
        for (i, nd) in self.nodes.iter().enumerate() {
            if self.free.contains(&(i as u32)) {
                continue;
            }
            for &c in nd.child.iter() {
                if c != 0 {
                    if c as usize >= self.nodes.len() {
                        return Err(format!("узел {} ссылается за арену: {}", i, c));
                    }
                    if self.nodes[c as usize].parent != i as u32 {
                        return Err(format!("родитель узла {} не {}", c, i));
                    }
                }
            }
            if i != 0 && nd.child[0] == 0 && nd.child[1] == 0 {
                counted_leaves += 1;
                if nd.leaf_pos == NONE {
                    return Err(format!("лист {} не в списке листьев", i));
                }
            } else if nd.leaf_pos != NONE {
                return Err(format!("узел {} с детьми числится листом", i));
            }
        }
        if counted_leaves != self.leaves.len() {
            return Err(format!(
                "список листьев рассинхронизован: {} против {}",
                self.leaves.len(),
                counted_leaves
            ));
        }
        let _ = live;
        Ok(())
    }
}

/// Разделить массу `total` в пропорции счётчиков родителя.
fn split_by_ratio(total: u64, parent: &Node) -> (u32, u32) {
    let p0 = parent.n[0] as u64;
    let p1 = parent.n[1] as u64;
    let sum = p0 + p1;
    if sum == 0 || total == 0 {
        return (0, 0);
    }
    let a = total * p0 / sum;
    ((a) as u32, (total - a) as u32)
}

// ---------------------------------------------------------------------------
// Драйвер
// ---------------------------------------------------------------------------

/// Печать Q24-величины как десятичной дроби — без плавающей точки.
fn fmt_q24(v: i64, decimals: u32) -> String {
    let neg = v < 0;
    let mut a = if neg { -v } else { v };
    let int_part = a >> Q;
    a &= ONE - 1;
    let mut frac = String::new();
    for _ in 0..decimals {
        a *= 10;
        frac.push((b'0' + (a >> Q) as u8) as char);
        a &= ONE - 1;
    }
    format!("{}{}.{}", if neg { "-" } else { "" }, int_part, frac)
}

fn bits_per_char(bits_q24: i64, bytes: u64) -> String {
    if bytes == 0 {
        return "n/a".to_string();
    }
    fmt_q24(bits_q24 / bytes as i64, 6)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("использование: ctw <файл> [--depth D] [--limit N] [--budget УЗЛОВ]");
        eprintln!("  [--victim lfu|ss|random] [--birth cold|spacesaving|parent]");
        eprintln!("  [--sample S] [--lazy K] [--gamma G] [--beta-reset] [--seed S]");
        eprintln!("  [--check] [--verify-sum]");
        process::exit(2);
    }
    let mut depth = 24usize;
    let mut limit = usize::MAX;
    let mut budget = usize::MAX;
    let mut victim = Victim::Lfu;
    let mut birth = Birth::Cold;
    let mut sample = 8usize;
    let mut lazy = 0u64;
    let mut gamma = 2u32;
    let mut beta_reset = false;
    let mut seed = 0x2545F4914F6CDD1Du64;
    let mut check = false;
    let mut verify_sum = false;

    let mut i = 2;
    while i < args.len() {
        let need = |i: usize| -> String {
            if i + 1 >= args.len() {
                eprintln!("{}: нужен аргумент", args[i]);
                process::exit(2);
            }
            args[i + 1].clone()
        };
        match args[i].as_str() {
            "--depth" => { depth = need(i).parse().expect("--depth"); i += 2; }
            "--limit" => { limit = need(i).parse().expect("--limit"); i += 2; }
            "--budget" => { budget = need(i).parse().expect("--budget"); i += 2; }
            "--sample" => { sample = need(i).parse().expect("--sample"); i += 2; }
            "--lazy" => { lazy = need(i).parse().expect("--lazy"); i += 2; }
            "--gamma" => { gamma = need(i).parse().expect("--gamma"); i += 2; }
            "--seed" => { seed = need(i).parse().expect("--seed"); i += 2; }
            "--victim" => {
                victim = match need(i).as_str() {
                    "lfu" => Victim::Lfu,
                    "ss" => Victim::Ss,
                    "random" => Victim::Random,
                    o => { eprintln!("--victim: lfu|ss|random, дано {}", o); process::exit(2); }
                };
                i += 2;
            }
            "--birth" => {
                birth = match need(i).as_str() {
                    "cold" => Birth::Cold,
                    "spacesaving" => Birth::SpaceSaving,
                    "parent" => Birth::Parent,
                    o => { eprintln!("--birth: cold|spacesaving|parent, дано {}", o); process::exit(2); }
                };
                i += 2;
            }
            "--beta-reset" => { beta_reset = true; i += 1; }
            "--check" => { check = true; i += 1; }
            "--verify-sum" => { verify_sum = true; i += 1; }
            other => { eprintln!("неизвестный аргумент: {}", other); process::exit(2); }
        }
    }

    let data = match fs::read(&args[1]) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("не читается {}: {}", args[1], e);
            process::exit(1);
        }
    };
    let data = &data[..data.len().min(limit)];

    assert!(gamma >= 1, "--gamma должен быть ≥ 1");
    let mut ctw = Ctw::new(depth, budget);
    ctw.victim = victim;
    ctw.birth = birth;
    ctw.sample = sample.max(1);
    ctw.lazy_k = lazy;
    ctw.gamma = gamma;
    ctw.beta_reset = beta_reset;
    ctw.verify_sum = verify_sum;
    ctw.rng = seed | 1; // xorshift не переносит нулевое состояние

    let mut path: Vec<u32> = Vec::with_capacity(depth + 1);
    for &byte in data {
        // Байт разбирается на 8 бинарных решений, старший бит первым
        // (design-spec §1: ядро работает над бинарным алфавитом).
        for k in (0..8).rev() {
            ctw.update(((byte >> k) & 1) as usize, &mut path);
        }
    }

    if check {
        if let Err(e) = ctw.check_invariants() {
            eprintln!("ИНВАРИАНТ НАРУШЕН: {}", e);
            process::exit(3);
        }
    }

    let bits = ctw.codelen;
    println!("байт            {}", data.len());
    println!("глубина         {} бит", depth);
    println!("бюджет          {}", if budget == usize::MAX { "нет".to_string() } else { budget.to_string() });
    println!("узлов           {}", ctw.nodes.len());
    println!("память          {} байт", ctw.nodes.len() * std::mem::size_of::<Node>());
    println!("создано         {}", ctw.stats.creations);
    println!("вытеснено       {}", ctw.stats.evictions);
    println!("масса вытесн.   {}", ctw.stats.evicted_mass);
    println!("обрыв бюджет    {}", ctw.stats.trunc_budget);
    println!("обрыв ленивый   {}", ctw.stats.trunc_lazy);
    println!("кодовая длина   {} бит", fmt_q24(bits, 6));
    println!("bpc             {}", bits_per_char(bits, data.len() as u64));
}
