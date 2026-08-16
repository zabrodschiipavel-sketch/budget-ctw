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

/// 40 байт. Индексы вместо указателей (design-spec §3).
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
    /// Биты 0/1: из этого слота ребёнок уже вытеснялся. Нужен, чтобы отличать
    /// ПОВТОРНОЕ создание узла от первого (design-spec §6). Лежит в
    /// существующем паддинге перед logbeta — размер узла не растёт.
    evicted_slots: u8,
    logbeta: i64,
}

/// Размер узла входит в отчётность по памяти и в сравнение политик, поэтому
/// зафиксирован проверкой на этапе компиляции.
const _: () = assert!(std::mem::size_of::<Node>() == 40);

impl Node {
    /// Свежий узел: log β = 0, поскольку у пустого узла P_e = 1 и у обоих
    /// (отсутствующих) детей P_w = 1, то есть β = 1.
    fn fresh(parent: u32, n0: u32, n1: u32, prio: u32) -> Node {
        Node {
            n: [n0, n1],
            child: [0, 0],
            parent,
            leaf_pos: NONE,
            prio,
            evicted_slots: 0,
            logbeta: 0,
        }
    }
}

/// Пять величин, через которые теория пункта (2) разговаривает с экспериментом
/// (design-spec §6): вытеснения, ПОВТОРНЫЕ создания отдельно от первых,
/// распределение времён жизни узла, доля символов с усечённым контекстом,
/// занятость арены во времени.
struct Stats {
    evictions: u64,
    creations: u64,
    /// Создания в слот, из которого ребёнок уже вытеснялся, — цикл
    /// «создан → вытеснен → создан». Именно он платит параметрическую цену
    /// заново и стоит в оценке E_T; при холодном рождении цена ≈ ½log₂n.
    ///
    /// Точность: недоучёт, если сам родитель успел быть вытеснен и создан
    /// заново (его флаги обнулились вместе с ним). Верхняя оценка недоучёта —
    /// число повторных созданий внутренних узлов, а они вытесняются последними
    /// (вытесняются только листья).
    recreations: u64,
    /// Масса счётчиков, ушедшая вместе с вытесненными узлами.
    evicted_mass: u64,
    /// Символы, где спуск оборвался из-за бюджета / из-за ленивого создания.
    trunc_budget: u64,
    trunc_lazy: u64,
    /// Символы, где спуск оборван детерминированным узлом (--defer-det).
    trunc_det: u64,
    peak_nodes: usize,
    /// Гистограмма времён жизни узла в лог₂-бакетах: life[k] — сколько узлов
    /// прожили от 2^(k−1) до 2^k бит. Только при --stats.
    life: [u64; 41],
    life_sum: u64,
    /// Срезы занятости: (бит, узлов, листьев, вытеснений к этому моменту).
    occupancy: Vec<(u64, u32, u32, u64)>,
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
    /// Не расщеплять узел, пока его распределение детерминировано, если он
    /// при этом набрал не меньше `det_k` посещений. 0 — блокировать всегда.
    defer_det: bool,
    det_k: u64,
    verify_sum: bool,
    /// Приоритет последнего вытесненного узла — c_min для политики Space-Saving.
    last_evicted_prio: u32,
    rng: u64,
    /// Номер обработанного бита — время для замеров жизни и занятости.
    t: u64,
    /// --stats: снимать времена жизни и занятость. Ценой памяти (см. birth_t),
    /// поэтому по умолчанию выключено.
    stats_full: bool,
    /// Момент рождения узла, параллельно арене. Заводится только при --stats:
    /// иначе это +4 байта на узел, то есть +10% памяти, а бюджет памяти —
    /// независимая переменная всего эксперимента.
    birth_t: Vec<u32>,
    /// Шаг между срезами занятости в битах; 0 — не снимать.
    occ_every: u64,
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
            defer_det: false,
            det_k: 0,
            verify_sum: false,
            last_evicted_prio: 0,
            rng: 0x2545F4914F6CDD1D,
            t: 0,
            stats_full: false,
            birth_t: Vec::new(),
            occ_every: 0,
            stats: Stats {
                evictions: 0,
                creations: 0,
                recreations: 0,
                evicted_mass: 0,
                trunc_budget: 0,
                trunc_lazy: 0,
                trunc_det: 0,
                peak_nodes: 1,
                life: [0; 41],
                life_sum: 0,
                occupancy: Vec::new(),
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

        // отцепить от родителя, пометив слот как побывавший вытесненным
        let p = self.nodes[v as usize].parent;
        let pn = &mut self.nodes[p as usize];
        if pn.child[0] == v {
            pn.child[0] = 0;
            pn.evicted_slots |= 1;
        } else {
            pn.child[1] = 0;
            pn.evicted_slots |= 2;
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
        if self.stats_full {
            let life = self.t - self.birth_t[v as usize] as u64;
            // бакет k = ⌈log₂ life⌉ + 1, нулевой — для life = 0
            let k = (64 - life.leading_zeros()) as usize;
            self.stats.life[k.min(40)] += 1;
            self.stats.life_sum += life;
        }
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

        // Повторное создание — до перезаписи узла: флаг живёт в РОДИТЕЛЕ и
        // говорит, что из этого слота уже вытесняли.
        if self.nodes[parent as usize].evicted_slots & (1 << slot) != 0 {
            self.stats.recreations += 1;
        }

        self.nodes[idx as usize] = Node::fresh(parent, n0, n1, prio);
        self.leaf_remove(parent); // родитель перестал быть листом
        self.leaf_add(idx);
        self.nodes[parent as usize].child[slot] = idx;
        self.stats.creations += 1;
        if self.stats_full {
            if self.birth_t.len() <= idx as usize {
                self.birth_t.resize(idx as usize + 1, 0);
            }
            self.birth_t[idx as usize] = self.t as u32;
        }
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
                let (a0, a1) = (self.nodes[cur as usize].n[0], self.nodes[cur as usize].n[1]);
                let visits = a0 as u64 + a1 as u64;
                if visits < self.lazy_k {
                    self.stats.trunc_lazy += 1;
                    break;
                }
                // Узел с детерминированным распределением расщеплять нечем:
                // счётчики ребёнка — подмножество счётчиков родителя, значит
                // ребёнок детерминирован в ту же сторону и с МЕНЬШЕЙ массой,
                // то есть предсказывает не лучше. Компаратор такой узел не
                // расщепляет тождественно (выигрыш энтропии c(u)−c(u0)−c(u1)
                // равен нулю при n0=0 или n1=0), а ядро до сих пор тратило на
                // это ёмкость: замер stage10 §6.3 показал, что 39% арены
                // уходит в узлы глубже листьев оптимума.
                if self.defer_det && (a0 == 0 || a1 == 0) && visits >= self.det_k {
                    self.stats.trunc_det += 1;
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

        self.t += 1;
        if self.occ_every != 0 && self.t % self.occ_every == 0 {
            self.stats.occupancy.push((
                self.t,
                self.nodes.len() as u32,
                self.leaves.len() as u32,
                self.stats.evictions,
            ));
        }
    }

    /// Включить дорогие замеры (design-spec §6): времена жизни узлов и срезы
    /// занятости арены. `total_bits` нужен, чтобы срезов было ~200 независимо
    /// от размера корпуса.
    fn enable_stats(&mut self, total_bits: u64) {
        // Момент рождения хранится в u32 ради памяти: 100 МБ постановки — это
        // 8·10⁸ бит, влезает. За 536 МБ счётчик переполнился бы и времена
        // жизни стали бы молча неверными — лучше отказать, чем соврать.
        if total_bits > u32::MAX as u64 {
            eprintln!("--stats: корпус > 536 МБ, времена жизни отключены (u32 переполнится)");
        } else {
            self.stats_full = true;
            self.birth_t = vec![0u32; self.nodes.len().max(1)];
        }
        self.occ_every = (total_bits / 200).max(1);
    }

    /// Выгрузить структуру удержанного дерева: по строке на узел, контекст —
    /// цепочка битов от самого свежего (порядок спуска: бит глубины d есть
    /// (hist>>d)&1). Счётчики не выгружаются намеренно: они у ядра сброшены
    /// вытеснениями, а вопрос, ради которого дамп и делается, — насколько
    /// хороша САМА структура. Оценивает её `comparator --structure` по
    /// истинным счётчикам корпуса.
    fn dump_tree(&self, path: &str) -> std::io::Result<usize> {
        use std::io::Write;
        let mut w = std::io::BufWriter::new(fs::File::create(path)?);
        // Рекурсия по дереву: её глубина ограничена D ≤ 63, стек не при чём.
        // Корень (пустой контекст) не выгружается — он есть всегда.
        fn go<W: std::io::Write>(
            me: &Ctw,
            u: u32,
            prefix: &mut String,
            w: &mut W,
            n: &mut usize,
        ) -> std::io::Result<()> {
            if !prefix.is_empty() {
                writeln!(w, "{}", prefix)?;
                *n += 1;
            }
            for b in 0..2usize {
                let c = me.nodes[u as usize].child[b];
                if c != 0 {
                    prefix.push(if b == 0 { '0' } else { '1' });
                    go(me, c, prefix, w, n)?;
                    prefix.pop();
                }
            }
            Ok(())
        }
        let mut n = 0usize;
        let mut prefix = String::with_capacity(self.depth + 1);
        go(self, 0, &mut prefix, &mut w, &mut n)?;
        w.flush()?;
        Ok(n)
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
        eprintln!("  [--check] [--verify-sum] [--stats] [--dump-tree ФАЙЛ] [--defer-det K]");
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
    let mut defer_det = false;
    let mut det_k: u64 = 0;
    let mut seed = 0x2545F4914F6CDD1Du64;
    let mut check = false;
    let mut verify_sum = false;
    let mut stats_full = false;
    let mut dump_tree: Option<String> = None;

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
            "--defer-det" => { defer_det = true; det_k = need(i).parse().expect("--defer-det K"); i += 2; }
            "--check" => { check = true; i += 1; }
            "--verify-sum" => { verify_sum = true; i += 1; }
            "--stats" => { stats_full = true; i += 1; }
            "--dump-tree" => { dump_tree = Some(need(i)); i += 2; }
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
    ctw.defer_det = defer_det;
    ctw.det_k = det_k;
    ctw.verify_sum = verify_sum;
    ctw.rng = seed | 1; // xorshift не переносит нулевое состояние
    if stats_full {
        ctw.enable_stats(data.len() as u64 * 8);
    }

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

    if let Some(p) = &dump_tree {
        match ctw.dump_tree(p) {
            Ok(n) => eprintln!("структура выгружена: {} узлов → {}", n, p),
            Err(e) => { eprintln!("не пишется {}: {}", p, e); process::exit(1); }
        }
    }

    let bits = ctw.codelen;
    println!("байт            {}", data.len());
    println!("глубина         {} бит", depth);
    println!("бюджет          {}", if budget == usize::MAX { "нет".to_string() } else { budget.to_string() });
    println!("узлов           {}", ctw.nodes.len());
    println!("память          {} байт", ctw.nodes.len() * std::mem::size_of::<Node>());
    println!("пик узлов       {}", ctw.stats.peak_nodes);
    let nbits = (data.len() as u64 * 8).max(1);
    let pct = |a: u64| 100.0_f64 * a as f64 / nbits as f64;
    println!("создано         {}", ctw.stats.creations);
    println!("  повторно      {} ({:.1}% созданий, {:.3} на бит)",
             ctw.stats.recreations,
             100.0 * ctw.stats.recreations as f64 / ctw.stats.creations.max(1) as f64,
             ctw.stats.recreations as f64 / nbits as f64);
    println!("вытеснено       {} ({:.3} на бит)",
             ctw.stats.evictions, ctw.stats.evictions as f64 / nbits as f64);
    println!("масса вытесн.   {}", ctw.stats.evicted_mass);
    println!("обрыв бюджет    {} ({:.2}% бит)", ctw.stats.trunc_budget, pct(ctw.stats.trunc_budget));
    println!("обрыв ленивый   {} ({:.2}% бит)", ctw.stats.trunc_lazy, pct(ctw.stats.trunc_lazy));
    println!("обрыв детерм.   {} ({:.2}% бит)", ctw.stats.trunc_det, pct(ctw.stats.trunc_det));
    println!("кодовая длина   {} бит", fmt_q24(bits, 6));
    println!("bpc             {}", bits_per_char(bits, data.len() as u64));

    if stats_full {
        let ev = ctw.stats.evictions.max(1);
        println!();
        println!("время жизни узла (бит): среднее {:.1}", ctw.stats.life_sum as f64 / ev as f64);
        // Медиана и хвост берутся по кумулятиве лог₂-бакетов: точность —
        // множитель 2, чего для формы распределения достаточно.
        let mut acc = 0u64;
        let (mut med, mut p90) = (0usize, 0usize);
        for (k, &c) in ctw.stats.life.iter().enumerate() {
            acc += c;
            if med == 0 && acc * 2 >= ev { med = k; }
            if p90 == 0 && acc * 10 >= ev * 9 { p90 = k; }
        }
        println!("  медиана < 2^{} бит, 90-й процентиль < 2^{} бит", med, p90);
        println!("  бакет  доля вытеснений");
        for (k, &c) in ctw.stats.life.iter().enumerate() {
            if c != 0 {
                println!("  <2^{:<3} {:>7.3}%  {}", k, 100.0 * c as f64 / ev as f64, c);
            }
        }
        println!();
        println!("занятость арены (бит, узлов, листьев, вытеснений):");
        for &(t, n, l, e) in ctw.stats.occupancy.iter() {
            println!("  {:>12} {:>10} {:>10} {:>12}", t, n, l, e);
        }
    }
}
