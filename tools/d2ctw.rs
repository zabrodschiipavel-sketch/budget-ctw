//! D2-CTW (Messias & Whiteson, NIPS 2017) — базлайн для пункта (1) П4.
//!
//! Реализация по статье «Dynamic-Depth Context Tree Weighting», §3. Это
//! ОТДЕЛЬНЫЙ базлайн, а не часть подачи: в лимит «≤1000 строк ядра» не входит.
//!
//! Что берётся из статьи дословно:
//!
//!   σ_t^s = P_w^s / P_e^s — отношение правдоподобий (у нашего ядра хранится
//!     обратная величина β = P_e/(P_w⁰P_w¹); связь σ = ½(1 + 1/β)), формулы (5)–(7):
//!       σ_t^s   = σ_{t−1}^s · P_w^{s'}(x_t) / P_e^s(x_t),  s' — ребёнок на пути;
//!       P_w^s(x_t) = P_e^s(x_t) · (1 + σ_t^s)/(1 + σ_{t−1}^s).
//!
//!   Бахрома (fringe): под каждым «фронтирным» узлом f держится поддерево
//!     глубины H, которое копит счётчики и своё σ, но НЕ участвует в выводе
//!     модели — выше f узел f трактуется как лист.
//!
//!   Критерий расширения (§3.2): Δ_exp^f = (1 + σ_t^f)/2,
//!     Γ^f = ∏_{d<|f|} σ^{p_d}/(1 + σ^{p_d}) по предкам, и глобальный эффект
//!     Δ_exp = 1 + Γ^f·(Δ_exp^f − 1) (предложение 1). Расширяем при Δ_exp > κ.
//!
//!   Обрезка (§3.3): Δ_prune^s = 2/(1 + σ_t^s), глобально
//!     Δ_prune = 1 + Γ^s·(Δ_prune^s − 1); при нехватке памяти обрезаем s с
//!     максимальным Δ_prune, если Δ_exp·Δ_prune > 1, места хватает, и s не
//!     предок f.
//!
//! Три сознательных отклонения, каждое отмечено в notes/stage13-d2ctw.md:
//!
//!   1. оценщик: у авторов SAD (для больших алфавитов), здесь KT — тот же, что
//!      в нашем ядре. При |Σ|=2 разница между ними мала, а сравнение изолирует
//!      именно управление памятью, а не оценщик;
//!   2. арифметика f64 (у нашего ядра целочисленная Q24). Для базлайна это
//!      допустимо: ошибка Q24 ≈ 3·10⁻⁵ bpc, на порядки ниже сравниваемых разниц;
//!   3. поиск кандидата на обрезку — по выборке из арены, а не точный arg max
//!      по всем узлам (в статье структура данных не описана).
//!
//! Сборка: rustc -O --edition 2021 -o bin/d2ctw.exe tools/d2ctw.rs
//! Запуск: d2ctw <файл> [--limit N] [--nodes L] [--fringe H] [--kappa K]
//!                [--max-depth D] [--sample S]

use std::env;
use std::fs;
use std::process;

const NONE: u32 = 0; // индекс 0 — корень, значит годится как «нет ребёнка»

#[derive(Clone, Copy)]
struct Node {
    n: [u32; 2],
    child: [u32; 2],
    parent: u32,
    depth: u16,
    proper: bool,
    /// log₂ σ. У фронтирного узла — величина, накопленная бахромой.
    lsig: f64,
    /// log₂ Γ — чувствительность модели к изменениям под этим узлом.
    /// Обновляется при каждом проходе по узлу (для непосещённых устаревает).
    lgam: f64,
}

impl Node {
    fn fresh(parent: u32, depth: u16, proper: bool) -> Node {
        // σ₀ = 1 для любого контекста (статья, после (7))
        Node { n: [0, 0], child: [NONE, NONE], parent, depth, proper, lsig: 0.0, lgam: 0.0 }
    }
    fn is_leaf(&self) -> bool {
        self.child[0] == NONE && self.child[1] == NONE
    }
}

/// log₂(1 + 2^x), устойчиво при больших |x|.
fn log2_1p_exp2(x: f64) -> f64 {
    if x > 60.0 {
        x
    } else if x < -60.0 {
        0.0
    } else {
        (1.0 + x.exp2()).log2()
    }
}

struct D2 {
    nodes: Vec<Node>,
    free: Vec<u32>,
    proper_count: usize,
    max_nodes: usize,
    fringe_h: u16,
    max_depth: u16,
    kappa: f64,
    sample: usize,
    rng: u64,
    codelen: f64,
    verify_sum: bool,
    max_sum_dev: f64,
    expansions: u64,
    prunes: u64,
    blocked: u64,
}

impl D2 {
    fn new(max_nodes: usize, fringe_h: u16, kappa: f64, max_depth: u16) -> D2 {
        D2 {
            nodes: vec![Node::fresh(NONE, 0, true)],
            free: Vec::new(),
            proper_count: 1,
            max_nodes,
            fringe_h,
            max_depth,
            kappa,
            sample: 16,
            rng: 0x2545F4914F6CDD1D,
            codelen: 0.0,
            verify_sum: false,
            max_sum_dev: 0.0,
            expansions: 0,
            prunes: 0,
            blocked: 0,
        }
    }

    fn rng_next(&mut self) -> u64 {
        let mut x = self.rng;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.rng = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }

    fn alloc(&mut self, parent: u32, depth: u16, proper: bool) -> Option<u32> {
        let idx = if let Some(f) = self.free.pop() {
            f
        } else {
            if self.nodes.len() >= self.max_nodes {
                return None;
            }
            self.nodes.push(Node::fresh(parent, depth, proper));
            return Some((self.nodes.len() - 1) as u32);
        };
        self.nodes[idx as usize] = Node::fresh(parent, depth, proper);
        Some(idx)
    }

    /// Освободить место под новый узел, обрезав худшее поддерево (§3.3).
    ///
    /// В статье бюджет L считает только proper-узлы, а бахрома объявлена
    /// «накладными расходами» вне бюджета. Здесь бюджет — вся арена, потому
    /// что сравнение идёт с нашим ядром при РАВНОЙ памяти, а бахрома память
    /// занимает. Поэтому давление памяти обрабатывается здесь, а не только в
    /// тесте расширения: без этого D2-CTW превратился бы в «CTW, переставший
    /// расти», то есть в тот самый слабый базлайн, который статья и критикует.
    ///
    /// Кандидат ищется по выборке (в статье структура данных не описана):
    /// максимум Δ_prune = 1 + Γ^s(2/(1+σ^s) − 1) среди proper-внутренних
    /// узлов, не лежащих на текущем пути.
    fn make_room(&mut self, protect: u32) -> bool {
        let mut best: Option<(f64, u32)> = None;
        for _ in 0..self.sample {
            let idx = (self.rng_next() % self.nodes.len() as u64) as u32;
            let nd = self.nodes[idx as usize];
            if idx == 0 || nd.is_leaf() || self.is_ancestor(idx, protect) {
                continue;
            }
            let dp_local = 2.0 / (1.0 + nd.lsig.exp2());
            let dp = 1.0 + nd.lgam.exp2() * (dp_local - 1.0);
            match best {
                Some((bd, _)) if bd >= dp => {}
                _ => best = Some((dp, idx)),
            }
        }
        match best {
            Some((_, s)) => {
                self.prune_subtree(s);
                self.prunes += 1;
                true
            }
            None => false,
        }
    }

    /// log₂ условной KT-вероятности символа x в узле i: (2n_x+1)/(2n+2).
    fn kt(&self, i: usize, x: usize) -> f64 {
        let nd = &self.nodes[i];
        let num = 2.0 * nd.n[x] as f64 + 1.0;
        let den = 2.0 * (nd.n[0] + nd.n[1]) as f64 + 2.0;
        (num / den).log2()
    }

    /// Обработать один бит.
    fn update(&mut self, x: usize, hist: u64, path: &mut Vec<u32>, frontier_pos: &mut usize) {
        // --- спуск: проперы, затем не более fringe_h уровней бахромы ---
        path.clear();
        path.push(0);
        let mut cur = 0u32;
        let mut last_proper = 0usize; // позиция фронтира в path
        for d in 0..self.max_depth as usize {
            let b = ((hist >> d) & 1) as usize;
            let c = self.nodes[cur as usize].child[b];
            let cur_depth = self.nodes[cur as usize].depth;
            let below_frontier = path.len() - 1 - last_proper;
            if c == NONE {
                // ниже бахромы не растём
                if below_frontier >= self.fringe_h as usize {
                    break;
                }
                let got = match self.alloc(cur, cur_depth + 1, false) {
                    Some(idx) => Some(idx),
                    None => {
                        // арена полна — освобождаем место обрезкой (§3.3)
                        if self.make_room(cur) {
                            self.alloc(cur, cur_depth + 1, false)
                        } else {
                            None
                        }
                    }
                };
                match got {
                    Some(idx) => {
                        self.nodes[cur as usize].child[b] = idx;
                        cur = idx;
                    }
                    None => {
                        self.blocked += 1;
                        break;
                    }
                }
            } else {
                cur = c;
            }
            path.push(cur);
            if self.nodes[cur as usize].proper {
                last_proper = path.len() - 1;
            } else if path.len() - 1 - last_proper >= self.fringe_h as usize {
                break;
            }
        }
        *frontier_pos = last_proper;

        // --- проверка инварианта Σ_x P(x) = 1 (только при --verify-sum) ---
        if self.verify_sum {
            let r0 = self.dry_run(0, path, *frontier_pos);
            let r1 = self.dry_run(1, path, *frontier_pos);
            let (hi, lo) = if r0 >= r1 { (r0, r1) } else { (r1, r0) };
            let total = hi + log2_1p_exp2(lo - hi); // log₂(2^r0 + 2^r1)
            // Допуск: арифметика здесь f64 в лог-домене, на пути до 48
            // уровней накапливается шум порядка 10⁻⁹ в log₂ (замерено). Для
            // сравнения, собственная проверка ядра допускает 8·10⁻⁵ (Q24 на
            // тот же путь). Порог 10⁻⁶ на два порядка строже неё и на три
            // порядка выше наблюдаемого шума; систематический сдвиг такой
            // величины дал бы ~1 бит на весь корпус в 8·10⁸ бит.
            if total.abs() > self.max_sum_dev {
                self.max_sum_dev = total.abs();
            }
            if total.abs() > 1e-6 {
                eprintln!("Σ_x P(x) ≠ 1: log₂ суммы = {:.3e}, длина пути {}", total, path.len());
                process::exit(3);
            }
        }

        // --- бахрома: снизу вверх до фронтира, обновляя σ бахромы и σ фронтира ---
        let mut k = path.len() - 1;
        let mut lpw = self.kt(path[k] as usize, x); // глубочайший узел — лист
        while k > *frontier_pos {
            k -= 1;
            let i = path[k] as usize;
            let lpe = self.kt(i, x);
            let lsig_old = self.nodes[i].lsig;
            let lsig_new = lsig_old + lpw - lpe;
            self.nodes[i].lsig = lsig_new;
            lpw = lpe + log2_1p_exp2(lsig_new) - log2_1p_exp2(lsig_old);
        }

        // --- модель: от фронтира (как лист) вверх до корня ---
        // Γ копится сверху вниз, поэтому сначала считаем вклад узлов пути.
        let mut lpw_model = self.kt(path[*frontier_pos] as usize, x);
        let mut k = *frontier_pos;
        while k > 0 {
            k -= 1;
            let i = path[k] as usize;
            let lpe = self.kt(i, x);
            let lsig_old = self.nodes[i].lsig;
            let lsig_new = lsig_old + lpw_model - lpe;
            self.nodes[i].lsig = lsig_new;
            lpw_model = lpe + log2_1p_exp2(lsig_new) - log2_1p_exp2(lsig_old);
        }
        self.codelen -= lpw_model;

        // --- счётчики на всём пути (бахрома тоже копит, статья §3.1) ---
        for &i in path.iter() {
            self.nodes[i as usize].n[x] += 1;
        }

        // --- Γ по пути сверху вниз: Γ^s = ∏_{предки} σ/(1+σ) ---
        let mut lgam = 0.0f64;
        for &i in path.iter() {
            self.nodes[i as usize].lgam = lgam;
            let ls = self.nodes[i as usize].lsig;
            lgam += ls - log2_1p_exp2(ls);
        }

        // --- тест расширения на фронтире ---
        let f = path[*frontier_pos];
        if (*frontier_pos + 1) < path.len() {
            let fi = f as usize;
            let d_exp_local = (1.0 + self.nodes[fi].lsig.exp2()) / 2.0;
            let gam = self.nodes[fi].lgam.exp2();
            let d_exp = 1.0 + gam * (d_exp_local - 1.0);
            if d_exp > self.kappa {
                self.try_expand(f);
            }
        }
    }

    /// Пробный расчёт log₂ P_w^корень(x) БЕЗ изменения состояния.
    /// Нужен для проверки Σ_x P(x) = 1: у этого проекта уже был случай, когда
    /// нарушение инварианта выглядело как рекордное сжатие (design-spec §2а),
    /// и базлайн, который обгоняет наше ядро, обязан пройти ту же проверку.
    fn dry_run(&self, x: usize, path: &[u32], frontier_pos: usize) -> f64 {
        // бахрома снизу вверх до фронтира
        let mut k = path.len() - 1;
        let mut lpw = self.kt(path[k] as usize, x);
        let mut lsig_f = self.nodes[path[frontier_pos] as usize].lsig;
        while k > frontier_pos {
            k -= 1;
            let i = path[k] as usize;
            let lpe = self.kt(i, x);
            let lsig_old = self.nodes[i].lsig;
            let lsig_new = lsig_old + lpw - lpe;
            if k == frontier_pos {
                lsig_f = lsig_new;
            }
            lpw = lpe + log2_1p_exp2(lsig_new) - log2_1p_exp2(lsig_old);
        }
        let _ = lsig_f;
        // модель: фронтир как лист, вверх до корня
        let mut lpw_model = self.kt(path[frontier_pos] as usize, x);
        let mut k = frontier_pos;
        while k > 0 {
            k -= 1;
            let i = path[k] as usize;
            let lpe = self.kt(i, x);
            let lsig_old = self.nodes[i].lsig;
            let lsig_new = lsig_old + lpw_model - lpe;
            lpw_model = lpe + log2_1p_exp2(lsig_new) - log2_1p_exp2(lsig_old);
        }
        lpw_model
    }

    /// Число узлов поддерева (не считая сам u).
    fn subtree_size(&self, u: u32) -> usize {
        let mut n = 0usize;
        let mut st = vec![u];
        while let Some(v) = st.pop() {
            for &c in &self.nodes[v as usize].child {
                if c != NONE {
                    n += 1;
                    st.push(c);
                }
            }
        }
        n
    }

    fn mark_proper(&mut self, u: u32) {
        let mut st = vec![u];
        while let Some(v) = st.pop() {
            let ch = self.nodes[v as usize].child;
            for &c in ch.iter() {
                if c != NONE {
                    if !self.nodes[c as usize].proper {
                        self.nodes[c as usize].proper = true;
                        self.proper_count += 1;
                    }
                    st.push(c);
                }
            }
        }
    }

    fn is_ancestor(&self, a: u32, mut b: u32) -> bool {
        loop {
            if a == b {
                return true;
            }
            if b == 0 {
                return false;
            }
            b = self.nodes[b as usize].parent;
        }
    }

    /// Освободить поддерево под s (сам s остаётся, становится листом).
    fn prune_subtree(&mut self, s: u32) -> usize {
        let mut freed = 0usize;
        let mut st: Vec<u32> = Vec::new();
        for b in 0..2 {
            let c = self.nodes[s as usize].child[b];
            if c != NONE {
                st.push(c);
                self.nodes[s as usize].child[b] = NONE;
            }
        }
        while let Some(v) = st.pop() {
            for &c in &self.nodes[v as usize].child {
                if c != NONE {
                    st.push(c);
                }
            }
            if self.nodes[v as usize].proper {
                self.proper_count -= 1;
            }
            self.free.push(v);
            freed += 1;
        }
        // узел стал листом: σ обнуляется, бахрома под ним вырастет заново
        self.nodes[s as usize].lsig = 0.0;
        freed
    }

    fn try_expand(&mut self, f: u32) {
        let need = self.subtree_size(f);
        if need == 0 {
            return;
        }
        if self.proper_count + need <= self.max_nodes {
            self.mark_proper(f);
            self.expansions += 1;
            return;
        }
        // Памяти нет: ищем кандидата на обрезку (§3.3), по выборке.
        let d_exp_local = (1.0 + self.nodes[f as usize].lsig.exp2()) / 2.0;
        let d_exp = 1.0 + self.nodes[f as usize].lgam.exp2() * (d_exp_local - 1.0);
        let mut best: Option<(f64, u32, usize)> = None;
        for _ in 0..self.sample {
            let idx = (self.rng_next() % self.nodes.len() as u64) as u32;
            let nd = self.nodes[idx as usize];
            if idx == 0 || !nd.proper || nd.is_leaf() {
                continue;
            }
            if self.is_ancestor(idx, f) {
                continue;
            }
            let dp_local = 2.0 / (1.0 + nd.lsig.exp2());
            let dp = 1.0 + nd.lgam.exp2() * (dp_local - 1.0);
            let frees = self.subtree_size(idx);
            if self.proper_count + need - frees > self.max_nodes {
                continue;
            }
            match best {
                Some((bd, _, _)) if bd >= dp => {}
                _ => best = Some((dp, idx, frees)),
            }
        }
        match best {
            Some((dp, s, _)) if d_exp * dp > 1.0 => {
                self.prune_subtree(s);
                self.prunes += 1;
                self.mark_proper(f);
                self.expansions += 1;
            }
            _ => self.blocked += 1,
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("использование: d2ctw <файл> [--limit N] [--nodes L] [--fringe H]");
        eprintln!("  [--kappa K] [--max-depth D] [--sample S] [--verify-sum]");
        process::exit(2);
    }
    let mut limit = usize::MAX;
    let mut max_nodes = usize::MAX;
    let mut fringe = 2u16;
    let mut kappa = 10.0f64;
    let mut max_depth = 48u16;
    let mut sample = 16usize;
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
            "--limit" => { limit = need(i).parse().expect("--limit"); i += 2; }
            "--nodes" => { max_nodes = need(i).parse().expect("--nodes"); i += 2; }
            "--fringe" => { fringe = need(i).parse().expect("--fringe"); i += 2; }
            "--kappa" => { kappa = need(i).parse().expect("--kappa"); i += 2; }
            "--max-depth" => { max_depth = need(i).parse().expect("--max-depth"); i += 2; }
            "--sample" => { sample = need(i).parse().expect("--sample"); i += 2; }
            "--verify-sum" => { verify_sum = true; i += 1; }
            o => { eprintln!("неизвестный аргумент: {}", o); process::exit(2); }
        }
    }

    let data = match fs::read(&args[1]) {
        Ok(d) => d,
        Err(e) => { eprintln!("не читается {}: {}", args[1], e); process::exit(1); }
    };
    let data = &data[..data.len().min(limit)];

    let mut m = D2::new(max_nodes, fringe, kappa, max_depth);
    m.sample = sample.max(1);
    m.verify_sum = verify_sum;
    let mut path: Vec<u32> = Vec::with_capacity(max_depth as usize + 2);
    let mut fpos = 0usize;
    let mut hist: u64 = 0;
    for &byte in data {
        for k in (0..8).rev() {
            let x = ((byte >> k) & 1) as usize;
            m.update(x, hist, &mut path, &mut fpos);
            hist = (hist << 1) | x as u64;
        }
    }

    let depth_max = m.nodes.iter().filter(|n| n.proper).map(|n| n.depth).max().unwrap_or(0);
    let nbytes = data.len() as f64;
    println!("байт            {}", data.len());
    println!("узлов всего     {}", m.nodes.len() - m.free.len());
    println!("  из них proper {}", m.proper_count);
    println!("глубина модели  {}", depth_max);
    println!("расширений      {}", m.expansions);
    println!("обрезок         {}", m.prunes);
    println!("отказов         {}", m.blocked);
    if verify_sum {
        println!("макс. |log₂ΣP|   {:.3e} (допуск 1e-6)", m.max_sum_dev);
    }
    println!("кодовая длина   {:.6} бит", m.codelen);
    println!("bpc             {:.6}", m.codelen / nbytes);
}
