//! Компаратор min_{S∈T_M} L_S(x) — этап 5б задачи П4.
//!
//! Считает лучшую кодовую длину, достижимую древесным источником с ≤ M
//! листьями (класс T_M постановки П4). Две модели стоимости листа
//! (design-spec §5), выбор — `--cost`:
//!
//!   entropy (по умолчанию) — ОСНОВНОЙ компаратор: L_S = Σ_листьев n·H(эмп.).
//!       Идеализация: параметр листа известен точно и достаётся бесплатно.
//!   kt                     — ВТОРИЧНЫЙ компаратор: L_S = Σ_листьев −log₂KT(n0,n1).
//!       Настоящая кодовая длина последовательного KT-кода, то есть ровно то,
//!       что постановка П4 называет L_S («накопленная кодовая длина, −log₂
//!       вероятностей»), и та же валюта, которой платит ядро ctw.rs.
//!       Дороже энтропийного на избыточность KT ≤ ½·log₂n + 1 на лист.
//!
//! Важное следствие для kt: расщепление узла перестаёт быть бесплатным
//! (каждый новый лист платит свою ½log₂n), поэтому полное дерево T_max
//! оптимальным НЕ обязано быть, α может быть отрицательным, а стоимость по
//! оболочке — немонотонной по числу листьев. Ответ на бюджет M поэтому берётся
//! как минимум по всем точкам с листьями ≤ M (так было и раньше).
//!
//! Отдельная программа (design-spec §7): в лимит ядра ≤1000 строк не входит.
//!
//! Алгоритм:
//!   1. Полное дерево встреченных контекстов (та же модель битов, что в
//!      ядре ctw.rs: байт → 8 бит MSB-first, контекст глубины d = (hist>>d)&1,
//!      hist = (hist<<1)|x; счётчики n[0], n[1] следующего бита). Контекст,
//!      ни разу не встретившийся, — легальный лист T_M с нулевой массой и
//!      нулевой стоимостью; в узлах он не материализуется (счётчик молчаливо
//!      подразумевается нулевым), а входит в дерево символически — см. п. 3.
//!   2. Стоимость узла как листа c(u) = n_u·H(n0/n_u, n1/n_u).
//!      Вогнутость энтропии ⇒ полное дерево оптимально без бюджета;
//!      с бюджетом M — выбор расщеплений максимального выигрыша
//!      g(u) = c(u) − c(u0) − c(u1) ≥ 0 (cost-complexity pruning).
//!   3. Жадное отщипывание слабейшего звена (Breiman): узел с минимальным
//!      α = (c(u) − R(u))/(листья(u) − 1), где R(u) — стоимость текущего
//!      поддерева. Даёт все точки нижней выпуклой оболочки (листья, биты).
//!      Узел с ровно одним встреченным ребёнком — ВНУТРЕННИЙ: у него есть
//!      и наблюдённое поддерево, и виртуальный лист-брат нулевой стоимости
//!      (n = 0 ⇒ c = 0). R(u) и число листьев(u) считают этого брата как
//!      (R=0, листьев=1), не создавая для него узла в arena.
//!   4. Для запрошенных бюджетов M — min стоимости по точкам с листьями ≤ M
//!      (для M вне оболочки это верхняя граница — оговорка спеки §5).
//!
//! Сборка:  rustc -O --edition 2021 -o bin/comparator.exe src/comparator.rs
//! Запуск:  comparator <файл> [--depth D] [--limit N] [--budgets "M1,M2,..."]
//!               [--points N]  (--points: вывести первые N точек оболочки)

use std::collections::BinaryHeap;
use std::env;
use std::fs;
use std::process;

// ---------------------------------------------------------------------------
// Дерево и построение
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
struct Node {
    n: [u32; 2],
    child: [u32; 2],
}

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

#[derive(Clone, Copy, PartialEq, Eq)]
enum Cost {
    Entropy,
    Kt,
}

/// ln Γ(x) для x > 0 — приближение Ланцоша (g=7, 9 коэффициентов).
///
/// В std Rust нет lgamma, а считать −log₂KT прямым произведением нельзя:
/// у корня n ≈ 8·10⁸. Сверено с math.lgamma питона в
/// tools/comparator_lgamma_check.py: относительная ошибка < 1e-14 на всём
/// используемом диапазоне (аргументы вида n+1 и n+½).
fn ln_gamma(x: f64) -> f64 {
    const G: [f64; 9] = [
        0.999_999_999_999_809_93,
        676.520_368_121_885_1,
        -1259.139_216_722_402_8,
        771.323_428_777_653_13,
        -176.615_029_162_140_59,
        12.507_343_278_686_905,
        -0.138_571_095_265_720_12,
        9.984_369_578_019_571_6e-6,
        1.505_632_735_149_311_6e-7,
    ];
    // Аргументы компаратора всегда ≥ ½, отражение нужно только для полноты.
    if x < 0.5 {
        let pi = std::f64::consts::PI;
        return (pi / (pi * x).sin()).ln() - ln_gamma(1.0 - x);
    }
    let z = x - 1.0;
    let mut a = G[0];
    for (i, &c) in G.iter().enumerate().skip(1) {
        a += c / (z + i as f64);
    }
    let t = z + 7.5;
    0.5 * (2.0 * std::f64::consts::PI).ln() + (z + 0.5) * t.ln() - t + a.ln()
}

/// −log₂KT(m, 0), бит — чисто перекошенный случай.
///
/// = log₂(√π·Γ(m+1)/Γ(m+½)). Прямая формула через lnΓ здесь ВЫЧИТАЕТ два
/// почти равных огромных числа (при m=4·10⁸ каждое ≈1.4·10¹⁰, а ответ ≈15),
/// теряя ~10 порядков: замерено расхождение 6.8·10⁻⁷ бита с точным значением.
/// Такие листья (детерминированное продолжение контекста) в дереве enwik8 —
/// самый массовый тип, поэтому считаем их отдельно и точно:
///   m < 128  — прямая сумма Σ_{k<m} log₂((k+1)/(k+½)) (все слагаемые
///              положительны, сокращений нет);
///   m ≥ 128  — асимптотика Γ(m+1)/Γ(m+½) = √m·(1 + 1/(8m) + 1/(128m²)
///              − 5/(1024m³) − 21/(32768m⁴)); сверено с прямой суммой:
///              расхождение 6·10⁻¹⁴ при m=128 и падает как m⁻⁵.
fn kt_cost_skew(m: f64) -> f64 {
    if m <= 0.0 {
        return 0.0;
    }
    if m < 128.0 {
        let mut s = 0.0;
        let mut k = 0.0;
        while k < m {
            s += ((k + 1.0) / (k + 0.5)).log2();
            k += 1.0;
        }
        return s;
    }
    let inv = 1.0 / m;
    let ratio = 1.0
        + inv * (0.125 + inv * (1.0 / 128.0 + inv * (-5.0 / 1024.0 + inv * (-21.0 / 32768.0))));
    0.5 * std::f64::consts::PI.log2() + 0.5 * m.log2() + ratio.log2()
}

/// −log₂KT(n0, n1), бит.
///
/// KT(a,b) = ∏_{i<a}(i+½)·∏_{j<b}(j+½)/(a+b)! = Γ(a+½)Γ(b+½)/(π·Γ(a+b+1)),
/// так как Γ(½)=√π. KT(0,0)=1 ⇒ невстреченный лист стоит 0 бит, как и в
/// энтропийной модели (виртуальные братья ничего не стоят).
///
/// KT обменяем, поэтому можно кодировать сначала mx одинаковых символов, потом
/// mn остальных:  −log₂KT(mx,mn) = −log₂KT(mx,0) + Σ_{j<mn} log₂((mx+j+1)/(j+½)).
/// При малом mn это точно и дёшево. При обоих больших счётчиках сама величина
/// сравнима с lnΓ-слагаемыми, сокращения нет — там прямая формула.
fn kt_cost(n0: f64, n1: f64) -> f64 {
    let n = n0 + n1;
    if n <= 0.0 {
        return 0.0;
    }
    let (mx, mn) = if n0 >= n1 { (n0, n1) } else { (n1, n0) };
    if mn <= 64.0 {
        let mut c = kt_cost_skew(mx);
        let mut j = 0.0;
        while j < mn {
            c += ((mx + j + 1.0) / (j + 0.5)).log2();
            j += 1.0;
        }
        return c;
    }
    let ln2 = std::f64::consts::LN_2;
    (ln_gamma(n + 1.0) + std::f64::consts::PI.ln() - ln_gamma(n0 + 0.5) - ln_gamma(n1 + 0.5)) / ln2
}

/// Стоимость узла как листа, биты.
fn cost_leaf(nd: &Node, model: Cost) -> f64 {
    let n0 = nd.n[0] as f64;
    let n1 = nd.n[1] as f64;
    if model == Cost::Kt {
        return kt_cost(n0, n1);
    }
    let n = n0 + n1;
    if n <= 0.0 {
        return 0.0;
    }
    let p = n0 / n;
    let h = if p <= 0.0 || p >= 1.0 {
        0.0
    } else {
        -p * p.log2() - (1.0 - p) * (1.0 - p).log2()
    };
    n * h
}

// ---------------------------------------------------------------------------
// Cost-complexity pruning (жадное отщипывание слабейшего звена)
// ---------------------------------------------------------------------------

struct Frontier {
    /// Точки (листья, биты) от стартового дерева (оптимум при λ=0) к корню.
    points: Vec<(u32, f64)>,
    /// T_max — всё встреченное дерево целиком. При entropy практически
    /// совпадает с points[0] (расходится лишь на float-шуме предредукции:
    /// на полном enwik8 D=24 это 91 лист из 4.9M при равной стоимости);
    /// при kt дороже, т.к. лишние расщепления там платные.
    tmax: (u64, f64),
}

fn weakest_link(nodes: &[Node], model: Cost) -> Frontier {
    let n = nodes.len();
    // Стоимость листа считается один раз на узел: точная ветка −log₂KT делает
    // до 64 log2 на узел, а α пересчитывается на каждом предке при каждом
    // отщипывании.
    let lc: Vec<f64> = nodes.iter().map(|nd| cost_leaf(nd, model)).collect();
    let mut ch0 = vec![0u32; n];
    let mut ch1 = vec![0u32; n];
    let mut par = vec![0u32; n];
    for (u, nd) in nodes.iter().enumerate() {
        ch0[u] = nd.child[0];
        ch1[u] = nd.child[1];
        for &c in &nd.child {
            if c != 0 {
                par[c as usize] = u as u32;
            }
        }
    }
    let mut R = vec![0.0f64; n];
    let mut leaves = vec![0u32; n];

    // T_max: реальные листья несут свою стоимость, виртуальные братья
    // унарных узлов стоят 0 бит, но бюджет занимают.
    let mut tmax_cost = 0.0f64;
    let mut tmax_leaves = 0u64;
    for (u, nd) in nodes.iter().enumerate() {
        let (c0, c1) = (nd.child[0] != 0, nd.child[1] != 0);
        if !c0 && !c1 {
            tmax_cost += lc[u];
            tmax_leaves += 1;
        } else if c0 != c1 {
            tmax_leaves += 1; // виртуальный брат
        }
    }

    // Отсутствующий ребёнок — виртуальный лист нулевой стоимости: он не
    // материализуется как узел arena, но участвует в R(u)/листьях(u) как
    // (0.0, 1). Реальный узел без единого ребёнка задаёт базовый случай.
    #[inline]
    fn rval(c: u32, r: &[f64]) -> f64 {
        if c != 0 { r[c as usize] } else { 0.0 }
    }
    #[inline]
    fn lval(c: u32, leaves: &[u32]) -> u32 {
        if c != 0 { leaves[c as usize] } else { 1 }
    }

    // Поддерево u исключается из дерева (u стал листом после отщипывания).
    // Помечает только РЕАЛЬНЫЕ узлы — виртуальные братья нигде не хранятся,
    // хоронить нечего.
    fn kill(leaves: &mut [u32], ch0: &[u32], ch1: &[u32], u: u32) {
        let mut stack = vec![u];
        while let Some(w) = stack.pop() {
            leaves[w as usize] = 0; // мёртвый узел
            if ch0[w as usize] != 0 {
                stack.push(ch0[w as usize]);
            }
            if ch1[w as usize] != 0 {
                stack.push(ch1[w as usize]);
            }
        }
    }

    // Стартовое дерево = оптимум при λ=0 (штрафа за лист нет). Узел
    // внутренний, если у него есть ХОТЯ БЫ ОДИН реальный ребёнок (второй
    // слот, если пуст, — виртуальный лист) И расщепление не дороже листа.
    //
    // Для entropy второе условие выполняется всегда (вогнутость: R(дети) ≤
    // c(u)), стартом остаётся ровно T_max и поведение бит-в-бит прежнее.
    // Для kt расщепление платное (новый лист несёт ½log₂n избыточности),
    // и такие узлы обязаны схлопнуться ДО развёртки: доказательство нестинга
    // у Бреймана опирается на α ≥ 0, при отрицательных α жадное отщипывание
    // перестаёт давать лагранжев оптимум (измерено на случайных корпусах:
    // 170 точек хребта из 4308 были хуже точного DP при своём же числе
    // листьев). После предредукции c(u) ≥ R(u) везде, и все α ≥ 0.
    for u in (0..n).rev() {
        if ch0[u] != 0 || ch1[u] != 0 {
            let rs = rval(ch0[u], &R) + rval(ch1[u], &R);
            if rs <= lc[u] {
                R[u] = rs;
                leaves[u] = lval(ch0[u], &leaves) + lval(ch1[u], &leaves);
                continue;
            }
        }
        R[u] = lc[u];
        leaves[u] = 1;
    }
    // Узлы под схлопнувшимися в дерево не входят: помечаем мёртвыми
    // (leaves = 0) обходом сверху за O(n).
    if (0..n).any(|u| leaves[u] == 1 && (ch0[u] != 0 || ch1[u] != 0)) {
        let mut reach = vec![false; n];
        let mut stack = vec![0u32];
        while let Some(w) = stack.pop() {
            let w = w as usize;
            reach[w] = true;
            if leaves[w] == 1 {
                continue;
            }
            if ch0[w] != 0 {
                stack.push(ch0[w]);
            }
            if ch1[w] != 0 {
                stack.push(ch1[w]);
            }
        }
        for u in 0..n {
            if !reach[u] {
                leaves[u] = 0;
            }
        }
    }

    let mut points = vec![(leaves[0], R[0])];
    let mut alpha = vec![f64::NAN; n];
    // min-куча по α; при равных α — меньший индекс первым (как heapq
    // Python-эталона: кортеж (α, индекс)). Reverse по индексу обязателен:
    // без него BinaryHeap при связях отдаёт больший индекс, и
    // последовательность отщипываний расходится с эталоном.
    // f64 не реализует Ord (из-за NaN); оборачиваем через total_cmp и
    // инвертируем для min-кучи. Кортеж (RevF64(alpha), Reverse(idx)):
    // при равных alpha первым идёт меньший idx (как heapq Python).
    #[derive(Clone, Copy)]
    struct RevF64(f64);
    impl PartialEq for RevF64 {
        fn eq(&self, o: &Self) -> bool { self.0.to_bits() == o.0.to_bits() }
    }
    impl Eq for RevF64 {}
    impl PartialOrd for RevF64 {
        fn partial_cmp(&self, o: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(o))
        }
    }
    impl Ord for RevF64 {
        fn cmp(&self, o: &Self) -> std::cmp::Ordering {
            // инверсия: большее f64 считается "меньшим" для min-кучи
            o.0.total_cmp(&self.0)
        }
    }

    let mut heap: BinaryHeap<(RevF64, std::cmp::Reverse<u32>)> = BinaryHeap::new();


    for u in 0..n {
        if (ch0[u] != 0 || ch1[u] != 0) && leaves[u] > 1 {
            let a = (lc[u] - R[u]) / (leaves[u] - 1) as f64;
            alpha[u] = a;
            heap.push((RevF64(a), std::cmp::Reverse(u as u32)));
        }
    }

    // Ленивая перестройка heap: записи устаревают при каждом пересчёте
    // предков (O(узлы×глубина) push'ей суммарно — это и был OOM 20 ГБ).
    // При переполнении (>) перестраиваем из живых кандидатов: O(n) за раз,
    // редко. Память heap ограничена ~2n записей.
    // Не даём устаревшим записям разрастись до размера дерева: для
    // больших входов это иначе добавляет гигабайты поверх самого trie.
    // На малых входах сохраняем прежний cap 2n, на больших — 8M записей.
    let heap_cap = n.saturating_mul(2).min(8_000_000) + 16;
    while let Some((RevF64(a), std::cmp::Reverse(uu))) = heap.pop() {
        let u = uu as usize;
        if leaves[u] <= 1 {
            continue; // мёртвый (0) или лист (1)
        }
        if alpha[u] != a {
            continue; // устаревшая запись
        }
        // отщипываем u: всё поддерево выбывает, u становится листом
        kill(&mut leaves, &ch0, &ch1, uu);
        R[u] = lc[u];
        leaves[u] = 1;
        // пересчёт предков до корня (виртуальные дети — снова (0.0, 1))
        let mut v = par[u] as usize;
        while v != u {
            R[v] = rval(ch0[v], &R) + rval(ch1[v], &R);
            leaves[v] = lval(ch0[v], &leaves) + lval(ch1[v], &leaves);
            if leaves[v] == 1 {
                break;
            }
            let a2 = (lc[v] - R[v]) / (leaves[v] - 1) as f64;
            alpha[v] = a2;
            heap.push((RevF64(a2), std::cmp::Reverse(v as u32)));
            if v == 0 {
                break;
            }
            v = par[v] as usize;
        }
        points.push((leaves[0], R[0]));
        if leaves[0] == 1 {
            break;
        }
        if heap.len() > heap_cap {
            heap.clear();
            for u in 0..n {
                if (ch0[u] != 0 || ch1[u] != 0) && leaves[u] > 1 {
                    heap.push((RevF64(alpha[u]), std::cmp::Reverse(u as u32)));
                }
            }
        }
    }

    Frontier { points, tmax: (tmax_leaves, tmax_cost) }
}

// ---------------------------------------------------------------------------
// Драйвер
// ---------------------------------------------------------------------------

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("использование: comparator <файл> [--depth D] [--limit N]");
        eprintln!("  [--budgets \"M1,M2,...\"] [--points N] [--cost entropy|kt]");
        process::exit(2);
    }
    let mut depth = 24usize;
    let mut limit = usize::MAX;
    let mut budgets: Vec<u64> = Vec::new();
    let mut npoints = 0usize;
    let mut model = Cost::Entropy;

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
            "--budgets" => {
                budgets = need(i)
                    .split(',')
                    .filter(|s| !s.is_empty())
                    .map(|s| s.parse().expect("--budgets"))
                    .collect();
                i += 2;
            }
            "--points" => { npoints = need(i).parse().expect("--points"); i += 2; }
            "--cost" => {
                model = match need(i).as_str() {
                    "entropy" => Cost::Entropy,
                    "kt" => Cost::Kt,
                    o => { eprintln!("--cost: entropy|kt, дано {}", o); process::exit(2); }
                };
                i += 2;
            }
            other => { eprintln!("неизвестный аргумент: {}", other); process::exit(2); }
        }
    }

    // Дамп −log₂KT на сетке счётчиков: вход для tools/comparator_lgamma_check.py,
    // который сверяет наш Ланцош с math.lgamma питона (включая n ~ 8·10⁸, где
    // ln_gamma ≈ 1.4·10¹⁰ и абсолютная ошибка важнее относительной).
    if args[1] == "--kt-selftest" {
        let grid: [f64; 13] = [
            0.0, 1.0, 2.0, 3.0, 5.0, 10.0, 100.0, 1000.0, 1e4, 1e6, 1e7, 1e8, 4e8,
        ];
        for &a in grid.iter() {
            for &b in grid.iter() {
                println!("{:.0} {:.0} {:.17e}", a, b, kt_cost(a, b));
            }
        }
        return;
    }

    let data = match fs::read(&args[1]) {
        Ok(d) => d,
        Err(e) => { eprintln!("не читается {}: {}", args[1], e); process::exit(1); }
    };
    let data = &data[..data.len().min(limit)];
    // Node.n хранит счётчики в u32. Корень получает один инкремент на бит,
    // поэтому входы > u32::MAX бит молча переполнили бы счётчики в release.
    // Явный backend всё равно не масштабируется до такого размера; для них
    // предназначен tools/sa_prod.py с u64-счётчиками.
    if data.len() > (u32::MAX as usize) / 8 {
        eprintln!(
            "вход слишком велик для explicit-компаратора: {} байт; максимум {} байт (u32 counters). Используйте tools/sa_prod.py",
            data.len(),
            (u32::MAX as usize) / 8
        );
        process::exit(2);
    }

    let nodes = build_tree(data, depth);
    let fr = weakest_link(&nodes, model);

    // bpc здесь и везде ниже — bits per character, бит/БАЙТ (как в ядре
    // ctw.rs и во всех заметках проекта); бит/бит = bpc / 8, отдельная
    // нормированная величина (доля от максимальной энтропии бита).
    let nbytes = data.len() as f64;
    let nbits = nbytes * 8.0;
    println!("модель стоимости        {}",
             if model == Cost::Kt { "kt (−log₂KT на лист)" } else { "entropy (n·H на лист)" });
    println!("узлов в полном дереве   {}", nodes.len());
    println!("точек на оболочке       {}", fr.points.len());
    println!("листья (полное дерево)  {}", fr.tmax.0);
    println!("стоимость полного дерева {:.3} бит ({:.4} бит/бит, {:.4} bpc)",
             fr.tmax.1, fr.tmax.1 / nbits, fr.tmax.1 / nbytes);
    // Стартовая точка хребта — оптимум при λ=0, то есть min_{S∈T_D} L_S без
    // бюджета вообще. Для entropy это ровно T_max (вогнутость), для kt —
    // строго дешевле и с меньшим числом листьев: лишние расщепления там
    // платят свою ½log₂n.
    println!("оптимум без бюджета     {:.3} бит ({:.4} бит/бит, {:.4} bpc) при {} листьях",
             fr.points[0].1, fr.points[0].1 / nbits, fr.points[0].1 / nbytes, fr.points[0].0);
    println!();

    if npoints > 0 {
        println!("первые {} точек оболочки (листья, биты, бит/бит, bpc):", npoints);
        for (l, c) in fr.points.iter().take(npoints) {
            println!("  {:>10}  {:>14.3}  {:>8.4}  {:>8.4}", l, c, c / nbits, c / nbytes);
        }
        println!();
    }

    if !budgets.is_empty() {
        // для каждого бюджета M: min стоимости по точкам с листьями ≤ M
        let mut best = Vec::with_capacity(budgets.len());
        for &m in &budgets {
            let mut b = f64::INFINITY;
            for &(l, c) in &fr.points {
                if (l as u64) <= m && c < b {
                    b = c;
                }
            }
            best.push(b);
        }
        println!("бюджет M (листья)  стоимость (бит)   бит/бит      bpc   верхняя?");
        for (i, &m) in budgets.iter().enumerate() {
            let b = best[i];
            if b.is_infinite() {
                println!("{:>16}  — дерево с ≤M листьев не существует", m);
                continue;
            }
            // точная ли это точка оболочки (т.е. достижим минимум)
            let exact = fr.points.iter().any(|&(l, c)| (l as u64) <= m && (c - b).abs() < 1e-9);
            println!(
                "{:>16}  {:>16.3}  {:>8.4}  {:>8.4}   {}",
                m, b, b / nbits, b / nbytes, if exact { "точная" } else { "верхняя" }
            );
        }
    }
}
