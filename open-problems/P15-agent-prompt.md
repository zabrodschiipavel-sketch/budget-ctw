# Стартовый промпт для многоагентной атаки на П15

Адаптация промпта из задачи о Cycle Double Cover. Скелет сохранён; изменены
предметная часть, список адверсариальных проверок и — единственное
существенное отличие — целевое утверждение: у П15 не одно верное утверждение,
которое надо доказать, а дихотомия, ровно одна ветвь которой предполагается
доказуемой.

Постановка задачи: [P15-eviction-restart-regret.md](P15-eviction-restart-regret.md).
Доказанная часть, которой можно пользоваться как данным: [`formal/`](../formal/).

---

```
Current task statement

A predictor here is a binary online sequence predictor of context-tree-weighting type
operating under a hard node budget. Fix a depth D and a budget of c·M nodes. A context is a
binary string u of length at most D, read root-to-leaf with the most recent symbol first;
the children of u are u0 and u1. For a sequence x in {0,1}^T and a context u, let n_b(u) be
the number of positions t < T at which the last |u| symbols before t equal u and x_t = b,
with positions before the start of the sequence read as 0. The Krichevsky-Trofimov estimator
is kt(a,b) = (prod_{i<a}(2i+1))(prod_{j<b}(2j+1)) / prod_{k<a+b}(2k+2), and kt(0,0)=1.

A comparison tree S is a full binary tree, every internal node having exactly two children.
T_M is the set of comparison trees with at most M leaves and depth at most D. The code length
of S on x is L_S(x) = sum over leaves v of S of -log2 kt(n_0(v), n_1(v)). The structural cost
Gamma_D(S) is the number of internal nodes of S plus the number of leaves of S at depth
strictly less than D.

An arena A is a prefix-closed set of contexts with |A| <= c·M. The truncated weighting is
defined by P_w^A(u) = kt(n_0(u), n_1(u)) if u has depth D or not both u0 and u1 lie in A, and
P_w^A(u) = (kt(n_0(u), n_1(u)) + P_w^A(u0) · P_w^A(u1)) / 2 otherwise. A node whose two
children are not both in the arena is therefore treated as a leaf.

The algorithm A: at each step it descends the current arena along the current context,
updates the KT counters on that path, and when the arena is full evicts a node by a policy pi
and creates the new node with counters (0,0) - a cold restart. Its cumulative code length is
L_A^dyn(x) = sum_t -log2 P_t(x_t), where P_t is computed from the state at time t. Write
L_A^stat(x) = -log2 P_w^{A_T}(root), the code length of the same weighting with the arena
frozen at its final state and the counters taken over all of x. Define

    E_T   = L_A^dyn(x) - L_A^stat(x)                    the restart cost
    R_T   = L_A^dyn(x) - min_{S in T_M} L_S(x)          the regret

Say that S fits an arena A if every split S performs is available in A.

The following three statements are already proved and machine-checked in Lean 4 (Mathlib,
no sorry); use them freely as given, and do not spend agents reproving them.

    Theorem A. For every arena A and every S fitting A,
               prod_{leaves v of S} kt(n_0(v), n_1(v))  <=  2^{Gamma_D(S)} · P_w^A(root).
    Corollary B. For every S in T_M fitting A,  -log2 P_w^A(root) - L_S(x) <= Gamma_D(S) <= 2M-1.
    Theorem C. P_w^A(...0) + P_w^A(...1) = P_w^A(...) for every arena and every depth.

Theorem A is the reduction that defines this task: truncation of the tree costs nothing
multiplicatively. Consequently R_T decomposes as

    R_T = E_T                                                                        (I)
        + [ L_A^stat(x) - min_{S in T_M, S fits A_T} (Gamma_D(S) + L_S(x)) ]         (II)
        + [ min_{S fits A_T} (Gamma_D(S) + L_S(x)) - min_{S in T_M} L_S(x) ]         (III)

with (II) <= 0 by Corollary B. Only (I) and (III) are open.

Resolve the eviction-restart regret problem completely. Exactly one of the following two
branches is to be established:

  Branch UPPER. Exhibit an explicit class X of individual sequences and prove that for the
  budgeted algorithm with cold restart under a named eviction policy, R_T = o(T) uniformly on
  X, with the constants and the dependence on M, D and c written out. The class X must be
  defined by verifiable properties of the sequence itself, must be proved nonempty and
  nontrivial, and must contain at minimum every sequence whose depth-D context frequency
  distribution has a Zipf tail with exponent alpha > 1. Both (I) and (III) must be bounded;
  bounding one and asserting the other is not a solution.

  Branch LOWER. Prove that for every eviction policy, every c, and every M below an explicit
  threshold expressed in terms of the sequence family, there exists a family of individual
  sequences on which R_T = Omega(T), with the adversary construction explicit and the constant
  written out.

Assume for purposes of this task that exactly one of the two branches is provable. A complete
solution must prove one branch in full, for the individual-sequence setting, without
additional assumptions such as stationarity, ergodicity, a memoryless or Markov source,
bounded depth beyond the stated D, unlimited arena, or a modified comparison class.

Partial progress does not count unless it implies exactly one of the two resolutions above.
In particular the following are insufficient: bounds proved only for stationary or i.i.d.
sources; bounds on the comparator's own memory-restricted minimum, that is on
cost(M) - cost(full) of the comparator, instead of on the algorithm's code length; vacuous
bounds, meaning any bound exceeding the trivial one bit per bit or exceeding the algorithm's
own achieved code length; reductions to an unproved statement of equal strength, in
particular to "the arena retains a near-optimal tree"; results stated for an idealized
entropy comparator rather than the KT comparator L_S defined above, unless the KT redundancy
lemma is proved as part of the submission; computational verification on any fixed corpus,
including all of enwik8; and candidate adversary families without an explicit construction
and an explicit constant.

Use multiagent v2 aggressively and dynamically. You have up to 64 concurrent agents
available. Do not use a fixed assignment such as "N agents for strategy X." Instead, manage
the search using the following heuristics:

- Begin with a genuinely diverse portfolio of approaches. Agents should explore substantially
different formulations, potential and telescoping arguments, phase decompositions over node
lifetimes, martingale and mixture arguments, two-part and MDL coding arguments, switching and
tracking-the-best-expert machinery, competitive analysis of caching against the offline
optimum, renewal and heavy-tail arguments for the Zipf regime, counting and entropy lower
bounds, transition-system invariants, reformulations of the comparison class, and
computational sanity checks against the reference implementation.
- Do not tell most agents the currently favored approach. Preserve independence during early
rounds so that agents do not all converge to the same attractive but incomplete reduction.
- Maintain an explicit registry of approach families. Group agents by the mathematical idea
they are using, not by superficial wording. If many agents converge to one family, redirect
some of them toward underexplored formulations.
- Do not allow one approach to dominate merely because it gives elegant reductions. A route
that ends at a lemma equivalent in strength to the original statement is not close to
completion unless it supplies a genuinely new proof of that lemma.
- When an approach stalls at a theorem-strength missing lemma, mark that route as blocked.
Only continue assigning agents to it if someone proposes a materially new mechanism,
invariant, or construction.
- Three routes are already blocked by measurement and must not be reopened without a new
mechanism. Per-eviction accounting, E_T <= sum over recreations of (1/2 log2 n_i + 1),
overestimates the measured leakage roughly thirtyfold at D=24 and degenerates entirely at
D=48, where it yields 7 bits per byte against an achieved 2.53. Switching arguments require
about 10^10 switches on a corpus of 8·10^8 bits. The trivial "a phase costs no more than its
mass" gives 1.54·10^10 bits against the same corpus. The common cause is that the intensity
of eviction and the cost of eviction are different quantities: depth 48 evicts ninety times
more often than depth 24 and predicts better. Any bound of the form (number of events) times
(worst-case cost per event) is doomed.
- Keep several incompatible proof routes alive through multiple rounds. Cross-pollinate ideas
only after independent agents have developed them far enough to expose their real strengths
and gaps.
- Use adversarial agents throughout: every candidate proof must be checked for the following.
The mass invariant of Theorem C must be preserved by every construction and every reduction;
a violation of it manifests as apparent compression and has already produced a spurious 0.204
bits per character once. The comparison class must be the full T_M and not the subclass
obtained by truncating a tree at its first unary node; that error survived in five
independent implementations. L_S must be the KT code length as defined and not an entropy
idealization. E_T must be the algorithm minus the same algorithm frozen, never the comparator
minus itself. The arena must remain prefix-closed after every reduction, and a truncated node
must be treated as a leaf and not silently as an internal node. Measured constants, the 2.49
and 1.51 counters carried by an evicted node and the alpha between 1.3 and 1.5, may motivate
a hypothesis but may never be substituted into a theorem as if proved. Finally, any claimed
lower bound must be consistent with the measurement R_T = -0.034 bits per character at D=24,
M = 838 860 on enwik8: regret is genuinely negative there, because an algorithm with cold
restarts is a mixture over trees-with-restarts and that class is strictly richer than T_M, so
a lower bound that would forbid this is wrong and its author has made an error.
- Require agents to return concrete lemmas, constructions, equations, or counterexamples to
proposed sublemmas. Reject status reports, vague optimism, and claims that an unproved global
compatibility statement is "routine."
- The root agent should repeatedly synthesize, challenge, redirect, and launch new rounds. Do
not stop after the first wave fails. Produce a complete proof if one survives audit;
otherwise report only the strongest rigorously proved derivation and its exact remaining gap.

Do not return merely because current approaches fail or agents report theorem-strength gaps.
Continue launching new rounds, reopening blocked approaches only when there is a genuinely
new mechanism, and searching for fresh formulations.

Return only when a complete proof of one branch has been found and survives adversarial
audit. Do not return a reduction, partial result, isolated missing lemma, "best effort"
summary, or explanation of why the problem is difficult.

Spend at least 8 hours on this before even thinking of returning or giving up.

Public search may be used only for ordinary mathematical background or standard named
theorems - context tree weighting, Krichevsky-Trofimov redundancy, tracking the best expert,
competitive paging, heavy-tailed renewal theory. It may not be used to search for a solution
to this exact problem or benchmark. Do not search the public web merely to determine whether
a regret bound for bounded-memory CTW exists, and do not answer that none is known.
```
