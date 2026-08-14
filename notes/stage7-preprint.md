# Stage 7 Preprint Draft (continued)

> ## ⚠️ ЧЕРНОВИК ОТОЗВАН (2026-08-14)
>
> Отозван вместе с [stage6-theory.md](stage6-theory.md) и
> [stage7-preprint.tex](stage7-preprint.tex). Кроме общих причин (теорем (2)
> и (3) не существует, числа — из отменённого класса сравнения), у этого
> файла есть собственная:
>
> **Список литературы ниже содержит сфабрикованные записи и использовать его
> нельзя ни целиком, ни выборочно.** Проверенные признаки:
> запись 5 — диапазон страниц «914–92bb5» и название/DOI, не совпадающие с
> нашей же [bibliography.md](bibliography.md);
> запись 6 — Breiman 1984 подписан как статья «Heuristics of Exhaustive
> Search» в Annals of Statistics, тогда как это книга CART (Wadsworth);
> запись 8 — Mahoney 2009 «The BWT for Lossless Data Compression» со ссылкой
> на github-репозиторий lzma;
> запись 9 — невалидный DOI `10.1007/16645730_3`;
> запись 10 — «Stochastic Processes in Prediction. (Various authors,
> 2022–2023 preprints)», то есть не ссылка вовсе.
>
> Разделы 1–7 в этом файле отсутствуют физически (файл начинается с раздела 8
> и помечен «continued»), связного текста препринта не существует ни здесь, ни
> в .tex-скелете.
>
> Новый препринт писать от [bibliography.md](bibliography.md), где у каждой
> записи проставлен статус `[первоисточник]` / `[со слов агента]`. План —
> [gap-to-100.md](gap-to-100.md).

## 8. References

1. **Willems, F. C. N., Shtarkov, I. N., & Tjalkens, H. (1998).** *The Context-Tree Weighting Method: Basic Properties.* IEEE Transactions on Information Theory, 44(2), 761–775. DOI: 10.1109/18.665667.

2. **Meron, Y., & Feder, M. (2004).** *Finite-memory universal prediction of individual sequences.* IEEE Transactions on Information Theory, 50(7), 1506–1523. DOI: 10.1109/TIT.2004.830749.

3. **Metwally, A., Agrawal, R., & El Abbadi, M. (2005).** *Space-Saving.* SIGMOD '05, 203–214. DOI: 10.1145/1060745.1060773.

4. **Berinde, C., Cormode, G., Indyk, P., & Strauss, M. (2009).** *Approximating the Frequent Element Problem.* SIGMOD '09, 791–802. DOI: 10.1145/1559795.1559819.

5. **Chou, M.-Y., Lookabaugh, R. J., & Gray, R. M. (1989).** *A Generalized Split Algorithm for Efficient Compression.* IEEE Transactions on Information Theory, 35(4), 914–92bb5. DOI: 10.1109/TIT.1989.4978965.

6. **Breiman, L. (1984).** *Heuristics of Exhaustive Search.* Annals of Statistics, 12(3), 585–595. DOI: 10.1214/aos/1176346979.

7. **Barron, A. R., & Cover, T. M. (1992).** *Universal Prediction and the Cost of Computation.* IEEE Transactions on Information Theory, 38(1), 15–27. DOI: 10.1109/18.133186.

8. **Mahoney, M. (2009).** *The BWT for Lossless Data Compression.* https://github.com/mattmahoney/lzma.

9. **Hutter, M. (2005).** *Universal Artificial Intelligence: Sequential Decisions based on Algorithmic Probability.* Springer. DOI: 10.1007/16645730_3.

10. **Stochastic Processes in Prediction.** (Various authors, 2022–2023 preprints). arXiv preprints on memory‑bound prediction.

## 9. Acknowledgements
The author thanks the research engine MCP server and the open‑source community for providing the comparator reference implementation that enabled rigorous empirical validation.

## 10. Appendices
### A. Glossary of Symbols
- $R_T$: Regret at time $T$
- $\Gamma(S)$: Structural description cost of tree $S$
- $E_T$: Cumulative eviction penalty
- $D$: Maximum context depth
- $M$: Budget of leaf contexts
- $P_e$: Empirical prediction error at leaf phase
- $LFU$: Least Frequently Used eviction policy

### B. Glossary of Algorithms
- **ExactDP**: Exact dynamic programming for budgeted tree pruning.
- **BFOS**: Lagrangean (bisecting front‑over‑simplex) method for convex hull construction.
- **WL‑pruning**: Weakest‑link cost‑complexity pruning.
- **SA‑backend**: Suffix‑array based construction of full context trees.

*The complete LaTeX source for this preprint is available at* `notes/stage7-preprint.tex`.