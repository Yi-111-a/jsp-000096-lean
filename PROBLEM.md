# JSP-000096

> Which minimal graphs prevent Ramsey numbers from growing linearly with the number of
> edges? Characterize these obstructions.

* **Mathematical area:** Graph theory / Ramsey theory.
* **Catalog:** volume 1, `JSP-000096`
  (`https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md`).
* **Current status:** Solved.
* **Lean proof (catalog):** No.  **Eligible to claim:** No.
* **Publication details:**
  * [EFRS93] P. Erdős, R. J. Faudree, C. C. Rousseau, R. H. Schelp,
    *Ramsey size linear graphs*, Combinatorics, Probability and Computing **2** (1993),
    389–399. <https://doi.org/10.1017/s096354830000078x>
  * [Wi24] Y. Wigderson, *Infinitely many minimally non-Ramsey size-linear graphs*,
    arXiv:2409.05931 (2024). <https://arxiv.org/abs/2409.05931>

## Mathematical content

A graph `G` is **Ramsey size linear** (RSL) if there is a constant `c_G > 0` such that
`r(G, H) ≤ c_G · e(H)` for every graph `H` with no isolated vertices, where `r(G, H)` is the
two-colour vertex Ramsey number (least `N` such that every 2-colouring of the edges of `K_N`
has a copy of `G` in the first colour or of `H` in the second).

A graph is **minimally non-Ramsey size linear** if it is not RSL but every proper subgraph
of it is.  `K₄` is the classical example (EFRS93); Wigderson (2024) proved that there are
infinitely many such graphs, answering the question.  The catalog statement asks precisely
for this characterisation.

Wigderson's proof has three ingredients:

1. every non-RSL graph contains an inclusion-minimal obstruction;
2. acyclic graphs are RSL (from Chvátal's `r(T, K_n) = (n−1)(n−1)+1`) and girth is
   antitone under the subgraph order, so obstructions inherit large girth;
3. graphs of arbitrarily large girth and average degree `≥ 4` are not RSL
   (EFRS93 Cor. 1, `e(G) ≥ 2v(G) − 2 ⟹ ¬ RSL G`, proved with Spencer's Lovász local
   lemma), hence there are infinitely many minimal obstructions.

## Lean formalization in this directory

* `JSPProblem/RamseySizeLinear.lean` — `SimpleGraph.graphRamsey`,
  `SimpleGraph.IsRamseySizeLinear` (EFRS93's definition, matching the
  `FormalConjectures` encoding), the degree-sum bound `v H ≤ 2 e H`, and the API
  (monotonicity, symmetry, isomorphism invariance, edge counts of complete graphs).
* `JSPProblem/MinimalObstruction.lean` — the obstruction theory and the headline
  theorem `jsp_000096_main`.

See `ACCEPTANCE.md` for exactly what is proved.
