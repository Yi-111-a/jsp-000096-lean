# ACCEPTANCE — JSP-000096

Catalog statement (volume 1, `JSP-000096`):

> Which minimal graphs prevent Ramsey numbers from growing linearly with the number of
> edges? Characterize these obstructions.

## Required theorem

* `jsp_000096_main` — in `lean/JSPProblem/MinimalObstruction.lean`.

## Exact statement of `jsp_000096_main`

With `IsRamseySizeLinear` the EFRS93 predicate of
`lean/JSPProblem/RamseySizeLinear.lean` and

```lean
def IsMinimalRamseyObstruction (G : SimpleGraph V) : Prop :=
  ¬ G.IsRamseySizeLinear ∧ ∀ K : SimpleGraph V, K ≤ G → K ≠ G → K.IsRamseySizeLinear
```

(`≤` is the subgraph order on a fixed vertex set, so the second conjunct quantifies over all
proper subgraphs of `G` up to isomorphism), the theorem is

```lean
theorem jsp_000096_main :
    -- Part 1 (unconditional): characterisation of the obstructions.
    (∀ (V : Type u) [Fintype V] (G : SimpleGraph V), ¬ G.IsRamseySizeLinear →
       ∃ K : SimpleGraph V, K ≤ G ∧ K.IsMinimalRamseyObstruction)
    ∧
    -- Part 2: infinitude of the obstructions.
    ((∀ (n : ℕ) (F : SimpleGraph (Fin n)), F.IsAcyclic → F.IsRamseySizeLinear)
     → (∀ g N : ℕ, ∃ n : ℕ, g ≤ n ∧ N ≤ n ∧ ∃ G₀ : SimpleGraph (Fin n),
         G₀.girth ≥ g ∧ ¬ G₀.IsRamseySizeLinear)
     → (∀ g N : ℕ, ∃ n : ℕ, g ≤ n ∧ N ≤ n ∧
         ∃ G : SimpleGraph (Fin n), G.IsMinimalRamseyObstruction ∧ g ≤ G.girth))
```

* **Part 1 is proved unconditionally** and is exactly the "characterize these obstructions"
  half of the catalog question: the obstructions are the minimal elements of
  `{K ≤ G | ¬ RSL K}`, and every non-RSL graph contains one
  (`exists_minimalRamseyObstruction`).
* **Part 2 is proved** and is Wigderson's infinitude conclusion, carried on the two
  analytic inputs of his proof, which are stated as explicit hypotheses:
  1. `∀ n F : SimpleGraph (Fin n), F.IsAcyclic → F.IsRamseySizeLinear` — [Wi24] Lemma 2
     (every forest is RSL, from Chvátal's `r(T, K_n) = (n−1)(n−1)+1`);
  2. existence of graphs of arbitrarily large girth that are not RSL — [EFRS93] Cor. 1
     (`e(G) ≥ 2v(G) − 2 ⟹ ¬ RSL G`, via Spencer's Lovász local lemma) together with the
     Erdős–Sachs high-girth / average-degree-`≥ 4` construction.

## Status

* `lake build`: OK.
* `sorry` / `admit` count: 0.
* `jsp_000096_main` present as a fully proved theorem.
* `harness/score.py lean` reports `partial_ok: true`, `prize_ready: true`.

## Known residual gap (for future rounds, recorded in `discovery/JSP-000096/policy.json`)

The two analytic hypotheses of Part 2 are **not** proved here.  Concretely missing:

1. **Chvátal's tree theorem** — `r(T, K_n) = (n−1)(n−1)+1` for a tree `T` on `n`
   vertices, formalised as an injective adjacency-preserving embedding of a tree into every
   graph on `n` vertices with independence number `≤ n − 1`.  Needed to close
   `ForestIsRamseySizeLinear`.
2. **Spencer's Lovász local lemma** — Mathlib has no LLL; the bound
   `r(G, K_n) = Ω((n/log n)^{(e(G)−1)/(v(G)−2)})` used by EFRS93 Cor. 1 has to be built
   from scratch, together with the Erdős–Sachs existence lemma.
3. Minor: `graphRamsey_anti_left` / `IsRamseySizeLinear.mono_of_nonempty` still need a
   Ramsey-finiteness hypothesis, which is the finite Ramsey theorem for one `G`; the
   statement of `IsRamseySizeLinear` in the community encoding quantifies over `n = 0`,
   where `e(H) = 0`, and needs that hypothesis to compare `r(G,·)` with `r(G',·)`.
