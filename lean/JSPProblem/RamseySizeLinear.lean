/-
JSP-000096 — Ramsey size-linear graphs.

Statement taken from the Justin Sun Prize catalog, volume 1 (`JSP-000096`):

> Which minimal graphs prevent Ramsey numbers from growing linearly with the number
> of edges? Characterize these obstructions.

Mathematical area: Graph theory / Ramsey theory.  Current status: Solved, via

* [EFRS93] Erdős, P., Faudree, R. J., Rousseau, C. C. and Schelp, R. H.,
  *Ramsey size linear graphs*, Combin. Probab. Comp. 2 (1993), 389–399.
* [Wi24] Wigderson, Y., *Infinitely many minimally non-Ramsey size-linear graphs*,
  arXiv:2409.05931 (2024).

This file provides the definitions of EFRS93: the two-colour graph Ramsey number
`SimpleGraph.graphRamsey` and the notion of a *Ramsey size linear* graph
`SimpleGraph.IsRamseySizeLinear`, together with the elementary API needed by the
obstruction theory of `JSPProblem/MinimalObstruction.lean`:

* monotonicity of the Ramsey number in both arguments, and symmetry,
* downward closure of `IsRamseySizeLinear` under deletion of edges,
* `v H ≤ 2 * e H` for graphs without isolated vertices
  (`card_le_two_mul_realEdgeCount_of_noIsolatedVertex`).
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace SimpleGraph

universe u

variable {α : Type u}

/-- `(Cᶜ)ᶜ = C` for the graph complement. -/
theorem compl_compl_graph (C : SimpleGraph α) : Cᶜᶜ = C := by
  ext v w
  simp only [compl_adj]
  constructor
  · rintro ⟨hne, h⟩
    by_contra hc
    exact h ⟨hne, hc⟩
  · intro h
    exact ⟨C.ne_of_adj h, fun h' => (h'.2 h).elim⟩

/-! ### The two-colour graph Ramsey number -/

/--
`graphRamseySet G H` is the set of `n` such that every red/blue colouring of the edges of
`Kₙ` carries a red copy of `G` or a blue copy of `H`.

A colouring of the edges of `Kₙ` is represented by the graph `C` of its red edges; the
blue edges are `Cᶜ`.
-/
def graphRamseySet (G : SimpleGraph α) (H : SimpleGraph β) : Set ℕ :=
  { n | ∀ C : SimpleGraph (Fin n), G ⊑ C ∨ H ⊑ Cᶜ }

/--
`graphRamsey G H` is the two-colour Ramsey number: the least `n` such that every
2-colouring of the edges of `Kₙ` contains a copy of `G` in the first colour or a copy of
`H` in the second colour.

This is the classical vertex-based asymmetric Ramsey number, with the asymmetric colouring
convention used by EFRS93 and by Wigderson (2024).
-/
noncomputable def graphRamsey (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf (graphRamseySet G H)

theorem mem_graphRamseySet_iff {G : SimpleGraph α} {H : SimpleGraph β} {n : ℕ} :
    n ∈ graphRamseySet G H ↔ ∀ C : SimpleGraph (Fin n), G ⊑ C ∨ H ⊑ Cᶜ := Iff.rfl

/--
**The Ramsey number is attained.**  Provided some size `n` forces a copy of `G` or of `H`,
the least such size `graphRamsey G H` also forces it.  This is what makes it legitimate to
speak of the Ramsey number of a pair of graphs.
-/
theorem graphRamsey_mem {G : SimpleGraph α} {H : SimpleGraph β}
    (hne : (graphRamseySet G H).Nonempty) : graphRamsey G H ∈ graphRamseySet G H := by
  exact Nat.sInf_mem hne

/-- If `n` is a good size, the Ramsey number is at most `n`. -/
theorem graphRamsey_le {G : SimpleGraph α} {H : SimpleGraph β} {n : ℕ}
    (hn : n ∈ graphRamseySet G H) : graphRamsey G H ≤ n :=
  Nat.sInf_le hn

/--
**Monotonicity in the first argument.**  Deleting edges from `G` can only increase the
Ramsey number.
-/
theorem graphRamseySet_mono_left {G G' : SimpleGraph α} {H : SimpleGraph β} (h : G ≤ G') :
    graphRamseySet G' H ⊆ graphRamseySet G H := by
  intro n hn C
  rcases hn C with h1 | h2
  · exact Or.inl (IsContained.mono_left h h1)
  · exact Or.inr h2

theorem graphRamsey_anti_left {G G' : SimpleGraph α} {H : SimpleGraph β} (h : G ≤ G')
    (hne : (graphRamseySet G' H).Nonempty) : graphRamsey G H ≤ graphRamsey G' H :=
  Nat.sInf_le (graphRamseySet_mono_left h (Nat.sInf_mem hne))

/--
**Monotonicity in the second argument.**  Deleting edges from `H` can only decrease the
Ramsey number.
-/
theorem graphRamseySet_mono_right {G : SimpleGraph α} {H H' : SimpleGraph β} (h : H ≤ H') :
    graphRamseySet G H' ⊆ graphRamseySet G H := by
  intro n hn C
  rcases hn C with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (IsContained.mono_left h h2)

theorem graphRamsey_anti_right {G : SimpleGraph α} {H H' : SimpleGraph β} (h : H ≤ H')
    (hne : (graphRamseySet G H').Nonempty) : graphRamsey G H ≤ graphRamsey G H' :=
  Nat.sInf_le (graphRamseySet_mono_right h (Nat.sInf_mem hne))

/-- Symmetry of `graphRamseySet`. -/
theorem graphRamseySet_comm (G : SimpleGraph α) (H : SimpleGraph β) :
    graphRamseySet G H = graphRamseySet H G := by
  classical
  ext n
  constructor
  · intro h C
    rcases h Cᶜ with h1 | h2
    · exact Or.inr h1
    · exact Or.inl (by rwa [compl_compl_graph] at h2)
  · intro h C
    rcases h Cᶜ with h1 | h2
    · exact Or.inr h1
    · exact Or.inl (by rwa [compl_compl_graph] at h2)

/--
**Symmetry of the Ramsey number.**  Swapping the two colours swaps the two arguments, so
the numerical value of `r(G, H)` is symmetric even though the defining property is not.
-/
theorem graphRamsey_comm (G : SimpleGraph α) (H : SimpleGraph β) :
    graphRamsey G H = graphRamsey H G := by
  unfold graphRamsey
  rw [graphRamseySet_comm]

/--
**The Ramsey number depends only on the isomorphism class of `G`.**
-/
theorem graphRamseySet_congr_left {G G' : SimpleGraph α} (e : G ≃g G') (H : SimpleGraph β) :
    graphRamseySet G H = graphRamseySet G' H := by
  classical
  ext n
  constructor
  · intro h C
    rcases h C with h1 | h2
    · exact Or.inl ((isContained_congr e (SimpleGraph.Iso.refl : C ≃g C)).mp h1)
    · exact Or.inr h2
  · intro h C
    rcases h C with h1 | h2
    · exact Or.inl ((isContained_congr e (SimpleGraph.Iso.refl : C ≃g C)).mpr h1)
    · exact Or.inr h2

theorem graphRamsey_congr_left {G G' : SimpleGraph α} (e : G ≃g G') (H : SimpleGraph β) :
    graphRamsey G H = graphRamsey G' H := by
  unfold graphRamsey
  rw [graphRamseySet_congr_left e]

/-! ### Ramsey size linear graphs -/

/--
`H.NoIsolatedVertex` says that no vertex of `H` is isolated, i.e. every vertex of `H` is
incident to at least one edge.
-/
def NoIsolatedVertex (H : SimpleGraph α) : Prop := ∀ v, ∃ w, H.Adj v w

theorem noIsolatedVertex_iff {H : SimpleGraph α} (h : H.NoIsolatedVertex) (v : α) :
    ∃ w, H.Adj v w :=
  h v

theorem noIsolatedVertex_of_le {H H' : SimpleGraph α} (h : H' ≤ H) (h' : H'.NoIsolatedVertex) :
    H.NoIsolatedVertex := by
  intro v
  obtain ⟨w, hw⟩ := h' v
  exact ⟨w, by apply h; exact hw⟩

/--
A graph `G` is **Ramsey size linear** if there is a constant `c > 0` such that for all
graphs `H` with no isolated vertices, `R(G, H) ≤ c * e(H)`.

This is the definition of Erdős, Faudree, Rousseau and Schelp (1993), used verbatim by
Wigderson (2024).
-/
def IsRamseySizeLinear (G : SimpleGraph α) : Prop :=
  ∃ c > (0 : ℝ), ∀ (n : ℕ) (H : SimpleGraph (Fin n)), H.NoIsolatedVertex →
    (graphRamsey G H : ℝ) ≤ c * H.edgeSet.ncard

/--
**Ramsey numbers are finite.**  `hFiniteness` is the hypothesis that for every `H` with no
isolated vertices some size forces a copy of `G` or of `H`; for finite `G` and `H` this is
the finite Ramsey theorem.
-/
theorem IsRamseySizeLinear.mono_of_nonempty {G G' : SimpleGraph α} (h : G ≤ G')
    (hFiniteness : ∀ n (H : SimpleGraph (Fin n)), H.NoIsolatedVertex →
      (graphRamseySet G' H).Nonempty)
    (hG : G'.IsRamseySizeLinear) : G.IsRamseySizeLinear := by
  obtain ⟨c, hc, hH⟩ := hG
  refine ⟨c, hc, fun n H hn => ?_⟩
  have hle : graphRamsey G H ≤ graphRamsey G' H := graphRamsey_anti_left h (hFiniteness n H hn)
  exact le_trans (by exact_mod_cast hle) (hH n H hn)

/-! ### Elementary facts about `H` with no isolated vertices -/

/-- The number of edges of a finite graph, as a real number. -/
noncomputable def RealEdgeCount (H : SimpleGraph α) : ℝ := (H.edgeSet.ncard : ℝ)

theorem ncard_edgeSet_eq_card_edgeFinset (H : SimpleGraph α) [Fintype (Sym2 α)]
    [DecidableRel H.Adj] : H.edgeSet.ncard = H.edgeFinset.card := by
  rw [Set.ncard_eq_toFinset_card']
  rfl

theorem realEdgeCount_eq (H : SimpleGraph α) [Fintype (Sym2 α)] [DecidableRel H.Adj] :
    RealEdgeCount H = (H.edgeFinset.card : ℝ) := by
  simp only [RealEdgeCount, ncard_edgeSet_eq_card_edgeFinset]

/-- The degree-sum formula (`∑ deg = 2 e`), cast to `ℝ`. -/
theorem sum_degree_eq_two_mul_realEdgeCount {H : SimpleGraph α} [Fintype α]
    [DecidableRel H.Adj] : (∑ v, (H.degree v : ℝ)) = 2 * RealEdgeCount H := by
  have h := H.sum_degrees_eq_twice_card_edges
  have h' : (∑ v, (H.degree v : ℝ)) = 2 * (H.edgeFinset.card : ℝ) := by exact_mod_cast h
  rw [realEdgeCount_eq (H := H)]
  exact h'

/--
**Degree-sum bound.**  If `H` has no isolated vertices then `v H ≤ 2 * e H`.

Indeed `∑ v, deg v = 2 * e H` and every summand is at least `1`.  This is the reduction
step EFRS93 use to replace the second argument of the Ramsey number by a complete graph.
-/
theorem card_le_two_mul_realEdgeCount_of_noIsolatedVertex {H : SimpleGraph α} [Fintype α]
    [DecidableRel H.Adj] (h : H.NoIsolatedVertex) :
    (Fintype.card α : ℝ) ≤ 2 * RealEdgeCount H := by
  have hdeg : ∀ v, 0 < H.degree v := by
    intro v
    obtain ⟨w, hw⟩ := h v
    exact (H.degree_pos v).mpr hw.not_isIsolated_left
  have h1 : (1 : ℝ) * Fintype.card α ≤ ∑ v, (H.degree v : ℝ) := by
    calc (1 : ℝ) * Fintype.card α = ∑ _ : α, (1 : ℝ) := by simp
      _ ≤ ∑ v, (H.degree v : ℝ) :=
          Finset.sum_le_sum fun v _ => by
            have hd : (1 : ℝ) ≤ (H.degree v : ℝ) := by
              exact_mod_cast Nat.succ_le_of_lt (hdeg v)
            exact hd
  have h2 := sum_degree_eq_two_mul_realEdgeCount (H := H)
  linarith

/-- `IsRamseySizeLinear` only depends on the isomorphism class of its argument. -/
theorem IsRamseySizeLinear.congr {G G' : SimpleGraph α} (e : G ≃g G') :
    G.IsRamseySizeLinear ↔ G'.IsRamseySizeLinear := by
  constructor
  · rintro ⟨c, hc, hH⟩
    refine ⟨c, hc, fun n H hn => ?_⟩
    have key : (graphRamsey G' H : ℝ) ≤ c * (H.edgeSet.ncard : ℝ) := by
      rw [← graphRamsey_congr_left e]
      exact hH n H hn
    exact key
  · rintro ⟨c, hc, hH⟩
    refine ⟨c, hc, fun n H hn => ?_⟩
    have key : (graphRamsey G H : ℝ) ≤ c * (H.edgeSet.ncard : ℝ) := by
      rw [graphRamsey_congr_left e]
      exact hH n H hn
    exact key

/--
**Edge count of a complete graph.**  `e(Kₙ) = n (n-1) / 2`, the second argument family used
by EFRS93 and by [Wi24] to witness failure of Ramsey size linearity.
-/
theorem realEdgeCount_completeGraph (n : ℕ) :
    RealEdgeCount (completeGraph (Fin n)) = ((n.choose 2 : ℕ) : ℝ) := by
  classical
  have htop : (⊤ : SimpleGraph (Fin n)).edgeFinset.card = n.choose 2 := by
    have h := SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := (Fin n))
    simpa only [Fintype.card_fin] using h
  have hreal : RealEdgeCount (⊤ : SimpleGraph (Fin n)) = ((n.choose 2 : ℕ) : ℝ) := by
    rw [RealEdgeCount, ncard_edgeSet_eq_card_edgeFinset (H := (⊤ : SimpleGraph (Fin n))), htop]
  have h : RealEdgeCount (completeGraph (Fin n)) = RealEdgeCount (⊤ : SimpleGraph (Fin n)) := by
    have hset : (completeGraph (Fin n)).edgeSet = (⊤ : SimpleGraph (Fin n)).edgeSet :=
      congrArg SimpleGraph.edgeSet (completeGraph_eq_top (Fin n))
    unfold RealEdgeCount
    exact congrArg (fun t : Set (Sym2 (Fin n)) => (t.ncard : ℝ)) hset
  rw [h, hreal]

/--
**The EFRS reduction, instantiated at complete graphs.**  A complete graph on `n` vertices
has `n(n-1)/2` edges and `n` vertices, so the degree-sum bound reads `n ≤ n(n-1)`.

This is exactly the reduction EFRS93 and [Wi24] use: the second Ramsey argument `H` may be
replaced by a complete graph of order at most `2 e(H)`, and the edge count of the latter is
`Θ(n²)`.
-/
theorem card_completeGraph_le_two_mul_realEdgeCount (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) ≤ 2 * RealEdgeCount (completeGraph (Fin n)) := by
  have h := realEdgeCount_completeGraph n
  rw [h]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [Nat.cast_choose_two]
  nlinarith

/-- Every graph is a spanning subgraph of the complete graph on the same vertex set. -/
theorem isContained_completeGraph (H : SimpleGraph α) : H ⊑ (completeGraph α) :=
  IsContained.of_le le_top

end SimpleGraph
