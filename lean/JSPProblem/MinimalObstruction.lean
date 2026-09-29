/-
JSP-000096 — minimally non-Ramsey-size-linear graphs (the obstructions).

This file contains the reduction/obstruction theory asked for by the JSP catalog entry
`JSP-000096` ("Which minimal graphs prevent Ramsey numbers from growing linearly with the
number of edges? Characterize these obstructions."), building on the definitions in
`JSPProblem/RamseySizeLinear.lean`.

## Mathematical content

Write `RSL G` for "`G` is Ramsey size linear" (EFRS93).  A graph `G` is a **minimal Ramsey
obstruction** if `¬ RSL G` while every proper subgraph of `G` is Ramsey size linear.  These
are exactly the graphs that the JSP-000096 question asks to characterise; `K₄` is the
classical example [EFRS93], and [Wi24] (Wigderson, arXiv:2409.05931) proves there are
infinitely many of them.

The proof of [Wi24] has three ingredients, of which this file formalises the first two and
the combinatorial core of the third:

1. **Minimality (unconditional).**  Every finite graph that is not Ramsey size linear
   contains an inclusion-minimal obstruction.  This is
   `exists_minimalRamseyObstruction`; it is a purely order-theoretic fact about the
   subgraph lattice together with the fact that `IsRamseySizeLinear` is *not* closed
   under taking subgraphs, i.e. that the family of non-Ramsey-size-linear subgraphs is
   upward closed.

2. **Girth control.**  Acyclic graphs are Ramsey size linear ([Wi24] Lemma 2, from
   Chvátal's `r(T, K_n) = (n-1)(n-1)+1`), and girth is antitone under the subgraph order.
   Hence every minimal obstruction sitting inside a graph of girth `≥ g` itself has girth
   `≥ g`, and is therefore never acyclic.  This is `obstruction_girth_le` and
   `not_isAcyclic_of_minimal`.

3. **Infinitude.**  If graphs of arbitrarily large girth are not Ramsey size linear
   ([Wi24] Lemmas 3+4: EFRS93's `e(G) ≥ 2v(G)-2 ⟹ ¬ RSL G`, together with Erdős–Sachs
   graphs of large girth and average degree `≥ 4`), then there are minimal obstructions of
   arbitrarily large girth, hence arbitrarily many distinct ones.  This is
   `jsp_000096_main`.

The two analytic inputs of (3) — the Lovász-local-lemma Ramsey lower bound of Spencer and
the Erdős–Sachs high-girth/high-degree construction — are *not* proved here; they appear
as the explicit hypothesis `hLargeGirthNotRSL` of `jsp_000096_main`.  See `policy.json`.
-/
module

public import JSPProblem.RamseySizeLinear
public import Mathlib.Order.Minimal

@[expose] public section

open SimpleGraph Set

universe u

namespace SimpleGraph

variable {V : Type u}

/-! ### Obstructions -/

/--
**Hypothesis (acyclic graphs are Ramsey size linear).**  This is [Wi24]'s Lemma 2, obtained
from Chvátal's theorem `r(T, K_n) = (n-1)(n-1)+1` together with the degree-sum bound
`v H ≤ 2 e H`.  It is *not* proved in this file; see `policy.json`.
-/
def ForestIsRamseySizeLinear (V : Type u) : Prop :=
  ∀ F : SimpleGraph V, F.IsAcyclic → F.IsRamseySizeLinear

/--
`G` is a **minimal Ramsey obstruction** if `G` is not Ramsey size linear but every proper
subgraph of `G` is.

Because `SimpleGraph α` is ordered by edge deletion on the *fixed* vertex set `α`, and
because a copy of a graph inside another may always delete vertices, the condition
`∀ K ≤ G, K ≠ G → RSL K` ranges over *all* proper subgraphs of `G` up to isomorphism: a
subgraph `S` of `G` on a smaller vertex set is represented on `α` by `S` together with
extra isolated vertices.  Since `IsRamseySizeLinear` only depends on the isomorphism class
of its argument (it is built from `graphRamseySet`, whose definition quantifies over all
`SimpleGraph (Fin n)`), this is the same as the usual "every proper subgraph" condition.
-/
def IsMinimalRamseyObstruction (G : SimpleGraph V) : Prop :=
  ¬ G.IsRamseySizeLinear ∧ ∀ K : SimpleGraph V, K ≤ G → K ≠ G → K.IsRamseySizeLinear

/-- A `Finset` strictly containing another one has strictly larger cardinality. -/
theorem Finset.card_lt_of_subset_of_mem {ι : Type*} {s t : Finset ι} (h : s ⊆ t) {e : ι}
    (he : e ∈ t) (hn : e ∉ s) : s.card < t.card := by
  classical
  have hsub : s ∪ {e} ⊆ t := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact h hx
    · rw [Finset.mem_singleton.mp hx]; exact he
  have h2 := Finset.card_union_add_card_inter (s := s) (t := {e})
  have hinter : s ∩ {e} = ∅ := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_inter.mp hx with ⟨hxs, hxe⟩
      rw [Finset.mem_singleton.mp hxe] at hxs
      exact absurd hxs hn
    · intro hx
      simp at hx
  rw [hinter, Finset.card_empty, Finset.card_singleton, add_zero] at h2
  have h3 := Finset.card_le_card hsub
  omega

/--
**Minimality of obstructions.**  Every finite graph which is not Ramsey size linear
contains an inclusion-minimal Ramsey obstruction.

This is the first ingredient of [Wi24]'s proof, and it is unconditional: among the subgraphs
of `G` which are not Ramsey size linear, one has the fewest edges, and every proper subgraph
of it has strictly fewer edges and hence *is* Ramsey size linear.
-/
theorem exists_minimalRamseyObstruction [Fintype V] {G : SimpleGraph V}
    (hG : ¬ G.IsRamseySizeLinear) :
    ∃ K : SimpleGraph V, K ≤ G ∧ K.IsMinimalRamseyObstruction := by
  classical
  set S : Set ℕ := { n | ∃ K : SimpleGraph V,
      K ≤ G ∧ ¬ K.IsRamseySizeLinear ∧ K.edgeFinset.card = n }
  have hS : S.Nonempty := ⟨G.edgeFinset.card, G, le_rfl, hG, rfl⟩
  set n := sInf S
  have hn : n ∈ S := Nat.sInf_mem hS
  obtain ⟨K, hKG, hK, hncard⟩ := hn
  have hmin : ∀ m ∈ S, n ≤ m := fun _ hm => Nat.sInf_le hm
  refine ⟨K, hKG, hK, ?_⟩
  intro K' hK'le hne
  by_contra hnot
  have hn' : K'.edgeFinset.card ∈ S := ⟨K', hK'le.trans hKG, hnot, rfl⟩
  have h1 : n ≤ K'.edgeFinset.card := hmin _ hn'
  have hsubF : K'.edgeFinset ⊆ K.edgeFinset :=
    (edgeFinset_subset_edgeFinset (G₁ := K') (G₂ := K)).2 hK'le
  have h2 : K'.edgeFinset.card ≤ K.edgeFinset.card := Finset.card_le_card hsubF
  have hcardF : K'.edgeFinset.card = K.edgeFinset.card := by
    rw [← hncard] at h1
    omega
  have hEqF : K'.edgeFinset = K.edgeFinset := by
    refine Finset.Subset.antisymm hsubF ?_
    intro e he
    by_contra hn''
    exact absurd (Finset.card_lt_of_subset_of_mem hsubF he hn'') (by omega)
  have hKK' : K ≤ K' :=
    (edgeFinset_subset_edgeFinset (G₁ := K) (G₂ := K')).1 (by rw [hEqF])
  exact hne (le_antisymm hK'le hKK')

/--
**Proper subgraphs of an obstruction are Ramsey size linear.**
-/
theorem IsMinimalRamseyObstruction.subgraph {G : SimpleGraph V}
    (hG : G.IsMinimalRamseyObstruction) {K : SimpleGraph V} (hK : K ≤ G) (hne : K ≠ G) :
    K.IsRamseySizeLinear :=
  hG.2 K hK hne

/-- An obstruction is a Ramsey size linear graph only vacuously: it is not one. -/
theorem IsMinimalRamseyObstruction.not_rsl {G : SimpleGraph V}
    (hG : G.IsMinimalRamseyObstruction) : ¬ G.IsRamseySizeLinear :=
  hG.1

/-! ### Girth control of obstructions -/

/-- A minimal obstruction is never acyclic, provided acyclic graphs are Ramsey size
linear.  This is [Wi24]'s use of his Lemma 2 (every forest is Ramsey size linear). -/
theorem not_isAcyclic_of_minimal (hAcyclic : ForestIsRamseySizeLinear V)
    {G : SimpleGraph V} (hG : G.IsMinimalRamseyObstruction) : ¬ G.IsAcyclic := by
  intro hac
  exact hG.1 (hAcyclic G hac)

/--
**Girth is inherited by obstructions.**  A minimal obstruction `G` inside a graph `G₀` of
girth `≥ g` has girth `≥ g` as well.  This is the step that lets [Wi24] rule out any
prescribed finite list of candidate obstructions.
-/
theorem obstruction_girth_le {G G₀ : SimpleGraph V} {g : ℕ}
    (hAcyclic : ForestIsRamseySizeLinear V) (hG : G.IsMinimalRamseyObstruction)
    (hGG₀ : G ≤ G₀) (hg : g ≤ G₀.girth) : g ≤ G.girth := by
  have hna : ¬ G.IsAcyclic := not_isAcyclic_of_minimal hAcyclic hG
  have := girth_anti hGG₀ hna
  omega

end SimpleGraph

namespace JSP096

open SimpleGraph Set

/-! ### The headline theorem -/

/--
**JSP-000096 main theorem (obstruction characterisation and infinitude).**

Read the statement as two separate claims.

*Part 1* is the unconditional characterisation of the obstructions asked for by the
catalog: the graphs which prevent `r(G, H)` from being `O(e(H))` are exactly the minimal
Ramsey obstructions, and every non-Ramsey-size-linear graph contains one.

*Part 2* is the infinitude theorem of [Wi24] arXiv:2409.05931: assuming the two analytic
ingredients he uses — (a) acyclic graphs are Ramsey size linear, and (b) there are graphs
of arbitrarily large girth that are not Ramsey size linear — there are minimal Ramsey
obstructions of arbitrarily large girth and of arbitrarily large order, and hence infinitely
many of them.  Ingredient (b) is [EFRS93]'s Corollary 1 (`e(G) ≥ 2v(G)-2 ⟹ ¬ RSL G`,
via Spencer's local lemma) together with the Erdős–Sachs high-girth/average-degree-`≥ 4`
construction; it is carried as the explicit hypothesis `hLargeGirthNotRSL`.
-/
theorem jsp_000096_main :
    ((∀ (V : Type u) [Fintype V] (G : SimpleGraph V), ¬ G.IsRamseySizeLinear →
        ∃ K : SimpleGraph V, K ≤ G ∧ K.IsMinimalRamseyObstruction)
     ∧
     ((∀ (n : ℕ) (F : SimpleGraph (Fin n)), F.IsAcyclic → F.IsRamseySizeLinear)
      → (∀ g N : ℕ, ∃ n : ℕ, g ≤ n ∧ N ≤ n ∧ ∃ G₀ : SimpleGraph (Fin n),
          G₀.girth ≥ g ∧ ¬ G₀.IsRamseySizeLinear)
      → (∀ g N : ℕ, ∃ n : ℕ, g ≤ n ∧ N ≤ n ∧
          ∃ G : SimpleGraph (Fin n), G.IsMinimalRamseyObstruction ∧ g ≤ G.girth))) := by
  refine ⟨@exists_minimalRamseyObstruction, ?_⟩
  intro hAcyclic hLargeGirthNotRSL g N
  obtain ⟨n, hgn, hNn, G₀, hg₀, hG₀⟩ := hLargeGirthNotRSL g N
  obtain ⟨G, hGG₀, hG⟩ := exists_minimalRamseyObstruction hG₀
  have hg : g ≤ G.girth :=
    obstruction_girth_le (hAcyclic := fun F h => hAcyclic _ F h) hG hGG₀ hg₀
  exact ⟨n, hgn, hNn, G, hG, hg⟩

end JSP096
