/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Total colourings of graphs of high maximum degree (statements)

H. P. Yap, Wang Jian-Fang and Zhang Zhongfu, *Total chromatic number of graphs of high degree*,
J. Austral. Math. Soc. (Series A) 47 (1989) 445–452, doi:10.1017/S1446788700033176;
H. P. Yap and K. H. Chew, *Total chromatic number of graphs of high degree, II*, J. Austral.
Math. Soc. (Series A) 53 (1992) 219–228, doi:10.1017/S1446788700035801.

A total colouring is a map on `V ⊕ E(G)` such that adjacent vertices, adjacent (distinct, sharing
an endpoint) edges, and incident vertex–edge pairs receive different colours. The total colouring
conjecture asserts a total colouring with `Δ(G) + 2` colours.

1. `tcc_of_independent` (Yap–Wang–Zhang, Lemma 2.2; Yap–Chew, Lemma 2.4): an independent set of
   size at least `|V| − Δ − 1` gives a total colouring with `Δ + 2` colours.
2. `tcc_of_card_le_maxDegree_add_three` (Yap–Wang–Zhang, Theorem 2.3 and the closing remarks):
   the conjecture holds when `Δ(G) ≥ |V| − 3`.
3. `tcc_of_card_le_maxDegree_add_four` (Yap–Wang–Zhang, Theorem 2.4): the conjecture holds for
   every finite simple graph with `Δ(G) ≥ |V| − 4`, with no further hypothesis. (The proof treats
   `Δ(G) ≥ 7` or three pairwise non-adjacent vertices by the enlarge-matching argument, and the
   remaining graphs, e.g. the complement of a 7-cycle, by alternating matchings of a Hamiltonian
   path; these are proof cases only, not restrictions of the statement.)
-/

@[expose] public section

namespace TCCHigh

open Finset

variable {V : Type*}

/-- `c : V ⊕ G.edgeSet → α` is a total colouring of `G`: adjacent vertices get different
colours, distinct edges with a common endpoint get different colours, and every vertex gets a
colour different from the colours of the edges incident to it. -/
def IsTotalColoring (G : SimpleGraph V) {α : Type*} (c : V ⊕ G.edgeSet → α) : Prop :=
  (∀ u v : V, G.Adj u v → c (Sum.inl u) ≠ c (Sum.inl v)) ∧
  (∀ e f : G.edgeSet, e ≠ f → ∀ v : V, v ∈ (e : Sym2 V) → v ∈ (f : Sym2 V) →
      c (Sum.inr e) ≠ c (Sum.inr f)) ∧
  (∀ (v : V) (e : G.edgeSet), v ∈ (e : Sym2 V) → c (Sum.inl v) ≠ c (Sum.inr e))

/-- **Yap–Wang–Zhang, Lemma 2.2 / Yap–Chew, Lemma 2.4.** An independent set `S` with
`|V| ≤ |S| + Δ + 1` gives a total colouring with `Δ + 2` colours. -/
theorem tcc_of_independent [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v)
    (hcard : Fintype.card V ≤ #S + G.maxDegree + 1) :
    ∃ c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2), IsTotalColoring G c := by
  sorry

/-- **Total colouring conjecture for `Δ(G) ≥ |V| − 3`** (Yap–Wang–Zhang 1989). -/
theorem tcc_of_card_le_maxDegree_add_three [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : Fintype.card V ≤ G.maxDegree + 3) :
    ∃ c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2), IsTotalColoring G c := by
  sorry

/-- **Total colouring conjecture for `Δ(G) ≥ |V| − 4`** (Yap–Wang–Zhang 1989, Theorem 2.4, with the
case without three pairwise non-adjacent vertices for `Δ(G) ≤ 6` completed here). -/
theorem tcc_of_card_le_maxDegree_add_four [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : Fintype.card V ≤ G.maxDegree + 4) :
    ∃ c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2), IsTotalColoring G c := by
  sorry

end TCCHigh
