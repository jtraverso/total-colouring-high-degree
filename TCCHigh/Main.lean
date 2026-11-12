/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import TCCHigh.Level2

/-!
# The total colouring conjecture for `Δ(G) ≥ |V| − 4` (main cases)

* `|V| ≤ Δ + 3`: `tcc_of_card_le_add_three` (Yap–Wang–Zhang 1989, Theorem 2.3 and remarks).
* `|V| = Δ + 4` and `G` has three pairwise non-adjacent vertices: `tcc_of_indep` (the first case
  of Yap–Wang–Zhang 1989, Theorem 2.4).
* `|V| = Δ + 4` and `Δ ≥ 7`: `tcc_two_level` (the second case of Theorem 2.4, for `|V| ≥ 11`).
-/

@[expose] public section

namespace TCCHighLib

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Total colouring conjecture for `Δ(G) ≥ |V| − 4`**, when `Δ ≥ 7` or `G` has three pairwise
non-adjacent vertices. -/
theorem tcc_of_card_le_add_four (h : Fintype.card V ≤ G.maxDegree + 4)
    (hcase : 7 ≤ G.maxDegree ∨ ∃ S : Finset V, #S = 3 ∧ ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v) :
    ∃ c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2), IsTotalColoring G c := by
  by_cases h3 : Fintype.card V ≤ G.maxDegree + 3
  · exact tcc_of_card_le_add_three G h3
  · rcases hcase with h7 | ⟨S, hS, hind⟩
    · exact tcc_two_level G (by omega) h7
    · exact tcc_of_indep G S hind (by omega)

end TCCHighLib
