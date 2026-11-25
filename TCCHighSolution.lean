/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import TCCHigh.Main

/-!
# Proofs of the statements in `TCCHighChallenge.lean`

The proofs are in `TCCHigh/` (`TCCHighLib` namespace): the apex-graph assembly
(`TCCHigh/Basic.lean`), one colour class (`TCCHigh/Level1.lean`), the enlarge-matching argument
(`TCCHigh/Matching.lean`) and two colour classes (`TCCHigh/Level2.lean`). Edge colourings of the
apex graph come from Vizing's theorem (jtraverso/vizing, PALOMAR-2026-10-15-000004) and Fournier's
theorem (jtraverso/fournier-class-one, PALOMAR-2026-11-08-000009), both lake dependencies.
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
  obtain ⟨c, hc⟩ := TCCHighLib.tcc_of_indep G S hS hcard
  exact ⟨c, hc⟩

/-- **Total colouring conjecture for `Δ(G) ≥ |V| − 3`** (Yap–Wang–Zhang 1989). -/
theorem tcc_of_card_le_maxDegree_add_three [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : Fintype.card V ≤ G.maxDegree + 3) :
    ∃ c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2), IsTotalColoring G c := by
  obtain ⟨c, hc⟩ := TCCHighLib.tcc_of_card_le_add_three G h
  exact ⟨c, hc⟩

/-- **Total colouring conjecture for `Δ(G) ≥ |V| − 4`** (Yap–Wang–Zhang 1989, Theorem 2.4, with the
case without three pairwise non-adjacent vertices for `Δ(G) ≤ 6` completed here). -/
theorem tcc_of_card_le_maxDegree_add_four [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : Fintype.card V ≤ G.maxDegree + 4) :
    ∃ c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2), IsTotalColoring G c := by
  obtain ⟨c, hc⟩ := TCCHighLib.tcc_of_card_le_add_four G h
  exact ⟨c, hc⟩

end TCCHigh
