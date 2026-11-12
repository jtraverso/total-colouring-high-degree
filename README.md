# Total colourings of graphs of high maximum degree in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A total colouring of a graph gives colours to vertices and edges so that adjacent vertices,
adjacent edges and incident vertex–edge pairs get different colours. The total colouring
conjecture (Behzad, Vizing) says that `Δ(G) + 2` colours suffice. This package proves it for
graphs whose maximum degree is close to the number of vertices, following

* H. P. Yap, Wang Jian-Fang, Zhang Zhongfu, *Total chromatic number of graphs of high degree*,
  J. Austral. Math. Soc. (A) 47 (1989) 445–452, doi:10.1017/S1446788700033176;
* H. P. Yap, K. H. Chew, *Total chromatic number of graphs of high degree, II*, J. Austral.
  Math. Soc. (A) 53 (1992) 219–228, doi:10.1017/S1446788700035801 (Lemma 2.4).

## Statements (`TCCHighChallenge.lean`, namespace `TCCHigh`)

```lean
def IsTotalColoring (G : SimpleGraph V) {α : Type*} (c : V ⊕ G.edgeSet → α) : Prop := ...

theorem tcc_of_independent (S : Finset V) (hS : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v)
    (hcard : Fintype.card V ≤ #S + G.maxDegree + 1) :
    ∃ c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2), IsTotalColoring G c

theorem tcc_of_card_le_maxDegree_add_three (h : Fintype.card V ≤ G.maxDegree + 3) :
    ∃ c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2), IsTotalColoring G c

theorem tcc_of_card_le_maxDegree_add_four (h : Fintype.card V ≤ G.maxDegree + 4)
    (hcase : 7 ≤ G.maxDegree ∨ ∃ S : Finset V, #S = 3 ∧ ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v) :
    ∃ c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2), IsTotalColoring G c
```

**Not covered:** `Δ(G) = |V| − 4` with `|V| ≤ 10` and no three pairwise non-adjacent vertices.
These are the complements of the triangle-free graphs of minimum degree 3 on at most 10 vertices
(232 graphs up to isomorphism); `scripts/` checks by brute force that each of them has a
`(Δ + 2)`-total colouring and that the construction of the proof works for them, but this is not
formalized. Yap–Chew's main theorem (`Δ = |V| − 5`) is not formalized.

## Proof

* **Apex graph** (`TCCHigh/Basic.lean`, Yap's technique): delete a set `F` of edges from `G` and
  add a vertex `c*` joined to a set `W`. A proper `K`-edge colouring of this graph, together with a
  total colouring of the vertices outside `W` and the edges of `F` with `t` new colours, gives a
  total colouring of `G` with `K + t` colours (each `v ∈ W` takes the colour of `c*v`).
* **One class** (`TCCHigh/Level1.lean`): with `S` independent, `|S| ≥ |V| − Δ − 1`, and a matching
  `M` of `G − S` covering as many vertices of degree `Δ` as possible, the vertices of degree `Δ + 1`
  of `G − M + c*·(V ∖ S)` span a star, so Fournier's theorem colours its edges with `Δ + 1`
  colours. For `Δ ≥ |V| − 3` take `S = ∅` or a non-adjacent pair.
* **Two classes** (`TCCHigh/Matching.lean`, `TCCHigh/Level2.lean`): for `|V| = Δ + 4`, two
  non-adjacent pairs `S₁`, `S₂` and coverage-maximal matchings `M₁ ⊆ G − S₁`, `M₂ ⊆ G − M₁ − S₂`.
  The enlarge-matching argument leaves at most one critical vertex uncovered at each step when
  `Δ ≥ 7`; the second pair is chosen through the first uncovered vertex, and the vertices of degree
  `Δ` of the apex graph again span a forest.

Dependencies (pinned, no code copied): Fournier's theorem, PALOMAR-2026-11-08-000009
(jtraverso/fournier-class-one @ b7baf7b), which brings Vizing's theorem (PALOMAR-2026-10-15-000004)
and Vizing's adjacency lemma (PALOMAR-2026-11-04-000009).

## Building

Lean `v4.35.0-rc3`, Mathlib `v4.35.0-rc3`:

```
lake exe cache get
lake build
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
