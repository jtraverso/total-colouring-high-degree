/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import TCCHigh.Paths

/-!
# Two colour classes for `|V| = Δ + 4`

The apex construction with two vertex classes: two disjoint non-adjacent pairs
`S₁ = {x, y}`, `S₂ = {s, t}` receive the colours `Δ + 1` and `Δ + 2`, together with edge-disjoint
matchings `M₁` (avoiding `S₁`) and `M₂` (avoiding `S₂`), and the apex graph
`G − M₁ − M₂ + c*·W`, `W = V ∖ (S₁ ∪ S₂)`, `|W| = Δ`, is edge coloured with `Δ` colours.

`tcc_frame` assumes that every vertex of `W` except possibly one vertex `r` is covered by both
matchings, that `r` (if it lies in `W`) is covered by at least one, and that two vertices other
than `r` covered by neither matching are not adjacent. Then the vertices of degree `Δ` of the
apex graph are `c*`, possibly `r`, and vertices of `S₁ ∪ S₂` covered by neither matching; every
edge among them contains `r`, so they span a forest and Fournier's theorem applies (or
Vizing's theorem if the maximum degree drops).
-/

@[expose] public section

namespace TCCHighLib

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Two-class apex construction** for `|V| = Δ + 4`. -/
theorem tcc_frame (hn : Fintype.card V = G.maxDegree + 4) (x y s t : V)
    (hxy : x ≠ y) (hxs : x ≠ s) (hxt : x ≠ t) (hys : y ≠ s) (hyt : y ≠ t) (hst : s ≠ t)
    (hnxy : ¬ G.Adj x y) (hnst : ¬ G.Adj s t)
    (M₁ M₂ : Finset (Sym2 V)) (hM₁ : IsMatchingAvoiding G M₁ {x, y})
    (hM₂ : IsMatchingAvoiding G M₂ {s, t}) (hdisj : Disjoint M₁ M₂) (r : V)
    (hW : ∀ v, v ≠ x → v ≠ y → v ≠ s → v ≠ t → v ≠ r → Covered M₁ v ∧ Covered M₂ v)
    (hr : r ≠ x → r ≠ y → r ≠ s → r ≠ t → Covered M₁ r ∨ Covered M₂ r)
    (hU : ∀ u v, u ≠ r → v ≠ r → ¬ Covered M₁ u → ¬ Covered M₂ u → ¬ Covered M₁ v →
      ¬ Covered M₂ v → ¬ G.Adj u v) :
    ∃ c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2), IsTotalColoring G c := by
  classical
  set Δ := G.maxDegree with hΔdef
  set S₁ : Finset V := {x, y} with hS₁
  set S₂ : Finset V := {s, t} with hS₂
  set W : Finset V := univ.filter fun v => v ∉ S₁ ∧ v ∉ S₂ with hWdef
  have hmemW : ∀ v, v ∈ W ↔ v ≠ x ∧ v ≠ y ∧ v ≠ s ∧ v ≠ t := by
    intro v
    simp only [hWdef, hS₁, hS₂, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    tauto
  have hWcard : #W = Δ := by
    have h1 : #W + #(S₁ ∪ S₂) = Fintype.card V := by
      have h := card_filter_add_card_filter_not (s := (univ : Finset V))
        (fun v => v ∉ S₁ ∧ v ∉ S₂)
      have he : (univ.filter fun v => ¬ (v ∉ S₁ ∧ v ∉ S₂)) = S₁ ∪ S₂ := by
        ext v; simp only [mem_filter, mem_univ, true_and, mem_union]; tauto
      rw [he, card_univ] at h
      exact h
    have h2 : #(S₁ ∪ S₂) = 4 := by
      have he : S₁ ∪ S₂ = {x, y, s, t} := by
        ext v; simp only [hS₁, hS₂, mem_union, mem_insert, mem_singleton]; tauto
      rw [he, card_insert_of_notMem (by simp [hxy, hxs, hxt]),
        card_insert_of_notMem (by simp [hys, hyt]), card_pair hst]
    omega
  have hS₁ind : ∀ a ∈ S₁, ∀ b ∈ S₁, ¬ G.Adj a b := by
    intro a ha b hb hab
    simp only [hS₁, mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact G.irrefl hab
    · exact hnxy hab
    · exact hnxy hab.symm
    · exact G.irrefl hab
  have hS₂ind : ∀ a ∈ S₂, ∀ b ∈ S₂, ¬ G.Adj a b := by
    intro a ha b hb hab
    simp only [hS₂, mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact G.irrefl hab
    · exact hnst hab
    · exact hnst hab.symm
    · exact G.irrefl hab
  have hdisjS : ∀ v, v ∈ S₂ → v ∉ S₁ := by
    intro v hv
    simp only [hS₂, hS₁, mem_insert, mem_singleton] at hv ⊢
    rcases hv with rfl | rfl
    · rintro (h | h)
      · exact hxs h.symm
      · exact hys h.symm
    · rintro (h | h)
      · exact hxt h.symm
      · exact hyt h.symm
  set F : Finset (Sym2 V) := M₁ ∪ M₂ with hF
  set G' := apex G (F : Set (Sym2 V)) (W : Set V) with hG'
  have hdegnone : G'.degree none = Δ := by
    rw [← hWcard]; exact apex_degree_none G F W
  have hq1 : ∀ v, (Covered M₁ v ∨ Covered M₂ v) →
      #((G.neighborFinset v).filter fun u => s(v, u) ∉ F) + 1 ≤ G.degree v := by
    intro v hv
    rcases hv with ⟨e, he, hve⟩ | ⟨e, he, hve⟩
    · obtain ⟨w, rfl⟩ : ∃ w, e = s(v, w) := (Sym2.mem_iff_exists.mp hve).imp fun w h => h
      exact card_filter_nbr_le_pred G F v w (hM₁.1 _ he) (mem_union_left _ he)
    · obtain ⟨w, rfl⟩ : ∃ w, e = s(v, w) := (Sym2.mem_iff_exists.mp hve).imp fun w h => h
      exact card_filter_nbr_le_pred G F v w (hM₂.1 _ he) (mem_union_right _ he)
  have hq2 : ∀ v, Covered M₁ v → Covered M₂ v →
      #((G.neighborFinset v).filter fun u => s(v, u) ∉ F) + 2 ≤ G.degree v := by
    rintro v ⟨e, he, hve⟩ ⟨f, hf, hvf⟩
    obtain ⟨w, rfl⟩ : ∃ w, e = s(v, w) := (Sym2.mem_iff_exists.mp hve).imp fun w h => h
    obtain ⟨w', rfl⟩ : ∃ w', f = s(v, w') := (Sym2.mem_iff_exists.mp hvf).imp fun w h => h
    have hne : w ≠ w' := by
      rintro rfl
      exact disjoint_left.mp hdisj he hf
    exact card_filter_nbr_le_pred2 G F v w w' (hM₁.1 _ he) (hM₂.1 _ hf) hne
      (mem_union_left _ he) (mem_union_right _ hf)
  have hdegsome : ∀ v, G'.degree (some v) ≤ Δ ∧ (G'.degree (some v) = Δ →
      v = r ∨ (v ∉ W ∧ ¬ Covered M₁ v ∧ ¬ Covered M₂ v)) := by
    intro v
    have h0 : G'.degree (some v) =
        (if v ∈ W then 1 else 0) + #((G.neighborFinset v).filter fun u => s(v, u) ∉ F) :=
      apex_degree_some G F W v
    rw [h0]
    have hd := G.degree_le_maxDegree v
    have hqv := card_filter_nbr_le G F v
    by_cases hvW : v ∈ W
    · simp only [hvW, ite_true]
      obtain ⟨h1, h2, h3, h4⟩ := (hmemW v).mp hvW
      by_cases hvr : v = r
      · have hc := hr (hvr ▸ h1) (hvr ▸ h2) (hvr ▸ h3) (hvr ▸ h4)
        rw [← hvr] at hc
        have := hq1 v hc
        exact ⟨by omega, fun _ => Or.inl hvr⟩
      · have hc := hW v h1 h2 h3 h4 hvr
        have := hq2 v hc.1 hc.2
        exact ⟨by omega, fun h => by omega⟩
    · simp only [hvW, ite_false, zero_add]
      refine ⟨by omega, fun heq => Or.inr ⟨id, fun hc => ?_, fun hc => ?_⟩⟩
      · have := hq1 v (Or.inl hc); omega
      · have := hq1 v (Or.inr hc); omega
  have hmaxdeg : G'.maxDegree ≤ Δ := by
    refine maxDegree_le_of_forall_degree_le _ _ fun z => ?_
    cases z with
    | none => exact hdegnone.le
    | some v => exact (hdegsome v).1
  have hcol : G'.lineGraph.Colorable Δ := by
    by_cases hlt : G'.maxDegree < Δ
    · exact (LeanPool.Vizing.lineGraph_colorable G').mono (by omega)
    · have heq : G'.maxDegree = Δ := by omega
      rw [← heq]
      refine FournierLib.fournier G' ?_
      refine isAcyclic_of_forall_adj _ (fun z => (z : Option V) = some r) ?_ ?_
      · rintro a b ha hb
        exact Subtype.ext (ha.trans hb.symm)
      · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
        simp only [Set.mem_setOf_eq] at ha hb
        change G'.Adj a b at hab
        rw [heq] at ha hb
        cases a with
        | none =>
          cases b with
          | none => exact absurd hab (apex_none_none _ _ _)
          | some w =>
            have hwW : w ∈ W := hab
            rcases (hdegsome w).2 hb with h | h
            · exact Or.inr (by simp [h])
            · exact absurd hwW h.1
        | some v =>
          cases b with
          | none =>
            have hvW : v ∈ W := hab
            rcases (hdegsome v).2 ha with h | h
            · exact Or.inl (by simp [h])
            · exact absurd hvW h.1
          | some w =>
            by_cases hvr : v = r
            · exact Or.inl (by simp [hvr])
            by_cases hwr : w = r
            · exact Or.inr (by simp [hwr])
            have h := ((hdegsome v).2 ha).resolve_left hvr
            have h' := ((hdegsome w).2 hb).resolve_left hwr
            exact absurd hab.1 (hU v w hvr hwr h.2.1 h.2.2 h'.2.1 h'.2.2)
  obtain ⟨c, hc⟩ := total_of_apex G (F : Set (Sym2 V)) (W : Set V) Δ 2 hcol
    (fun v => if v ∈ S₁ then 0 else 1) (fun e => if e ∈ M₁ then 0 else 1)
    (by
      intro u v hu hv huv
      have hu' : u ∈ S₁ ∨ u ∈ S₂ := by
        by_contra h; push_neg at h; exact hu (mem_filter.mpr ⟨mem_univ _, h.1, h.2⟩)
      have hv' : v ∈ S₁ ∨ v ∈ S₂ := by
        by_contra h; push_neg at h; exact hv (mem_filter.mpr ⟨mem_univ _, h.1, h.2⟩)
      rcases hu' with hu1 | hu2 <;> rcases hv' with hv1 | hv2
      · exact absurd huv (hS₁ind u hu1 v hv1)
      · simp [hu1, hdisjS v hv2]
      · simp [hv1, hdisjS u hu2]
      · exact absurd huv (hS₂ind u hu2 v hv2))
    (by
      intro e he f hf hef v hve hvf
      simp only [hF, coe_union, Set.mem_union, mem_coe] at he hf
      by_cases he1 : e ∈ M₁ <;> by_cases hf1 : f ∈ M₁
      · exact absurd hvf (hM₁.2.1 e he1 f hf1 hef v hve)
      · simp [he1, hf1]
      · simp [he1, hf1]
      · have he2 : e ∈ M₂ := he.resolve_left he1
        have hf2 : f ∈ M₂ := hf.resolve_left hf1
        exact absurd hvf (hM₂.2.1 e he2 f hf2 hef v hve))
    (by
      intro v hv e he hve
      simp only [hF, coe_union, Set.mem_union, mem_coe] at he
      have hv' : v ∈ S₁ ∨ v ∈ S₂ := by
        by_contra h; push_neg at h; exact hv (mem_filter.mpr ⟨mem_univ _, h.1, h.2⟩)
      rcases hv' with hv1 | hv2
      · have he1 : e ∉ M₁ := fun h => hM₁.2.2 e h v hve hv1
        simp [hv1, he1]
      · have he2 : e ∉ M₂ := fun h => hM₂.2.2 e h v hve hv2
        have he1 : e ∈ M₁ := he.resolve_right he2
        simp [hdisjS v hv2, he1])
  exact ⟨c, hc⟩

end TCCHighLib
