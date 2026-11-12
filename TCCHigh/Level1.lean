/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import TCCHigh.Basic

/-!
# One independent class: `α(G) ≥ |V| − Δ − 1` implies `χ''(G) ≤ Δ + 2`

Yap–Wang–Zhang (1989), Lemma 2.2, restated by Yap–Chew (1992) as Lemma 2.4: if `G` has an
independent set `S` with `|S| ≥ |V| − Δ − 1` then `χ''(G) ≤ Δ + 2`. (YWZ state the matching
hypothesis separately; the matching is supplied here.) Take a matching `M` of `G − S` covering as
many vertices of maximum degree as possible and the apex graph `G − M + c*·(V ∖ S)`. Its
maximum degree is at most `Δ + 1`; its vertices of degree `Δ + 1` are `c*` and uncovered
vertices of degree `Δ`, which are pairwise non-adjacent by the maximality of `M`, so they span a
star and Fournier's theorem gives a `(Δ + 1)`-edge colouring. The vertices of `S` and the edges
of `M` receive the colour `Δ + 2`.

Consequence (Yap–Wang–Zhang 1989, Theorem 2.3 and the closing remarks): the total colouring
conjecture holds when `Δ(G) ≥ |V| − 3`.
-/

@[expose] public section

namespace TCCHighLib

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `M` is a matching of `G` avoiding the vertex set `S`. -/
def IsMatchingAvoiding (G : SimpleGraph V) (M : Finset (Sym2 V)) (S : Finset V) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧ (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v, v ∈ e → v ∉ f) ∧
    (∀ e ∈ M, ∀ v ∈ e, v ∉ S)

/-- `v` is covered by `M`. -/
abbrev Covered (M : Finset (Sym2 V)) (v : V) : Prop := ∃ e ∈ M, v ∈ e

instance (M : Finset (Sym2 V)) : DecidablePred (Covered M) :=
  fun v => inferInstanceAs (Decidable (∃ e ∈ M, v ∈ e))

lemma covered_insert {M : Finset (Sym2 V)} {e : Sym2 V} {v : V} (h : Covered M v) :
    Covered (insert e M) v := by
  obtain ⟨f, hf, hv⟩ := h
  exact ⟨f, mem_insert_of_mem hf, hv⟩

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Adding an edge between two uncovered vertices outside `S` keeps a matching avoiding `S`. -/
lemma isMatchingAvoiding_insert {M : Finset (Sym2 V)} {S : Finset V}
    (hM : IsMatchingAvoiding G M S) {u v : V} (huv : G.Adj u v) (hu : ¬ Covered M u)
    (hv : ¬ Covered M v) (huS : u ∉ S) (hvS : v ∉ S) :
    IsMatchingAvoiding G (insert s(u, v) M) S := by
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · exact huv
    · exact h1 e he
  · intro e he f hf hef x hxe hxf
    rcases mem_insert.mp he with he' | he' <;> rcases mem_insert.mp hf with hf' | hf'
    · exact hef (he'.trans hf'.symm)
    · subst he'
      rcases Sym2.mem_iff.mp hxe with rfl | rfl
      · exact hu ⟨f, hf', hxf⟩
      · exact hv ⟨f, hf', hxf⟩
    · subst hf'
      rcases Sym2.mem_iff.mp hxf with rfl | rfl
      · exact hu ⟨e, he', hxe⟩
      · exact hv ⟨e, he', hxe⟩
    · exact h2 e he' f hf' hef x hxe hxf
  · intro e he x hx
    rcases mem_insert.mp he with rfl | he
    · rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact huS
      · exact hvS
    · exact h3 e he x hx

/-- A matching avoiding `S` that covers the maximum number of vertices of a set `A`. -/
lemma exists_max_matching (S A : Finset V) :
    ∃ M : Finset (Sym2 V), IsMatchingAvoiding G M S ∧
      ∀ M' : Finset (Sym2 V), IsMatchingAvoiding G M' S →
        #(A.filter (Covered M')) ≤ #(A.filter (Covered M)) := by
  classical
  let cands := (G.edgeFinset.powerset).filter fun M => IsMatchingAvoiding G M S
  have hne : cands.Nonempty :=
    ⟨∅, mem_filter.mpr ⟨empty_mem_powerset _, by simp [IsMatchingAvoiding]⟩⟩
  obtain ⟨M, hM, hmax⟩ := exists_max_image cands (fun M => #(A.filter (Covered M))) hne
  refine ⟨M, (mem_filter.mp hM).2, fun M' hM' => hmax M' (mem_filter.mpr ⟨?_, hM'⟩)⟩
  refine mem_powerset.mpr fun e he => ?_
  exact mem_edgeFinset.mpr (hM'.1 e he)

/-- In a coverage-maximal matching, two uncovered vertices of `A` outside `S` are not adjacent. -/
lemma not_adj_of_max {S A : Finset V} {M : Finset (Sym2 V)} (hM : IsMatchingAvoiding G M S)
    (hmax : ∀ M' : Finset (Sym2 V), IsMatchingAvoiding G M' S →
      #(A.filter (Covered M')) ≤ #(A.filter (Covered M)))
    {u v : V} (huA : u ∈ A) (hu : ¬ Covered M u) (hv : ¬ Covered M v) (huS : u ∉ S)
    (hvS : v ∉ S) : ¬ G.Adj u v := by
  intro huv
  have hM' := isMatchingAvoiding_insert G hM huv hu hv huS hvS
  have h := hmax _ hM'
  have hsub : A.filter (Covered M) ⊂ A.filter (Covered (insert s(u, v) M)) := by
    refine ssubset_iff_of_subset (fun x hx => ?_) |>.mpr ⟨u, ?_, ?_⟩
    · simp only [mem_filter] at hx ⊢
      exact ⟨hx.1, covered_insert hx.2⟩
    · simp only [mem_filter]
      exact ⟨huA, _, mem_insert_self _ _, Sym2.mem_mk_left _ _⟩
    · simp only [mem_filter, not_and]
      exact fun _ => hu
  have := card_lt_card hsub
  omega

/-- Degree bound for vertices of the apex graph built from a matching. -/
lemma apex_degree_some_le {M : Finset (Sym2 V)} {S : Finset V} (hM : IsMatchingAvoiding G M S)
    (W : Finset V) (v : V) :
    (apex G (M : Set (Sym2 V)) (W : Set V)).degree (some v) + (if Covered M v then 1 else 0) ≤
      (if v ∈ W then 1 else 0) + G.degree v := by
  rw [apex_degree_some]
  by_cases hc : Covered M v
  · obtain ⟨e, he, hve⟩ := hc
    obtain ⟨w, rfl⟩ : ∃ w, e = s(v, w) := (Sym2.mem_iff_exists.mp hve).imp fun w h => h
    have hadj : G.Adj v w := hM.1 _ he
    have := card_filter_nbr_le_pred G M v w hadj he
    simp only [show Covered M v from ⟨_, he, hve⟩, ite_true]
    omega
  · simp only [hc, ite_false]
    have := card_filter_nbr_le G M v
    omega

/-- **Yap–Wang–Zhang, Lemma 2.2 / Yap–Chew, Lemma 2.4.** An independent set `S` with
`|V| ≤ |S| + Δ + 1` gives a total colouring with `Δ + 2` colours. -/
theorem tcc_of_indep (S : Finset V) (hS : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v)
    (hcard : Fintype.card V ≤ #S + G.maxDegree + 1) :
    ∃ c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2), IsTotalColoring G c := by
  set Δ := G.maxDegree with hΔ
  let A : Finset V := univ.filter fun v => G.degree v = Δ ∧ v ∉ S
  obtain ⟨M, hM, hmax⟩ := exists_max_matching G S A
  set W : Finset V := univ.filter fun v => v ∉ S with hWdef
  let G' := apex G (M : Set (Sym2 V)) (W : Set V)
  have hW : #W + #S = Fintype.card V := by
    have := card_filter_add_card_filter_not (s := (univ : Finset V)) (fun v => v ∉ S)
    simp only [not_not] at this
    rw [show (univ.filter fun v => v ∈ S) = S by ext; simp, card_univ] at this
    exact this
  have hdeg_none : G'.degree none ≤ Δ + 1 := by
    have h : G'.degree none = #W := apex_degree_none G M W
    omega
  have hdeg_some : ∀ v, G'.degree (some v) ≤ Δ + 1 := by
    intro v
    have h1 : G'.degree (some v) + (if Covered M v then 1 else 0) ≤
        (if v ∈ W then 1 else 0) + G.degree v := apex_degree_some_le G hM W v
    have h2 := G.degree_le_maxDegree v
    split_ifs at h1 <;> omega
  have hmaxdeg : G'.maxDegree ≤ Δ + 1 := by
    refine maxDegree_le_of_forall_degree_le _ _ fun x => ?_
    cases x with
    | none => exact hdeg_none
    | some v => exact hdeg_some v
  have hcol : G'.lineGraph.Colorable (Δ + 1) := by
    by_cases hlt : G'.maxDegree ≤ Δ
    · exact (LeanPool.Vizing.lineGraph_colorable G').mono (by omega)
    · have heq : G'.maxDegree = Δ + 1 := by omega
      rw [← heq]
      refine FournierLib.fournier G' ?_
      refine isAcyclic_of_forall_adj _ (fun x => (x : Option V) = none)
        (fun a b ha hb => Subtype.ext (ha.trans hb.symm)) ?_
      rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [Set.mem_setOf_eq] at hx hy
      change G'.Adj x y at hxy
      cases x with
      | none => exact Or.inl rfl
      | some u =>
        cases y with
        | none => exact Or.inr rfl
        | some v =>
          exfalso
          rw [heq] at hx hy
          have hu : G'.degree (some u) + (if Covered M u then 1 else 0) ≤
              (if u ∈ W then 1 else 0) + G.degree u := apex_degree_some_le G hM W u
          have hv : G'.degree (some v) + (if Covered M v then 1 else 0) ≤
              (if v ∈ W then 1 else 0) + G.degree v := apex_degree_some_le G hM W v
          have hu2 := G.degree_le_maxDegree u
          have hv2 := G.degree_le_maxDegree v
          have huW : u ∈ W := by by_contra h; simp only [h, ite_false] at hu; split_ifs at hu <;> omega
          have hvW : v ∈ W := by by_contra h; simp only [h, ite_false] at hv; split_ifs at hv <;> omega
          have huS : u ∉ S := (mem_filter.mp huW).2
          have hvS : v ∉ S := (mem_filter.mp hvW).2
          simp only [huW, hvW, ite_true] at hu hv
          have hcu : ¬ Covered M u := by intro h; simp only [h, ite_true] at hu; omega
          have hcv : ¬ Covered M v := by intro h; simp only [h, ite_true] at hv; omega
          simp only [hcu, hcv, ite_false] at hu hv
          have huA : u ∈ A := mem_filter.mpr ⟨mem_univ _, by omega, huS⟩
          exact not_adj_of_max G hM hmax huA hcu hcv huS hvS hxy.1
  obtain ⟨c, hc⟩ := total_of_apex G (M : Set (Sym2 V)) (W : Set V) (Δ + 1) 1 hcol
    (fun _ => 0) (fun _ => 0)
    (fun u v hu hv huv => by
      have hu' : u ∈ S := by simpa [hWdef] using hu
      have hv' : v ∈ S := by simpa [hWdef] using hv
      exact absurd huv (hS u hu' v hv'))
    (fun e he f hf hef v hve hvf => absurd hvf (hM.2.1 e he f hf hef v hve))
    (fun v hv e he hve => by
      have hv' : v ∈ S := by simpa [hWdef] using hv
      exact absurd hv' (hM.2.2 e he v hve))
  exact ⟨c, hc⟩

/-- **The total colouring conjecture for `Δ(G) ≥ |V| − 3`** (Yap–Wang–Zhang 1989, Theorem 2.3
for `Δ = |V| − 3`; `Δ = |V| − 1` is Behzad–Chartrand–Cooper, `Δ = |V| − 2` the closing remark). -/
theorem tcc_of_card_le_add_three (h : Fintype.card V ≤ G.maxDegree + 3) :
    ∃ c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2), IsTotalColoring G c := by
  by_cases h1 : Fintype.card V ≤ G.maxDegree + 1
  · exact tcc_of_indep G ∅ (by simp) (by simpa using h1)
  · push_neg at h1
    have hne : Nonempty V := by
      rw [← Fintype.card_pos_iff]; omega
    obtain ⟨v⟩ := hne
    -- `v` has a non-neighbour `u ≠ v`
    have hcompl : #(univ.filter fun u => ¬ G.Adj v u) + G.degree v = Fintype.card V := by
      rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, add_comm,
        card_filter_add_card_filter_not]
      rfl
    have hdv := G.degree_le_maxDegree v
    have hcard : 1 < #(univ.filter fun u => ¬ G.Adj v u) := by omega
    obtain ⟨u, hu, huv⟩ := exists_mem_ne hcard v
    simp only [mem_filter, mem_univ, true_and] at hu
    refine tcc_of_indep G {u, v} ?_ ?_
    · intro a ha b hb hab
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact G.irrefl hab
      · exact hu hab.symm
      · exact hu hab
      · exact G.irrefl hab
    · rw [card_pair huv]; omega

end TCCHighLib
