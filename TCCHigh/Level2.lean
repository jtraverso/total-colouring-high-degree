/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import TCCHigh.Matching

/-!
# Two colour classes: `Δ(G) = |V| − 4`

Following the second part of the proof of Yap–Wang–Zhang (1989), Theorem 2.4: two disjoint
non-adjacent pairs `S₁`, `S₂` take the colours `Δ + 1`, `Δ + 2`, together with matchings
`M₁ ⊆ G − S₁`, `M₂ ⊆ G − M₁ − S₂`, and the apex graph `G − M₁ − M₂ + c*·W`, `W = V ∖ (S₁ ∪ S₂)`,
is edge coloured with `Δ` colours.

* `M₁` covers as many vertices of degree `Δ` outside `S₁` as possible; by the enlarge-matching
  argument at most one of them, `u`, stays uncovered when `Δ ≥ 5`, and `S₂` is chosen through `u`.
* `M₂` covers as many as possible of the vertices that would otherwise have degree `Δ` in the apex
  graph; at most one of them stays uncovered when `Δ ≥ 7`.

The vertices of degree `Δ` of the apex graph are then `c*`, possibly `u ∈ S₂` (not adjacent to
`c*`) and possibly one more vertex `v`; every edge among them contains `v`, so they span a forest
and Fournier's theorem applies. This replaces the use of the Chetwynd–Hilton theorem on graphs
with three vertices of maximum degree in Yap–Wang–Zhang.
-/

@[expose] public section

namespace TCCHighLib

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma card_nonnbr (v : V) :
    #(univ.filter fun u => ¬ G.Adj v u) + G.degree v = Fintype.card V := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, add_comm,
    card_filter_add_card_filter_not]
  rfl

/-- A vertex with at least `k + 1` non-neighbours (itself included) has a non-neighbour outside
any set `T` of size at most `k - 1`, different from itself. -/
lemma exists_nonnbr_not_mem (v : V) (T : Finset V) (h : #T + 2 ≤ #(univ.filter fun u => ¬ G.Adj v u)) :
    ∃ z, z ∉ T ∧ z ≠ v ∧ ¬ G.Adj v z := by
  by_contra hcon
  push_neg at hcon
  have hsub : univ.filter (fun u => ¬ G.Adj v u) ⊆ insert v T := by
    intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz
    by_cases hzT : z ∈ T
    · exact mem_insert_of_mem hzT
    · by_cases hzv : z = v
      · exact hzv ▸ mem_insert_self _ _
      · exact absurd (hcon z hzT hzv) hz
  have := card_le_card hsub
  have := card_insert_le v T
  omega

lemma card_filter_not_mem_ge (s : Finset V) (T : Finset V) :
    #s ≤ #(s.filter (· ∉ T)) + #T := by
  have h := card_filter_add_card_filter_not (s := s) (fun x => x ∉ T)
  have h2 : #(s.filter fun x => ¬ x ∉ T) ≤ #T := by
    refine card_le_card fun x hx => ?_
    simp only [mem_filter, not_not] at hx
    exact hx.2
  omega

/-- **Total colouring for `|V| = Δ + 4` and `Δ ≥ 7`.** -/
theorem tcc_two_level (hn : Fintype.card V = G.maxDegree + 4) (hΔ : 7 ≤ G.maxDegree) :
    ∃ c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2), IsTotalColoring G c := by
  classical
  set Δ := G.maxDegree with hΔdef
  have hnn : ∀ v, 4 ≤ #(univ.filter fun u => ¬ G.Adj v u) := by
    intro v
    have := card_nonnbr G v
    have := G.degree_le_maxDegree v
    omega
  have hnn3 : ∀ v, G.degree v = Δ → #(univ.filter fun u => ¬ G.Adj v u) = 4 := by
    intro v hv
    have := card_nonnbr G v
    omega
  -- Step 1: the first pair `S₁ = {x, y}`
  have hne : Nonempty V := by rw [← Fintype.card_pos_iff]; omega
  obtain ⟨x⟩ := hne
  obtain ⟨y, -, hyx, hxy⟩ := exists_nonnbr_not_mem G x ∅ (by rw [card_empty]; have := hnn x; omega)
  set S₁ : Finset V := {x, y} with hS₁
  have hS₁card : #S₁ = 2 := card_pair hyx.symm
  have hS₁ind : ∀ a ∈ S₁, ∀ b ∈ S₁, ¬ G.Adj a b := by
    intro a ha b hb hab
    simp only [hS₁, mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact G.irrefl hab
    · exact hxy hab
    · exact hxy hab.symm
    · exact G.irrefl hab
  -- Step 2: `M₁`
  set A₁ : Finset V := univ.filter fun v => G.degree v = Δ ∧ v ∉ S₁ with hA₁
  obtain ⟨M₁, hM₁, hmax₁⟩ := exists_max_matching G S₁ A₁
  -- Step 3: at most one uncovered vertex of `A₁`
  have huniq₁ : ∀ u ∈ A₁, ∀ u' ∈ A₁, ¬ Covered M₁ u → ¬ Covered M₁ u' → u = u' := by
    intro u hu u' hu' hcu hcu'
    by_contra hne
    have hu2 := (mem_filter.mp hu).2
    have hu'2 := (mem_filter.mp hu').2
    have h := card_nbr_le_of_two_uncovered G hM₁ hmax₁ hu hcu hcu' hu2.2 hu'2.2 hne
    -- right side at most 2
    have hT : #(univ.filter fun b => b ∉ S₁ ∧ b ≠ u ∧ b ≠ u' ∧ ¬ G.Adj u' b) + 2 ≤ 4 := by
      have hsub : univ.filter (fun b => b ∉ S₁ ∧ b ≠ u ∧ b ≠ u' ∧ ¬ G.Adj u' b) ⊆
          ((univ.filter fun b => ¬ G.Adj u' b).erase u').erase u := by
        intro b hb
        simp only [mem_filter, mem_univ, true_and] at hb
        simp only [mem_erase, mem_filter, mem_univ, true_and]
        exact ⟨hb.2.1, hb.2.2.1, hb.2.2.2⟩
      have h1 := card_le_card hsub
      have hu'm : u' ∈ univ.filter fun b => ¬ G.Adj u' b := by simp
      have hum : u ∈ (univ.filter fun b => ¬ G.Adj u' b).erase u' := by
        simp only [mem_erase, mem_filter, mem_univ, true_and]
        exact ⟨hne, fun h' => by
          have := not_adj_of_max G hM₁ hmax₁ hu hcu hcu' hu2.2 hu'2.2
          exact this h'.symm⟩
      rw [card_erase_of_mem hum, card_erase_of_mem hu'm, hnn3 u' hu'2.1] at h1
      omega
    -- left side at least `Δ - 2`
    have hL : Δ ≤ #((G.neighborFinset u).filter (· ∉ S₁)) + 2 := by
      have := card_filter_not_mem_ge (G.neighborFinset u) S₁
      rw [card_neighborFinset_eq_degree, hu2.1] at this
      omega
    omega
  -- Step 4: the second pair `S₂`
  obtain ⟨s, s', hss', hsadj, hsS₁, hs'S₁, hU₁⟩ : ∃ s s' : V, s ≠ s' ∧ ¬ G.Adj s s' ∧ s ∉ S₁ ∧
      s' ∉ S₁ ∧ ∀ v ∈ A₁, ¬ Covered M₁ v → v = s ∨ v = s' := by
    by_cases hU : ∃ u ∈ A₁, ¬ Covered M₁ u
    · obtain ⟨u, hu, hcu⟩ := hU
      obtain ⟨z, hzS, hzu, huz⟩ := exists_nonnbr_not_mem G u S₁ (by rw [hS₁card]; exact hnn u)
      exact ⟨u, z, hzu.symm, huz, (mem_filter.mp hu).2.2, hzS,
        fun v hv hcv => Or.inl (huniq₁ v hv u hu hcv hcu)⟩
    · push_neg at hU
      obtain ⟨a, haS⟩ : ∃ a, a ∉ S₁ := by
        by_contra hcon
        push_neg at hcon
        have hsub : (univ : Finset V) ⊆ S₁ := fun a _ => hcon a
        have := card_le_card hsub
        rw [card_univ] at this
        omega
      obtain ⟨z, hzS, hza, haz⟩ := exists_nonnbr_not_mem G a S₁ (by rw [hS₁card]; exact hnn a)
      exact ⟨a, z, hza.symm, haz, haS, hzS, fun v hv hcv => absurd (hU v hv) hcv⟩
  set S₂ : Finset V := {s, s'} with hS₂
  have hS₂card : #S₂ = 2 := card_pair hss'
  have hS₂ind : ∀ a ∈ S₂, ∀ b ∈ S₂, ¬ G.Adj a b := by
    intro a ha b hb hab
    simp only [hS₂, mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact G.irrefl hab
    · exact hsadj hab
    · exact hsadj hab.symm
    · exact G.irrefl hab
  have hdisj : ∀ v, v ∈ S₂ → v ∉ S₁ := by
    intro v hv
    simp only [hS₂, mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hsS₁
    · exact hs'S₁
  -- Step 5: `W`
  set W : Finset V := univ.filter fun v => v ∉ S₁ ∧ v ∉ S₂ with hW
  have hWcard : #W = Δ := by
    have h1 : #W + #(S₁ ∪ S₂) = Fintype.card V := by
      have h := card_filter_add_card_filter_not (s := (univ : Finset V))
        (fun v => v ∉ S₁ ∧ v ∉ S₂)
      have he : (univ.filter fun v => ¬ (v ∉ S₁ ∧ v ∉ S₂)) = S₁ ∪ S₂ := by
        ext v; simp only [mem_filter, mem_univ, true_and, mem_union]; tauto
      rw [he, card_univ] at h
      exact h
    have h2 : #(S₁ ∪ S₂) + #(S₁ ∩ S₂) = #S₁ + #S₂ := card_union_add_card_inter S₁ S₂
    have h3 : S₁ ∩ S₂ = ∅ :=
      disjoint_iff_inter_eq_empty.mp (disjoint_left.mpr fun v h1 h2 => hdisj v h2 h1)
    rw [h3, card_empty] at h2
    omega
  -- Step 6: `M₂`
  set q₁ : V → ℕ := fun v => #((G.neighborFinset v).filter fun u => s(v, u) ∉ M₁) with hq₁
  set p : V → ℕ := fun v => q₁ v + (if v ∈ W then 1 else 0) with hp
  set Γ := G.deleteEdges (M₁ : Set (Sym2 V)) with hΓ
  have hΓnbr : ∀ v, Γ.neighborFinset v = (G.neighborFinset v).filter fun u => s(v, u) ∉ M₁ := by
    intro v; ext u; simp [hΓ]
  set A₂ : Finset V := univ.filter fun v => v ∉ S₂ ∧ Δ ≤ p v with hA₂
  obtain ⟨M₂, hM₂, hmax₂⟩ := exists_max_matching Γ S₂ A₂
  -- Step 7: `p v ≤ Δ` outside `S₂`
  have hq₁le : ∀ v, q₁ v ≤ G.degree v := fun v => card_filter_nbr_le G M₁ v
  have hq₁cov : ∀ v, Covered M₁ v → q₁ v + 1 ≤ G.degree v := by
    intro v hv
    obtain ⟨e, he, hve⟩ := hv
    obtain ⟨w, rfl⟩ : ∃ w, e = s(v, w) := (Sym2.mem_iff_exists.mp hve).imp fun w h => h
    exact card_filter_nbr_le_pred G M₁ v w (hM₁.1 _ he) he
  have hple : ∀ v, v ∉ S₂ → p v ≤ Δ := by
    intro v hv
    have hdeg := G.degree_le_maxDegree v
    simp only [hp]
    by_cases hvW : v ∈ W
    · simp only [hvW, ite_true]
      have hvS₁ : v ∉ S₁ := (mem_filter.mp hvW).2.1
      by_cases hdv : G.degree v = Δ
      · have hvA : v ∈ A₁ := mem_filter.mpr ⟨mem_univ _, hdv, hvS₁⟩
        have hcv : Covered M₁ v := by
          by_contra hcv
          rcases hU₁ v hvA hcv with rfl | rfl <;> simp [hS₂] at hv
        have := hq₁cov v hcv
        omega
      · have := hq₁le v
        omega
    · simp only [hvW, ite_false]
      have := hq₁le v
      omega
  -- Step 8: at most one uncovered vertex of `A₂`
  have hq₁A₂ : ∀ v ∈ A₂, Δ ≤ q₁ v + 1 := by
    intro v hv
    have := (mem_filter.mp hv).2.2
    simp only [hp] at this
    split_ifs at this <;> omega
  have huniq₂ : ∀ v ∈ A₂, ∀ v' ∈ A₂, ¬ Covered M₂ v → ¬ Covered M₂ v' → v = v' := by
    intro v hv v' hv' hcv hcv'
    by_contra hne
    have hvS := (mem_filter.mp hv).2.1
    have hv'S := (mem_filter.mp hv').2.1
    have h := card_nbr_le_of_two_uncovered Γ hM₂ hmax₂ hv hcv hcv' hvS hv'S hne
    have hnadj : ¬ Γ.Adj v' v := fun h' =>
      not_adj_of_max Γ hM₂ hmax₂ hv hcv hcv' hvS hv'S h'.symm
    -- right side at most 3
    have hdegΓ : ∀ w, #(Γ.neighborFinset w) = q₁ w := fun w => by rw [hΓnbr]
    have hR : #(univ.filter fun b => b ∉ S₂ ∧ b ≠ v ∧ b ≠ v' ∧ ¬ Γ.Adj v' b) ≤ 3 := by
      set Y : Finset V := univ.filter fun b => b ∉ S₂ with hY
      set N' : Finset V := (Γ.neighborFinset v').filter (· ∉ S₂) with hN'
      have hsub : univ.filter (fun b => b ∉ S₂ ∧ b ≠ v ∧ b ≠ v' ∧ ¬ Γ.Adj v' b) ⊆
          ((Y \ N').erase v).erase v' := by
        intro b hb
        simp only [mem_filter, mem_univ, true_and] at hb
        refine mem_erase.mpr ⟨hb.2.2.1, mem_erase.mpr ⟨hb.2.1, mem_sdiff.mpr ⟨?_, ?_⟩⟩⟩
        · exact mem_filter.mpr ⟨mem_univ _, hb.1⟩
        · intro hbN
          exact hb.2.2.2 ((mem_neighborFinset _ _ _).mp (mem_filter.mp hbN).1)
      have h1 := card_le_card hsub
      have hvm : v ∈ Y \ N' := by
        refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, hvS⟩, ?_⟩
        intro hvN
        exact hnadj ((mem_neighborFinset _ _ _).mp (mem_filter.mp hvN).1)
      have hv'm : v' ∈ (Y \ N').erase v := by
        refine mem_erase.mpr ⟨Ne.symm hne, mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, hv'S⟩, ?_⟩⟩
        intro hvN
        exact Γ.irrefl ((mem_neighborFinset _ _ _).mp (mem_filter.mp hvN).1)
      rw [card_erase_of_mem hv'm, card_erase_of_mem hvm] at h1
      have hNY : N' ⊆ Y := fun b hb => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hb).2⟩
      have h2 := card_sdiff_add_card_eq_card hNY
      have hYc : #Y + #S₂ = Fintype.card V := by
        have h := card_filter_add_card_filter_not (s := (univ : Finset V)) (fun b => b ∉ S₂)
        rw [show (univ.filter fun b => ¬ b ∉ S₂) = S₂ by ext; simp, card_univ] at h
        exact h
      have hN : q₁ v' ≤ #N' + 2 := by
        have := card_filter_not_mem_ge (Γ.neighborFinset v') S₂
        rw [hdegΓ v', hS₂card] at this
        exact this
      have := hq₁A₂ v' hv'
      omega
    have hL : Δ ≤ #((Γ.neighborFinset v).filter (· ∉ S₂)) + 3 := by
      have := card_filter_not_mem_ge (Γ.neighborFinset v) S₂
      rw [hdegΓ v, hS₂card] at this
      have := hq₁A₂ v hv
      omega
    omega
  -- Step 9: the apex graph
  set F : Finset (Sym2 V) := M₁ ∪ M₂ with hF
  set G' := apex G (F : Set (Sym2 V)) (W : Set V) with hG'
  have hM₂G : ∀ e ∈ M₂, e ∈ G.edgeSet ∧ e ∉ M₁ := by
    intro e he
    have h := hM₂.1 e he
    revert h
    induction e using Sym2.ind with
    | h a b =>
      intro h
      simp only [hΓ, mem_edgeSet, deleteEdges_adj, Finset.mem_coe] at h
      exact ⟨h.1, h.2⟩
  have hdegnone : G'.degree none = Δ := by
    have h : G'.degree none = #W := apex_degree_none G F W
    rw [h, hWcard]
  have hq12 : ∀ v, #((G.neighborFinset v).filter fun u => s(v, u) ∉ F) ≤ q₁ v := by
    intro v
    refine card_le_card fun u hu => ?_
    simp only [mem_filter, hF, mem_union, not_or] at hu ⊢
    exact ⟨hu.1, hu.2.1⟩
  have hq12cov : ∀ v, Covered M₂ v → #((G.neighborFinset v).filter fun u => s(v, u) ∉ F) + 1 ≤ q₁ v := by
    intro v hv
    obtain ⟨e, he, hve⟩ := hv
    obtain ⟨w, rfl⟩ : ∃ w, e = s(v, w) := (Sym2.mem_iff_exists.mp hve).imp fun w h => h
    obtain ⟨hadj, hnot⟩ := hM₂G _ he
    have hsub : (G.neighborFinset v).filter (fun u => s(v, u) ∉ F) ⊆
        ((G.neighborFinset v).filter fun u => s(v, u) ∉ M₁).erase w := by
      intro u hu
      simp only [mem_filter, hF, mem_union, not_or] at hu
      refine mem_erase.mpr ⟨?_, mem_filter.mpr ⟨hu.1, hu.2.1⟩⟩
      rintro rfl
      exact hu.2.2 he
    have := card_le_card hsub
    have hmem : w ∈ (G.neighborFinset v).filter fun u => s(v, u) ∉ M₁ :=
      mem_filter.mpr ⟨(mem_neighborFinset _ _ _).mpr hadj, hnot⟩
    have hpos : 0 < #((G.neighborFinset v).filter fun u => s(v, u) ∉ M₁) := card_pos.mpr ⟨w, hmem⟩
    have hq : q₁ v = #((G.neighborFinset v).filter fun u => s(v, u) ∉ M₁) := rfl
    rw [card_erase_of_mem hmem] at this
    omega
  -- degree of `some v`
  have hdegsome : ∀ v, G'.degree (some v) ≤ Δ ∧ (G'.degree (some v) = Δ →
      (v ∈ S₂ ∧ v ∈ A₁ ∧ ¬ Covered M₁ v) ∨ (v ∉ S₂ ∧ v ∈ A₂ ∧ ¬ Covered M₂ v)) := by
    intro v
    have h0 : G'.degree (some v) =
        (if v ∈ W then 1 else 0) + #((G.neighborFinset v).filter fun u => s(v, u) ∉ F) :=
      apex_degree_some G F W v
    rw [h0]
    have h12 := hq12 v
    have hdeg := G.degree_le_maxDegree v
    by_cases hvS₂ : v ∈ S₂
    · have hvW : v ∉ W := fun h => (mem_filter.mp h).2.2 hvS₂
      simp only [hvW, ite_false, zero_add]
      have hq := hq₁le v
      refine ⟨by omega, fun heq => Or.inl ⟨hvS₂, ?_, ?_⟩⟩
      · exact mem_filter.mpr ⟨mem_univ _, by omega, hdisj v hvS₂⟩
      · intro hc; have := hq₁cov v hc; omega
    · have hpv := hple v hvS₂
      simp only [hp] at hpv
      by_cases hc2 : Covered M₂ v
      · have := hq12cov v hc2
        refine ⟨by split_ifs at hpv ⊢ <;> omega, fun heq => by split_ifs at hpv heq <;> omega⟩
      · refine ⟨by split_ifs at hpv ⊢ <;> omega, fun heq => Or.inr ⟨hvS₂, ?_, hc2⟩⟩
        refine mem_filter.mpr ⟨mem_univ _, hvS₂, ?_⟩
        simp only [hp]
        split_ifs at heq ⊢ <;> omega
  have hmaxdeg : G'.maxDegree ≤ Δ := by
    refine maxDegree_le_of_forall_degree_le _ _ fun z => ?_
    cases z with
    | none => exact hdegnone.le
    | some v => exact (hdegsome v).1
  -- Step 10: `Δ`-edge colouring of the apex graph
  have hcol : G'.lineGraph.Colorable Δ := by
    by_cases hlt : G'.maxDegree < Δ
    · exact (LeanPool.Vizing.lineGraph_colorable G').mono (by omega)
    · have heq : G'.maxDegree = Δ := by omega
      rw [← heq]
      refine FournierLib.fournier G' ?_
      refine isAcyclic_of_forall_adj _
        (fun z => ∃ v, (z : Option V) = some v ∧ v ∉ S₂ ∧ v ∈ A₂ ∧ ¬ Covered M₂ v) ?_ ?_
      · rintro a b ⟨v, hav, hv1, hv2, hv3⟩ ⟨w, hbw, hw1, hw2, hw3⟩
        have := huniq₂ v hv2 w hw2 hv3 hw3
        subst this
        exact Subtype.ext (hav.trans hbw.symm)
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
            have hwS : w ∉ S₂ := (mem_filter.mp hwW).2.2
            rcases (hdegsome w).2 hb with h | h
            · exact absurd h.1 hwS
            · exact Or.inr ⟨w, rfl, h⟩
        | some v =>
          cases b with
          | none =>
            have hvW : v ∈ W := hab
            have hvS : v ∉ S₂ := (mem_filter.mp hvW).2.2
            rcases (hdegsome v).2 ha with h | h
            · exact absurd h.1 hvS
            · exact Or.inl ⟨v, rfl, h⟩
          | some w =>
            rcases (hdegsome v).2 ha with h | h
            · rcases (hdegsome w).2 hb with h' | h'
              · exfalso
                have := huniq₁ v h.2.1 w h'.2.1 h.2.2 h'.2.2
                subst this
                exact G.irrefl hab.1
              · exact Or.inr ⟨w, rfl, h'⟩
            · exact Or.inl ⟨v, rfl, h⟩
  -- Step 11: assembly
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
      · simp [hu1, hdisj v hv2]
      · simp [hv1, hdisj u hu2]
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
        simp [hdisj v hv2, he1])
  exact ⟨c, hc⟩

end TCCHighLib
