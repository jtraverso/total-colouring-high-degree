/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import TCCHigh.Split

/-!
# The total colouring conjecture for `Δ(G) ≥ |V| − 4`

* `|V| ≤ Δ + 3`: `tcc_of_card_le_add_three` (Yap–Wang–Zhang 1989, Theorem 2.3 and remarks).
* `|V| = Δ + 4` and `G` has three pairwise non-adjacent vertices: `tcc_of_indep` (the first case
  of Yap–Wang–Zhang 1989, Theorem 2.4).
* `|V| = Δ + 4` and `G` has no three pairwise non-adjacent vertices: `tcc_of_noIndepTriple`.
  A vertex `z` of degree `Δ` has exactly three non-neighbours, forming a triangle; if one of them
  has a neighbour outside the triangle, `tcc_case_hub` chooses the two non-adjacent pairs (a
  short counting argument when `|V|` is even) and applies `tcc_case_even` / `tcc_case_odd`;
  otherwise `tcc_case_split` applies. This replaces the case analysis of Yap–Wang–Zhang for
  `|V| = 9, 10` and the appeal to Kostochka's theorem for `Δ ≤ 4`.
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

/-- Every vertex has at least three non-neighbours when `|V| = Δ + 4`. -/
lemma three_le_nonnbr (hn : Fintype.card V = G.maxDegree + 4) (a : V) :
    3 ≤ #(univ.filter fun u => u ≠ a ∧ ¬ G.Adj a u) := by
  have h1 := card_nonnbr G a
  have h2 := G.degree_le_maxDegree a
  have hsub : (univ.filter fun u => ¬ G.Adj a u) ⊆
      insert a (univ.filter fun u => u ≠ a ∧ ¬ G.Adj a u) := by
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    by_cases hua : u = a
    · exact hua ▸ mem_insert_self _ _
    · exact mem_insert_of_mem (by simp [hua, hu])
  have h3 := (card_le_card hsub).trans (card_insert_le _ _)
  omega

/-- Non-neighbours of `x` other than `x` and `z`. -/
lemma two_le_nonnbr (hn : Fintype.card V = G.maxDegree + 4) (z x : V) (hzx : z ≠ x)
    (hnzx : ¬ G.Adj z x) :
    2 ≤ #((univ.filter fun u => u ≠ x ∧ ¬ G.Adj x u).erase z) := by
  have h := three_le_nonnbr G hn x
  have hxz : ¬ G.Adj x z := fun h => hnzx h.symm
  rw [card_erase_of_mem (by simp [hzx, hxz])]
  omega

/-- **A vertex of the triangle has an outside neighbour.** -/
theorem tcc_case_hub (hα : NoIndepTriple G) (hn : Fintype.card V = G.maxDegree + 4)
    (z a b c u : V) (hz : ∀ w, w ≠ z → w ≠ a → w ≠ b → w ≠ c → G.Adj z w)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c)
    (hnza : ¬ G.Adj z a) (hnzb : ¬ G.Adj z b) (hnzc : ¬ G.Adj z c)
    (hub : u ≠ b) (huc : u ≠ c) (hau : G.Adj a u) :
    ∃ col : V ⊕ G.edgeSet → Fin (G.maxDegree + 2), IsTotalColoring G col := by
  classical
  have huz : u ≠ z := fun h => hnza (h ▸ hau).symm
  set N : V → Finset V := fun x => (univ.filter fun w => w ≠ x ∧ ¬ G.Adj x w).erase z with hN
  have hmemN : ∀ x w, w ∈ N x ↔ w ≠ z ∧ w ≠ x ∧ ¬ G.Adj x w := by
    intro x w; simp [hN]
  have hNa : 2 ≤ #(N a) := two_le_nonnbr G hn z a hza hnza
  have hNb : 2 ≤ #(N b) := two_le_nonnbr G hn z b hzb hnzb
  have hNc : 2 ≤ #(N c) := two_le_nonnbr G hn z c hzc hnzc
  rcases em (Even (Fintype.card V)) with hev | hodd
  · by_cases h : ∃ y ∈ N b, ∃ t ∈ N c, y ≠ u ∧ t ≠ u ∧ t ≠ y
    · obtain ⟨y, hy, t, ht, hyu, htu, hty⟩ := h
      obtain ⟨hy1, hy2, hy3⟩ := (hmemN b y).mp hy
      obtain ⟨ht1, ht2, ht3⟩ := (hmemN c t).mp ht
      exact tcc_case_even G hα hn hev z b c a y t u
        (fun w h0 h1 h2 h3 => hz w h0 h3 h1 h2) hbc hab.symm hac.symm hzb hzc hza
        hy1 hy2 hy3 ht1 hty ht2 ht3 huz hyu.symm htu.symm hau hub huc
    · push_neg at h
      obtain ⟨y₀, hy₀, hy₀u⟩ := exists_mem_ne (by omega : 1 < #(N b)) u
      have hNcsub : N c ⊆ {u, y₀} := by
        intro t ht
        by_cases htu : t = u
        · simp [htu]
        · simp [h y₀ hy₀ t ht hy₀u htu]
      have hNbsub : N b ⊆ {u, y₀} := by
        intro y hy
        by_cases hyu : y = u
        · simp [hyu]
        · have hy₀c : y₀ ∈ N c := by
            by_contra hn'
            have : N c ⊆ {u} := by
              intro t ht
              rcases mem_insert.mp (hNcsub ht) with h' | h'
              · simp [h']
              · rw [mem_singleton] at h'; exact absurd (h' ▸ ht) hn'
            have := card_le_card this
            simp at this; omega
          simp [(h y hy y₀ hy₀c hyu hy₀u).symm]
      have huc' : u ∈ N c := by
        by_contra hn'
        have : N c ⊆ {y₀} := by
          intro t ht
          rcases mem_insert.mp (hNcsub ht) with h' | h'
          · exact absurd (h' ▸ ht) hn'
          · exact h'
        have := card_le_card this
        simp at this; omega
      obtain ⟨t', ht'⟩ : (N a).Nonempty := card_pos.mp (by omega)
      obtain ⟨t1, t2, t3⟩ := (hmemN a t').mp ht'
      have ht'u : t' ≠ u := fun h => t3 (h ▸ hau)
      have ht'b : t' ≠ b := fun h => t3 (h ▸ hab)
      have ht'c : t' ≠ c := fun h => t3 (h ▸ hac)
      set O : Finset V := ({z, a, b, c} : Finset V)ᶜ with hO
      have hmemO : ∀ w, w ∈ O ↔ w ≠ z ∧ w ≠ a ∧ w ≠ b ∧ w ≠ c := by intro w; simp [hO]
      have hab' : a ≠ b := G.ne_of_adj hab
      have hac' : a ≠ c := G.ne_of_adj hac
      have hbc' : b ≠ c := G.ne_of_adj hbc
      have hcard4 : #({z, a, b, c} : Finset V) = 4 := by
        rw [card_insert_of_notMem (by simp [hza, hzb, hzc]),
          card_insert_of_notMem (by simp [hab', hac']), card_pair hbc']
      have hOcard : #O = Fintype.card V - 4 := by rw [hO, card_compl, hcard4]
      have hNaO : N a ⊆ O.erase u := by
        intro w hw
        obtain ⟨w1, w2, w3⟩ := (hmemN a w).mp hw
        refine mem_erase.mpr ⟨fun h => w3 (h ▸ hau), (hmemO w).mpr ⟨w1, w2, ?_, ?_⟩⟩
        · exact fun h => w3 (h ▸ hab)
        · exact fun h => w3 (h ▸ hac)
      have huO : u ∈ O := (hmemO u).mpr ⟨huz, (G.ne_of_adj hau).symm, hub, huc⟩
      have h3 : 3 ≤ #O := by
        have := card_le_card hNaO
        rw [card_erase_of_mem huO] at this
        omega
      have h4 : 4 ≤ #O := by
        rw [hOcard] at h3 ⊢
        obtain ⟨k, hk⟩ := hev
        omega
      obtain ⟨v', hv'O, hv'⟩ : ∃ v' ∈ O, v' ∉ ({u, y₀, t'} : Finset V) := by
        by_contra hcon
        push_neg at hcon
        have := card_le_card (show O ⊆ {u, y₀, t'} from hcon)
        have := card_le_three (a := u) (b := y₀) (c := t')
        omega
      simp only [mem_insert, mem_singleton, not_or] at hv'
      obtain ⟨hv'u, hv'y₀, hv't'⟩ := hv'
      obtain ⟨v1, v2, v3, v4⟩ := (hmemO v').mp hv'O
      have hbv' : G.Adj b v' := by
        by_contra hn'
        have := hNbsub ((hmemN b v').mpr ⟨v1, v3, hn'⟩)
        simp only [mem_insert, mem_singleton] at this
        rcases this with h' | h'
        · exact hv'u h'
        · exact hv'y₀ h'
      obtain ⟨u1, u2, u3⟩ := (hmemN c u).mp huc'
      exact tcc_case_even G hα hn hev z c a b u t' v'
        (fun w h0 h1 h2 h3 => hz w h0 h2 h3 h1) hac.symm hbc.symm hab hzc hza hzb
        huz huc u3 t1 ht'u t2 t3 v1 hv'u hv't' hbv' v4 v2
  · obtain ⟨y₁, hy₁, y₂, hy₂, hy12⟩ := one_lt_card.mp (by omega : 1 < #(N a))
    obtain ⟨hy₁1, hy₁2, hy₁3⟩ := (hmemN a y₁).mp hy₁
    obtain ⟨hy₂1, hy₂2, hy₂3⟩ := (hmemN a y₂).mp hy₂
    have hy₁u : y₁ ≠ u := fun h => hy₁3 (h ▸ hau)
    by_cases h : ∃ t ∈ N b, t ≠ y₁ ∧ t ≠ u
    · obtain ⟨t, ht, hty, htu⟩ := h
      obtain ⟨ht1, ht2, ht3⟩ := (hmemN b t).mp ht
      exact tcc_case_odd G hα hn hodd z a b c y₁ t u hz hab hac hbc hza hzb hzc
        hy₁1 hy₁2 hy₁3 ht1 hty ht2 ht3 huz hub huc htu.symm hau
    · push_neg at h
      have hy₁b : y₁ ∈ N b := by
        by_contra hn'
        have : N b ⊆ {u} := fun t ht => mem_singleton.mpr (h t ht (fun e => hn' (e ▸ ht)))
        have := card_le_card this
        simp at this; omega
      obtain ⟨ht1, ht2, ht3⟩ := (hmemN b y₁).mp hy₁b
      exact tcc_case_odd G hα hn hodd z a b c y₂ y₁ u hz hab hac hbc hza hzb hzc
        hy₂1 hy₂2 hy₂3 ht1 hy12 ht2 ht3 huz hub huc hy₁u.symm hau

/-- **`|V| = Δ + 4` without three independent vertices.** -/
theorem tcc_of_noIndepTriple (hα : NoIndepTriple G) (hn : Fintype.card V = G.maxDegree + 4) :
    ∃ col : V ⊕ G.edgeSet → Fin (G.maxDegree + 2), IsTotalColoring G col := by
  classical
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨z, hzdeg⟩ := G.exists_maximal_degree_vertex
  set Qs : Finset V := univ.filter fun u => u ≠ z ∧ ¬ G.Adj z u with hQs
  have hQcard : #Qs = 3 := by
    have h1 := card_nonnbr G z
    have heq : (univ.filter fun u => ¬ G.Adj z u) = insert z Qs := by
      ext u
      simp only [hQs, mem_filter, mem_univ, true_and, mem_insert]
      by_cases huz : u = z
      · simp [huz]
      · simp [huz]
    rw [heq, card_insert_of_notMem (by simp [hQs])] at h1
    omega
  obtain ⟨q₁, q₂, q₃, h12, h13, h23, hQ⟩ := card_eq_three.mp hQcard
  have hq : ∀ u, (u = q₁ ∨ u = q₂ ∨ u = q₃) → u ≠ z ∧ ¬ G.Adj z u := by
    intro u hu
    have : u ∈ Qs := by rw [hQ]; simpa using hu
    simpa [hQs] using this
  obtain ⟨hzq₁, hnzq₁⟩ := hq q₁ (Or.inl rfl)
  obtain ⟨hzq₂, hnzq₂⟩ := hq q₂ (Or.inr (Or.inl rfl))
  obtain ⟨hzq₃, hnzq₃⟩ := hq q₃ (Or.inr (Or.inr rfl))
  have hzdom : ∀ w, w ≠ z → w ≠ q₁ → w ≠ q₂ → w ≠ q₃ → G.Adj z w := by
    intro w h0 h1 h2 h3
    by_contra hn'
    have : w ∈ Qs := by simp [hQs, h0, hn']
    rw [hQ] at this
    simp only [mem_insert, mem_singleton] at this
    rcases this with h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
  have hadj : ∀ a b, a ≠ z → ¬ G.Adj z a → b ≠ z → ¬ G.Adj z b → a ≠ b → G.Adj a b :=
    fun a b ha hna hb hnb hab => hα a z b ha (Ne.symm hb) hab (fun h => hna h.symm) hnb
  have a12 := hadj q₁ q₂ hzq₁ hnzq₁ hzq₂ hnzq₂ h12
  have a13 := hadj q₁ q₃ hzq₁ hnzq₁ hzq₃ hnzq₃ h13
  have a23 := hadj q₂ q₃ hzq₂ hnzq₂ hzq₃ hnzq₃ h23
  by_cases hC1 : ∃ u, u ≠ q₁ ∧ u ≠ q₂ ∧ u ≠ q₃ ∧ G.Adj q₁ u
  · obtain ⟨u, -, hu2, hu3, hau⟩ := hC1
    exact tcc_case_hub G hα hn z q₁ q₂ q₃ u hzdom a12 a13 a23 hzq₁.symm hzq₂.symm hzq₃.symm
      hnzq₁ hnzq₂ hnzq₃ hu2 hu3 hau
  by_cases hC2 : ∃ u, u ≠ q₁ ∧ u ≠ q₂ ∧ u ≠ q₃ ∧ G.Adj q₂ u
  · obtain ⟨u, hu1, -, hu3, hau⟩ := hC2
    exact tcc_case_hub G hα hn z q₂ q₁ q₃ u (fun w h0 h1 h2 h3 => hzdom w h0 h2 h1 h3)
      a12.symm a23 a13 hzq₂.symm hzq₁.symm hzq₃.symm hnzq₂ hnzq₁ hnzq₃ hu1 hu3 hau
  by_cases hC3 : ∃ u, u ≠ q₁ ∧ u ≠ q₂ ∧ u ≠ q₃ ∧ G.Adj q₃ u
  · obtain ⟨u, hu1, hu2, -, hau⟩ := hC3
    exact tcc_case_hub G hα hn z q₃ q₁ q₂ u (fun w h0 h1 h2 h3 => hzdom w h0 h2 h3 h1)
      a13.symm a23.symm a12 hzq₃.symm hzq₁.symm hzq₂.symm hnzq₃ hnzq₁ hnzq₂ hu1 hu2 hau
  push_neg at hC1 hC2
  exact tcc_case_split G hα hn z q₁ q₂ q₃ a12 a13 a23 hzq₁.symm hzq₂.symm hzq₃.symm
    fun w h1 h2 h3 => ⟨hC1 w h1 h2 h3, hC2 w h1 h2 h3⟩

/-- **Total colouring conjecture for `Δ(G) ≥ |V| − 4`** (Yap–Wang–Zhang 1989). -/
theorem tcc_of_card_le_add_four (h : Fintype.card V ≤ G.maxDegree + 4) :
    ∃ c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2), IsTotalColoring G c := by
  classical
  by_cases h3 : Fintype.card V ≤ G.maxDegree + 3
  · exact tcc_of_card_le_add_three G h3
  have hn : Fintype.card V = G.maxDegree + 4 := by omega
  by_cases hS : ∃ S : Finset V, #S = 3 ∧ ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v
  · obtain ⟨S, hS, hind⟩ := hS
    exact tcc_of_indep G S hind (by omega)
  · refine tcc_of_noIndepTriple G ?_ hn
    intro a b c hab hbc hac h1 h2
    by_contra h3'
    refine hS ⟨{a, b, c}, ?_, ?_⟩
    · rw [card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]
    · intro u hu v hv huv
      simp only [mem_insert, mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
      · exact G.irrefl huv
      · exact h1 huv
      · exact h3' huv
      · exact h1 huv.symm
      · exact G.irrefl huv
      · exact h2 huv
      · exact h3' huv.symm
      · exact h2 huv.symm
      · exact G.irrefl huv

end TCCHighLib
