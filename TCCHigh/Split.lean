/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import TCCHigh.Alpha2

/-!
# `|V| = Δ + 4`: a triangle plus a disjoint clique

If `q₁ q₂ q₃` is a triangle with no edges to the rest of the graph and `G` has no three
independent vertices, the rest `R` is a clique. With `S₁ = {q₁, z}`, `S₂ = {q₂, c₂}`
(`z, c₂ ∈ R`), the path `q₁ q₃ q₂` and a path through `R ∖ {c₂}` starting at `z` (extended to
`c₂` when `|V|` is even) give the data of `tcc_frame`.
-/

@[expose] public section

namespace TCCHighLib

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **A triangle without outside neighbours.** -/
theorem tcc_case_split (hα : NoIndepTriple G) (hn : Fintype.card V = G.maxDegree + 4)
    (z q₁ q₂ q₃ : V) (hq12 : G.Adj q₁ q₂) (hq13 : G.Adj q₁ q₃) (hq23 : G.Adj q₂ q₃)
    (hzq₁ : z ≠ q₁) (hzq₂ : z ≠ q₂) (hzq₃ : z ≠ q₃)
    (hD : ∀ w, w ≠ q₁ → w ≠ q₂ → w ≠ q₃ → ¬ G.Adj q₁ w ∧ ¬ G.Adj q₂ w) :
    ∃ c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2), IsTotalColoring G c := by
  classical
  have hq₁q₂ : q₁ ≠ q₂ := G.ne_of_adj hq12
  have hq₁q₃ : q₁ ≠ q₃ := G.ne_of_adj hq13
  have hq₂q₃ : q₂ ≠ q₃ := G.ne_of_adj hq23
  set R : Finset V := ({q₁, q₂, q₃} : Finset V)ᶜ with hR
  have hmemR : ∀ w, w ∈ R ↔ w ≠ q₁ ∧ w ≠ q₂ ∧ w ≠ q₃ := by intro w; simp [hR]
  have hRadj : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → G.Adj a b := by
    intro a ha b hb hab
    obtain ⟨a1, a2, a3⟩ := (hmemR a).mp ha
    obtain ⟨b1, b2, b3⟩ := (hmemR b).mp hb
    exact hα a q₁ b a1 (Ne.symm b1) hab (fun h => (hD a a1 a2 a3).1 h.symm) (hD b b1 b2 b3).1
  have hcard3 : #({q₁, q₂, q₃} : Finset V) = 3 := by
    rw [card_insert_of_notMem (by simp [hq₁q₂, hq₁q₃]), card_pair hq₂q₃]
  have hRcard : #R = Fintype.card V - 3 := by rw [hR, card_compl, hcard3]
  have hΔ2 : 2 ≤ G.maxDegree := by
    have hsub : ({q₂, q₃} : Finset V) ⊆ G.neighborFinset q₁ := by
      intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl <;> simp [hq12, hq13]
    have h1 := card_le_card hsub
    rw [card_pair hq₂q₃, card_neighborFinset_eq_degree] at h1
    have := G.degree_le_maxDegree q₁
    omega
  have hzR : z ∈ R := (hmemR z).mpr ⟨hzq₁, hzq₂, hzq₃⟩
  obtain ⟨c₂, hc₂R, hc₂z⟩ := exists_mem_ne (s := R) (by omega) z
  obtain ⟨c21, c22, c23⟩ := (hmemR c₂).mp hc₂R
  set mid : List V := ((R.erase z).erase c₂).toList with hmid
  have hmemmid : ∀ w, w ∈ mid ↔ w ∈ R ∧ w ≠ z ∧ w ≠ c₂ := by
    intro w; simp only [hmid, mem_toList, mem_erase]; tauto
  have hmidlen : mid.length = Fintype.card V - 5 := by
    rw [hmid, length_toList, card_erase_of_mem (mem_erase.mpr ⟨hc₂z, hc₂R⟩),
      card_erase_of_mem hzR, hRcard]; omega
  set ext : List V := if Even (Fintype.card V) then [c₂] else [] with hext
  have hmemext : ∀ w, w ∈ ext → w = c₂ := by
    intro w hw
    rw [hext] at hw
    split_ifs at hw
    · exact List.mem_singleton.mp hw
    · simp at hw
  set l : List V := z :: (mid ++ ext) with hl
  have hlR : ∀ w ∈ l, w ∈ R := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hzR
    rcases List.mem_append.mp hw with hw | hw
    · exact ((hmemmid w).mp hw).1
    · rw [hmemext w hw]; exact hc₂R
  have hnd : l.Nodup := by
    rw [hl, List.nodup_cons, List.nodup_append]
    refine ⟨?_, ⟨nodup_toList _, ?_, ?_⟩⟩
    · intro h
      rcases List.mem_append.mp h with h | h
      · exact ((hmemmid z).mp h).2.1 rfl
      · exact hc₂z (hmemext z h).symm
    · rw [hext]; split_ifs <;> simp
    · intro a ha b hb hab
      subst hab
      exact ((hmemmid a).mp ha).2.2 (hmemext a hb)
  have hc : l.IsChain G.Adj := isChain_of_pairwise_adj G l hnd
    fun a ha b hb hab => hRadj a (hlR a ha) b (hlR b hb) hab
  have hlen : l.length = 1 + (Fintype.card V - 5) + ext.length := by
    rw [hl, List.length_cons, List.length_append, hmidlen]; omega
  have hodd : ¬ Even l.length := by
    rw [hlen, hext]
    split_ifs with h
    · obtain ⟨k, hk⟩ := h
      simp only [List.length_singleton]
      rw [Nat.not_even_iff_odd]; exact ⟨k - 2, by omega⟩
    · simp only [List.length_nil]
      rcases Nat.even_or_odd (Fintype.card V) with h' | ⟨k, hk⟩
      · exact absurd h' h
      · rw [Nat.not_even_iff_odd]; exact ⟨k - 2, by omega⟩
  have hlen2 : 2 ≤ l.length := by
    rw [hlen, hext]
    split_ifs with h
    · simp
    · rcases Nat.even_or_odd (Fintype.card V) with h' | ⟨k, hk⟩
      · exact absurd h' h
      · simp only [List.length_nil]; omega
  obtain ⟨lst, hlst⟩ : ∃ b, l.getLast? = some b := Option.isSome_iff_exists.mp
    (by rw [List.getLast?_isSome, hl]; simp)
  have hlstl : lst ∈ l := List.mem_of_getLast? hlst
  have hhead := alt_head' hnd hlen2 (show l.head? = some z by rw [hl]; rfl)
  have hlast := alt_last l hnd hlen2 lst hlst
  have hlast2 : Covered (alt l).2 lst := hlast.2.mpr hodd
  have hint : ∀ w ∈ l, w ≠ z → w ≠ lst → Covered (alt l).1 w ∧ Covered (alt l).2 w := by
    intro w hw hwz hwl
    refine alt_interior l hnd w hw ?_ ?_
    · rw [hl]; simp only [List.head?_cons, ne_eq, Option.some.injEq]; exact Ne.symm hwz
    · rw [hlst]; intro h; exact hwl (Option.some.inj h).symm
  have hout : ∀ w, w ∉ l → ¬ Covered (alt l).1 w ∧ ¬ Covered (alt l).2 w :=
    fun w hw => not_covered_alt hw
  have hq₁l : q₁ ∉ l := fun h => ((hmemR q₁).mp (hlR q₁ h)).1 rfl
  have hq₂l : q₂ ∉ l := fun h => ((hmemR q₂).mp (hlR q₂ h)).2.1 rfl
  have hq₃l : q₃ ∉ l := fun h => ((hmemR q₃).mp (hlR q₃ h)).2.2 rfl
  have hc₂cov : ¬ Covered (alt l).1 c₂ := by
    by_cases hc₂l : c₂ ∈ l
    · have hev : Even (Fintype.card V) := by
        by_contra hne
        rcases List.mem_cons.mp hc₂l with h | h
        · exact hc₂z h
        rcases List.mem_append.mp h with h | h
        · exact ((hmemmid c₂).mp h).2.2 rfl
        · rw [hext, if_neg hne] at h; simp at h
      have : lst = c₂ := by
        have h2 : l.getLast? = some c₂ := by
          rw [hl, hext, if_pos hev, ← List.cons_append, List.getLast?_concat]
        rw [hlst] at h2; exact Option.some.inj h2
      rw [← this]
      exact fun h => hodd (hlast.1.mp h)
    · exact (hout _ hc₂l).1
  have hnq₁z : ¬ G.Adj q₁ z := (hD z hzq₁ hzq₂ hzq₃).1
  have hnq₂c₂ : ¬ G.Adj q₂ c₂ := (hD c₂ c21 c22 c23).2
  have hM₁0 : IsMatchingAvoiding G (alt l).2 {q₁, z} := by
    refine (isMatchingAvoiding_alt G hnd hc {q₁, z}).2 ?_
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact (hout _ hq₁l).2
    · exact hhead.2
  have hM₁ : IsMatchingAvoiding G (insert s(q₃, q₂) (alt l).2) {q₁, z} :=
    isMatchingAvoiding_insert G hM₁0 hq23.symm (hout _ hq₃l).2 (hout _ hq₂l).2
      (by simp [hq₁q₃.symm, hzq₃.symm]) (by simp [hq₁q₂.symm, hzq₂.symm])
  have hM₂0 : IsMatchingAvoiding G (alt l).1 {q₂, c₂} := by
    refine (isMatchingAvoiding_alt G hnd hc {q₂, c₂}).1 ?_
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact (hout _ hq₂l).1
    · exact hc₂cov
  have hM₂ : IsMatchingAvoiding G (insert s(q₁, q₃) (alt l).1) {q₂, c₂} :=
    isMatchingAvoiding_insert G hM₂0 hq13 (hout _ hq₁l).1 (hout _ hq₃l).1
      (by simp [hq₁q₂, Ne.symm c21]) (by simp [hq₂q₃.symm, Ne.symm c23])
  have hdisj : Disjoint (insert s(q₃, q₂) (alt l).2) (insert s(q₁, q₃) (alt l).1) := by
    refine disjoint_left.mpr fun e he1 he2 => ?_
    rcases mem_insert.mp he1 with rfl | he1 <;> rcases mem_insert.mp he2 with he2 | he2
    · have : q₂ ∈ s(q₁, q₃) := he2 ▸ Sym2.mem_mk_right _ _
      rcases Sym2.mem_iff.mp this with h | h
      · exact hq₁q₂ h.symm
      · exact hq₂q₃ h
    · exact hq₂l (alt_support l (Or.inl he2) q₂ (Sym2.mem_mk_right _ _))
    · subst he2
      exact hq₁l (alt_support l (Or.inr he1) q₁ (Sym2.mem_mk_left _ _))
    · exact disjoint_left.mp (alt_disjoint l hnd) he2 he1
  refine tcc_frame G hn q₁ z q₂ c₂ hzq₁.symm hq₁q₂ (Ne.symm c21) hzq₂ (Ne.symm hc₂z)
    (Ne.symm c22) hnq₁z hnq₂c₂ _ _ hM₁ hM₂ hdisj lst ?_ (fun _ _ _ _ => Or.inl
      (covered_insert hlast2)) ?_
  · intro w h1 h2 h3 h4 h5
    by_cases hw3 : w = q₃
    · subst hw3
      exact ⟨⟨s(w, q₂), mem_insert_self _ _, Sym2.mem_mk_left _ _⟩,
        ⟨s(q₁, w), mem_insert_self _ _, Sym2.mem_mk_right _ _⟩⟩
    have hwl : w ∈ l := by
      refine List.mem_cons_of_mem _ (List.mem_append_left _ ((hmemmid w).mpr ?_))
      exact ⟨(hmemR w).mpr ⟨h1, h3, hw3⟩, h2, h4⟩
    have := hint w hwl h2 h5
    exact ⟨covered_insert this.2, covered_insert this.1⟩
  · have key : ∀ a, a ≠ lst → ¬ Covered (insert s(q₃, q₂) (alt l).2) a →
        ¬ Covered (insert s(q₁, q₃) (alt l).1) a → a = c₂ := by
      intro a ha h1 h2
      by_contra hac
      by_cases ha1 : a = q₁
      · exact h2 ⟨s(q₁, q₃), mem_insert_self _ _, ha1 ▸ Sym2.mem_mk_left _ _⟩
      by_cases ha2 : a = q₂
      · exact h1 ⟨s(q₃, q₂), mem_insert_self _ _, ha2 ▸ Sym2.mem_mk_right _ _⟩
      by_cases ha3 : a = q₃
      · exact h1 ⟨s(q₃, q₂), mem_insert_self _ _, ha3 ▸ Sym2.mem_mk_left _ _⟩
      have hal : a ∈ l := by
        by_cases haz : a = z
        · rw [haz, hl]; exact List.mem_cons_self
        · refine List.mem_cons_of_mem _ (List.mem_append_left _ ((hmemmid a).mpr ?_))
          exact ⟨(hmemR a).mpr ⟨ha1, ha2, ha3⟩, haz, hac⟩
      by_cases haz : a = z
      · exact h2 (covered_insert (haz ▸ hhead.1))
      · exact h2 (covered_insert (hint a hal haz ha).1)
    intro u w hu hw hu1 hu2 hw1 hw2
    rw [key u hu hu1 hu2, key w hw hw1 hw2]
    exact G.irrefl

end TCCHighLib
