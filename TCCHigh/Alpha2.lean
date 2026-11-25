/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import TCCHigh.Frame

/-!
# `|V| = Δ + 4` without three independent vertices: the constructions

Let `|V| = Δ + 4` and suppose `G` has no three pairwise non-adjacent vertices. Take a vertex `z`
of degree `Δ`; its three non-neighbours `q₁, q₂, q₃` form a triangle, and `z` is adjacent to
everything else, so every vertex set containing `z` and avoiding the `qᵢ` is connected. The data
of `tcc_frame` come from one Hamiltonian path (`ham_path_ends`):

* `|V|` even (`tcc_case_even`): `S₁ = {q₁, y}`, `S₂ = {q₂, t}` and a path from `q₁` to `y`
  through all of `V ∖ S₂` (`q₃` has a neighbour `v ∉ {y, t}` outside the triangle, which keeps
  `V ∖ (S₁ ∪ S₂)` connected); its odd-numbered edges form `M₂`, the even-numbered ones `M₁`.
* `|V|` odd (`tcc_case_odd`): `S₁ = {q₁, y}`, `S₂ = {q₂, t}`, a path from `q₁` to `y` through
  `V ∖ (S₂ ∪ {q₃})`, and the edge `q₂q₃` is added to `M₁`.
* If no `qᵢ` has a neighbour outside the triangle (`tcc_case_split`), `G` is a triangle plus a
  disjoint clique; the path `q₁ q₃ q₂` and a path through the clique are used.
-/

@[expose] public section

namespace TCCHighLib

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Connectivity of a vertex set with a hub `z` adjacent to all its vertices but possibly `c`,
where `c` (if present) has a neighbour `v ≠ z` in the set. -/
lemma conn_of_hub (K : Finset V) (z c v : V) (hz : z ∈ K) (hv : v ∈ K) (hvc : v ≠ c)
    (hvz : v ≠ z) (hcv : c ∈ K → G.Adj c v) (hdom : ∀ w ∈ K, w ≠ z → w ≠ c → G.Adj z w) :
    ∀ P ⊆ K, P.Nonempty → P ≠ K → ∃ p ∈ P, ∃ r ∈ K, r ∉ P ∧ G.Adj p r := by
  intro P hP hne hPK
  obtain ⟨r, hrK, hrP⟩ : ∃ r ∈ K, r ∉ P := by
    by_contra h
    push_neg at h
    exact hPK (Subset.antisymm hP h)
  by_cases hzP : z ∈ P
  · by_cases hrc : r = c
    · subst hrc
      by_cases hvP : v ∈ P
      · exact ⟨v, hvP, r, hrK, hrP, (hcv hrK).symm⟩
      · exact ⟨z, hzP, v, hv, hvP, hdom v hv hvz hvc⟩
    · exact ⟨z, hzP, r, hrK, hrP, hdom r hrK (fun h => hrP (h ▸ hzP)) hrc⟩
  · obtain ⟨p, hp⟩ := hne
    by_cases hpc : p = c
    · subst hpc
      by_cases hvP : v ∈ P
      · exact ⟨v, hvP, z, hz, hzP, (hdom v hv hvz hvc).symm⟩
      · exact ⟨p, hp, v, hv, hvP, hcv (hP hp)⟩
    · exact ⟨p, hp, z, hz, hzP, (hdom p (hP hp) (fun h => hzP (h ▸ hp)) hpc).symm⟩

lemma length_eq_card_of_mem_iff (l : List V) (hnd : l.Nodup) (T : Finset V)
    (h : ∀ v, v ∈ l ↔ v ∈ T) : l.length = #T := by
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext v
  simp [h]

/-- Coverage of the vertices of an even path from `a` to `b` by its alternating matchings. -/
lemma alt_even_cover {l : List V} (hnd : l.Nodup) {a b : V} (hh : l.head? = some a)
    (hl : l.getLast? = some b) (hlen : 2 ≤ l.length) (hev : Even l.length) :
    (Covered (alt l).1 a ∧ ¬ Covered (alt l).2 a) ∧ (Covered (alt l).1 b ∧ ¬ Covered (alt l).2 b) ∧
      (∀ w ∈ l, w ≠ a → w ≠ b → Covered (alt l).1 w ∧ Covered (alt l).2 w) := by
  have hlast := alt_last l hnd hlen b hl
  refine ⟨alt_head' hnd hlen hh, ⟨hlast.1.mpr hev, fun h => hlast.2.mp h hev⟩, ?_⟩
  intro w hw hwa hwb
  refine alt_interior l hnd w hw ?_ ?_
  · rw [hh]; intro h; exact hwa (Option.some.inj h).symm
  · rw [hl]; intro h; exact hwb (Option.some.inj h).symm

/-- **Even order.** -/
theorem tcc_case_even (hα : NoIndepTriple G) (hn : Fintype.card V = G.maxDegree + 4)
    (hev : Even (Fintype.card V)) (z q₁ q₂ q₃ y t v : V)
    (hz : ∀ w, w ≠ z → w ≠ q₁ → w ≠ q₂ → w ≠ q₃ → G.Adj z w)
    (hq12 : G.Adj q₁ q₂) (hq13 : G.Adj q₁ q₃) (hq23 : G.Adj q₂ q₃)
    (hzq₁ : z ≠ q₁) (hzq₂ : z ≠ q₂) (hzq₃ : z ≠ q₃)
    (hyz : y ≠ z) (hyq₁ : y ≠ q₁) (hq₁y : ¬ G.Adj q₁ y)
    (htz : t ≠ z) (hty : t ≠ y) (htq₂ : t ≠ q₂) (hq₂t : ¬ G.Adj q₂ t)
    (hvz : v ≠ z) (hvy : v ≠ y) (hvt : v ≠ t) (hq₃v : G.Adj q₃ v)
    (hvq₁ : v ≠ q₁) (hvq₂ : v ≠ q₂) :
    ∃ c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2), IsTotalColoring G c := by
  classical
  have hyq₂ : y ≠ q₂ := fun h => hq₁y (h ▸ hq12)
  have hyq₃ : y ≠ q₃ := fun h => hq₁y (h ▸ hq13)
  have htq₁ : t ≠ q₁ := fun h => hq₂t (h ▸ hq12.symm)
  have htq₃ : t ≠ q₃ := fun h => hq₂t (h ▸ hq23)
  have hvq₃ : v ≠ q₃ := fun h => G.irrefl (h ▸ hq₃v)
  have hq₁q₂ : q₁ ≠ q₂ := G.ne_of_adj hq12
  have hyzadj : G.Adj y z := (hz y hyz hyq₁ hyq₂ hyq₃).symm
  set K : Finset V := ({q₁, q₂, y, t} : Finset V)ᶜ with hK
  have hmemK : ∀ w, w ∈ K ↔ w ≠ q₁ ∧ w ≠ q₂ ∧ w ≠ y ∧ w ≠ t := by
    intro w; simp [hK]
  have hzK : z ∈ K := (hmemK z).mpr ⟨hzq₁, hzq₂, hyz.symm, htz.symm⟩
  have hq₃K : q₃ ∈ K := (hmemK q₃).mpr ⟨(G.ne_of_adj hq13).symm, (G.ne_of_adj hq23).symm,
    hyq₃.symm, htq₃.symm⟩
  have hvK : v ∈ K := (hmemK v).mpr ⟨hvq₁, hvq₂, hvy, hvt⟩
  have hconn := conn_of_hub G K z q₃ v hzK hvK hvq₃ hvz (fun _ => hq₃v)
    (fun w hw hwz hwq₃ => by
      obtain ⟨h1, h2, -, -⟩ := (hmemK w).mp hw
      exact hz w hwz h1 h2 hwq₃)
  obtain ⟨l, hnd, hc, hh, hl, hmem⟩ := ham_path_ends G hα K q₁ y
    (fun h => ((hmemK q₁).mp h).1 rfl) (fun h => ((hmemK y).mp h).2.2.1 rfl) hyq₁.symm hq₁y
    ⟨z, hzK⟩ hconn ⟨q₃, hq₃K, hq13⟩ ⟨z, hzK, hyzadj⟩
  have hmem' : ∀ w, w ∈ l ↔ w ∈ ({q₂, t} : Finset V)ᶜ := by
    intro w
    rw [hmem, hmemK]
    simp only [mem_compl, mem_insert, mem_singleton, not_or]
    constructor
    · rintro (rfl | rfl | ⟨-, h2, -, h4⟩)
      · exact ⟨hq₁q₂, htq₁.symm⟩
      · exact ⟨hyq₂, hty.symm⟩
      · exact ⟨h2, h4⟩
    · rintro ⟨h2, h4⟩
      by_cases h1 : w = q₁
      · exact Or.inl h1
      by_cases h3 : w = y
      · exact Or.inr (Or.inl h3)
      · exact Or.inr (Or.inr ⟨h1, h2, h3, h4⟩)
  have hlen : l.length = Fintype.card V - 2 := by
    rw [length_eq_card_of_mem_iff l hnd _ hmem', card_compl, card_pair htq₂.symm]
  have hlen2 : 2 ≤ l.length := by rw [hlen]; omega
  have hevl : Even l.length := by
    rw [hlen]; obtain ⟨k, hk⟩ := hev; exact ⟨k - 1, by omega⟩
  obtain ⟨hhead, hlast, hint⟩ := alt_even_cover hnd hh hl hlen2 hevl
  have hout : ∀ w, w ∉ l → ¬ Covered (alt l).1 w ∧ ¬ Covered (alt l).2 w :=
    fun w hw => not_covered_alt hw
  have hq₂l : q₂ ∉ l := fun h => by
    have := (hmem' q₂).mp h; simp at this
  have htl : t ∉ l := fun h => by
    have := (hmem' t).mp h; simp at this
  have hM₁ : IsMatchingAvoiding G (alt l).2 {q₁, y} := by
    refine (isMatchingAvoiding_alt G hnd hc {q₁, y}).2 ?_
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hhead.2
    · exact hlast.2
  have hM₂ : IsMatchingAvoiding G (alt l).1 {q₂, t} := by
    refine (isMatchingAvoiding_alt G hnd hc {q₂, t}).1 ?_
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact (hout _ hq₂l).1
    · exact (hout _ htl).1
  refine tcc_frame G hn q₁ y q₂ t hyq₁.symm hq₁q₂ htq₁.symm hyq₂ hty.symm htq₂.symm hq₁y hq₂t
    (alt l).2 (alt l).1 hM₁ hM₂ (alt_disjoint l hnd).symm q₁ ?_ (fun h => absurd rfl h) ?_
  · intro w h1 h2 h3 h4 _
    have hwl : w ∈ l := (hmem' w).mpr (by simp [h3, h4])
    exact (hint w hwl h1 h2).symm
  · have key : ∀ a, a ≠ q₁ → ¬ Covered (alt l).2 a → ¬ Covered (alt l).1 a → a = q₂ ∨ a = t := by
      intro a ha h1 h2
      by_contra hcon
      push_neg at hcon
      have hal : a ∈ l := (hmem' a).mpr (by simp [hcon.1, hcon.2])
      by_cases hay : a = y
      · exact h2 (hay ▸ hlast.1)
      · exact h2 (hint a hal ha hay).1
    intro u w hu hw hu1 hu2 hw1 hw2
    rcases key u hu hu1 hu2 with rfl | rfl <;> rcases key w hw hw1 hw2 with rfl | rfl
    · exact G.irrefl
    · exact hq₂t
    · exact fun h => hq₂t h.symm
    · exact G.irrefl

/-- **Odd order.** -/
theorem tcc_case_odd (hα : NoIndepTriple G) (hn : Fintype.card V = G.maxDegree + 4)
    (hodd : ¬ Even (Fintype.card V)) (z q₁ q₂ q₃ y t u : V)
    (hz : ∀ w, w ≠ z → w ≠ q₁ → w ≠ q₂ → w ≠ q₃ → G.Adj z w)
    (hq12 : G.Adj q₁ q₂) (hq13 : G.Adj q₁ q₃) (hq23 : G.Adj q₂ q₃)
    (hzq₁ : z ≠ q₁) (hzq₂ : z ≠ q₂) (hzq₃ : z ≠ q₃)
    (hyz : y ≠ z) (hyq₁ : y ≠ q₁) (hq₁y : ¬ G.Adj q₁ y)
    (htz : t ≠ z) (hty : t ≠ y) (htq₂ : t ≠ q₂) (hq₂t : ¬ G.Adj q₂ t)
    (huz : u ≠ z) (huq₂ : u ≠ q₂) (huq₃ : u ≠ q₃) (hut : u ≠ t) (hq₁u : G.Adj q₁ u) :
    ∃ c : V ⊕ G.edgeSet → Fin (G.maxDegree + 2), IsTotalColoring G c := by
  classical
  have hyq₂ : y ≠ q₂ := fun h => hq₁y (h ▸ hq12)
  have hyq₃ : y ≠ q₃ := fun h => hq₁y (h ▸ hq13)
  have htq₁ : t ≠ q₁ := fun h => hq₂t (h ▸ hq12.symm)
  have htq₃ : t ≠ q₃ := fun h => hq₂t (h ▸ hq23)
  have huq₁ : u ≠ q₁ := (G.ne_of_adj hq₁u).symm
  have huy : u ≠ y := fun h => hq₁y (h ▸ hq₁u)
  have hq₁q₂ : q₁ ≠ q₂ := G.ne_of_adj hq12
  have hq₁q₃ : q₁ ≠ q₃ := G.ne_of_adj hq13
  have hq₂q₃ : q₂ ≠ q₃ := G.ne_of_adj hq23
  have hyzadj : G.Adj y z := (hz y hyz hyq₁ hyq₂ hyq₃).symm
  set K : Finset V := ({q₁, q₂, q₃, y, t} : Finset V)ᶜ with hK
  have hmemK : ∀ w, w ∈ K ↔ w ≠ q₁ ∧ w ≠ q₂ ∧ w ≠ q₃ ∧ w ≠ y ∧ w ≠ t := by
    intro w; simp [hK]
  have hzK : z ∈ K := (hmemK z).mpr ⟨hzq₁, hzq₂, hzq₃, hyz.symm, htz.symm⟩
  have huK : u ∈ K := (hmemK u).mpr ⟨huq₁, huq₂, huq₃, huy, hut⟩
  have hq₁K : q₁ ∉ K := fun h => ((hmemK q₁).mp h).1 rfl
  have hconn := conn_of_hub G K z q₁ u hzK huK huq₁ huz (fun h => absurd h hq₁K)
    (fun w hw hwz _ => by
      obtain ⟨h1, h2, h3, -, -⟩ := (hmemK w).mp hw
      exact hz w hwz h1 h2 h3)
  obtain ⟨l, hnd, hc, hh, hl, hmem⟩ := ham_path_ends G hα K q₁ y hq₁K
    (fun h => ((hmemK y).mp h).2.2.2.1 rfl) hyq₁.symm hq₁y ⟨z, hzK⟩ hconn ⟨u, huK, hq₁u⟩
    ⟨z, hzK, hyzadj⟩
  have hmem' : ∀ w, w ∈ l ↔ w ∈ ({q₂, q₃, t} : Finset V)ᶜ := by
    intro w
    rw [hmem, hmemK]
    simp only [mem_compl, mem_insert, mem_singleton, not_or]
    constructor
    · rintro (rfl | rfl | ⟨-, h2, h3, -, h5⟩)
      · exact ⟨hq₁q₂, hq₁q₃, htq₁.symm⟩
      · exact ⟨hyq₂, hyq₃, hty.symm⟩
      · exact ⟨h2, h3, h5⟩
    · rintro ⟨h2, h3, h5⟩
      by_cases h1 : w = q₁
      · exact Or.inl h1
      by_cases h4 : w = y
      · exact Or.inr (Or.inl h4)
      · exact Or.inr (Or.inr ⟨h1, h2, h3, h4, h5⟩)
  have hcard3 : #({q₂, q₃, t} : Finset V) = 3 := by
    rw [card_insert_of_notMem (by simp [hq₂q₃, htq₂.symm]), card_pair htq₃.symm]
  have hlen : l.length = Fintype.card V - 3 := by
    rw [length_eq_card_of_mem_iff l hnd _ hmem', card_compl, hcard3]
  have hlen2 : 2 ≤ l.length := by
    rw [hlen]
    -- `n` is odd and `n ≥ 4`, hence `n ≥ 5`
    rcases Nat.even_or_odd (Fintype.card V) with h | ⟨k, hk⟩
    · exact absurd h hodd
    · omega
  have hevl : Even l.length := by
    rw [hlen]
    rcases Nat.even_or_odd (Fintype.card V) with h | ⟨k, hk⟩
    · exact absurd h hodd
    · exact ⟨k - 1, by omega⟩
  obtain ⟨hhead, hlast, hint⟩ := alt_even_cover hnd hh hl hlen2 hevl
  have hout : ∀ w, w ∉ l → ¬ Covered (alt l).1 w ∧ ¬ Covered (alt l).2 w :=
    fun w hw => not_covered_alt hw
  have hq₂l : q₂ ∉ l := fun h => by have := (hmem' q₂).mp h; simp at this
  have hq₃l : q₃ ∉ l := fun h => by have := (hmem' q₃).mp h; simp at this
  have htl : t ∉ l := fun h => by have := (hmem' t).mp h; simp at this
  have hM₁0 : IsMatchingAvoiding G (alt l).2 {q₁, y} := by
    refine (isMatchingAvoiding_alt G hnd hc {q₁, y}).2 ?_
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hhead.2
    · exact hlast.2
  have hM₁ : IsMatchingAvoiding G (insert s(q₂, q₃) (alt l).2) {q₁, y} :=
    isMatchingAvoiding_insert G hM₁0 hq23 (hout _ hq₂l).2 (hout _ hq₃l).2
      (by simp [hq₁q₂.symm, hyq₂.symm]) (by simp [hq₁q₃.symm, hyq₃.symm])
  have hM₂ : IsMatchingAvoiding G (alt l).1 {q₂, t} := by
    refine (isMatchingAvoiding_alt G hnd hc {q₂, t}).1 ?_
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact (hout _ hq₂l).1
    · exact (hout _ htl).1
  have hdisj : Disjoint (insert s(q₂, q₃) (alt l).2) (alt l).1 := by
    refine disjoint_left.mpr fun e he1 he2 => ?_
    rcases mem_insert.mp he1 with rfl | he1
    · exact hq₂l (alt_support l (Or.inl he2) q₂ (Sym2.mem_mk_left _ _))
    · exact disjoint_left.mp (alt_disjoint l hnd) he2 he1
  have hq₃cov : Covered (insert s(q₂, q₃) (alt l).2) q₃ :=
    ⟨s(q₂, q₃), mem_insert_self _ _, Sym2.mem_mk_right _ _⟩
  have hq₂cov : Covered (insert s(q₂, q₃) (alt l).2) q₂ :=
    ⟨s(q₂, q₃), mem_insert_self _ _, Sym2.mem_mk_left _ _⟩
  refine tcc_frame G hn q₁ y q₂ t hyq₁.symm hq₁q₂ htq₁.symm hyq₂ hty.symm htq₂.symm hq₁y hq₂t
    _ _ hM₁ hM₂ hdisj q₃ ?_ (fun _ _ _ _ => Or.inl hq₃cov) ?_
  · intro w h1 h2 h3 h4 h5
    have hwl : w ∈ l := (hmem' w).mpr (by simp [h3, h5, h4])
    have := hint w hwl h1 h2
    exact ⟨covered_insert this.2, this.1⟩
  · have key : ∀ a, a ≠ q₃ → ¬ Covered (insert s(q₂, q₃) (alt l).2) a →
        ¬ Covered (alt l).1 a → a = t := by
      intro a ha h1 h2
      by_cases hal : a ∈ l
      · exfalso
        by_cases ha1 : a = q₁
        · exact h2 (ha1 ▸ hhead.1)
        by_cases hay : a = y
        · exact h2 (hay ▸ hlast.1)
        · exact h2 (hint a hal ha1 hay).1
      · have := (hmem' a).not.mp hal
        simp only [mem_compl, mem_insert, mem_singleton, not_not] at this
        rcases this with rfl | rfl | rfl
        · exact absurd hq₂cov h1
        · exact absurd rfl ha
        · rfl
    intro u' w hu hw hu1 hu2 hw1 hw2
    rw [key u' hu hu1 hu2, key w hw hw1 hw2]
    exact G.irrefl

end TCCHighLib
