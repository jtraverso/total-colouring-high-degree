/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import TCCHigh.Level1

/-!
# Exchange arguments for coverage-maximal matchings

The "Enlarge-Matching Argument" of Yap–Wang–Zhang: if `M` is a matching avoiding `S` that
covers as many vertices of `A` as possible, and `u, u' ∈ A` are uncovered, then every neighbour
`a ∉ S` of `u` is covered, and its partner `b` is not adjacent to `u'` (otherwise
`M − ab + ua + bu'` covers more). Hence the partner map injects the neighbours of `u` outside `S`
into the non-neighbours of `u'`.
-/

@[expose] public section

namespace TCCHighLib

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The partner of `a` in `M` (or `a` itself if `a` is uncovered). -/
noncomputable def partner (M : Finset (Sym2 V)) (a : V) : V :=
  if h : ∃ e ∈ M, a ∈ e then Sym2.Mem.other (Classical.choose_spec h).2 else a

variable (Γ : SimpleGraph V)

lemma partner_spec {M : Finset (Sym2 V)} {S : Finset V} (hM : IsMatchingAvoiding Γ M S) {a : V}
    {e : Sym2 V} (he : e ∈ M) (ha : a ∈ e) : e = s(a, partner M a) := by
  have h : ∃ e ∈ M, a ∈ e := ⟨e, he, ha⟩
  have he' := (Classical.choose_spec h).1
  have ha' := (Classical.choose_spec h).2
  have heq : Classical.choose h = e := by
    by_contra hne
    exact hM.2.1 _ he' e he hne a ha' ha
  unfold partner
  rw [dif_pos h, Sym2.other_spec ha', heq]

lemma partner_mem {M : Finset (Sym2 V)} {S : Finset V} (hM : IsMatchingAvoiding Γ M S) {a : V}
    (ha : Covered M a) : s(a, partner M a) ∈ M := by
  obtain ⟨e, he, hae⟩ := ha
  rw [← partner_spec Γ hM he hae]
  exact he

lemma partner_adj {M : Finset (Sym2 V)} {S : Finset V} (hM : IsMatchingAvoiding Γ M S) {a : V}
    (ha : Covered M a) : Γ.Adj a (partner M a) :=
  hM.1 _ (partner_mem Γ hM ha)

lemma partner_covered {M : Finset (Sym2 V)} {S : Finset V} (hM : IsMatchingAvoiding Γ M S)
    {a : V} (ha : Covered M a) : Covered M (partner M a) :=
  ⟨_, partner_mem Γ hM ha, Sym2.mem_mk_right _ _⟩

lemma partner_not_mem {M : Finset (Sym2 V)} {S : Finset V} (hM : IsMatchingAvoiding Γ M S)
    {a : V} (ha : Covered M a) : partner M a ∉ S :=
  hM.2.2 _ (partner_mem Γ hM ha) _ (Sym2.mem_mk_right _ _)

lemma partner_injOn {M : Finset (Sym2 V)} {S : Finset V} (hM : IsMatchingAvoiding Γ M S)
    {a a' : V} (ha : Covered M a) (ha' : Covered M a') (h : partner M a = partner M a') :
    a = a' := by
  have h1 := partner_mem Γ hM ha
  have h2 := partner_mem Γ hM ha'
  by_contra hne
  have hne' : s(a, partner M a) ≠ s(a', partner M a') := by
    rw [h]; intro heq; exact hne (Sym2.congr_left.mp heq)
  exact hM.2.1 _ h1 _ h2 hne' (partner M a) (Sym2.mem_mk_right _ _)
    (by rw [h]; exact Sym2.mem_mk_right _ _)

lemma covered_erase_of_ne {M : Finset (Sym2 V)} {S : Finset V} (hM : IsMatchingAvoiding Γ M S)
    {a b v : V} (hab : s(a, b) ∈ M) (hv : Covered M v) (hva : v ≠ a) (hvb : v ≠ b) :
    Covered (M.erase s(a, b)) v := by
  obtain ⟨f, hf, hvf⟩ := hv
  refine ⟨f, mem_erase.mpr ⟨?_, hf⟩, hvf⟩
  rintro rfl
  rcases Sym2.mem_iff.mp hvf with h | h
  · exact hva h
  · exact hvb h

lemma not_covered_erase {M : Finset (Sym2 V)} {S : Finset V} (hM : IsMatchingAvoiding Γ M S)
    {a b v : V} (hab : s(a, b) ∈ M) (hv : v = a ∨ v = b) : ¬ Covered (M.erase s(a, b)) v := by
  rintro ⟨f, hf, hvf⟩
  have hf' := mem_erase.mp hf
  have hvab : v ∈ s(a, b) := by rcases hv with rfl | rfl <;> simp
  exact hM.2.1 _ hf'.2 _ hab hf'.1 v hvf hvab

lemma isMatchingAvoiding_erase {M : Finset (Sym2 V)} {S : Finset V}
    (hM : IsMatchingAvoiding Γ M S) (e : Sym2 V) : IsMatchingAvoiding Γ (M.erase e) S :=
  ⟨fun f hf => hM.1 f (mem_of_mem_erase hf),
    fun f hf g hg hfg => hM.2.1 f (mem_of_mem_erase hf) g (mem_of_mem_erase hg) hfg,
    fun f hf => hM.2.2 f (mem_of_mem_erase hf)⟩

variable [DecidableRel Γ.Adj]

/-- The double exchange `M − ab + ua + bu'`. -/
lemma swap2 {M : Finset (Sym2 V)} {S : Finset V} (hM : IsMatchingAvoiding Γ M S) {a b u u' : V}
    (hab : s(a, b) ∈ M) (hu : ¬ Covered M u) (hu' : ¬ Covered M u') (huS : u ∉ S)
    (hu'S : u' ∉ S) (hua : Γ.Adj u a) (hbu' : Γ.Adj b u') (huu' : u ≠ u') :
    IsMatchingAvoiding Γ (insert s(u, a) (insert s(b, u') (M.erase s(a, b)))) S ∧
      ∀ v, Covered M v ∨ v = u ∨ v = u' →
        Covered (insert s(u, a) (insert s(b, u') (M.erase s(a, b)))) v := by
  have haS : a ∉ S := hM.2.2 _ hab a (Sym2.mem_mk_left _ _)
  have hbS : b ∉ S := hM.2.2 _ hab b (Sym2.mem_mk_right _ _)
  have hcova : Covered M a := ⟨_, hab, Sym2.mem_mk_left _ _⟩
  have hcovb : Covered M b := ⟨_, hab, Sym2.mem_mk_right _ _⟩
  have hua' : u ≠ a := fun h => hu (h ▸ hcova)
  have hub : u ≠ b := fun h => hu (h ▸ hcovb)
  have hu'a : u' ≠ a := fun h => hu' (h ▸ hcova)
  have hu'b : u' ≠ b := fun h => hu' (h ▸ hcovb)
  have hab' : a ≠ b := Γ.ne_of_adj (hM.1 _ hab)
  have h0 := isMatchingAvoiding_erase Γ hM s(a, b)
  have hu0 : ¬ Covered (M.erase s(a, b)) u := fun ⟨f, hf, h⟩ => hu ⟨f, mem_of_mem_erase hf, h⟩
  have hu'0 : ¬ Covered (M.erase s(a, b)) u' :=
    fun ⟨f, hf, h⟩ => hu' ⟨f, mem_of_mem_erase hf, h⟩
  have ha0 := not_covered_erase Γ hM hab (Or.inl rfl)
  have hb0 := not_covered_erase Γ hM hab (Or.inr rfl)
  have h1 := isMatchingAvoiding_insert Γ h0 hbu' hb0 hu'0 hbS hu'S
  have hu1 : ¬ Covered (insert s(b, u') (M.erase s(a, b))) u := by
    rintro ⟨f, hf, h⟩
    rcases mem_insert.mp hf with rfl | hf
    · rcases Sym2.mem_iff.mp h with h | h
      · exact hub h
      · exact huu' h
    · exact hu0 ⟨f, hf, h⟩
  have ha1 : ¬ Covered (insert s(b, u') (M.erase s(a, b))) a := by
    rintro ⟨f, hf, h⟩
    rcases mem_insert.mp hf with rfl | hf
    · rcases Sym2.mem_iff.mp h with h | h
      · exact hab' h
      · exact hu'a h.symm
    · exact ha0 ⟨f, hf, h⟩
  refine ⟨isMatchingAvoiding_insert Γ h1 hua hu1 ha1 huS haS, ?_⟩
  rintro v (hv | rfl | rfl)
  · by_cases hva : v = a
    · exact ⟨_, mem_insert_self _ _, by rw [hva]; exact Sym2.mem_mk_right _ _⟩
    by_cases hvb : v = b
    · exact ⟨_, mem_insert_of_mem (mem_insert_self _ _), by rw [hvb]; exact Sym2.mem_mk_left _ _⟩
    exact covered_insert (covered_insert (covered_erase_of_ne Γ hM hab hv hva hvb))
  · exact ⟨_, mem_insert_self _ _, Sym2.mem_mk_left _ _⟩
  · exact ⟨_, mem_insert_of_mem (mem_insert_self _ _), Sym2.mem_mk_right _ _⟩

/-- **Enlarge-Matching Argument.** For a coverage-maximal matching and two uncovered vertices
`u, u'` of `A` outside `S`, the neighbours of `u` outside `S` inject into the vertices outside `S`
that are not adjacent to `u'` (and differ from `u`, `u'`). -/
lemma card_nbr_le_of_two_uncovered {S A : Finset V} {M : Finset (Sym2 V)}
    (hM : IsMatchingAvoiding Γ M S)
    (hmax : ∀ M' : Finset (Sym2 V), IsMatchingAvoiding Γ M' S →
      #(A.filter (Covered M')) ≤ #(A.filter (Covered M)))
    {u u' : V} (huA : u ∈ A) (hu : ¬ Covered M u) (hu' : ¬ Covered M u') (huS : u ∉ S)
    (hu'S : u' ∉ S) (hne : u ≠ u') :
    #((Γ.neighborFinset u).filter (· ∉ S)) ≤
      #(univ.filter fun b => b ∉ S ∧ b ≠ u ∧ b ≠ u' ∧ ¬ Γ.Adj u' b) := by
  have hcov : ∀ a ∈ (Γ.neighborFinset u).filter (· ∉ S), Covered M a := by
    intro a ha
    simp only [mem_filter, mem_neighborFinset] at ha
    by_contra hca
    exact not_adj_of_max Γ hM hmax huA hu hca huS ha.2 ha.1
  refine card_le_card_of_injOn (partner M) ?_ ?_
  · intro a ha
    rw [Finset.mem_coe] at ha
    have hca := hcov a ha
    rw [mem_filter, mem_neighborFinset] at ha
    rw [Finset.mem_coe, mem_filter]
    have hpc := partner_covered Γ hM hca
    refine ⟨mem_univ _, partner_not_mem Γ hM hca, fun h => hu (h ▸ hpc), fun h => hu' (h ▸ hpc), ?_⟩
    intro hadj
    have hab := partner_mem Γ hM hca
    obtain ⟨hM', hcov'⟩ := swap2 Γ hM hab hu hu' huS hu'S ha.1 hadj.symm hne
    have h := hmax _ hM'
    have hsub : A.filter (Covered M) ⊂
        A.filter (Covered (insert s(u, a) (insert s(partner M a, u') (M.erase s(a, partner M a))))) := by
      refine (ssubset_iff_of_subset (fun x hx => ?_)).mpr ⟨u, ?_, ?_⟩
      · simp only [mem_filter] at hx ⊢
        exact ⟨hx.1, hcov' x (Or.inl hx.2)⟩
      · simp only [mem_filter]
        exact ⟨huA, hcov' u (Or.inr (Or.inl rfl))⟩
      · simp only [mem_filter, not_and]
        exact fun _ => hu
    have := card_lt_card hsub
    omega
  · intro a ha a' ha' h
    exact partner_injOn Γ hM (hcov a (Finset.mem_coe.mp ha)) (hcov a' (Finset.mem_coe.mp ha')) h

end TCCHighLib
