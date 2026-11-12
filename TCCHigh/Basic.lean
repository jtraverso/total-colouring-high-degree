/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Fournier.Basic
public import LeanPool.Vizing.Main
public import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# Total colourings from edge colourings of an apex graph

The technique of Yap (Yap–Wang–Zhang 1989, Lemma 2.2; Chetwynd–Hilton): add a new vertex `c*`
(`none : Option V`) joined to a set `W` of vertices and delete a set `F` of edges. A proper
`K`-edge colouring of the resulting graph gives, together with a "small" total colouring of the
vertices outside `W` and the edges of `F` with `t` further colours, a total colouring of `G` with
`K + t` colours: a vertex `v ∈ W` takes the colour of the edge `c* v`.
-/

@[expose] public section

namespace TCCHighLib

open SimpleGraph Finset

variable {V : Type*}

/-- `c : V ⊕ G.edgeSet → α` is a total colouring of `G`: adjacent vertices get different
colours, distinct edges with a common endpoint get different colours, and every vertex gets a
colour different from the colours of the edges incident to it. -/
def IsTotalColoring (G : SimpleGraph V) {α : Type*} (c : V ⊕ G.edgeSet → α) : Prop :=
  (∀ u v : V, G.Adj u v → c (Sum.inl u) ≠ c (Sum.inl v)) ∧
  (∀ e f : G.edgeSet, e ≠ f → ∀ v : V, v ∈ (e : Sym2 V) → v ∈ (f : Sym2 V) →
      c (Sum.inr e) ≠ c (Sum.inr f)) ∧
  (∀ (v : V) (e : G.edgeSet), v ∈ (e : Sym2 V) → c (Sum.inl v) ≠ c (Sum.inr e))

/-- The apex graph: delete the edges of `F` from `G` and add a new vertex `none` joined to the
vertices of `W`. -/
def apex (G : SimpleGraph V) (F : Set (Sym2 V)) (W : Set V) : SimpleGraph (Option V) where
  Adj
    | some u, some v => G.Adj u v ∧ s(u, v) ∉ F
    | none, some v => v ∈ W
    | some u, none => u ∈ W
    | none, none => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> simp_all [G.adj_comm, Sym2.eq_swap]⟩
  loopless := ⟨by
    intro x h
    cases x <;> simp_all⟩

section apex

variable (G : SimpleGraph V) (F : Set (Sym2 V)) (W : Set V)

@[simp] lemma apex_some_some {u v : V} :
    (apex G F W).Adj (some u) (some v) ↔ G.Adj u v ∧ s(u, v) ∉ F := Iff.rfl

@[simp] lemma apex_none_some {v : V} : (apex G F W).Adj none (some v) ↔ v ∈ W := Iff.rfl

@[simp] lemma apex_some_none {v : V} : (apex G F W).Adj (some v) none ↔ v ∈ W := Iff.rfl

@[simp] lemma apex_none_none : ¬ (apex G F W).Adj none none := fun h => h

instance apexDecRel [DecidableRel G.Adj] [DecidablePred (· ∈ F)] [DecidablePred (· ∈ W)] :
    DecidableRel (apex G F W).Adj
  | some u, some v => inferInstanceAs (Decidable (G.Adj u v ∧ s(u, v) ∉ F))
  | none, some v => inferInstanceAs (Decidable (v ∈ W))
  | some u, none => inferInstanceAs (Decidable (u ∈ W))
  | none, none => inferInstanceAs (Decidable False)

lemma map_some_mem_edgeSet {e : Sym2 V} (he : e ∈ G.edgeSet) (hF : e ∉ F) :
    e.map some ∈ (apex G F W).edgeSet := by
  induction e using Sym2.ind with
  | h u v => simpa [Sym2.map_mk] using ⟨he, hF⟩

end apex

lemma castAdd_ne_natAdd {K t : ℕ} (a : Fin K) (b : Fin t) : Fin.castAdd t a ≠ Fin.natAdd K b := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

/-- **Assembly.** A proper `K`-edge colouring of the apex graph plus a total colouring of the
vertices outside `W` and the edges of `F` with `t` colours give a total colouring of `G` with
`K + t` colours. -/
theorem total_of_apex (G : SimpleGraph V) (F : Set (Sym2 V)) (W : Set V) [DecidablePred (· ∈ F)]
    [DecidablePred (· ∈ W)] (K t : ℕ) (hcol : (apex G F W).lineGraph.Colorable K)
    (σV : V → Fin t) (σE : Sym2 V → Fin t)
    (hV : ∀ u v, u ∉ W → v ∉ W → G.Adj u v → σV u ≠ σV v)
    (hE : ∀ e ∈ F, ∀ f ∈ F, e ≠ f → ∀ v, v ∈ e → v ∈ f → σE e ≠ σE f)
    (hVE : ∀ v, v ∉ W → ∀ e ∈ F, v ∈ e → σV v ≠ σE e) :
    ∃ c : V ⊕ G.edgeSet → Fin (K + t), IsTotalColoring G c := by
  obtain ⟨π⟩ := hcol
  let ap : ∀ v, v ∈ W → (apex G F W).edgeSet := fun v h => ⟨s(none, some v), h⟩
  let lift : ∀ e : G.edgeSet, e.1 ∉ F → (apex G F W).edgeSet :=
    fun e h => ⟨e.1.map some, map_some_mem_edgeSet G F W e.2 h⟩
  let c : V ⊕ G.edgeSet → Fin (K + t) := fun x =>
    match x with
    | Sum.inl v => if h : v ∈ W then Fin.castAdd t (π (ap v h)) else Fin.natAdd K (σV v)
    | Sum.inr e => if h : e.1 ∈ F then Fin.natAdd K (σE e.1) else Fin.castAdd t (π (lift e h))
  have hπ : ∀ a b : (apex G F W).edgeSet, a ≠ b →
      (∃ x, x ∈ (a : Sym2 (Option V)) ∧ x ∈ (b : Sym2 (Option V))) → π a ≠ π b := by
    intro a b hab hx
    exact π.valid (lineGraph_adj_iff_exists.mpr ⟨hab, hx⟩)
  have hcast : ∀ a b : Fin K, Fin.castAdd t a ≠ Fin.castAdd t b → a ≠ b := by
    intro a b h hab; exact h (hab ▸ rfl)
  refine ⟨c, ?_, ?_, ?_⟩
  · intro u v huv
    have hne : u ≠ v := G.ne_of_adj huv
    by_cases hu : u ∈ W <;> by_cases hv : v ∈ W
    · simp only [c, hu, hv, dite_true]
      intro h
      have h' := Fin.castAdd_injective _ _ h
      refine hπ (ap u hu) (ap v hv) ?_ ⟨none, by simp [ap], by simp [ap]⟩ h'
      intro hab
      have := congrArg Subtype.val hab
      simp [ap] at this
      exact hne this
    · simp only [c, hu, hv, dite_true, dite_false]
      exact castAdd_ne_natAdd _ _
    · simp only [c, hu, hv, dite_true, dite_false]
      exact (castAdd_ne_natAdd _ _).symm
    · simp only [c, hu, hv, dite_false]
      intro h
      exact hV u v hu hv huv (Fin.natAdd_injective _ _ h)
  · intro e f hef v hve hvf
    by_cases he : e.1 ∈ F <;> by_cases hf : f.1 ∈ F
    · simp only [c, he, hf, dite_true]
      intro h
      exact hE e.1 he f.1 hf (fun h' => hef (Subtype.ext h')) v hve hvf
        (Fin.natAdd_injective _ _ h)
    · simp only [c, he, hf, dite_true, dite_false]
      exact (castAdd_ne_natAdd _ _).symm
    · simp only [c, he, hf, dite_true, dite_false]
      exact castAdd_ne_natAdd _ _
    · simp only [c, he, hf, dite_false]
      intro h
      refine hπ (lift e he) (lift f hf) ?_ ⟨some v, ?_, ?_⟩ (Fin.castAdd_injective _ _ h)
      · intro hab
        have := congrArg Subtype.val hab
        simp only [lift] at this
        exact hef (Subtype.ext (Sym2.map.injective (Option.some_injective V) this))
      · simpa [lift, Sym2.mem_map] using hve
      · simpa [lift, Sym2.mem_map] using hvf
  · intro v e hve
    by_cases hv : v ∈ W <;> by_cases he : e.1 ∈ F
    · simp only [c, hv, he, dite_true]
      exact castAdd_ne_natAdd _ _
    · simp only [c, hv, he, dite_true, dite_false]
      intro h
      refine hπ (ap v hv) (lift e he) ?_ ⟨some v, by simp [ap], ?_⟩ (Fin.castAdd_injective _ _ h)
      · intro hab
        have := congrArg Subtype.val hab
        simp only [ap, lift] at this
        have hn : none ∈ e.1.map some := this ▸ Sym2.mem_mk_left _ _
        simp [Sym2.mem_map] at hn
      · simpa [lift, Sym2.mem_map] using hve
    · simp only [c, hv, he, dite_true, dite_false]
      intro h
      exact hVE v hv e.1 he hve (Fin.natAdd_injective _ _ h)
    · simp only [c, hv, he, dite_false]
      exact (castAdd_ne_natAdd _ _).symm

/-- A graph all of whose edges contain one fixed vertex (or no edges at all) is acyclic. -/
lemma isAcyclic_of_forall_adj {α : Type*} (H : SimpleGraph α) (P : α → Prop)
    (hP : ∀ a b, P a → P b → a = b) (h : ∀ a b, H.Adj a b → P a ∨ P b) : H.IsAcyclic := by
  by_cases hr : ∃ r, P r
  · obtain ⟨r, hr⟩ := hr
    refine (isAcyclic_starGraph r).anti ?_
    intro a b hab
    refine (starGraph_adj).mpr ⟨H.ne_of_adj hab, ?_⟩
    rcases h a b hab with ha | hb
    · exact Or.inl (hP a r ha hr)
    · exact Or.inr (hP b r hb hr)
  · push_neg at hr
    refine isAcyclic_bot.anti ?_
    intro a b hab
    rcases h a b hab with ha | hb
    · exact absurd ha (hr a)
    · exact absurd hb (hr b)

/-! ### Degrees in the apex graph -/

instance decMemCoeFinset [DecidableEq V] (F : Finset V) : DecidablePred (· ∈ (F : Set V)) :=
  fun v => inferInstanceAs (Decidable (v ∈ F))

section degrees

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (F : Finset (Sym2 V)) (W : Finset V)

lemma card_filter_option (p : Option V → Prop) [DecidablePred p] :
    #(univ.filter p) = (if p none then 1 else 0) + #(univ.filter fun v => p (some v)) := by
  simp only [Finset.card_filter]
  rw [Fintype.sum_option]

lemma apex_degree_none : (apex G (F : Set (Sym2 V)) (W : Set V)).degree none = #W := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter_option]
  simp

lemma apex_degree_some (v : V) :
    (apex G (F : Set (Sym2 V)) (W : Set V)).degree (some v) =
      (if v ∈ W then 1 else 0) + #((G.neighborFinset v).filter fun u => s(v, u) ∉ F) := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter_option,
    neighborFinset_eq_filter, Finset.filter_filter]
  simp

lemma card_filter_nbr_le (v : V) :
    #((G.neighborFinset v).filter fun u => s(v, u) ∉ F) ≤ G.degree v := by
  rw [← card_neighborFinset_eq_degree]
  exact card_filter_le _ _

lemma card_filter_nbr_le_pred (v w : V) (hw : G.Adj v w) (hF : s(v, w) ∈ F) :
    #((G.neighborFinset v).filter fun u => s(v, u) ∉ F) + 1 ≤ G.degree v := by
  rw [← card_neighborFinset_eq_degree]
  have hsub : (G.neighborFinset v).filter (fun u => s(v, u) ∉ F) ⊆ (G.neighborFinset v).erase w := by
    intro u hu
    simp only [mem_filter] at hu
    refine mem_erase.mpr ⟨?_, hu.1⟩
    rintro rfl
    exact hu.2 hF
  have := card_le_card hsub
  rw [card_erase_of_mem ((mem_neighborFinset _ _ _).mpr hw)] at this
  have hpos : 0 < #(G.neighborFinset v) :=
    card_pos.mpr ⟨w, (mem_neighborFinset _ _ _).mpr hw⟩
  omega

/-- Two edges at `v` deleted. -/
lemma card_filter_nbr_le_pred2 (v w w' : V) (hw : G.Adj v w) (hw' : G.Adj v w') (hne : w ≠ w')
    (hF : s(v, w) ∈ F) (hF' : s(v, w') ∈ F) :
    #((G.neighborFinset v).filter fun u => s(v, u) ∉ F) + 2 ≤ G.degree v := by
  rw [← card_neighborFinset_eq_degree]
  have hsub : (G.neighborFinset v).filter (fun u => s(v, u) ∉ F) ⊆
      ((G.neighborFinset v).erase w).erase w' := by
    intro u hu
    simp only [mem_filter] at hu
    refine mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_, hu.1⟩⟩
    · rintro rfl; exact hu.2 hF'
    · rintro rfl; exact hu.2 hF
  have := card_le_card hsub
  rw [card_erase_of_mem (mem_erase.mpr ⟨hne.symm, (mem_neighborFinset _ _ _).mpr hw'⟩),
    card_erase_of_mem ((mem_neighborFinset _ _ _).mpr hw)] at this
  have h2 : 2 ≤ #(G.neighborFinset v) := by
    have : ({w, w'} : Finset V) ⊆ G.neighborFinset v := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (mem_neighborFinset _ _ _).mpr hw
      · exact (mem_neighborFinset _ _ _).mpr hw'
    have := card_le_card this
    rwa [card_pair hne] at this
  omega

end degrees

end TCCHighLib
