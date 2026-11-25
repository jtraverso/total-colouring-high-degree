/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import TCCHigh.Level1
public import Mathlib.Data.List.TakeWhile

/-!
# Paths, alternating matchings and Hamiltonian paths in graphs without independent triples

* `alt l` splits the edges of a path `l : List V` into the odd-numbered and the even-numbered
  edges; both are matchings, the interior vertices of the path are covered by both, the first
  vertex only by the first one, and the last vertex by exactly one of them according to parity.
* `ham_path_ends`: in a graph without three pairwise non-adjacent vertices, if `x`, `y` are
  non-adjacent, `K` is a vertex set not containing them which is connected (no non-trivial
  subset without edges to its complement in `K`), and `x`, `y` both have neighbours in `K`, then
  there is a path from `x` to `y` whose vertex set is `K ∪ {x, y}`. The proof builds a
  Hamiltonian path of `K` by extensions and rotations, and rotates it once more to fix the ends.
-/

@[expose] public section

namespace TCCHighLib

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Alternating matchings of a path -/

/-- The edges of the path `l` at positions `0, 2, 4, …` and at positions `1, 3, 5, …`. -/
def alt : List V → Finset (Sym2 V) × Finset (Sym2 V)
  | a :: b :: l => (insert s(a, b) (alt (b :: l)).2, (alt (b :: l)).1)
  | _ => (∅, ∅)

lemma alt_cons_cons (a b : V) (l : List V) :
    alt (a :: b :: l) = (insert s(a, b) (alt (b :: l)).2, (alt (b :: l)).1) := rfl

lemma alt_nil : alt ([] : List V) = (∅, ∅) := rfl

lemma alt_single (a : V) : alt [a] = (∅, ∅) := rfl

lemma alt_support : ∀ (l : List V) {e : Sym2 V}, (e ∈ (alt l).1 ∨ e ∈ (alt l).2) →
    ∀ v ∈ e, v ∈ l
  | [], e, h => by simp [alt_nil] at h
  | [a], e, h => by simp [alt_single] at h
  | a :: b :: l, e, h => by
    intro v hv
    rw [alt_cons_cons] at h
    simp only [mem_insert] at h
    rcases h with (rfl | h) | h
    · rcases Sym2.mem_iff.mp hv with rfl | rfl <;> simp
    · exact List.mem_cons_of_mem _ (alt_support (b :: l) (Or.inr h) v hv)
    · exact List.mem_cons_of_mem _ (alt_support (b :: l) (Or.inl h) v hv)

lemma not_covered_alt {l : List V} {v : V} (hv : v ∉ l) :
    ¬ Covered (alt l).1 v ∧ ¬ Covered (alt l).2 v :=
  ⟨fun ⟨_, he, hve⟩ => hv (alt_support l (Or.inl he) v hve),
    fun ⟨_, he, hve⟩ => hv (alt_support l (Or.inr he) v hve)⟩

lemma alt_edges (G : SimpleGraph V) : ∀ (l : List V), l.IsChain G.Adj → ∀ {e : Sym2 V},
    (e ∈ (alt l).1 ∨ e ∈ (alt l).2) → e ∈ G.edgeSet
  | [], _, e, h => by simp [alt_nil] at h
  | [a], _, e, h => by simp [alt_single] at h
  | a :: b :: l, hc, e, h => by
    rw [List.isChain_cons_cons] at hc
    rw [alt_cons_cons] at h
    simp only [mem_insert] at h
    rcases h with (rfl | h) | h
    · exact hc.1
    · exact alt_edges G (b :: l) hc.2 (Or.inr h)
    · exact alt_edges G (b :: l) hc.2 (Or.inl h)

/-- The first vertex of a path with at least one edge is covered by the first matching only. -/
lemma alt_head (a b : V) (l : List V) (hnd : (a :: b :: l).Nodup) :
    Covered (alt (a :: b :: l)).1 a ∧ ¬ Covered (alt (a :: b :: l)).2 a := by
  rw [alt_cons_cons]
  refine ⟨⟨s(a, b), mem_insert_self _ _, Sym2.mem_mk_left _ _⟩, ?_⟩
  exact (not_covered_alt (List.nodup_cons.mp hnd).1).1

lemma alt_head' {l : List V} {a : V} (hnd : l.Nodup) (hlen : 2 ≤ l.length)
    (hh : l.head? = some a) : Covered (alt l).1 a ∧ ¬ Covered (alt l).2 a := by
  match l, hlen, hh with
  | a' :: b :: l, _, hh =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    exact alt_head a' b l hnd

/-- Interior vertices are covered by both matchings. -/
lemma alt_interior : ∀ (l : List V), l.Nodup → ∀ v ∈ l, l.head? ≠ some v →
    l.getLast? ≠ some v → Covered (alt l).1 v ∧ Covered (alt l).2 v
  | [], _, v, hv, _, _ => by simp at hv
  | [a], _, v, hv, hh, _ => by simp_all
  | a :: b :: l, hnd, v, hv, hh, hl => by
    rw [alt_cons_cons]
    have hva : v ≠ a := fun h => hh (by simp [h])
    have hv' : v ∈ b :: l := by
      rcases List.mem_cons.mp hv with h | h
      · exact absurd h hva
      · exact h
    have hnd' : (b :: l).Nodup := (List.nodup_cons.mp hnd).2
    by_cases hvb : v = b
    · subst hvb
      cases l with
      | nil => simp at hl
      | cons c l =>
        have h := alt_head v c l hnd'
        exact ⟨⟨s(a, v), mem_insert_self _ _, Sym2.mem_mk_right _ _⟩, h.1⟩
    · have hl' : (b :: l).getLast? ≠ some v := by
        intro h; apply hl
        rw [List.getLast?_cons_cons]; exact h
      have h := alt_interior (b :: l) hnd' v hv' (by simp [Ne.symm hvb]) hl'
      exact ⟨covered_insert h.2, h.1⟩

/-- The last vertex of a path with at least one edge is covered by exactly one matching,
according to the parity of the number of vertices. -/
lemma alt_last : ∀ (l : List V), l.Nodup → 2 ≤ l.length → ∀ v, l.getLast? = some v →
    (Covered (alt l).1 v ↔ Even l.length) ∧ (Covered (alt l).2 v ↔ ¬ Even l.length)
  | [], _, h, _, _ => by simp at h
  | [a], _, h, _, _ => by simp at h
  | [a, b], hnd, _, v, hv => by
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hv
    subst hv
    rw [alt_cons_cons, alt_single]
    simp only [insert_empty, List.length_cons, List.length_nil]
    refine ⟨⟨fun _ => by decide, fun _ => ⟨s(a, b), mem_singleton_self _, Sym2.mem_mk_right _ _⟩⟩,
      ⟨fun ⟨_, he, _⟩ => by simp at he, fun h => absurd (by decide) h⟩⟩
  | a :: b :: c :: l, hnd, _, v, hv => by
    have hnd' : (b :: c :: l).Nodup := (List.nodup_cons.mp hnd).2
    have hv' : (b :: c :: l).getLast? = some v := by
      rw [List.getLast?_cons_cons] at hv; exact hv
    have ih := alt_last (b :: c :: l) hnd' (by simp) v hv'
    have hvmem : v ∈ c :: l := by
      have := List.mem_of_getLast? (l := c :: l) (by rw [List.getLast?_cons_cons] at hv'; exact hv')
      exact this
    have hva : v ≠ a := by
      rintro rfl
      exact (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ hvmem)
    have hvb : v ≠ b := by
      rintro rfl
      exact (List.nodup_cons.mp hnd').1 hvmem
    have hlen : (a :: b :: c :: l).length = (b :: c :: l).length + 1 := rfl
    rw [alt_cons_cons, hlen]
    simp only
    constructor
    · constructor
      · rintro ⟨e, he, hve⟩
        rcases mem_insert.mp he with rfl | he
        · rcases Sym2.mem_iff.mp hve with h | h
          · exact absurd h hva
          · exact absurd h hvb
        · have := ih.2.mp ⟨e, he, hve⟩
          rw [Nat.even_add_one]; exact this
      · intro h
        rw [Nat.even_add_one] at h
        exact covered_insert (ih.2.mpr h)
    · constructor
      · intro h
        have := ih.1.mp h
        rw [Nat.even_add_one]; exact not_not.mpr this
      · intro h
        rw [Nat.even_add_one, not_not] at h
        exact ih.1.mpr h

/-- The two alternating edge sets are matchings. -/
lemma alt_matching : ∀ (l : List V), l.Nodup →
    (∀ e ∈ (alt l).1, ∀ f ∈ (alt l).1, e ≠ f → ∀ v, v ∈ e → v ∉ f) ∧
      (∀ e ∈ (alt l).2, ∀ f ∈ (alt l).2, e ≠ f → ∀ v, v ∈ e → v ∉ f)
  | [], _ => by simp [alt_nil]
  | [a], _ => by simp [alt_single]
  | a :: b :: l, hnd => by
    have hnd' : (b :: l).Nodup := (List.nodup_cons.mp hnd).2
    have ha : a ∉ b :: l := (List.nodup_cons.mp hnd).1
    have ih := alt_matching (b :: l) hnd'
    have hb : ¬ Covered (alt (b :: l)).2 b := by
      cases l with
      | nil => simp [alt_single]
      | cons c l => exact (alt_head b c l hnd').2
    have key : ∀ f ∈ (alt (b :: l)).2, ∀ v, v ∈ s(a, b) → v ∉ f := by
      intro f hf v hv hvf
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact ha (alt_support (b :: l) (Or.inr hf) v hvf)
      · exact hb ⟨f, hf, hvf⟩
    rw [alt_cons_cons]
    refine ⟨?_, ih.1⟩
    intro e he f hf hef v hve hvf
    rcases mem_insert.mp he with rfl | he <;> rcases mem_insert.mp hf with rfl | hf
    · exact hef rfl
    · exact key f hf v hve hvf
    · exact key e he v hvf hve
    · exact ih.2 e he f hf hef v hve hvf

lemma alt_disjoint : ∀ (l : List V), l.Nodup → Disjoint (alt l).1 (alt l).2
  | [], _ => by simp [alt_nil]
  | [a], _ => by simp [alt_single]
  | a :: b :: l, hnd => by
    have hnd' : (b :: l).Nodup := (List.nodup_cons.mp hnd).2
    have ha : a ∉ b :: l := (List.nodup_cons.mp hnd).1
    rw [alt_cons_cons]
    refine disjoint_left.mpr fun e he1 he2 => ?_
    rcases mem_insert.mp he1 with rfl | he1
    · exact ha (alt_support (b :: l) (Or.inl he2) a (Sym2.mem_mk_left _ _))
    · exact disjoint_left.mp (alt_disjoint (b :: l) hnd') he2 he1

/-- The alternating edge sets of a path are matchings of `G` avoiding any set `S` whose vertices
they do not cover. -/
lemma isMatchingAvoiding_alt (G : SimpleGraph V) {l : List V} (hnd : l.Nodup)
    (hc : l.IsChain G.Adj) (S : Finset V) :
    ((∀ v ∈ S, ¬ Covered (alt l).1 v) → IsMatchingAvoiding G (alt l).1 S) ∧
      ((∀ v ∈ S, ¬ Covered (alt l).2 v) → IsMatchingAvoiding G (alt l).2 S) := by
  refine ⟨fun hS => ⟨fun e he => alt_edges G l hc (Or.inl he), (alt_matching l hnd).1, ?_⟩,
    fun hS => ⟨fun e he => alt_edges G l hc (Or.inr he), (alt_matching l hnd).2, ?_⟩⟩
  · intro e he v hve hvS; exact hS v hvS ⟨e, he, hve⟩
  · intro e he v hve hvS; exact hS v hvS ⟨e, he, hve⟩

/-- A duplicate-free list of pairwise adjacent vertices is a path. -/
lemma isChain_of_pairwise_adj (G : SimpleGraph V) :
    ∀ (l : List V), l.Nodup → (∀ a ∈ l, ∀ b ∈ l, a ≠ b → G.Adj a b) → l.IsChain G.Adj
  | [], _, _ => List.IsChain.nil
  | [a], _, _ => List.IsChain.singleton a
  | a :: b :: l, hnd, h => by
    rw [List.isChain_cons_cons]
    refine ⟨h a (by simp) b (by simp) ?_, isChain_of_pairwise_adj G (b :: l)
      (List.nodup_cons.mp hnd).2 fun x hx y hy hxy => h x (List.mem_cons_of_mem _ hx) y
        (List.mem_cons_of_mem _ hy) hxy⟩
    intro hab; subst hab; exact (List.nodup_cons.mp hnd).1 (by simp)

/-! ### Hamiltonian paths when there are no three independent vertices -/

section ham

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `G` has no three pairwise non-adjacent (distinct) vertices. -/
def NoIndepTriple : Prop :=
  ∀ a b c : V, a ≠ b → b ≠ c → a ≠ c → ¬ G.Adj a b → ¬ G.Adj b c → G.Adj a c

/-- Extension step: a path inside a connected set `K` that misses a vertex of `K` can be
replaced by a longer one. -/
lemma path_extend (hα : NoIndepTriple G) (K : Finset V)
    (hconn : ∀ P ⊆ K, P.Nonempty → P ≠ K → ∃ p ∈ P, ∃ r ∈ K, r ∉ P ∧ G.Adj p r)
    (p : List V) (hp : p ≠ []) (hnd : p.Nodup) (hc : p.IsChain G.Adj) (hK : ∀ v ∈ p, v ∈ K)
    (hlt : p.length < #K) :
    ∃ q : List V, q ≠ [] ∧ q.Nodup ∧ q.IsChain G.Adj ∧ (∀ v ∈ q, v ∈ K) ∧
      q.length = p.length + 1 := by
  have hsub : p.toFinset ⊆ K := fun v hv => hK v (List.mem_toFinset.mp hv)
  have hne : p.toFinset ≠ K := by
    intro h
    have := List.toFinset_card_of_nodup hnd
    rw [h] at this; omega
  have hpne : p.toFinset.Nonempty := by
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil p hp
    exact ⟨a, List.mem_toFinset.mpr ha⟩
  obtain ⟨pi, hpi, r, hrK, hrP, hadj⟩ := hconn _ hsub hpne hne
  rw [List.mem_toFinset] at hpi hrP
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hpi
  -- extending at the front or at the back
  have hfront : ∀ a, (s ++ pi :: t).head? = some a → G.Adj r a →
      ∃ q : List V, q ≠ [] ∧ q.Nodup ∧ q.IsChain G.Adj ∧ (∀ v ∈ q, v ∈ K) ∧
        q.length = (s ++ pi :: t).length + 1 := by
    intro a hs hra
    refine ⟨r :: (s ++ pi :: t), by simp, List.nodup_cons.mpr ⟨hrP, hnd⟩, ?_, ?_, by simp⟩
    · rw [List.isChain_cons]
      refine ⟨?_, hc⟩
      intro y hy
      rw [hs, Option.mem_def, Option.some.injEq] at hy
      exact hy ▸ hra
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hrK
      · exact hK v hv
  have hback : ∀ b, (s ++ pi :: t).getLast? = some b → G.Adj b r →
      ∃ q : List V, q ≠ [] ∧ q.Nodup ∧ q.IsChain G.Adj ∧ (∀ v ∈ q, v ∈ K) ∧
        q.length = (s ++ pi :: t).length + 1 := by
    intro b hl hbr
    refine ⟨(s ++ pi :: t) ++ [r], by simp, ?_, ?_, ?_, by simp; omega⟩
    · rw [List.nodup_append]
      refine ⟨hnd, List.nodup_singleton r, ?_⟩
      intro a ha b' hb' hab
      rw [List.mem_singleton] at hb'
      subst hb'; subst hab; exact hrP ha
    · refine List.IsChain.append hc (List.IsChain.singleton r) ?_
      intro x hx y hy
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      rw [hl, Option.mem_def, Option.some.injEq] at hx
      exact hx ▸ hbr
    · intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hK v hv
      · rw [List.mem_singleton] at hv; exact hv ▸ hrK
  rcases List.eq_nil_or_concat t with ht | ⟨t', b, ht⟩
  · -- `pi` is the last vertex
    subst ht
    exact hback pi (by rw [List.getLast?_append]; simp) hadj
  · rw [List.concat_eq_append] at ht
    cases s with
    | nil =>
      exact hfront pi (by simp) hadj.symm
    | cons a s' =>
      by_cases hra : G.Adj r a
      · exact hfront a (by simp) hra
      by_cases hbr : G.Adj b r
      · exact hback b (by subst ht; rw [show a :: s' ++ pi :: (t' ++ [b]) =
            (a :: s' ++ pi :: t') ++ [b] by simp, List.getLast?_concat]) hbr
      subst ht
      -- rotation: `a` and `b` are adjacent
      have hma : a ∈ a :: s' ++ pi :: (t' ++ [b]) := by simp
      have hmb : b ∈ a :: s' ++ pi :: (t' ++ [b]) := by simp
      have hab : a ≠ b := by
        intro hab
        subst hab
        have h1 : (a :: s' ++ pi :: (t' ++ [a])).Nodup := hnd
        rw [List.cons_append, List.nodup_cons] at h1
        exact h1.1 (by simp)
      have hadjab : G.Adj a b :=
        hα a r b (fun h => hrP (h ▸ hma)) (fun h => hrP (h ▸ hmb)) hab
          (fun h => hra h.symm) (fun h => hbr h.symm)
      refine ⟨(t' ++ [b]) ++ ((a :: s' ++ [pi]) ++ [r]), by simp, ?_, ?_, ?_, ?_⟩
      · have hperm : ((t' ++ [b]) ++ ((a :: s' ++ [pi]) ++ [r])).Perm
            ((a :: s' ++ pi :: (t' ++ [b])) ++ [r]) := by
          rw [← List.append_assoc]
          refine List.Perm.append_right _ ?_
          rw [show a :: s' ++ pi :: (t' ++ [b]) = (a :: s' ++ [pi]) ++ (t' ++ [b]) by simp]
          exact List.perm_append_comm
        refine hperm.nodup_iff.mpr ?_
        rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton r, ?_⟩
        intro x hx y hy hxy
        rw [List.mem_singleton] at hy
        subst hy; subst hxy; exact hrP hx
      · have hc1 : (t' ++ [b]).IsChain G.Adj := by
          have : (a :: s' ++ [pi] ++ (t' ++ [b])).IsChain G.Adj := by
            rw [show a :: s' ++ [pi] ++ (t' ++ [b]) = a :: s' ++ pi :: (t' ++ [b]) by simp]
            exact hc
          exact this.right_of_append
        have hc2 : (a :: s' ++ [pi]).IsChain G.Adj := by
          have : (a :: s' ++ [pi] ++ (t' ++ [b])).IsChain G.Adj := by
            rw [show a :: s' ++ [pi] ++ (t' ++ [b]) = a :: s' ++ pi :: (t' ++ [b]) by simp]
            exact hc
          exact this.left_of_append
        refine List.IsChain.append hc1 (List.IsChain.append hc2 (List.IsChain.singleton r) ?_) ?_
        · intro x hx y hy
          rw [show a :: s' ++ [pi] = (a :: s') ++ [pi] from rfl, List.getLast?_concat,
            Option.mem_def, Option.some.injEq] at hx
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          subst hx; subst hy; exact hadj
        · intro x hx y hy
          rw [List.getLast?_concat, Option.mem_def, Option.some.injEq] at hx
          simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          subst hx; subst hy; exact hadjab.symm
      · intro v hv
        simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hv
        rcases hv with (hv | rfl) | ((rfl | hv) | rfl) | rfl
        · exact hK v (by simp [hv])
        · exact hK _ (by simp)
        · exact hK _ (by simp)
        · exact hK v (by simp [hv])
        · exact hK _ (by simp)
        · exact hrK
      · simp; omega

/-- A connected vertex set of a graph without independent triples has a Hamiltonian path. -/
lemma exists_ham_path (hα : NoIndepTriple G) (K : Finset V)
    (hconn : ∀ P ⊆ K, P.Nonempty → P ≠ K → ∃ p ∈ P, ∃ r ∈ K, r ∉ P ∧ G.Adj p r)
    (hne : K.Nonempty) :
    ∃ p : List V, p ≠ [] ∧ p.Nodup ∧ p.IsChain G.Adj ∧ ∀ v, v ∈ p ↔ v ∈ K := by
  have key : ∀ k, 1 ≤ k → k ≤ #K → ∃ p : List V, p ≠ [] ∧ p.Nodup ∧ p.IsChain G.Adj ∧
      (∀ v ∈ p, v ∈ K) ∧ p.length = k := by
    intro k hk1 hkK
    induction k, hk1 using Nat.le_induction with
    | base =>
      obtain ⟨a, ha⟩ := hne
      exact ⟨[a], by simp, List.nodup_singleton a, List.IsChain.singleton a,
        fun v hv => by rw [List.mem_singleton] at hv; exact hv ▸ ha, rfl⟩
    | succ k hk ih =>
      obtain ⟨p, hp, hnd, hc, hK, hlen⟩ := ih (by omega)
      obtain ⟨q, hq⟩ := path_extend G hα K hconn p hp hnd hc hK (by omega)
      exact ⟨q, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, by rw [hq.2.2.2.2, hlen]⟩
  obtain ⟨p, hp, hnd, hc, hK, hlen⟩ := key #K (card_pos.mpr hne) le_rfl
  have hsub : p.toFinset ⊆ K := fun v hv => hK v (List.mem_toFinset.mp hv)
  have heq : p.toFinset = K :=
    eq_of_subset_of_card_le hsub (by rw [List.toFinset_card_of_nodup hnd, hlen])
  refine ⟨p, hp, hnd, hc, fun v => ⟨hK v, fun hv => ?_⟩⟩
  rw [← heq] at hv
  exact List.mem_toFinset.mp hv

/-- Rotation fixing the ends: a path whose two ends are not adjacent to `y`, while some vertex
is, is rotated (as a cycle) so that it starts at a neighbour of `x` and ends at a neighbour of
`y`. -/
lemma rotate_ends (hα : NoIndepTriple G) (x y : V) (p : List V) (hnd : p.Nodup)
    (hc : p.IsChain G.Adj) (hyp : y ∉ p) (hxy : ∀ v ∈ p, G.Adj x v ∨ G.Adj y v)
    (a b : V) (ha : p.head? = some a) (hb : p.getLast? = some b) (hya : ¬ G.Adj y a)
    (hyb : ¬ G.Adj y b) (hy : ∃ k ∈ p, G.Adj y k) :
    ∃ q : List V, q.Nodup ∧ q.IsChain G.Adj ∧ (∀ v, v ∈ q ↔ v ∈ p) ∧
      (∃ a', q.head? = some a' ∧ G.Adj x a') ∧ (∃ b', q.getLast? = some b' ∧ G.Adj y b') := by
  have hamem : a ∈ p := List.mem_of_head? ha
  have hbmem : b ∈ p := List.mem_of_getLast? hb
  have hab : a ≠ b := by
    rintro rfl
    obtain ⟨k, hk, hyk⟩ := hy
    cases p with
    | nil => simp at hk
    | cons c p' =>
      simp only [List.head?_cons, Option.some.injEq] at ha
      subst ha
      cases p' with
      | nil => simp at hk; subst hk; exact hya hyk
      | cons d p'' =>
        rw [List.getLast?_cons_cons] at hb
        have := List.mem_of_getLast? hb
        exact (List.nodup_cons.mp hnd).1 this
  have hadjab : G.Adj a b :=
    hα a y b (fun h => hyp (h ▸ hamem)) (fun h => hyp (h ▸ hbmem)) hab (fun h => hya h.symm) hyb
  set P : V → Bool := fun v => !decide (G.Adj y v) with hP
  set A := p.takeWhile P with hA
  set B := p.dropWhile P with hB
  have hAB : A ++ B = p := List.takeWhile_append_dropWhile
  have hBne : B ≠ [] := by
    intro h
    obtain ⟨k, hk, hyk⟩ := hy
    have := List.dropWhile_eq_nil_iff.mp h k hk
    simp [hP, hyk] at this
  have hAne : A ≠ [] := by
    cases p with
    | nil => simp at ha
    | cons c p' =>
      simp only [List.head?_cons, Option.some.injEq] at ha
      subst ha
      rw [hA, List.takeWhile_cons_of_pos (by simp [hP, hya])]
      simp
  -- the ends of `A` and `B`
  have hAhead : A.head? = some a := by
    rw [← ha, ← hAB, List.head?_append_of_ne_nil _ hAne]
  have hBlast : B.getLast? = some b := by
    rw [← hb, ← hAB, List.getLast?_append_of_ne_nil _ hBne]
  obtain ⟨b', hb'⟩ : ∃ b', B.head? = some b' := ⟨B.head hBne, List.head?_eq_some_head hBne⟩
  obtain ⟨a', ha'⟩ : ∃ a', A.getLast? = some a' := Option.isSome_iff_exists.mp
    (by rw [List.getLast?_isSome]; exact hAne)
  have hyb' : G.Adj y b' := by
    have h := List.head_dropWhile_not P (l := p) hBne
    have hhd : B.head hBne = b' := by
      rw [List.head?_eq_some_head hBne] at hb'; exact Option.some.inj hb'
    rw [hhd] at h
    simpa [hP] using h
  have ha'mem : a' ∈ A := List.mem_of_getLast? ha'
  have hxa' : G.Adj x a' := by
    have hPa' := List.mem_takeWhile_imp ha'mem
    simp only [hP, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hPa'
    have ha'p : a' ∈ p := by rw [← hAB]; exact List.mem_append_left _ ha'mem
    exact (hxy a' ha'p).resolve_right hPa'
  have hcA : A.IsChain G.Adj := by rw [← hAB] at hc; exact hc.left_of_append
  have hcB : B.IsChain G.Adj := by rw [← hAB] at hc; exact hc.right_of_append
  have hcBA : (B ++ A).IsChain G.Adj := by
    refine List.IsChain.append hcB hcA ?_
    intro u hu w hw
    rw [hBlast, Option.mem_def, Option.some.injEq] at hu
    rw [hAhead, Option.mem_def, Option.some.injEq] at hw
    subst hu; subst hw; exact hadjab.symm
  have hperm : (B ++ A).reverse.Perm p := by
    rw [← hAB]
    exact (List.reverse_perm _).trans List.perm_append_comm
  refine ⟨(B ++ A).reverse, hperm.nodup_iff.mpr hnd, ?_, fun v => hperm.mem_iff, ⟨a', ?_, hxa'⟩,
    ⟨b', ?_, hyb'⟩⟩
  · rw [List.isChain_reverse]
    exact hcBA.imp fun u w h => h.symm
  · rw [List.head?_reverse, List.getLast?_append_of_ne_nil _ hAne, ha']
  · rw [List.getLast?_reverse, List.head?_append_of_ne_nil _ hBne, hb']

/-- **Hamiltonian paths with prescribed ends.** In a graph without independent triples, let
`x`, `y` be non-adjacent and `K` a connected vertex set avoiding them, in which both `x` and `y`
have neighbours. Then some path from `x` to `y` has vertex set `K ∪ {x, y}`. -/
theorem ham_path_ends (hα : NoIndepTriple G) (K : Finset V) (x y : V) (hxK : x ∉ K)
    (hyK : y ∉ K) (hxy : x ≠ y) (hn : ¬ G.Adj x y) (hne : K.Nonempty)
    (hconn : ∀ P ⊆ K, P.Nonempty → P ≠ K → ∃ p ∈ P, ∃ r ∈ K, r ∉ P ∧ G.Adj p r)
    (hx : ∃ k ∈ K, G.Adj x k) (hy : ∃ k ∈ K, G.Adj y k) :
    ∃ l : List V, l.Nodup ∧ l.IsChain G.Adj ∧ l.head? = some x ∧ l.getLast? = some y ∧
      ∀ v, v ∈ l ↔ (v = x ∨ v = y ∨ v ∈ K) := by
  obtain ⟨p, hp, hnd, hc, hmem⟩ := exists_ham_path G hα K hconn hne
  have hxyp : ∀ v ∈ p, G.Adj x v ∨ G.Adj y v := by
    intro v hv
    have hvK := (hmem v).mp hv
    by_contra h
    push_neg at h
    exact hn (hα x v y (fun h' => hxK (h' ▸ hvK)) (fun h' => hyK (h' ▸ hvK)) hxy h.1
      (fun h' => h.2 h'.symm))
  have hxp : x ∉ p := fun h => hxK ((hmem x).mp h)
  have hyp : y ∉ p := fun h => hyK ((hmem y).mp h)
  -- a Hamiltonian path of `K` starting next to `x` and ending next to `y`
  obtain ⟨q, hqnd, hqc, hqmem, ⟨a, ha, hxa⟩, ⟨b, hb, hyb⟩⟩ :
      ∃ q : List V, q.Nodup ∧ q.IsChain G.Adj ∧ (∀ v, v ∈ q ↔ v ∈ p) ∧
        (∃ a', q.head? = some a' ∧ G.Adj x a') ∧ (∃ b', q.getLast? = some b' ∧ G.Adj y b') := by
    obtain ⟨e, he⟩ : ∃ e, p.head? = some e := Option.isSome_iff_exists.mp
      (by cases p with | nil => exact absurd rfl hp | cons _ _ => rfl)
    obtain ⟨f, hf⟩ : ∃ f, p.getLast? = some f := Option.isSome_iff_exists.mp
      (by rw [List.getLast?_isSome]; exact hp)
    have hep : e ∈ p := List.mem_of_head? he
    have hfp : f ∈ p := List.mem_of_getLast? hf
    have hyK' : ∃ k ∈ p, G.Adj y k := by
      obtain ⟨k, hk, hyk⟩ := hy; exact ⟨k, (hmem k).mpr hk, hyk⟩
    have hxK' : ∃ k ∈ p, G.Adj x k := by
      obtain ⟨k, hk, hxk⟩ := hx; exact ⟨k, (hmem k).mpr hk, hxk⟩
    by_cases h1 : G.Adj x e ∧ G.Adj y f
    · exact ⟨p, hnd, hc, fun v => Iff.rfl, ⟨e, he, h1.1⟩, ⟨f, hf, h1.2⟩⟩
    by_cases h2 : G.Adj x f ∧ G.Adj y e
    · refine ⟨p.reverse, List.nodup_reverse.mpr hnd, ?_, fun v => List.mem_reverse,
        ⟨f, by rw [List.head?_reverse, hf], h2.1⟩, ⟨e, by rw [List.getLast?_reverse, he], h2.2⟩⟩
      rw [List.isChain_reverse]; exact hc.imp fun u w h => h.symm
    have hcase : (¬ G.Adj y e ∧ ¬ G.Adj y f) ∨ (¬ G.Adj x e ∧ ¬ G.Adj x f) := by
      by_cases hye : G.Adj y e
      · right
        have hxf : ¬ G.Adj x f := fun h => h2 ⟨h, hye⟩
        have hyf : G.Adj y f := (hxyp f hfp).resolve_left hxf
        exact ⟨fun h => h1 ⟨h, hyf⟩, hxf⟩
      · left
        have hxe : G.Adj x e := (hxyp e hep).resolve_right hye
        exact ⟨hye, fun h => h1 ⟨hxe, h⟩⟩
    rcases hcase with ⟨hye, hyf⟩ | ⟨hxe, hxf⟩
    · exact rotate_ends G hα x y p hnd hc hyp hxyp e f he hf hye hyf hyK'
    · obtain ⟨q, hqnd, hqc, hqmem, ⟨a', ha', hya'⟩, ⟨b', hb', hxb'⟩⟩ :=
        rotate_ends G hα y x p hnd hc hxp (fun v hv => (hxyp v hv).symm) e f he hf hxe hxf hxK'
      refine ⟨q.reverse, List.nodup_reverse.mpr hqnd, ?_, fun v => by rw [List.mem_reverse, hqmem],
        ⟨b', by rw [List.head?_reverse, hb'], hxb'⟩, ⟨a', by rw [List.getLast?_reverse, ha'], hya'⟩⟩
      rw [List.isChain_reverse]; exact hqc.imp fun u w h => h.symm
  have hxq : x ∉ q := fun h => hxp ((hqmem x).mp h)
  have hyq : y ∉ q := fun h => hyp ((hqmem y).mp h)
  have hqne : q ≠ [] := by rintro rfl; simp at ha
  refine ⟨x :: (q ++ [y]), ?_, ?_, rfl, ?_, ?_⟩
  · rw [List.nodup_cons, List.nodup_append]
    refine ⟨?_, hqnd, List.nodup_singleton y, ?_⟩
    · simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨hxq, hxy⟩
    · intro u hu w hw huw
      rw [List.mem_singleton] at hw
      subst hw; subst huw; exact hyq hu
  · rw [List.isChain_cons]
    refine ⟨?_, List.IsChain.append hqc (List.IsChain.singleton y) ?_⟩
    · intro w hw
      rw [List.head?_append_of_ne_nil _ hqne, ha, Option.mem_def, Option.some.injEq] at hw
      subst hw; exact hxa
    · intro u hu w hw
      rw [hb, Option.mem_def, Option.some.injEq] at hu
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hw
      subst hu; subst hw; exact hyb.symm
  · rw [List.getLast?_cons, List.getLast?_concat]; rfl
  · intro v
    simp only [List.mem_cons, List.mem_append, List.mem_singleton, hqmem, hmem]
    tauto

end ham

end TCCHighLib
