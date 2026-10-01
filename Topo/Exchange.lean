/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Order.WellFounded
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# The combinatorial interface of Seifert exchange complexes

The graph represents its flag complex: the nonempty finite cliques are precisely its faces.
There is no finiteness assumption on vertices or links. Complexity values range over any
linear order with well-founded strict order, with independent universes for vertices and values.
Definition 2.1 allows ties; the injective variant records the convention from line 155.
-/

universe u w

namespace Seifert

variable {V : Type u} {W : Type w}

/-- The standard abstract flag complex of a graph, using Mathlib's nonempty-face convention. -/
def flagComplex (G : SimpleGraph V) : AbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ G.IsClique (s : Set V)}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    exact ⟨ht, hs.2.subset (by exact_mod_cast hts)⟩
  singleton_mem := by
    intro v
    exact ⟨Finset.singleton_nonempty v, by simp⟩

@[simp] theorem mem_flagComplex (G : SimpleGraph V) (s : Finset V) :
    s ∈ flagComplex G ↔ s.Nonempty ∧ G.IsClique (s : Set V) := Iff.rfl

/-- `I(u,w) = N(u) ∩ N(w)` (paper lines 126–131). -/
def TwoInterval (G : SimpleGraph V) (u w : V) : Set V :=
  {x | G.Adj u x ∧ G.Adj w x}

/-- An apex belongs to the entire two-interval and is equal or adjacent to every member.
The universal quantifier is inside the existential in N1 and N2. -/
def IsApex (G : SimpleGraph V) (u w x : V) : Prop :=
  x ∈ TwoInterval G u w ∧ ∀ y ∈ TwoInterval G u w, x = y ∨ G.Adj x y

/-- Distance two, expressed without any disconnected-distance convention. -/
def DistanceTwo (G : SimpleGraph V) (u w : V) : Prop :=
  u ≠ w ∧ ¬ G.Adj u w ∧ (TwoInterval G u w).Nonempty

theorem distanceTwo_iff_edist (G : SimpleGraph V) (u w : V) :
    DistanceTwo G u w ↔ G.edist u w = 2 := by
  exact (G.edist_eq_two_iff (u := u) (v := w)).symm

variable [LinearOrder W] [WellFoundedLT W]

/-- Definition 2.1, lines 132–135. Neither a selection map nor link contractibility is data. -/
structure ExchangeStructure (G : SimpleGraph V) (c : V → W) [WellFoundedLT W] : Prop where
  n1 : ∀ u w, DistanceTwo G u w → ∃ x, IsApex G u w x
  n2 : ∀ u w, DistanceTwo G u w →
    ∃ x, IsApex G u w x ∧ c x < max (c u) (c w)

/-- A nonempty connected flag complex with exchange structure (line 136).
Mathlib graph connectedness already includes nonemptiness; flagness is supplied by `flagComplex`. -/
structure ExchangeComplex (G : SimpleGraph V) (c : V → W) : Prop
    extends ExchangeStructure G c where
  connected : G.Connected

/-- The injective convention used in Corollary 2.3 and Lemma 2.4, not in Definition 2.1. -/
structure InjectiveExchangeComplex (G : SimpleGraph V) (c : V → W) : Prop
    extends ExchangeComplex G c where
  injective : Function.Injective c

omit [WellFoundedLT W] in
theorem n1_of_n2 (G : SimpleGraph V) (c : V → W)
    (h : ∀ u w, DistanceTwo G u w →
      ∃ x, IsApex G u w x ∧ c x < max (c u) (c w)) :
    ∀ u w, DistanceTwo G u w → ∃ x, IsApex G u w x := by
  intro u w huw
  obtain ⟨x, hx, _⟩ := h u w huw
  exact ⟨x, hx⟩

/-- Downward closed for complexity, including equality. -/
def DownwardClosed (c : V → W) (D : Set V) : Prop :=
  ∀ ⦃u v⦄, v ∈ D → c u ≤ c v → u ∈ D

/-- The vertices of the full descending link, lines 189–190. -/
def DescendingLink (G : SimpleGraph V) (c : V → W) (v : V) : Set V :=
  {u | G.Adj v u ∧ c u < c v}

/-- Being the least vertex means least among attained complexity values. -/
def IsLeastVertex (c : V → W) (v : V) : Prop := ∀ u, c v ≤ c u

theorem distanceTwo_induce {G : SimpleGraph V} {D : Set V} {u w : D}
    (h : DistanceTwo (G.induce D) u w) : DistanceTwo G u.val w.val := by
  refine ⟨fun he => h.1 (Subtype.ext he), h.2.1, ?_⟩
  obtain ⟨x, hx⟩ := h.2.2
  exact ⟨x.val, hx⟩

theorem apex_induce {G : SimpleGraph V} {D : Set V} {u w : D} {x : V}
    (hx : IsApex G u.val w.val x) (hD : x ∈ D) :
    IsApex (G.induce D) u w ⟨x, hD⟩ := by
  refine ⟨hx.1, ?_⟩
  intro y hy
  rcases hx.2 y.val hy with he | ha
  · exact Or.inl (Subtype.ext he)
  · exact Or.inr ha

/-- Lemma 2.4(1), the exchange-axiom portion (lines 195–205).
This is valid even for an empty full subcomplex. -/
theorem downward_exchangeStructure {G : SimpleGraph V} {c : V → W}
    (h : ExchangeStructure G c) {D : Set V} (hD : DownwardClosed c D) :
    ExchangeStructure (G.induce D) (fun u : D => c u.val) := by
  have n2 : ∀ u w : D, DistanceTwo (G.induce D) u w →
      ∃ x, IsApex (G.induce D) u w x ∧ c x.val < max (c u.val) (c w.val) := by
    intro u w huw
    obtain ⟨x, hx, hcx⟩ := h.n2 u.val w.val (distanceTwo_induce huw)
    have hxD : x ∈ D := by
      rcases le_total (c u.val) (c w.val) with hc | hc
      · exact hD w.property (le_of_lt (by simpa [max_eq_right hc] using hcx))
      · exact hD u.property (le_of_lt (by simpa [max_eq_left hc] using hcx))
    exact ⟨⟨x, hxD⟩, apex_induce hx hxD, hcx⟩
  exact ⟨n1_of_n2 _ _ n2, n2⟩

/-- The crucial use of the apex's universal quantifier in Lemma 2.4(2).
Every pair of distinct nonadjacent descending neighbors has a lower apex in the link. -/
theorem descending_apex {G : SimpleGraph V} {c : V → W}
    (h : ExchangeStructure G c) (v : V) (u w : DescendingLink G c v)
    (hne : u ≠ w) (hna : ¬ (G.induce (DescendingLink G c v)).Adj u w) :
    ∃ x : DescendingLink G c v,
      IsApex (G.induce (DescendingLink G c v)) u w x ∧
        c x.val < max (c u.val) (c w.val) := by
  have hd : DistanceTwo G u.val w.val :=
    ⟨fun he => hne (Subtype.ext he), hna, ⟨v, u.property.1.symm, w.property.1.symm⟩⟩
  obtain ⟨x, hx, hcx⟩ := h.n2 u.val w.val hd
  have hcv : c x < c v := lt_trans hcx (max_lt u.property.2 w.property.2)
  have hxv : G.Adj v x := by
    rcases hx.2 v ⟨u.property.1.symm, w.property.1.symm⟩ with he | ha
    · exact False.elim ((ne_of_lt hcv) (congrArg c he))
    · exact ha.symm
  exact ⟨⟨x, hxv, hcv⟩, apex_induce hx ⟨hxv, hcv⟩, hcx⟩

theorem descending_exchangeStructure {G : SimpleGraph V} {c : V → W}
    (h : ExchangeStructure G c) (v : V) :
    ExchangeStructure (G.induce (DescendingLink G c v))
      (fun u : DescendingLink G c v => c u.val) := by
  have n2 := fun u w (huw : DistanceTwo (G.induce (DescendingLink G c v)) u w) =>
    descending_apex h v u w huw.1 huw.2.1
  exact ⟨n1_of_n2 _ _ n2, n2⟩

/-- The diameter bound in the proof of Lemma 2.4(2), lines 206–207. -/
theorem descending_walk_length_le_two {G : SimpleGraph V} {c : V → W}
    (h : ExchangeStructure G c) (v : V) (u w : DescendingLink G c v) :
    ∃ p : (G.induce (DescendingLink G c v)).Walk u w, p.length ≤ 2 := by
  classical
  by_cases he : u = w
  · subst w
    exact ⟨.nil, by simp⟩
  by_cases ha : (G.induce (DescendingLink G c v)).Adj u w
  · exact ⟨.cons ha .nil, by simp⟩
  obtain ⟨x, hx, _⟩ := descending_apex h v u w he ha
  exact ⟨.cons hx.1.1 (.cons hx.1.2.symm .nil), by simp⟩

theorem descending_connected {G : SimpleGraph V} {c : V → W}
    (h : ExchangeStructure G c) (v : V) (hne : (DescendingLink G c v).Nonempty) :
    (G.induce (DescendingLink G c v)).Connected := by
  have : Nonempty (DescendingLink G c v) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  refine ⟨fun u w => ?_⟩
  obtain ⟨p, _⟩ := descending_walk_length_le_two h v u w
  exact ⟨p⟩

end Seifert
