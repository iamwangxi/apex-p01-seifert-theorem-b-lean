/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.ExchangeGeodesic

/-!
# Corollary 2.3 and Lemma 2.4

For an empty D, pairwise reachability and isometry still hold. `Connected`, following Mathlib's
explicit nonempty convention, is asserted only for nonempty D. This is also exactly the
nonempty qualification in Lemma 2.4(1).
-/

universe u w

namespace Seifert

open SimpleGraph

variable {V : Type u} {W : Type w} [LinearOrder W] [WellFoundedLT W]
variable {G : SimpleGraph V} {c : V → W}

/-- Complexity induces a well-founded strict relation on vertices, without a finiteness bound. -/
theorem complexity_wellFounded (c : V → W) :
    WellFounded (fun u v : V => c u < c v) := InvImage.wf c wellFounded_lt

/-- The least vertex used in the paper's last paragraph exists and is unique. -/
theorem exists_unique_leastVertex (h : InjectiveExchangeComplex G c) :
    ∃! v, IsLeastVertex c v := by
  have hne : (Set.univ : Set V).Nonempty := by
    obtain ⟨v⟩ := h.connected.nonempty
    exact ⟨v, Set.mem_univ v⟩
  obtain ⟨v, _, hv⟩ := (complexity_wellFounded c).has_min Set.univ hne
  have hleast : IsLeastVertex c v := fun u => le_of_not_gt (hv u (Set.mem_univ u))
  refine ⟨v, hleast, ?_⟩
  intro u hu
  exact h.injective (le_antisymm (hu v) (hleast u))

/-- A shortest ambient walk lifts to the full downward-closed subcomplex, at the same length. -/
theorem downward_geodesic (h : InjectiveExchangeComplex G c) {D : Set V}
    (hD : DownwardClosed c D) (s t : D) :
    ∃ q : (G.induce D).Walk s t, q.length = G.dist s.val t.val := by
  obtain ⟨p, _, hlen, hbound⟩ := bounded_geodesic h s.val t.val
  have hpD : ∀ z ∈ p.support, z ∈ D := by
    intro z hz
    have hb := hbound z hz
    rcases le_total (c s.val) (c t.val) with he | he
    · exact hD t.property (by simpa [max_eq_right he] using hb)
    · exact hD s.property (by simpa [max_eq_left he] using hb)
  let q := p.induce D hpD
  have hq : q.length = p.length := by
    calc
      q.length = (q.map (Embedding.induce D).toHom).length :=
        (Walk.length_map _ _).symm
      _ = p.length := congrArg (fun w : G.Walk s.val t.val => w.length) (p.map_induce hpD)
  exact ⟨q, hq.trans hlen⟩

/-- Corollary 2.3: isometric embedding in the edge-path metric, lines 156–178. -/
theorem downward_dist_eq (h : InjectiveExchangeComplex G c) {D : Set V}
    (hD : DownwardClosed c D) (s t : D) :
    (G.induce D).dist s t = G.dist s.val t.val := by
  obtain ⟨q, hq⟩ := downward_geodesic h hD s t
  apply le_antisymm
  · exact hq ▸ (G.induce D).dist_le q
  · obtain ⟨p, hp⟩ := q.reachable.exists_walk_length_eq_dist
    have hd := G.dist_le (p.map (Embedding.induce D).toHom)
    rw [Walk.length_map] at hd
    change G.dist s.val t.val ≤ p.length at hd
    exact hp ▸ hd

/-- The same isometry using extended distances, whose infinite value detects disconnectedness. -/
theorem downward_edist_eq (h : InjectiveExchangeComplex G c) {D : Set V}
    (hD : DownwardClosed c D) (s t : D) :
    (G.induce D).edist s t = G.edist s.val t.val := by
  obtain ⟨q, _⟩ := downward_geodesic h hD s t
  rw [← q.reachable.coe_dist_eq_edist,
    ← (h.connected s.val t.val).coe_dist_eq_edist, downward_dist_eq h hD]

/-- Corollary 2.3: the pairwise connectedness conclusion, valid also when D is empty. -/
theorem downward_preconnected (h : InjectiveExchangeComplex G c) {D : Set V}
    (hD : DownwardClosed c D) : (G.induce D).Preconnected := by
  intro s t
  obtain ⟨q, _⟩ := downward_geodesic h hD s t
  exact ⟨q⟩

theorem downward_connected (h : InjectiveExchangeComplex G c) {D : Set V}
    (hD : DownwardClosed c D) (hne : D.Nonempty) : (G.induce D).Connected := by
  have : Nonempty D := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  exact ⟨downward_preconnected h hD⟩

/-- Lemma 2.4(1): if nonempty, every full downward subcomplex is an injective exchange complex. -/
theorem downward_injectiveExchangeComplex (h : InjectiveExchangeComplex G c) {D : Set V}
    (hD : DownwardClosed c D) (hne : D.Nonempty) :
    InjectiveExchangeComplex (G.induce D) (fun u : D => c u.val) :=
  { downward_exchangeStructure h.toExchangeStructure hD with
    connected := downward_connected h hD hne
    injective := h.injective.comp Subtype.val_injective }

/-- The particular strict sublevel X_<v of Lemma 2.4(1), lines 180–191. -/
theorem strictSublevel_injectiveExchangeComplex (h : InjectiveExchangeComplex G c) (v : V)
    (hne : ({u | c u < c v} : Set V).Nonempty) :
    InjectiveExchangeComplex (G.induce {u | c u < c v})
      (fun u : {u | c u < c v} => c u.val) := by
  apply downward_injectiveExchangeComplex h (hne := hne)
  intro u w hw huw
  exact lt_of_le_of_lt huw hw

/-- Lemma 2.4(2), nonemptiness away from the least vertex, lines 208–210.
The argument uses the first neighbor on a bounded shortest path to a lower vertex. -/
theorem descendingLink_nonempty (h : InjectiveExchangeComplex G c) (v : V)
    (hv : ¬ IsLeastVertex c v) : (DescendingLink G c v).Nonempty := by
  classical
  obtain ⟨u, hu⟩ : ∃ u, c u < c v := by
    simpa [IsLeastVertex, not_forall, not_le] using hv
  obtain ⟨p, _, _, hb⟩ := bounded_geodesic h v u
  cases p with
  | nil => exact (lt_irrefl _ hu).elim
  | @cons v z u hvz r =>
    have hzle : c z ≤ c v := by
      simpa [max_eq_left (le_of_lt hu)] using hb z (by simp)
    have hzne : c z ≠ c v := fun he => hvz.ne (h.injective he).symm
    exact ⟨z, hvz, lt_of_le_of_ne hzle hzne⟩

theorem descendingLink_nonempty_iff (h : InjectiveExchangeComplex G c) (v : V) :
    (DescendingLink G c v).Nonempty ↔ ¬ IsLeastVertex c v := by
  refine ⟨?_, descendingLink_nonempty h v⟩
  rintro ⟨u, _, hu⟩ hv
  exact (not_lt_of_ge (hv u)) hu

/-- Lemma 2.4(2): a nonempty descending link inherits the entire injective exchange complex. -/
theorem descending_injectiveExchangeComplex (h : InjectiveExchangeComplex G c) (v : V)
    (hne : (DescendingLink G c v).Nonempty) :
    InjectiveExchangeComplex (G.induce (DescendingLink G c v))
      (fun u : DescendingLink G c v => c u.val) :=
  { descending_exchangeStructure h.toExchangeStructure v with
    connected := descending_connected h.toExchangeStructure v hne
    injective := h.injective.comp Subtype.val_injective }

/-- A single package of the two conclusions for every nonleast vertex. -/
theorem nonleast_descending_exchangeComplex (h : InjectiveExchangeComplex G c) (v : V)
    (hv : ¬ IsLeastVertex c v) :
    (DescendingLink G c v).Nonempty ∧
      InjectiveExchangeComplex (G.induce (DescendingLink G c v))
        (fun u : DescendingLink G c v => c u.val) :=
  ⟨descendingLink_nonempty h v hv,
    descending_injectiveExchangeComplex h v (descendingLink_nonempty h v hv)⟩

/-- Diameter at most two, in the actual graph metric. -/
theorem descending_dist_le_two (h : ExchangeStructure G c) (v : V)
    (u w : DescendingLink G c v) :
    (G.induce (DescendingLink G c v)).dist u w ≤ 2 := by
  obtain ⟨p, hp⟩ := descending_walk_length_le_two h v u w
  exact le_trans (SimpleGraph.dist_le p) hp

end Seifert
