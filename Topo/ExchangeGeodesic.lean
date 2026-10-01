/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.Exchange

/-! Corollary 2.3: minimizing the largest complexity on a shortest walk. -/

universe u w

namespace Seifert

open SimpleGraph

variable {V : Type u} {W : Type w} {G : SimpleGraph V}

/-- An occurrence other than either endpoint has two incident edges and a prefix/suffix. -/
theorem interior_decomposition {s t m : V} (p : G.Walk s t)
    (hm : m ∈ p.support) (hms : m ≠ s) (hmt : m ≠ t) :
    ∃ (a b : V) (l : G.Walk s a) (r : G.Walk b t)
      (ham : G.Adj a m) (hmb : G.Adj m b),
      p = l.append (.cons ham (.cons hmb r)) := by
  induction p with
  | nil => simp only [Walk.support_nil, List.mem_singleton] at hm; exact (hms hm).elim
  | @cons s k t hsk p ih =>
    have hmp : m ∈ p.support := by simpa [hms] using hm
    by_cases hmk : m = k
    · subst k
      cases p with
      | nil => exact (hmt rfl).elim
      | @cons m b t hmb r => exact ⟨s, b, .nil, r, hsk, hmb, rfl⟩
    · obtain ⟨a, b, l, r, ham, hmb, he⟩ := ih hmp hmk hmt
      exact ⟨a, b, .cons hsk l, r, ham, hmb, by simp [he]⟩

variable [LinearOrder W]

/-- The maximum attained value on a finite walk; W need not have a bottom element. -/
noncomputable def walkHeight (c : V → W) {s t : V} (p : G.Walk s t) : W := by
  classical
  exact (p.support.toFinset.image c).max'
    ⟨c s, Finset.mem_image.mpr ⟨s, by simp, rfl⟩⟩

theorem le_walkHeight (c : V → W) {s t z : V} (p : G.Walk s t) (hz : z ∈ p.support) :
    c z ≤ walkHeight c p := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨z, by simpa using hz, rfl⟩)

theorem walkHeight_mem (c : V → W) {s t : V} (p : G.Walk s t) :
    ∃ z ∈ p.support, c z = walkHeight c p := by
  classical
  have hm : walkHeight c p ∈ p.support.toFinset.image c := Finset.max'_mem _ _
  obtain ⟨z, hz, hc⟩ := Finset.mem_image.mp hm
  exact ⟨z, by simpa using hz, hc⟩

theorem walkHeight_lt (c : V → W) {s t : V} (p : G.Walk s t) {a : W}
    (h : ∀ z ∈ p.support, c z < a) : walkHeight c p < a := by
  obtain ⟨z, hz, he⟩ := walkHeight_mem c p
  exact he ▸ h z hz

variable [WellFoundedLT W]

/-- Corollary 2.3, last sentence (lines 158–159), with an actual Mathlib shortest path.
No cardinality, local-finiteness, or natural-number-valued-complexity hypothesis is used. -/
theorem bounded_geodesic {c : V → W} (h : InjectiveExchangeComplex G c) (s t : V) :
    ∃ p : G.Walk s t, p.IsPath ∧ p.length = G.dist s t ∧
      ∀ z ∈ p.support, c z ≤ max (c s) (c t) := by
  classical
  let H : Set W := {a | ∃ p : G.Walk s t, p.length = G.dist s t ∧ walkHeight c p = a}
  have hH : H.Nonempty := by
    obtain ⟨p, hp⟩ := h.connected.exists_walk_length_eq_dist s t
    exact ⟨walkHeight c p, p, hp, rfl⟩
  obtain ⟨M, ⟨p, hplen, hpM⟩, hmin⟩ := wellFounded_lt.has_min H hH
  have hp : p.IsPath := p.isPath_of_length_eq_dist hplen
  refine ⟨p, hp, hplen, ?_⟩
  intro z hz
  by_contra hbound
  have hbound : max (c s) (c t) < c z := lt_of_not_ge hbound
  obtain ⟨m, hm, hmM⟩ := walkHeight_mem c p
  have hends : max (c s) (c t) < c m := by
    rw [hmM]
    exact lt_of_lt_of_le hbound (le_walkHeight c p hz)
  have hms : m ≠ s := by
    intro he
    have ht := lt_of_le_of_lt (le_max_left (c s) (c t)) hends
    simp [he] at ht
  have hmt : m ≠ t := by
    intro he
    have ht := lt_of_le_of_lt (le_max_right (c s) (c t)) hends
    simp [he] at ht
  obtain ⟨a, b, l, r, ham, hmb, he⟩ := interior_decomposition p hm hms hmt
  have hp' : (l.append (.cons ham (.cons hmb r))).IsPath := he ▸ hp
  have hm_l : m ∉ l.support := by
    intro hml
    exact hp'.ne_of_mem_support_of_append ham.ne.symm hml (by simp) rfl
  have hm_r : m ∉ r.support := by
    have hs := hp'.of_append_right.support_nodup
    simp only [Walk.support_cons, List.nodup_cons] at hs
    exact hs.2.1
  have hsmall : ∀ y, y ∈ l.support ∨ y ∈ r.support → c y < c m := by
    intro y hy
    have hym : y ≠ m := by
      intro hym
      subst y
      exact hy.elim hm_l hm_r
    have hyp : y ∈ p.support := by
      rw [he, Walk.mem_support_append_iff]
      rcases hy with hy | hy
      · exact Or.inl hy
      · exact Or.inr (by simp [hy])
    have hle : c y ≤ c m := by simpa [hmM] using le_walkHeight c p hyp
    exact lt_of_le_of_ne hle (fun he => hym (h.injective he))
  have hab : a ≠ b := by
    have hs := hp'.of_append_right.support_nodup
    simp only [Walk.support_cons, List.nodup_cons] at hs
    intro heab
    exact hs.1 (List.mem_cons_of_mem m (heab.symm ▸ r.start_mem_support))
  have hna : ¬ G.Adj a b := by
    intro ha
    have hlen := G.dist_le (l.append (.cons ha r))
    have hlenp : p.length = l.length + (r.length + 2) := by simp [he]
    simp only [Walk.length_append, Walk.length_cons] at hlen
    omega
  have hd : DistanceTwo G a b := ⟨hab, hna, ⟨m, ham, hmb.symm⟩⟩
  obtain ⟨x, hx, hcx⟩ := h.n2 a b hd
  have hxm : c x < c m := lt_trans hcx (max_lt
    (hsmall a (Or.inl l.end_mem_support)) (hsmall b (Or.inr r.start_mem_support)))
  let q := l.append (.cons hx.1.1 (.cons hx.1.2.symm r))
  have hqlen : q.length = G.dist s t := by
    rw [← hplen, he]
    simp [q]
  have hqsmall : ∀ y ∈ q.support, c y < c m := by
    intro y hy
    simp only [q, Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons] at hy
    rcases hy with hy | hy | hy | hy
    · exact hsmall y (Or.inl hy)
    · subst y; exact hsmall a (Or.inl l.end_mem_support)
    · subst y; exact hxm
    · exact hsmall y (Or.inr hy)
  have hqM : walkHeight c q < M := by
    rw [← hpM, ← hmM]
    exact walkHeight_lt c q hqsmall
  exact hmin (walkHeight c q) ⟨q, hqlen, rfl⟩ hqM

end Seifert
