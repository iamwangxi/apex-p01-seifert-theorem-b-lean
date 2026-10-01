/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.ExchangeContractible

/-!
# Conditional application of Seifert's geometric exchange lemma

No surface geometry is proved here. The geometric inputs are precisely `SurfaceSystem`:
§4.1 connectedness/nonemptiness, Definition 4.7 positive relative area, Lemma 4.8(iii)
well-foundedness of attained values, and Theorem 5.1(a)–(d). Flagness (Lemma 4.3(1))
is represented by taking the clique complex. In particular apices and descent are conclusions.
-/

noncomputable section
universe u
namespace Seifert.Application
variable {V : Type u} {G : SimpleGraph V} {g : V → ℕ} {A : V → ℝ}

/-- Definition 4.7: genus first, relative area second. -/
def complexity (g : V → ℕ) (A : V → ℝ) (v : V) : ℕ ×ₗ ℝ := toLex (g v, A v)

/-- Only actually attained values, with the subtype's induced lexicographic order. -/
def Values (g : V → ℕ) (A : V → ℝ) := Set.range (complexity g A)

/-- Complexity as a map into the actual value set W. -/
def value (g : V → ℕ) (A : V → ℝ) (v : V) : Values g A :=
  ⟨complexity g A v, ⟨v, rfl⟩⟩

/-- Equality or adjacency, with no simultaneous-disjointness assertion. -/
def EqAdj (G : SimpleGraph V) (u v : V) : Prop := u = v ∨ G.Adj u v

theorem EqAdj.symm {u v : V} (h : EqAdj G u v) : EqAdj G v u := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

/-- The four clauses of Theorem 5.1. The output vertices precede the universal `z`. -/
structure Outputs (G : SimpleGraph V) (g : V → ℕ) (A : V → ℝ)
    (x u w p q : V) : Prop where
  a_up : EqAdj G p x ∧ EqAdj G p u ∧ EqAdj G p w
  a_down : EqAdj G q x ∧ EqAdj G q u ∧ EqAdj G q w
  b : ∀ z, EqAdj G z u → EqAdj G z w → EqAdj G z p ∧ EqAdj G z q
  c : g p + g q ≤ g u + g w
  d : g p + g q = g u + g w → A p + A q < A u + A w

/-- All unformalized geometric conclusions, individually exposed as premises.
Connected includes nonempty (§4.1); positive area is Definition 4.7; only W is well-ordered
(Lemma 4.8(iii)); the last field is exactly the existential/universal order of Theorem 5.1. -/
structure SurfaceSystem (G : SimpleGraph V) (g : V → ℕ) (A : V → ℝ) : Prop where
  positive : ∀ v, 0 < A v
  connected : G.Connected
  wellFounded : WellFounded ((· < ·) : Values g A → Values g A → Prop)
  outputs : ∀ x u w, G.Adj x u → G.Adj x w → G.edist u w = 2 →
    ∃ p q, Outputs G g A x u w p q

/-- The geometry-free part of the assumptions; no well-order or connectedness is needed. -/
def HasOutputs (G : SimpleGraph V) (g : V → ℕ) (A : V → ℝ) : Prop :=
  ∀ x u w, G.Adj x u → G.Adj x w → G.edist u w = 2 →
    ∃ p q, Outputs G g A x u w p q

@[simp] theorem complexity_le {u v : V} :
    complexity g A u ≤ complexity g A v ↔
      g u < g v ∨ g u = g v ∧ A u ≤ A v := Prod.Lex.toLex_le_toLex

@[simp] theorem complexity_lt {u v : V} :
    complexity g A u < complexity g A v ↔
      g u < g v ∨ g u = g v ∧ A u < A v := Prod.Lex.toLex_lt_toLex

theorem genus_le_of_complexity_le {u v : V}
    (h : complexity g A u ≤ complexity g A v) : g u ≤ g v := by
  rcases complexity_le.mp h with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

theorem area_le_of_complexity_le {u v : V}
    (h : complexity g A u ≤ complexity g A v) (he : g u = g v) : A u ≤ A v := by
  rcases complexity_le.mp h with h | ⟨_, h⟩
  · omega
  · exact h

/-- Equal-or-adjacent to both nonadjacent, distinct endpoints means a genuine common neighbor. -/
theorem commonNeighbor_of_eqAdj {u w p : V} (huw : Seifert.DistanceTwo G u w)
    (hpu : EqAdj G p u) (hpw : EqAdj G p w) : p ∈ Seifert.TwoInterval G u w := by
  have hpu' : p ≠ u := by
    intro he
    subst p
    rcases hpw with he | ha
    · exact huw.1 he
    · exact huw.2.1 ha
  have hpw' : p ≠ w := by
    intro he
    subst p
    rcases hpu with he | ha
    · exact huw.1 he.symm
    · exact huw.2.1 ha.symm
  exact ⟨(hpu.resolve_left hpu').symm, (hpw.resolve_left hpw').symm⟩

/-- Proposition 5.2(1), for both outputs of any prescribed common neighbor. -/
theorem Outputs.apices {x u w p q : V} (h : Outputs G g A x u w p q)
    (huw : Seifert.DistanceTwo G u w) :
    Seifert.IsApex G u w p ∧ Seifert.IsApex G u w q := by
  refine ⟨⟨commonNeighbor_of_eqAdj huw h.a_up.2.1 h.a_up.2.2, ?_⟩,
    ⟨commonNeighbor_of_eqAdj huw h.a_down.2.1 h.a_down.2.2, ?_⟩⟩
  · intro z hz
    exact ((h.b z (Or.inr hz.1.symm) (Or.inr hz.2.symm)).1).symm
  · intro z hz
    exact ((h.b z (Or.inr hz.1.symm) (Or.inr hz.2.symm)).2).symm

/-- Proposition 5.2(1): existence; the distance-two premise supplies a common neighbor. -/
theorem apex_exists (h : HasOutputs G g A) {u w : V}
    (huw : Seifert.DistanceTwo G u w) : ∃ p, Seifert.IsApex G u w p := by
  obtain ⟨x, hxu, hxw⟩ := huw.2.2
  obtain ⟨p, q, hpq⟩ := h x u w hxu.symm hxw.symm
    ((Seifert.distanceTwo_iff_edist G u w).mp huw)
  exact ⟨p, (hpq.apices huw).1⟩

/-- Quantitative local descent, without any well-order. If both outputs fail to descend,
(c) forces all four genera to equal the upper bound's genus; then (d) contradicts their areas. -/
theorem Outputs.below_upper {x u w p q v : V} (h : Outputs G g A x u w p q)
    (hu : complexity g A u ≤ complexity g A v)
    (hw : complexity g A w ≤ complexity g A v) :
    complexity g A p < complexity g A v ∨ complexity g A q < complexity g A v := by
  by_contra hn
  have hp : complexity g A v ≤ complexity g A p := le_of_not_gt (fun hh => hn (Or.inl hh))
  have hq : complexity g A v ≤ complexity g A q := le_of_not_gt (fun hh => hn (Or.inr hh))
  have hgu := genus_le_of_complexity_le hu
  have hgw := genus_le_of_complexity_le hw
  have hgp := genus_le_of_complexity_le hp
  have hgq := genus_le_of_complexity_le hq
  have hc := h.c
  have eu : g u = g v := by omega
  have ew : g w = g v := by omega
  have ep : g v = g p := by omega
  have eq : g v = g q := by omega
  have he : g p + g q = g u + g w := by omega
  have hau := area_le_of_complexity_le hu eu
  have haw := area_le_of_complexity_le hw ew
  have hap := area_le_of_complexity_le hp ep
  have haq := area_le_of_complexity_le hq eq
  have hd := h.d he
  linarith

/-- The original local descent assertion, including its genus bound. -/
theorem Outputs.local_descent {x u w p q : V} (h : Outputs G g A x u w p q)
    (hu : complexity g A u ≤ complexity g A x)
    (hw : complexity g A w ≤ complexity g A x) :
    (complexity g A p < complexity g A x ∧ g p ≤ g x) ∨
      (complexity g A q < complexity g A x ∧ g q ≤ g x) := by
  rcases h.below_upper hu hw with hp | hq
  · exact Or.inl ⟨hp, genus_le_of_complexity_le (le_of_lt hp)⟩
  · exact Or.inr ⟨hq, genus_le_of_complexity_le (le_of_lt hq)⟩

/-- At least one of the two outputs is below max(c(u),c(w)), directly from (c),(d). -/
theorem Outputs.one_below_max {x u w p q : V} (h : Outputs G g A x u w p q) :
    complexity g A p < max (complexity g A u) (complexity g A w) ∨
      complexity g A q < max (complexity g A u) (complexity g A w) := by
  rcases le_total (complexity g A u) (complexity g A w) with hu | hw
  · simpa only [max_eq_right hu] using h.below_upper hu le_rfl
  · simpa only [max_eq_left hw] using h.below_upper le_rfl hw

/-- Proposition 5.2(2), direct proof. No positivity, connectedness or well-order is assumed. -/
theorem lower_apex_direct (h : HasOutputs G g A) {u w : V}
    (huw : Seifert.DistanceTwo G u w) :
    ∃ p, Seifert.IsApex G u w p ∧
      complexity g A p < max (complexity g A u) (complexity g A w) := by
  obtain ⟨x, hxu, hxw⟩ := huw.2.2
  obtain ⟨p, q, hpq⟩ := h x u w hxu.symm hxw.symm
    ((Seifert.distanceTwo_iff_edist G u w).mp huw)
  rcases hpq.one_below_max with hp | hq
  · exact ⟨p, (hpq.apices huw).1, hp⟩
  · exact ⟨q, (hpq.apices huw).2, hq⟩

/-- Proposition 5.2(2), the paper's minimal-apex + local-descent proof.
The minimum is taken for attained complexity, allowing ties among vertices. -/
theorem lower_apex_minimal (h : HasOutputs G g A)
    (hwf : WellFounded ((· < ·) : Values g A → Values g A → Prop))
    {u w : V} (huw : Seifert.DistanceTwo G u w) :
    ∃ x, Seifert.IsApex G u w x ∧
      complexity g A x < max (complexity g A u) (complexity g A w) := by
  have hne : ({x | Seifert.IsApex G u w x} : Set V).Nonempty := apex_exists h huw
  obtain ⟨x, hx, hmin⟩ := (InvImage.wf (value g A) hwf).has_min _ hne
  refine ⟨x, hx, ?_⟩
  by_contra hn
  have hmax : max (complexity g A u) (complexity g A w) ≤ complexity g A x :=
    le_of_not_gt hn
  obtain ⟨p, q, hpq⟩ := h x u w hx.1.1.symm hx.1.2.symm
    ((Seifert.distanceTwo_iff_edist G u w).mp huw)
  rcases hpq.local_descent (le_trans (le_max_left _ _) hmax)
      (le_trans (le_max_right _ _) hmax) with ⟨hp, _⟩ | ⟨hq, _⟩
  · exact hmin p (hpq.apices huw).1 hp
  · exact hmin q (hpq.apices huw).2 hq

/-- Strict complexity descent bounds the first coordinate by both endpoints' maximum genus. -/
theorem genus_le_max_of_lt {u w p : V}
    (hp : complexity g A p < max (complexity g A u) (complexity g A w)) :
    g p ≤ max (g u) (g w) := by
  rcases lt_max_iff.mp hp with hu | hw
  · exact le_trans (genus_le_of_complexity_le (le_of_lt hu)) (le_max_left _ _)
  · exact le_trans (genus_le_of_complexity_le (le_of_lt hw)) (le_max_right _ _)

/-- Proposition 5.2(3), retaining the apex and strict descent as well as the genus bound. -/
theorem lower_apex_genus (h : HasOutputs G g A) {u w : V}
    (huw : Seifert.DistanceTwo G u w) (ℓ : ℕ) (hu : g u ≤ ℓ) (hw : g w ≤ ℓ) :
    ∃ p, Seifert.IsApex G u w p ∧
      complexity g A p < max (complexity g A u) (complexity g A w) ∧ g p ≤ ℓ := by
  obtain ⟨p, hp, hc⟩ := lower_apex_direct h huw
  exact ⟨p, hp, hc, le_trans (genus_le_max_of_lt hc) (max_le hu hw)⟩

/-- Theorem 5.1 implies the exchange axioms on W, whose order is induced, not invented. -/
theorem exchangeComplex (h : SurfaceSystem G g A) :
    let : WellFoundedLT (Values g A) := h.wellFounded
    Seifert.ExchangeComplex G (value g A) := by
  let : WellFoundedLT (Values g A) := h.wellFounded
  have hn2 : ∀ u w, Seifert.DistanceTwo G u w →
      ∃ x, Seifert.IsApex G u w x ∧ value g A x < max (value g A u) (value g A w) := by
    intro u w huw
    obtain ⟨x, hx, hc⟩ := lower_apex_direct h.outputs huw
    refine ⟨x, hx, ?_⟩
    rcases lt_max_iff.mp hc with hu | hw
    · exact lt_max_iff.mpr (Or.inl hu)
    · exact lt_max_iff.mpr (Or.inr hw)
  exact { n1 := Seifert.n1_of_n2 _ _ hn2, n2 := hn2, connected := h.connected }

/-- Conditional Theorem A (§6.1), invoking the already formalized Theorem B. -/
theorem theoremA (h : SurfaceSystem G g A) :
    ContractibleSpace (Seifert.cliqueComplex G).Realization := by
  let : WellFoundedLT (Values g A) := h.wellFounded
  exact Seifert.theoremB (exchangeComplex h)

end Seifert.Application
