/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Statements

/-! No project proof module is imported in this declaration-resolution test. -/
#print SeifertStatement.WeakRealization
#print SeifertStatement.weakTopology
#print SeifertStatement.ExchangeStructure
#print SeifertStatement.TheoremB
#print axioms SeifertStatement.TheoremB

open Topology Convexity
namespace AdversarialAudit
universe u w

/-- Quantifier order, stated using Mathlib's fully qualified metric. -/
theorem statement_n2_metric {V : Type u} {W : Type w}
    [LinearOrder W] [WellFoundedLT W] (G : SimpleGraph V) (c : V → W)
    (h : SeifertStatement.ExchangeStructure G c) :
    ∀ u v, SimpleGraph.edist G u v = 2 →
      ∃ x, SeifertStatement.TwoInterval G u v x ∧
        (∀ y, SeifertStatement.TwoInterval G u v y → x = y ∨ G.Adj x y) ∧
        c x < max (c u) (c v) := by
  intro u v huv
  obtain ⟨x, hx, hc⟩ := h.n2 u v huv
  exact ⟨x, hx.1, hx.2, hc⟩

/-- This is the literal closed-simplex weak-topology criterion from the standalone source. -/
theorem independent_closed_criterion {V : Type u} (G : SimpleGraph V)
    (A : Set (SeifertStatement.WeakRealization G)) :
    IsClosed A ↔ ∀ s : {s // s ∈ SeifertStatement.cliqueComplex G},
      IsClosed (SeifertStatement.closedSimplex G s ⁻¹' A) := by
  change IsClosed[⨆ s : {s // s ∈ SeifertStatement.cliqueComplex G},
    TopologicalSpace.coinduced (SeifertStatement.closedSimplex G s) inferInstance] A ↔ _
  simp only [isClosed_iSup_iff, isClosed_coinduced]

#print axioms statement_n2_metric
#print axioms independent_closed_criterion
end AdversarialAudit
