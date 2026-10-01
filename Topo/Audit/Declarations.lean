/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.Audit.Statements

/-! Declaration identity, binder and universe probes. -/

#print SeifertStatement.ExchangeStructure
#print SeifertStatement.ExchangeComplex
#print SeifertStatement.TheoremB
#check @SeifertAudit.theoremB_verified
#check @Seifert.theoremB
#check @SeifertAudit.theoremB_verified.{0, 0}
#check @SeifertAudit.theoremB_verified.{3, 2}
#print Seifert.ties_may_be_broken
#print Seifert.tieComplexity_wellOrdersVertices
#check @Seifert.injective_sublevel_contractible
#check @Topo.Complex.contractible_sublevel
#check @Topo.Complex.contractible_of_cofinal_contractible
#check @Topo.Complex.contractible_of_directed_union
#print WellFoundedLT
#print ContractibleSpace
#print Convexity.StdSimplex
#print SimpleGraph.edist
#check @SimpleGraph.edist_eq_two_iff
#check @SimpleGraph.Connected
#check @SimpleGraph.Preconnected
#check @Topo.Complex.isClosed_iff
#print axioms SeifertAudit.theoremB_verified
#print axioms Seifert.theoremB
#print axioms Seifert.ties_may_be_broken
#print axioms Seifert.tieComplexity_wellOrdersVertices
#print axioms Seifert.injective_sublevel_contractible
#print axioms Topo.Complex.contractible_sublevel
#print axioms Topo.Complex.contractible_of_finiteInclusionsNull
#print axioms Topo.Complex.contractible_of_cofinal_contractible
#print axioms Topo.Complex.continuous_prod_iff

/-! Fully qualified equalities require the actual Mathlib declarations. -/
namespace AdversarialAudit
open Topology Convexity
universe u w

theorem mathlib_realization_identity {V : Type u} (G : SimpleGraph V) :
    SeifertStatement.WeakRealization G =
      {x : Convexity.StdSimplex ℝ V // x.weights.support ∈ SeifertStatement.cliqueComplex G} := rfl

theorem mathlib_edist_n1_identity {V : Type u} {W : Type w}
    [LinearOrder W] [WellFoundedLT W] (G : SimpleGraph V) (c : V → W)
    (h : SeifertStatement.ExchangeStructure G c) :
    ∀ u v, SimpleGraph.edist G u v = 2 → ∃ x, SeifertStatement.IsApex G u v x := h.n1

/-- In particular no extra universe equality or hidden typeclass parameter is needed. -/
theorem theoremB_all_universes (V : Type u) (W : Type w)
    [LinearOrder W] [WellFoundedLT W] (G : SimpleGraph V) (c : V → W)
    (h : SeifertStatement.ExchangeComplex G c) :
    _root_.ContractibleSpace (SeifertStatement.WeakRealization G) :=
  SeifertAudit.theoremB_verified V W G c h

#print axioms mathlib_realization_identity
#print axioms mathlib_edist_n1_identity
#print axioms theoremB_all_universes
end AdversarialAudit
