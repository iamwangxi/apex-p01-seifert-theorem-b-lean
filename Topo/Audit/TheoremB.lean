/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.Audit.Statements
import Topo.Examples.Exchange

/-! The theorem signatures and all new public mathematical components are kernel-audited. -/
#check @Seifert.theoremB
#check @Seifert.ties_may_be_broken
#check @SeifertAudit.theoremB_verified

#print axioms Seifert.cliqueComplex
#print axioms Seifert.mem_cliqueComplex
#print axioms Seifert.singleton_cliqueComplex
#print axioms Seifert.pair_cliqueComplex
#print axioms Seifert.cliqueComplex_isFlag
#print axioms Seifert.cliqueComplex_eq_ofPreAbstract
#print axioms Seifert.clique_induce_face
#print axioms Seifert.fullInduceHomeomorph
#print axioms Seifert.descendingLink_cliqueComplex
#print axioms Seifert.tieComplexity
#print axioms Seifert.tieComplexity_wellOrdersVertices
#print axioms Seifert.tieComplexity_injective
#print axioms Seifert.tieComplexity_exchangeStructure
#print axioms Seifert.ties_may_be_broken
#print axioms Seifert.exchangeComplex_ties_may_be_broken
#print axioms Seifert.contractible_of_sublevels
#print axioms Seifert.contractible_sublevel_of_least
#print axioms Seifert.injective_sublevel_contractible
#print axioms Seifert.injective_exchangeComplex_contractible
#print axioms Seifert.theoremB

#print axioms SeifertStatement.cliqueComplex
#print axioms SeifertStatement.WeakRealization
#print axioms SeifertStatement.closedSimplex
#print axioms SeifertStatement.weakTopology
#print axioms SeifertStatement.TwoInterval
#print axioms SeifertStatement.IsApex
#print axioms SeifertStatement.ExchangeStructure
#print axioms SeifertStatement.ExchangeComplex
#print axioms SeifertStatement.TheoremB
#print axioms SeifertAudit.cliqueComplex_eq
#print axioms SeifertAudit.realization_eq
#print axioms SeifertAudit.weakTopology_eq
#print axioms SeifertAudit.realizationHomeomorph
#print axioms SeifertAudit.twoInterval_eq
#print axioms SeifertAudit.isApex_iff
#print axioms SeifertAudit.exchangeStructure_iff
#print axioms SeifertAudit.exchangeComplex_iff
#print axioms SeifertAudit.theoremB_verified

#print axioms Seifert.seven_nonempty
#print axioms Seifert.seven_contractible
#print axioms Seifert.OmegaStar.Vertex
#print axioms Seifert.OmegaStar.graph
#print axioms Seifert.OmegaStar.nonempty_realization
#print axioms Seifert.OmegaStar.exchange
#print axioms Seifert.OmegaStar.complexity_orderType
#print axioms Seifert.OmegaStar.distanceTwo_one_top
#print axioms Seifert.OmegaStar.infinite_neighbors
#print axioms Seifert.OmegaStar.not_locallyFinite
#print axioms Seifert.OmegaStar.limit_stage_no_largest
#print axioms Seifert.OmegaStar.contractible
#print axioms Seifert.OmegaStar.limit_stage_contractible
#print axioms Seifert.OmegaStar.successor_after_limit_contractible

-- Previously proved ingredients that enter the assembled proof.
#print axioms Seifert.bounded_geodesic
#print axioms Seifert.downward_edist_eq
#print axioms Seifert.strictSublevel_injectiveExchangeComplex
#print axioms Seifert.descending_injectiveExchangeComplex
#print axioms Seifert.descendingLink_nonempty
#print axioms Topo.Complex.contractible_of_cofinal_contractible
#print axioms Topo.Complex.contractible_of_directed_union
#print axioms Topo.Complex.contractible_sublevel
#print axioms Topo.Complex.contractible_of_largest_vertex
