/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.SurfacePathExample
import Topo.SurfaceExamples
import Topo.SurfaceCounterexample
import Topo.Audit.ApplicationStatements

/-! Kernel-dependency audit for every new public mathematical declaration. -/

#check Seifert.Application.SurfaceSystem
#check Seifert.Application.Outputs
#check Seifert.Application.lower_apex_direct
#check Seifert.Application.lower_apex_minimal
#check Seifert.Application.exchangeComplex
#check Seifert.Application.theoremA
#check Seifert.Application.theoremC_genus
#check Seifert.Application.theoremC_area
#check SeifertApplicationAudit.theoremA_verified
#check SeifertApplicationAudit.theoremC_genus_verified
#check SeifertApplicationAudit.theoremC_area_verified

#print axioms Seifert.theoremB
#print axioms Seifert.cliqueComplex_isFlag
#print axioms Seifert.tieComplexity_exchangeStructure
#print axioms Seifert.downward_dist_eq
#print axioms Seifert.downward_edist_eq
#print axioms Seifert.downward_injectiveExchangeComplex

#print axioms Seifert.Application.complexity
#print axioms Seifert.Application.Values
#print axioms Seifert.Application.value
#print axioms Seifert.Application.EqAdj
#print axioms Seifert.Application.EqAdj.symm
#print axioms Seifert.Application.Outputs
#print axioms Seifert.Application.SurfaceSystem
#print axioms Seifert.Application.HasOutputs
#print axioms Seifert.Application.complexity_le
#print axioms Seifert.Application.complexity_lt
#print axioms Seifert.Application.genus_le_of_complexity_le
#print axioms Seifert.Application.area_le_of_complexity_le
#print axioms Seifert.Application.commonNeighbor_of_eqAdj
#print axioms Seifert.Application.Outputs.apices
#print axioms Seifert.Application.apex_exists
#print axioms Seifert.Application.Outputs.below_upper
#print axioms Seifert.Application.Outputs.local_descent
#print axioms Seifert.Application.Outputs.one_below_max
#print axioms Seifert.Application.lower_apex_direct
#print axioms Seifert.Application.lower_apex_minimal
#print axioms Seifert.Application.genus_le_max_of_lt
#print axioms Seifert.Application.lower_apex_genus
#print axioms Seifert.Application.exchangeComplex
#print axioms Seifert.Application.theoremA

#print axioms Seifert.Application.tie_le_original
#print axioms Seifert.Application.downward_tie
#print axioms Seifert.Application.FullConclusion
#print axioms Seifert.Application.downward_fullConclusion
#print axioms Seifert.Application.GenusSet
#print axioms Seifert.Application.AreaSet
#print axioms Seifert.Application.genus_downward
#print axioms Seifert.Application.area_downward
#print axioms Seifert.Application.theoremC_genus
#print axioms Seifert.Application.theoremC_area

#print axioms Seifert.Application.StarFour.Adjacent
#print axioms Seifert.Application.StarFour.graph
#print axioms Seifert.Application.StarFour.genus
#print axioms Seifert.Application.StarFour.areaWeight
#print axioms Seifert.Application.StarFour.area
#print axioms Seifert.Application.StarFour.output_data
#print axioms Seifert.Application.StarFour.hasOutputs
#print axioms Seifert.Application.StarFour.positive
#print axioms Seifert.Application.StarFour.connected
#print axioms Seifert.Application.StarFour.values_wellFounded
#print axioms Seifert.Application.StarFour.system
#print axioms Seifert.Application.StarFour.distance_two
#print axioms Seifert.Application.StarFour.distance_two_mixed
#print axioms Seifert.Application.StarFour.area_mechanism
#print axioms Seifert.Application.StarFour.genus_mechanism
#print axioms Seifert.Application.StarFour.values_description
#print axioms Seifert.Application.StarFour.genuine_tie
#print axioms Seifert.Application.StarFour.contractible
#print axioms Seifert.Application.StarFour.genus_zero
#print axioms Seifert.Application.StarFour.area_one
#print axioms Seifert.Application.StarFour.area_top_two
#print axioms Seifert.Application.StarFour.proper_genus_truncation
#print axioms Seifert.Application.StarFour.proper_area_truncation

#print axioms Seifert.Application.DisconnectedTwo.graph
#print axioms Seifert.Application.DisconnectedTwo.genus
#print axioms Seifert.Application.DisconnectedTwo.area
#print axioms Seifert.Application.DisconnectedTwo.positive
#print axioms Seifert.Application.DisconnectedTwo.values_wellFounded
#print axioms Seifert.Application.DisconnectedTwo.hasOutputs
#print axioms Seifert.Application.DisconnectedTwo.not_connected
#print axioms Seifert.Application.DisconnectedTwo.coordinate_dichotomy
#print axioms Seifert.Application.DisconnectedTwo.not_contractible
#print axioms Seifert.Application.DisconnectedTwo.counterexample

#print axioms SeifertApplicationStatement.cliqueComplex
#print axioms SeifertApplicationStatement.WeakRealization
#print axioms SeifertApplicationStatement.closedSimplex
#print axioms SeifertApplicationStatement.fullComplex
#print axioms SeifertApplicationStatement.FullRealization
#print axioms SeifertApplicationStatement.fullClosedSimplex
#print axioms SeifertApplicationStatement.complexity
#print axioms SeifertApplicationStatement.Values
#print axioms SeifertApplicationStatement.EqAdj
#print axioms SeifertApplicationStatement.Outputs
#print axioms SeifertApplicationStatement.SurfaceSystem
#print axioms SeifertApplicationStatement.GenusSet
#print axioms SeifertApplicationStatement.AreaSet
#print axioms SeifertApplicationStatement.FullConclusion
#print axioms SeifertApplicationStatement.TheoremA
#print axioms SeifertApplicationStatement.TheoremC_genus
#print axioms SeifertApplicationStatement.TheoremC_area

#print axioms SeifertApplicationAudit.complexity_eq
#print axioms SeifertApplicationAudit.values_eq
#print axioms SeifertApplicationAudit.outputs_iff
#print axioms SeifertApplicationAudit.surfaceSystem_iff
#print axioms SeifertApplicationAudit.cliqueComplex_eq
#print axioms SeifertApplicationAudit.realization_eq
#print axioms SeifertApplicationAudit.weakTopology_eq
#print axioms SeifertApplicationAudit.realizationHomeomorph
#print axioms SeifertApplicationAudit.fullComplex_eq
#print axioms SeifertApplicationAudit.fullRealization_eq
#print axioms SeifertApplicationAudit.fullWeakTopology_eq
#print axioms SeifertApplicationAudit.fullConclusion_iff
#print axioms SeifertApplicationAudit.genusSet_eq
#print axioms SeifertApplicationAudit.areaSet_eq
#print axioms SeifertApplicationAudit.theoremA_verified
#print axioms SeifertApplicationAudit.theoremC_genus_verified
#print axioms SeifertApplicationAudit.theoremC_area_verified

#print axioms Seifert.Application.PathFive.Adjacent
#print axioms Seifert.Application.PathFive.graph
#print axioms Seifert.Application.PathFive.genus
#print axioms Seifert.Application.PathFive.areaWeight
#print axioms Seifert.Application.PathFive.area
#print axioms Seifert.Application.PathFive.output_data
#print axioms Seifert.Application.PathFive.hasOutputs
#print axioms Seifert.Application.PathFive.positive
#print axioms Seifert.Application.PathFive.connected
#print axioms Seifert.Application.PathFive.values_wellFounded
#print axioms Seifert.Application.PathFive.system
#print axioms Seifert.Application.PathFive.no_cone_vertex
#print axioms Seifert.Application.PathFive.distance_two
#print axioms Seifert.Application.PathFive.distance_two_mixed
#print axioms Seifert.Application.PathFive.area_mechanism
#print axioms Seifert.Application.PathFive.genus_mechanism
#print axioms Seifert.Application.PathFive.contractible
#print axioms Seifert.Application.PathFive.genus_zero
#print axioms Seifert.Application.PathFive.area_one
#print axioms Seifert.Application.PathFive.proper_genus_truncation

#print axioms SeifertApplicationStatement.weakTopology
#print axioms SeifertApplicationStatement.fullWeakTopology
