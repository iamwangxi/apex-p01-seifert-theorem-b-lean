/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.Cone

/-! Kernel dependency audit and two extreme-case specialization checks. -/

open Topo.Complex

-- An empty base still has a one-point, hence contractible, cone.
example : ContractibleSpace
    (ofPreAbstract (⊥ : PreAbstractSimplicialComplex Empty)).cone.Realization :=
  inferInstance

-- No finite-vertex or local-finiteness assumption: all nonempty finite subsets of ℕ.
example : ContractibleSpace
    (ofPreAbstract (⊤ : PreAbstractSimplicialComplex ℕ)).cone.Realization :=
  inferInstance

#print axioms Topo.Complex.support_mem_ofPreAbstract
#print axioms Topo.Complex.isOpen_iff
#print axioms Topo.Complex.isClosed_iff
#print axioms Topo.Complex.continuous_iff
#print axioms Topo.Complex.isEmbedding_faceInclusion
#print axioms Topo.Complex.isClosedEmbedding_faceInclusion
#print axioms Topo.Complex.realizationT2Space
#print axioms Topo.Complex.isQuotientMap_faceQuotient
#print axioms Topo.Complex.continuous_prod_iff
#print axioms Topo.Complex.contraction_weights
#print axioms Topo.Complex.continuous_contraction
#print axioms Topo.Complex.contraction_zero
#print axioms Topo.Complex.contraction_one
#print axioms Topo.Complex.contraction_vertex
#print axioms Topo.Complex.contractible_of_coneVertex
#print axioms Topo.Complex.cone_isConeVertex
#print axioms Topo.Complex.contractible_cone
#print axioms Topo.Complex.contractible_cone_of_abstract
