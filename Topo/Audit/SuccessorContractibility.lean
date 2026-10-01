/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.SuccessorContractibility

/-! Kernel dependency audit for the relative cone and successor step. -/

noncomputable section

#print axioms Topo.Complex.isQuotientMap_coneCylinder
#print axioms Topo.Complex.coneCylinder_fibre
#print axioms Topo.ConeParameters.continuous_resolved
#print axioms Topo.Complex.RelativeCone.continuous_cylinderHomotopy
#print axioms Topo.Complex.RelativeCone.continuous_homotopy
#print axioms Topo.Complex.RelativeCone.strongDeformationRetract
#print axioms Topo.Complex.nonempty_strongDeformationRetract_coneAt
#print axioms Topo.Complex.strongDeformationRetract_coneAt
#print axioms Topo.Complex.coneBaseHomeomorph
#print axioms Topo.Complex.coneBase_coneAt
#print axioms Topo.Complex.nonempty_strongDeformationRetract_cone
#print axioms Topo.Complex.strongDeformationRetract_cone
#print axioms Topo.Complex.homotopyEquiv_cone_base
#print axioms Topo.Complex.coneAt_inter_faces
#print axioms Topo.Complex.strongDeformationRetract_attachCone
#print axioms Topo.Complex.nonempty_strongDeformationRetract_attachCone
#print axioms Topo.Complex.homotopyEquiv_attachCone
#print axioms Topo.Complex.contractible_attachCone
#print axioms Topo.Complex.newVertexAttachment_eq_union
#print axioms Topo.Complex.strongDeformationRetract_newVertexAttachment
#print axioms Topo.Complex.homotopyEquiv_newVertexAttachment
#print axioms Topo.Complex.contractible_newVertexAttachment
#print axioms Topo.Complex.IsFlag.full
#print axioms Topo.Complex.descendingLink_eq_full_link
#print axioms Topo.Complex.sublevel_eq_attachCone
#print axioms Topo.Complex.sublevel_cone_inter
#print axioms Topo.Complex.nonempty_strongDeformationRetract_sublevel
#print axioms Topo.Complex.contractible_sublevel
#print axioms Topo.Complex.contractible_of_largest_vertex
#print axioms Topo.Examples.ConeAttachment.path_no_cone_vertex
#print axioms Topo.Examples.ConeAttachment.successorDeformation
#print axioms Topo.Examples.ConeAttachment.successor_contractible
#print axioms Topo.Examples.ConeAttachment.nonvacuous

-- Contractibility supplies a point; the nonempty-base hypothesis is enforced.
example {V : Type*} (L : Topo.Complex V) [ContractibleSpace L.Realization] :
    Nonempty L.Realization := by
  obtain ⟨c, _⟩ := id_nullhomotopic L.Realization
  exact ⟨c⟩

-- Task 1 has no restriction on the original vertex universe or face family.
example {V : Type*} (L : Topo.Complex V) [ContractibleSpace L.Realization] :
    Topo.Complex.StrongDeformationRetract L.coneBase_subset_cone :=
  L.strongDeformationRetract_cone

-- Task 2 can always add a new vertex by changing the ambient type to `Option V`.
example {V : Type*} (X L : Topo.Complex V) (hLX : L.faces ⊆ X.faces)
    [ContractibleSpace L.Realization] [ContractibleSpace X.Realization] :
    ContractibleSpace (X.newVertexAttachment L).Realization :=
  X.contractible_newVertexAttachment L hLX
