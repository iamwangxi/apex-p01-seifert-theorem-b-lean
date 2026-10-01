/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.BlockDeformation

/-! Kernel dependency audit for the subcomplex, gluing, and sanity theorems. -/

open Topo.Complex

-- The theorem also handles no blocks at all, with K itself as the fixed target.
example {V : Type*} (K : Topo.Complex V) :
    Nonempty (StrongDeformationRetract (Set.Subset.refl K.faces)) := by
  let C : BlockCover K K (fun _ : Empty ↦ K) :=
    { target_subset := Set.Subset.refl _
      block_subset := fun _ ↦ Set.Subset.refl _
      cover := fun _ hs ↦ Or.inl hs
      overlap := fun i ↦ nomatch i }
  exact C.nonempty_strongDeformationRetract (fun i ↦ nomatch i)

#print Topo.Complex.BlockCover.nonempty_strongDeformationRetract
#print Topo.Complex.BlockCover.contractible_of_nonempty

#print axioms Topo.Complex.isClosedMap_inclusion
#print axioms Topo.Complex.isClosedEmbedding_inclusion
#print axioms Topo.Complex.isClosed_range_inclusion
#print axioms Topo.Complex.isClosed_subcomplex
#print axioms Topo.Complex.StrongDeformationRetract.retraction
#print axioms Topo.Complex.StrongDeformationRetract.homotopyRel
#print axioms Topo.Complex.StrongDeformationRetract.homotopyEquiv
#print axioms Topo.Complex.StrongDeformationRetract.contractible
#print axioms Topo.Complex.BlockCover.glued_on_block
#print axioms Topo.Complex.BlockCover.continuous_gluedHomotopy
#print axioms Topo.Complex.BlockCover.strongDeformationRetract
#print axioms Topo.Complex.BlockCover.nonempty_strongDeformationRetract
#print axioms Topo.Complex.BlockCover.contractible
#print axioms Topo.Complex.BlockCover.contractible_of_nonempty
#print axioms Topo.Complex.strongDeformationRetract_of_coneVertex
#print axioms Topo.InfiniteBlocks.cover
#print axioms Topo.InfiniteBlocks.localDeformation
#print axioms Topo.InfiniteBlocks.strongDeformation
#print axioms Topo.InfiniteBlocks.contractible_bouquet
#print axioms Topo.InfiniteBlocks.triangle_card
#print axioms Topo.InfiniteBlocks.infinite_incident_faces
#print axioms Topo.InfiniteBlocks.infinite_incident_triangles
#print axioms Topo.InfiniteBlocks.not_locallyFinite_blockRanges
#print axioms Topo.InfiniteBlocks.blockRange_eq_triangleRange
#print axioms Topo.InfiniteBlocks.not_locallyFinite_triangleRanges
