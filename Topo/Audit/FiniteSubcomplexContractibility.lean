/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.FiniteSubcomplexContractibility

/-! # Kernel dependency audit of finite-subcomplex contractibility
Includes degenerate finite simplices. -/

#print axioms Topo.Complex.finite_generated
#print axioms Topo.Complex.isClosed_of_support_injOn
#print axioms Topo.Complex.isDiscrete_of_support_injOn
#print axioms Topo.Complex.IsCompact.finite_supports
#print axioms Topo.Complex.IsCompact.exists_finite_subcomplex
#print axioms Topo.SimplexExtension.coneMap_surjective
#print axioms Topo.SimplexExtension.coneMap_fibers
#print axioms Topo.SimplexExtension.exists_extension
#print axioms Topo.Complex.isQuotientMap_boundaryQuotient
#print axioms Topo.Complex.continuous_boundary
#print axioms Topo.Complex.ExtensionStage.exists_next
#print axioms Topo.Complex.exists_continuous_extension
#print axioms Topo.Complex.exists_extension_subcomplex
#print axioms Topo.Complex.FiniteInclusionsNull.nullhomotopic_compact
#print axioms Topo.Complex.FiniteInclusionsNull.exists_extension_subcomplex
#print axioms Topo.Complex.contractible_of_finiteInclusionsNull
#print axioms Topo.Complex.contractible_of_finiteInclusionsNull_of_face
#print axioms Topo.Complex.contractible_of_cofinal_contractible
#print axioms Topo.Complex.finite_subcomplex_subset_stage
#print axioms Topo.Complex.contractible_unionFamily
#print axioms Topo.Complex.contractible_of_directed_union
#print axioms Topo.Complex.contractible_of_increasing_union
#print axioms Topo.Examples.InfiniteSimplex.stage_finite
#print axioms Topo.Examples.InfiniteSimplex.contractible_infiniteSimplex
#print axioms Topo.Examples.InfiniteSimplex.infinite_incident_faces
#print axioms Topo.Examples.InfiniteSimplex.not_locallyFinite_faces

open Topology Convexity in
example {Y : Type*} [TopologicalSpace Y]
    (f : C(Topo.SimplexExtension.boundary (T := Empty), Y)) (hf : f.Nullhomotopic) :
    ∃ g : C(StdSimplex ℝ Empty, Y), ∀ b, g b.1 = f b :=
  Topo.SimplexExtension.exists_extension f hf

open Topology Convexity in
example {Y : Type*} [TopologicalSpace Y]
    (f : C(Topo.SimplexExtension.boundary (T := Unit), Y)) (hf : f.Nullhomotopic) :
    ∃ g : C(StdSimplex ℝ Unit, Y), ∀ b, g b.1 = f b :=
  Topo.SimplexExtension.exists_extension f hf

open Topology Convexity in
example {Y : Type*} [TopologicalSpace Y]
    (f : C(Topo.SimplexExtension.boundary (T := Fin 2), Y)) (hf : f.Nullhomotopic) :
    ∃ g : C(StdSimplex ℝ (Fin 2), Y), ∀ b, g b.1 = f b :=
  Topo.SimplexExtension.exists_extension f hf
