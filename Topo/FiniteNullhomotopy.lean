/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.CompactSubcomplex
import Mathlib.Topology.Homotopy.Contractible

/-! # Nullhomotopies of maps with compact source -/

noncomputable section
open Topology Convexity
namespace Topo.Complex
universe u v w
variable {V : Type u} (K : Topo.Complex V)

/-- Every inclusion of a finite subcomplex is homotopic to a constant map. -/
def FiniteInclusionsNull : Prop :=
  ∀ (F : Topo.Complex V) (hFK : F.faces ⊆ K.faces), F.faces.Finite →
    (⟨inclusion hFK, continuous_inclusion hFK⟩ : C(F.Realization, K.Realization)).Nullhomotopic

/-- Under the finite-inclusion hypothesis every map with compact source is nullhomotopic. -/
theorem FiniteInclusionsNull.nullhomotopic_compact (hK : K.FiniteInclusionsNull)
    {X : Type v} [TopologicalSpace X] [CompactSpace X] (f : C(X, K.Realization)) :
    f.Nullhomotopic := by
  obtain ⟨F, hFK, hF, hcont⟩ := IsCompact.exists_finite_subcomplex K
    (isCompact_range f.continuous)
  have hmem (x : X) : (f x).1.weights.support ∈ F.faces :=
    (mem_range_inclusion hFK (f x)).mp (hcont ⟨x, rfl⟩)
  let g : C(X, F.Realization) := ⟨fun x ↦ ⟨(f x).1, hmem x⟩, by
    exact (isClosedEmbedding_inclusion hFK).isEmbedding.continuous_iff.mpr f.continuous⟩
  exact (hK F hFK hF).comp_left g

/-- Cofinal contractible subcomplexes imply the finite-inclusion hypothesis.
The index type and the family may be arbitrary: directedness is needed only to
establish the stated finite cofinality in applications. -/
theorem finiteInclusionsNull_of_cofinal_contractible {ι : Type w}
    (B : ι → Topo.Complex V) (hBK : ∀ i, (B i).faces ⊆ K.faces)
    (hB : ∀ i, ContractibleSpace (B i).Realization)
    (hcofinal : ∀ F : Topo.Complex V, F.faces ⊆ K.faces → F.faces.Finite →
      ∃ i, F.faces ⊆ (B i).faces) : K.FiniteInclusionsNull := by
  intro F hFK hF
  obtain ⟨i, hFi⟩ := hcofinal F hFK hF
  let := hB i
  let f : C(F.Realization, (B i).Realization) := ⟨inclusion hFi, continuous_inclusion hFi⟩
  let g : C((B i).Realization, K.Realization) :=
    ⟨inclusion (hBK i), continuous_inclusion (hBK i)⟩
  exact ((id_nullhomotopic (B i).Realization).comp_left f).comp_right g

end Topo.Complex
