/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.FiniteNullhomotopy
import Topo.SkeletalExtension
import Topo.RealizationMap

/-! # Finite subcomplex inclusions being nullhomotopic imply contractibility

The identity extends across the simplicial cone by skeletal induction. Its extension
is a left inverse to the base map. Composing with the explicit cone contraction
produces a nullhomotopy of the identity, without a Whitehead theorem.
-/

noncomputable section
open Topology Convexity
namespace Topo.Complex
universe u v w
variable {V : Type u} (K : Topo.Complex V)

/-- The finite-inclusion hypothesis gives a genuine extension theorem for all subcomplexes. -/
theorem FiniteInclusionsNull.exists_extension_subcomplex (hK : K.FiniteInclusionsNull)
    {W : Type v} (D A : Topo.Complex W) (hAD : A.faces ⊆ D.faces)
    (fA : C(A.Realization, K.Realization)) (y₀ : K.Realization) :
    ∃ f : C(D.Realization, K.Realization),
      f.comp ⟨inclusion hAD, continuous_inclusion hAD⟩ = fA := by
  apply Topo.Complex.exists_extension_subcomplex D A hAD fA y₀
  intro s f
  exact SimplexExtension.exists_extension f (hK.nullhomotopic_compact K f)

/-- Finite-subcomplex contractibility theorem for arbitrary weak realizations,
including complexes that are not locally finite. -/
theorem contractible_of_finiteInclusionsNull (hNE : Nonempty K.Realization)
    (hK : K.FiniteInclusionsNull) : ContractibleSpace K.Realization := by
  classical
  obtain ⟨x₀⟩ := hNE
  obtain ⟨a, _⟩ := x₀.1.support_weights_nonempty
  let fA : C(K.coneBase.Realization, K.Realization) :=
    ⟨K.fromConeBase a, K.continuous_fromConeBase a⟩
  obtain ⟨r, hr⟩ := hK.exists_extension_subcomplex K K.cone K.coneBase
    K.coneBase_subset fA x₀
  let b : C(K.Realization, K.cone.Realization) := ⟨K.intoCone, K.continuous_intoCone⟩
  have hretract : r.comp b = ContinuousMap.id K.Realization := by
    ext x
    have he := congrArg (fun f : C(K.coneBase.Realization, K.Realization) ↦ f (K.intoConeBase x)) hr
    change r (K.intoCone x) = K.fromConeBase a (K.intoConeBase x) at he
    exact he.trans (K.fromConeBase_intoConeBase a x)
  have hnull : (r.comp b).Nullhomotopic :=
    ((id_nullhomotopic K.cone.Realization).comp_left b).comp_right r
  rw [hretract] at hnull
  exact (contractible_iff_id_nullhomotopic K.Realization).mpr hnull

/-- A nonempty face is an equivalent convenient nonemptiness hypothesis. -/
theorem contractible_of_finiteInclusionsNull_of_face
    (hNE : ∃ s ∈ K.faces, s.Nonempty) (hK : K.FiniteInclusionsNull) :
    ContractibleSpace K.Realization := by
  obtain ⟨s, hs, a, ha⟩ := hNE
  exact K.contractible_of_finiteInclusionsNull
    ⟨K.vertex a (K.downward (Finset.singleton_subset_iff.mpr ha) hs)⟩ hK

/-- Theorem B's limit step: a cofinal family of contractible subcomplexes has contractible union.
No ordering or countability restriction on the indexing type is needed. -/
theorem contractible_of_cofinal_contractible {ι : Type w}
    (B : ι → Topo.Complex V) (hBK : ∀ i, (B i).faces ⊆ K.faces)
    (hB : ∀ i, ContractibleSpace (B i).Realization)
    (hcofinal : ∀ F : Topo.Complex V, F.faces ⊆ K.faces → F.faces.Finite →
      ∃ i, F.faces ⊆ (B i).faces) : ContractibleSpace K.Realization := by
  classical
  obtain ⟨i, _⟩ := hcofinal (K.generated ∅) (K.generated_subset ∅) (K.finite_generated ∅)
  let : ContractibleSpace (B i).Realization := hB i
  obtain ⟨x⟩ := (inferInstance : Nonempty (B i).Realization)
  exact K.contractible_of_finiteInclusionsNull ⟨inclusion (hBK i) x⟩
    (K.finiteInclusionsNull_of_cofinal_contractible B hBK hB hcofinal)

end Topo.Complex
