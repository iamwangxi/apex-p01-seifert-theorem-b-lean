/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.Subcomplex
import Mathlib.Topology.Homotopy.Contractible

/-! # Strong deformation retractions onto subcomplexes -/

noncomputable section

open Topology Convexity ContinuousMap

namespace Topo.Complex

universe u
variable {V : Type u} {L K : Topo.Complex V}

/-- A spatial-variable-first strong deformation retraction. The target at time
one lies in `L`, and every point of `L` is fixed throughout the deformation. -/
structure StrongDeformationRetract (hLK : L.faces ⊆ K.faces) where
  homotopy : K.Realization × unitInterval → K.Realization
  continuous : Continuous homotopy
  at_zero : ∀ x, homotopy (x, 0) = x
  at_one : ∀ x, (homotopy (x, 1)).1.weights.support ∈ L.faces
  fixed : ∀ (x : L.Realization) t, homotopy (inclusion hLK x, t) = inclusion hLK x

/-- The natural inclusion, as a bundled continuous map. -/
def inclusionMap (hLK : L.faces ⊆ K.faces) : C(L.Realization, K.Realization) :=
  ⟨inclusion hLK, continuous_inclusion hLK⟩

namespace StrongDeformationRetract

variable {hLK : L.faces ⊆ K.faces} (D : StrongDeformationRetract hLK)

theorem fixed_of_mem (x : K.Realization) (hx : x.1.weights.support ∈ L.faces)
    (t : unitInterval) : D.homotopy (x, t) = x :=
  D.fixed ⟨x.1, hx⟩ t

/-- The endpoint, corestricted to the target with its own weak topology. -/
def retraction : C(K.Realization, L.Realization) where
  toFun x := ⟨(D.homotopy (x, 1)).1, D.at_one x⟩
  continuous_toFun := by
    apply (isClosedEmbedding_inclusion hLK).isEmbedding.continuous_iff.mpr
    exact D.continuous.comp (continuous_id.prodMk continuous_const)

@[simp] theorem inclusion_retraction (x : K.Realization) :
    inclusion hLK (D.retraction x) = D.homotopy (x, 1) := rfl

@[simp] theorem retraction_inclusion (x : L.Realization) :
    D.retraction (inclusion hLK x) = x := by
  apply inclusion_injective hLK
  exact D.fixed x 1

/-- A Mathlib homotopy relative to the whole image of `L`. -/
def homotopyRel :
    (ContinuousMap.id K.Realization).HomotopyRel
      ((inclusionMap hLK).comp D.retraction) (Set.range (inclusion hLK)) where
  toFun p := D.homotopy (p.2, p.1)
  continuous_toFun := D.continuous.comp continuous_swap
  map_zero_left := D.at_zero
  map_one_left _ := rfl
  prop' t x hx := D.fixed_of_mem x ((mem_range_inclusion hLK x).mp hx) t

/-- A strong deformation retraction gives an actual Mathlib homotopy equivalence. -/
def homotopyEquiv : K.Realization ≃ₕ L.Realization where
  toFun := D.retraction
  invFun := inclusionMap hLK
  left_inv := ⟨D.homotopyRel.toHomotopy.symm⟩
  right_inv := by
    have h : D.retraction.comp (inclusionMap hLK) = ContinuousMap.id L.Realization := by
      ext x
      exact D.retraction_inclusion x
    rw [h]

include D in
theorem contractible [ContractibleSpace L.Realization] : ContractibleSpace K.Realization :=
  ContinuousMap.HomotopyEquiv.contractibleSpace (homotopyEquiv D)

end StrongDeformationRetract
end Topo.Complex
