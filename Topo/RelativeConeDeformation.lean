/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.ConeCylinder
import Topo.ConeParameters

/-! Strong deformation of a cone onto its contractible, nonempty base. -/

noncomputable section
open Topology Convexity ContinuousMap

namespace Topo.Complex
universe u
variable {V : Type u} {L : Topo.Complex V} {a : V}
open Topo.ConeParameters

namespace RelativeCone

variable (c : L.Realization)
variable (h : (ContinuousMap.id L.Realization).Homotopy
  (ContinuousMap.const L.Realization c))

/-- Relative formula on the cylinder. The contraction need not fix its endpoint. -/
def cylinderHomotopy (p : L.Realization × (unitInterval × unitInterval)) :
    (L.coneAt a).Realization :=
  L.coneCylinder a (h (parameter p.2.1 p.2.2, p.1), height p.2.1 p.2.2)

theorem cylinder_top (x : L.Realization) (t : unitInterval) :
    cylinderHomotopy c h (x, 1, t) = L.coneCylinder a (c, height 1 t) := by
  by_cases ht : t = 0
  · subst t
    simp [cylinderHomotopy]
  · simp [cylinderHomotopy, parameter_one_left ht]

theorem continuous_cylinderHomotopy : Continuous (cylinderHomotopy c h (a := a)) := by
  rw [L.continuous_prod_iff]
  intro s
  let : T2Space (StdSimplex ℝ s.1) :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ s.1).t2Space
  let Q : StdSimplex ℝ s.1 × (unitInterval × unitInterval) → (L.coneAt a).Realization :=
    fun p ↦ L.coneCylinder a (h (p.2.1, L.faceInclusion s p.1), p.2.2)
  have hQ : Continuous Q := (L.continuous_coneCylinder a).comp
    ((h.continuous.comp ((continuous_fst.comp continuous_snd).prodMk
      ((L.continuous_faceInclusion s).comp continuous_fst))).prodMk
        (continuous_snd.comp continuous_snd))
  exact continuous_resolved Q hQ ((L.coneAt a).vertex a
    (L.coneAt_isConeVertex a).singleton_mem) (fun x r ↦ L.coneCylinder_one a _)

variable [Nonempty L.Realization]

def representative (x : (L.coneAt a).Realization) : L.Realization × unitInterval :=
  Classical.choose (L.coneCylinder_surjective a x)

theorem representative_spec (x : (L.coneAt a).Realization) :
    L.coneCylinder a (representative x) = x :=
  Classical.choose_spec (L.coneCylinder_surjective a x)

/-- Descend the relative cylinder homotopy through its collapsed top. -/
def homotopy (p : (L.coneAt a).Realization × unitInterval) : (L.coneAt a).Realization :=
  cylinderHomotopy c h ((representative p.1).1, (representative p.1).2, p.2)

theorem on_cylinder (ha : L.Fresh a) (x : L.Realization) (s t : unitInterval) :
    homotopy c h (L.coneCylinder a (x, s), t) = cylinderHomotopy c h (x, s, t) := by
  let r := representative (L.coneCylinder a (x, s))
  have hf := coneCylinder_fibre ha (representative_spec (L.coneCylinder a (x, s)))
  change r.2 = s ∧ (r.2 = 1 ∨ r.1 = x) at hf
  change cylinderHomotopy c h (r.1, r.2, t) = _
  rw [hf.1]
  rcases hf.2 with hr | hr
  · have hs : s = 1 := hf.1.symm.trans hr
    rw [hs, cylinder_top, cylinder_top]
  · rw [hr]

theorem continuous_homotopy (ha : L.Fresh a) : Continuous (homotopy c h (a := a)) := by
  apply (L.isQuotientMap_coneCylinder a).continuous_lift_prod_left
  have he : (fun p : (L.Realization × unitInterval) × unitInterval ↦
      homotopy c h (L.coneCylinder a p.1, p.2)) =
      (fun p ↦ cylinderHomotopy c h (p.1.1, p.1.2, p.2)) := by
    funext p
    exact on_cylinder c h ha _ _ _
  rw [he]
  exact (continuous_cylinderHomotopy c h).comp
    ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd))

theorem at_zero (x : (L.coneAt a).Realization) : homotopy c h (x, 0) = x := by
  simp only [homotopy, cylinderHomotopy, parameter_zero_right, height_zero_right,
    Homotopy.apply_zero, ContinuousMap.id_apply]
  exact representative_spec x

theorem at_one (x : (L.coneAt a).Realization) :
    (homotopy c h (x, 1)).1.weights.support ∈ L.faces := by
  simp only [homotopy, cylinderHomotopy, parameter_one_right, height_one_right,
    coneCylinder_zero, inclusion_val]
  exact (h ((representative x).2, (representative x).1)).2

theorem fixed (ha : L.Fresh a) (x : L.Realization) (t : unitInterval) :
    homotopy c h (inclusion (L.subset_coneAt a) x, t) =
      inclusion (L.subset_coneAt a) x := by
  rw [← L.coneCylinder_zero a x, on_cylinder c h ha]
  simp [cylinderHomotopy]

def strongDeformationRetract (ha : L.Fresh a) :
    StrongDeformationRetract (L.subset_coneAt a) where
  homotopy := homotopy c h
  continuous := continuous_homotopy c h ha
  at_zero := at_zero c h
  at_one := at_one c h
  fixed := fixed c h ha

end RelativeCone

/-- The relative cone theorem: any contraction of the base suffices. -/
theorem nonempty_strongDeformationRetract_coneAt (L : Topo.Complex V) (a : V)
    (ha : L.Fresh a) [ContractibleSpace L.Realization] :
    Nonempty (StrongDeformationRetract (L.subset_coneAt a)) := by
  obtain ⟨c, ⟨h⟩⟩ := id_nullhomotopic L.Realization
  let : Nonempty L.Realization := ⟨c⟩
  exact ⟨RelativeCone.strongDeformationRetract c h ha⟩

def strongDeformationRetract_coneAt (L : Topo.Complex V) (a : V)
    (ha : L.Fresh a) [ContractibleSpace L.Realization] :
    StrongDeformationRetract (L.subset_coneAt a) :=
  Classical.choice (L.nonempty_strongDeformationRetract_coneAt a ha)

end Topo.Complex
