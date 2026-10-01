/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.Cone
import Topo.StrongDeformation

/-! # Cone contractions as strong deformation retractions -/

noncomputable section

open Topology Convexity

namespace Topo.Complex

universe u
variable {V : Type u}

/-- All subfaces of a specified finite simplex. -/
def simplexOn (s : Finset V) : Topo.Complex V where
  faces := {t | t ⊆ s}
  empty_mem := Finset.empty_subset s
  downward hst ht := hst.trans ht

@[simp] theorem mem_simplexOn (s t : Finset V) :
    t ∈ (simplexOn s).faces ↔ t ⊆ s := Iff.rfl

/-- The one-vertex subcomplex, including its empty face. -/
def pointComplex (a : V) : Topo.Complex V := simplexOn {a}

@[simp] theorem mem_pointComplex (a : V) (s : Finset V) :
    s ∈ (pointComplex a).faces ↔ s ⊆ {a} := Iff.rfl

theorem eq_single_of_support_subset (w : StdSimplex ℝ V) (a : V)
    (hw : w.weights.support ⊆ {a}) : w = .single a := by
  classical
  exact StdSimplex.support_weights_eq_singleton.mp
    (w.support_weights_nonempty.subset_singleton_iff.mp hw)

theorem pointRealization_eq (a : V) (x : (pointComplex a).Realization) :
    x.1 = StdSimplex.single a := eq_single_of_support_subset x.1 a x.2

instance pointRealizationSubsingleton (a : V) : Subsingleton (pointComplex a).Realization where
  allEq x y := Subtype.ext ((pointRealization_eq a x).trans (pointRealization_eq a y).symm)

instance pointRealizationNonempty (a : V) : Nonempty (pointComplex a).Realization :=
  ⟨(pointComplex a).vertex a (Finset.Subset.refl _)⟩

/-- The explicit cone contraction is strong relative to any subcomplex whose
realization is precisely the apex. This also applies to block/target intersections. -/
def strongDeformationRetract_of_coneVertex {K L : Topo.Complex V}
    (hLK : L.faces ⊆ K.faces) {a : V} (ha : K.IsConeVertex a)
    (hLa : {a} ∈ L.faces) (hL : ∀ s ∈ L.faces, s ⊆ {a}) :
    StrongDeformationRetract hLK where
  homotopy := K.contraction ha
  continuous := K.continuous_contraction ha
  at_zero := K.contraction_zero ha
  at_one x := by simpa [vertex] using hLa
  fixed x t := by
    apply Subtype.ext
    change line x.1 a t = x.1
    rw [eq_single_of_support_subset x.1 a (hL _ x.2), line_vertex]

end Topo.Complex
