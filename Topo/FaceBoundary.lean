/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.Subcomplex
import Topo.SimplexExtension

/-! # Face coordinates and continuity on a simplex boundary -/

noncomputable section
open Topology Convexity
namespace Topo.Complex
universe u v
variable {V : Type u} (K : Topo.Complex V)

def supportFace (x : K.Realization) : K.Face := ⟨x.1.weights.support, x.2⟩

def faceLift (s : K.Face) (x : K.Realization) (hx : x.1.weights.support ⊆ s.1) :
    StdSimplex ℝ s.1 := ((K.mem_range_faceInclusion s x).mpr hx).choose

@[simp] theorem faceInclusion_faceLift (s : K.Face) (x : K.Realization)
    (hx : x.1.weights.support ⊆ s.1) : K.faceInclusion s (K.faceLift s x hx) = x :=
  ((K.mem_range_faceInclusion s x).mpr hx).choose_spec

theorem faceLift_faceInclusion (s : K.Face) (w : StdSimplex ℝ s.1)
    (hx : (K.faceInclusion s w).1.weights.support ⊆ s.1) :
    K.faceLift s (K.faceInclusion s w) hx = w :=
  (K.isEmbedding_faceInclusion s).injective (K.faceInclusion_faceLift s _ hx)

theorem eval_supportFace {Y : Type v} (e : ∀ s : K.Face, StdSimplex ℝ s.1 → Y)
    (x : K.Realization) (s : K.Face) (w : StdSimplex ℝ s.1)
    (hs : K.supportFace x = s) (hw : K.faceInclusion s w = x) :
    e (K.supportFace x) (K.faceLift (K.supportFace x) x (Finset.Subset.refl _)) = e s w := by
  subst s
  congr 1
  exact (K.isEmbedding_faceInclusion (K.supportFace x)).injective
    ((K.faceInclusion_faceLift _ _ _).trans hw.symm)

def faceMap {t s : K.Face} (hts : t.1 ⊆ s.1) (w : StdSimplex ℝ t.1) :
    StdSimplex ℝ s.1 := w.map (fun v ↦ (⟨v.1, hts v.2⟩ : s.1))

@[fun_prop] theorem continuous_faceMap {t s : K.Face} (hts : t.1 ⊆ s.1) :
    Continuous (K.faceMap hts) := StdSimplex.continuous_map ℝ _

@[simp] theorem faceInclusion_faceMap {t s : K.Face} (hts : t.1 ⊆ s.1)
    (w : StdSimplex ℝ t.1) : K.faceInclusion s (K.faceMap hts w) = K.faceInclusion t w := by
  apply Subtype.ext
  exact StdSimplex.map_map _ _ _

theorem faceInclusion_weights (s : K.Face) (w : StdSimplex ℝ s.1) (v : s.1) :
    (K.faceInclusion s w).1.weights v.1 = w.weights v :=
  Finsupp.mapDomain_apply_of_injective Subtype.val_injective w.weights v

/-- Being on the Euclidean simplex boundary means having proper ambient support. -/
theorem mem_boundary_iff (s : K.Face) (w : StdSimplex ℝ s.1) :
    w ∈ SimplexExtension.boundary ↔ (K.faceInclusion s w).1.weights.support ⊂ s.1 := by
  classical
  rw [Finset.ssubset_iff_subset_ne]
  have hsub := support_map_val_subset s.1 w
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨hsub, ?_⟩
    intro he
    have hm : v.1 ∈ (K.faceInclusion s w).1.weights.support := he.symm ▸ v.2
    exact Finsupp.mem_support_iff.mp hm ((K.faceInclusion_weights s w v).trans hv)
  · rintro ⟨_, hn⟩
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hn⟩)
    obtain ⟨v, hvs, hvw⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨⟨v, hvs⟩, ?_⟩
    rw [← K.faceInclusion_weights s w ⟨v, hvs⟩]
    exact Finsupp.notMem_support_iff.mp hvw

def boundaryFaceMap (s : K.Face) (t : {t : K.Face // t.1 ⊂ s.1})
    (w : StdSimplex ℝ t.1.1) : SimplexExtension.boundary (T := s.1) :=
  ⟨K.faceMap t.2.le w, (K.mem_boundary_iff s _).mpr (by
    rw [K.faceInclusion_faceMap]
    exact (support_map_val_subset _ _).trans_ssubset t.2)⟩

@[fun_prop] theorem continuous_boundaryFaceMap (s : K.Face)
    (t : {t : K.Face // t.1 ⊂ s.1}) : Continuous (K.boundaryFaceMap s t) :=
  (K.continuous_faceMap t.2.le).subtype_mk _

def boundaryQuotient (s : K.Face) :
    (Σ t : {t : K.Face // t.1 ⊂ s.1}, StdSimplex ℝ t.1.1) →
      SimplexExtension.boundary (T := s.1) := fun p ↦ K.boundaryFaceMap s p.1 p.2

theorem boundaryQuotient_surjective (s : K.Face) :
    Function.Surjective (K.boundaryQuotient s) := by
  intro b
  let x := K.faceInclusion s b.1
  let t : {t : K.Face // t.1 ⊂ s.1} :=
    ⟨K.supportFace x, (K.mem_boundary_iff s b.1).mp b.2⟩
  let w := K.faceLift t.1 x (Finset.Subset.refl _)
  refine ⟨⟨t, w⟩, ?_⟩
  apply Subtype.ext
  apply (K.isEmbedding_faceInclusion s).injective
  change K.faceInclusion s (K.faceMap t.2.le w) = x
  rw [K.faceInclusion_faceMap]
  exact K.faceInclusion_faceLift _ _ _

theorem isQuotientMap_boundaryQuotient (s : K.Face) :
    IsQuotientMap (K.boundaryQuotient s) := by
  have hf : Set.Finite {t : K.Face | t.1 ⊂ s.1} :=
    (finite_faces_subset K s.1).subset (fun t ht ↦ (show t.1 ⊂ s.1 from ht).le)
  let : Finite {t : K.Face // t.1 ⊂ s.1} := hf.to_subtype
  exact .of_surjective_continuous (K.boundaryQuotient_surjective s)
    (continuous_sigma (K.continuous_boundaryFaceMap s))

/-- Continuity of a boundary map follows from continuity on all proper faces. -/
theorem continuous_boundary {Y : Type v} [TopologicalSpace Y] (s : K.Face)
    (f : K.Realization → Y)
    (hf : ∀ t : K.Face, t.1 ⊂ s.1 → Continuous (f ∘ K.faceInclusion t)) :
    Continuous (fun b : SimplexExtension.boundary (T := s.1) ↦ f (K.faceInclusion s b.1)) := by
  apply (K.isQuotientMap_boundaryQuotient s).continuous_iff.mpr
  apply continuous_sigma
  intro t
  have he : (fun w : StdSimplex ℝ t.1.1 ↦
      f (K.faceInclusion s (K.boundaryFaceMap s t w).1)) = f ∘ K.faceInclusion t.1 := by
    funext w
    simp only [boundaryFaceMap, K.faceInclusion_faceMap, Function.comp_apply]
  exact he ▸ hf t.1 t.2

end Topo.Complex
