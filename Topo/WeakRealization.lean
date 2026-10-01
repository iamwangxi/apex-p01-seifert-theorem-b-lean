/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Geometry.Convex.ConvexSpace.Topology
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.UnitInterval

/-!
# The weak geometric realization of an abstract simplicial complex

We include the empty face in the combinatorial convention. It contributes an empty
standard simplex, so it does not change the realization. The topology is defined
directly as the final topology of all finite closed faces.
-/

noncomputable section

open Topology Convexity

namespace Topo

universe u

/-- An abstract simplicial complex, with the empty face included. Vertices need
not all be used; neither finiteness nor local finiteness is required. -/
structure Complex (V : Type u) where
  faces : Set (Finset V)
  empty_mem : ∅ ∈ faces
  downward : ∀ {s t}, s ⊆ t → t ∈ faces → s ∈ faces

namespace Complex

variable {V : Type u}

/-- Translate Mathlib's convention of nonempty faces to ours. -/
def ofPreAbstract (K : PreAbstractSimplicialComplex V) : Complex V where
  faces := {s | s = ∅ ∨ s ∈ K.faces}
  empty_mem := Or.inl rfl
  downward := by
    intro s t hst ht
    rcases ht with rfl | ht
    · exact Or.inl (Finset.subset_empty.mp hst)
    · by_cases hs : s = ∅
      · exact Or.inl hs
      · exact Or.inr ((K.isRelLowerSet_faces ht).2 hst (Finset.nonempty_iff_ne_empty.mpr hs))

/-- Adding the empty face makes no difference to the allowed barycentric points. -/
@[simp]
theorem support_mem_ofPreAbstract (K : PreAbstractSimplicialComplex V) (w : StdSimplex ℝ V) :
    w.weights.support ∈ (ofPreAbstract K).faces ↔ w.weights.support ∈ K.faces := by
  change w.weights.support = ∅ ∨ w.weights.support ∈ K.faces ↔ _
  simp [w.support_weights_nonempty.ne_empty]

abbrev Face (K : Complex V) := {s : Finset V // s ∈ K.faces}

/-- Finitely supported nonnegative weights of total mass one, whose support is a face.
The topology is supplied separately below, rather than inherited from a coordinate space. -/
def Realization (K : Complex V) := {w : StdSimplex ℝ V // w.weights.support ∈ K.faces}

variable (K : Complex V)

lemma support_map_val_subset (s : Finset V) (w : StdSimplex ℝ s) :
    (w.map (Subtype.val : s → V)).weights.support ⊆ s := by
  classical
  intro v hv
  by_contra hvs
  have hz : (w.map (Subtype.val : s → V)).weights v = 0 :=
    Finsupp.mapDomain_of_notMem_range w.weights v (by simpa using hvs)
  exact (Finsupp.mem_support_iff.mp hv) hz

/-- The inclusion of the closed simplex with vertex set `s`. Its source has the
usual finite-dimensional Euclidean simplex topology. -/
def faceInclusion (s : K.Face) (w : StdSimplex ℝ s.1) : K.Realization :=
  ⟨w.map Subtype.val, K.downward (support_map_val_subset s.1 w) s.2⟩

/-- The weak (final) topology relative to all closed simplices of the complex. -/
instance realizationTopology : TopologicalSpace K.Realization :=
  ⨆ s : K.Face, TopologicalSpace.coinduced (K.faceInclusion s) inferInstance

theorem continuous_iff {Y : Type*} [TopologicalSpace Y] (f : K.Realization → Y) :
    Continuous f ↔ ∀ s : K.Face, Continuous (f ∘ K.faceInclusion s) := by
  change Continuous[⨆ s : K.Face, TopologicalSpace.coinduced
    (K.faceInclusion s) inferInstance, _] f ↔ _
  rw [continuous_iSup_dom]
  exact forall_congr' fun s ↦ continuous_coinduced_dom

theorem isOpen_iff (A : Set K.Realization) :
    IsOpen A ↔ ∀ s : K.Face, IsOpen (K.faceInclusion s ⁻¹' A) := by
  change IsOpen[⨆ s : K.Face, TopologicalSpace.coinduced
    (K.faceInclusion s) inferInstance] A ↔ _
  simp only [isOpen_iSup_iff, isOpen_coinduced]

theorem isClosed_iff (A : Set K.Realization) :
    IsClosed A ↔ ∀ s : K.Face, IsClosed (K.faceInclusion s ⁻¹' A) := by
  rw [← isOpen_compl_iff, K.isOpen_iff]
  simp only [Set.preimage_compl, isOpen_compl_iff]

@[fun_prop]
theorem continuous_faceInclusion (s : K.Face) : Continuous (K.faceInclusion s) := by
  rw [continuous_iff_coinduced_le]
  exact le_iSup (fun s : K.Face ↦ TopologicalSpace.coinduced
    (K.faceInclusion s) inferInstance) s

@[fun_prop]
theorem continuous_coordinate (v : V) :
    Continuous (fun x : K.Realization ↦ x.1.weights v) := by
  rw [K.continuous_iff]
  intro s
  exact (StdSimplex.continuous_weights_apply ℝ v).comp
    (StdSimplex.continuous_map ℝ (Subtype.val : s.1 → V))

theorem isEmbedding_faceInclusion (s : K.Face) : IsEmbedding (K.faceInclusion s) := by
  let c : K.Realization → s.1 → ℝ := fun x v ↦ x.1.weights v.1
  have hc : Continuous c := continuous_pi fun v ↦ K.continuous_coordinate v.1
  have he : IsEmbedding (c ∘ K.faceInclusion s) := by
    have h : c ∘ K.faceInclusion s =
        (fun w : StdSimplex ℝ s.1 ↦ (w.weights : s.1 → ℝ)) := by
      funext w v
      exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective w.weights v
    rw [h]
    exact StdSimplex.isEmbedding_toFun_comp_weights ℝ s.1
  exact IsEmbedding.of_comp (K.continuous_faceInclusion s) hc he

theorem mem_range_faceInclusion (s : K.Face) (x : K.Realization) :
    x ∈ Set.range (K.faceInclusion s) ↔ x.1.weights.support ⊆ s.1 := by
  constructor
  · rintro ⟨w, rfl⟩
    exact support_map_val_subset s.1 w
  · intro hx
    obtain ⟨w, hw⟩ := (StdSimplex.mem_range_map_iff (Subtype.val : s.1 → V) x.1).2 (by
      intro v hv
      exact Finsupp.notMem_support_iff.mp (fun h ↦ hv (by simpa using hx h)))
    exact ⟨w, Subtype.ext hw⟩

theorem isClosedEmbedding_faceInclusion (s : K.Face) :
    IsClosedEmbedding (K.faceInclusion s) where
  toIsEmbedding := K.isEmbedding_faceInclusion s
  isClosed_range := by
    have h : Set.range (K.faceInclusion s) =
        ⋂ (v : V) (_ : v ∉ s.1), {x : K.Realization | x.1.weights v = 0} := by
      ext x
      rw [K.mem_range_faceInclusion]
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · intro hx v hv
        exact Finsupp.notMem_support_iff.mp (fun h ↦ hv (hx h))
      · intro hx v hv
        by_contra hn
        exact Finsupp.mem_support_iff.mp hv (hx v hn)
    rw [h]
    exact isClosed_iInter fun v ↦ isClosed_iInter fun _ ↦
      isClosed_eq (K.continuous_coordinate v) continuous_const

instance realizationT2Space : T2Space K.Realization := by
  apply T2Space.of_injective_continuous
    (f := fun x : K.Realization ↦ (x.1.weights : V → ℝ))
  · intro x y h
    apply Subtype.ext
    apply StdSimplex.ext
    ext v
    exact congr_fun h v
  · exact continuous_pi fun v ↦ K.continuous_coordinate v

/-- The disjoint union of all closed simplices maps onto the realization. -/
def faceQuotient : (Σ s : K.Face, StdSimplex ℝ s.1) → K.Realization :=
  fun p ↦ K.faceInclusion p.1 p.2

theorem faceQuotient_surjective : Function.Surjective K.faceQuotient := by
  intro x
  let s : K.Face := ⟨x.1.weights.support, x.2⟩
  obtain ⟨w, hw⟩ := (StdSimplex.mem_range_map_iff (Subtype.val : s.1 → V) x.1).2 (by
    intro v hv
    exact Finsupp.notMem_support_iff.mp (by simpa [s] using hv))
  refine ⟨⟨s, w⟩, ?_⟩
  exact Subtype.ext hw

theorem isQuotientMap_faceQuotient : IsQuotientMap K.faceQuotient where
  eq_coinduced := by
    change (⨆ s : K.Face, TopologicalSpace.coinduced (K.faceInclusion s) _) =
      TopologicalSpace.coinduced K.faceQuotient
        (⨆ s : K.Face, TopologicalSpace.coinduced (Sigma.mk s) _)
    rw [coinduced_iSup]
    simp_rw [coinduced_compose]
    rfl
  surjective := K.faceQuotient_surjective

/-- The parameterized final-topology criterion. Local compactness is essential
to this proof: the quotient map remains suitable after taking this product. -/
theorem continuous_prod_iff {Y Z : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y]
    [TopologicalSpace Z] (f : K.Realization × Y → Z) :
    Continuous f ↔ ∀ s : K.Face,
      Continuous (fun p : StdSimplex ℝ s.1 × Y ↦ f (K.faceInclusion s p.1, p.2)) := by
  constructor
  · intro h s
    exact h.comp ((K.continuous_faceInclusion s).comp continuous_fst |>.prodMk continuous_snd)
  · intro h
    apply K.isQuotientMap_faceQuotient.continuous_lift_prod_left
    have hs : Continuous (fun p : Σ s : K.Face, StdSimplex ℝ s.1 × Y ↦
        f (K.faceInclusion p.1 p.2.1, p.2.2)) := continuous_sigma h
    exact hs.comp (Homeomorph.sigmaProdDistrib.continuous_toFun)

end Complex
end Topo
