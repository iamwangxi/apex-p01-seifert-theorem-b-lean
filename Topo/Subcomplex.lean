/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.WeakRealization

/-!
# Closed embeddings of subcomplex realizations

Complexes share the ambient vertex type. A subcomplex is expressed by inclusion
of face sets. The closed-map proof only uses finitely many subfaces of each face,
and therefore applies without any local finiteness hypothesis.
-/

noncomputable section

open Topology Convexity

namespace Topo.Complex

universe u
variable {V : Type u} {L K : Topo.Complex V}

/-- The intersection of two complexes on the same vertex set. -/
def inter (L K : Topo.Complex V) : Topo.Complex V where
  faces := L.faces ∩ K.faces
  empty_mem := ⟨L.empty_mem, K.empty_mem⟩
  downward hst ht := ⟨L.downward hst ht.1, K.downward hst ht.2⟩

@[simp] theorem mem_inter (s : Finset V) :
    s ∈ (L.inter K).faces ↔ s ∈ L.faces ∧ s ∈ K.faces := Iff.rfl

theorem inter_subset_left : (L.inter K).faces ⊆ L.faces := fun _ h ↦ h.1
theorem inter_subset_right : (L.inter K).faces ⊆ K.faces := fun _ h ↦ h.2

/-- The natural map induced by inclusion of face sets. -/
def inclusion (hLK : L.faces ⊆ K.faces) (x : L.Realization) : K.Realization :=
  ⟨x.1, hLK x.2⟩

@[simp] theorem inclusion_val (hLK : L.faces ⊆ K.faces) (x : L.Realization) :
    (inclusion hLK x).1 = x.1 := rfl

theorem inclusion_injective (hLK : L.faces ⊆ K.faces) :
    Function.Injective (inclusion hLK) := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : K.Realization ↦ z.1) h)

@[simp] theorem inclusion_faceInclusion (hLK : L.faces ⊆ K.faces) (s : L.Face)
    (w : StdSimplex ℝ s.1) :
    inclusion hLK (L.faceInclusion s w) = K.faceInclusion ⟨s.1, hLK s.2⟩ w := rfl

@[fun_prop] theorem continuous_inclusion (hLK : L.faces ⊆ K.faces) :
    Continuous (inclusion hLK) := by
  rw [L.continuous_iff]
  intro s
  exact K.continuous_faceInclusion ⟨s.1, hLK s.2⟩

theorem mem_range_inclusion (hLK : L.faces ⊆ K.faces) (x : K.Realization) :
    x ∈ Set.range (inclusion hLK) ↔ x.1.weights.support ∈ L.faces := by
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x.1, hx⟩, rfl⟩

/-- There are only finitely many faces of `L` contained in a fixed finite set. -/
theorem finite_faces_subset (L : Topo.Complex V) (s : Finset V) :
    Set.Finite {t : L.Face | t.1 ⊆ s} := by
  classical
  have h := s.powerset.finite_toSet.preimage
    (f := (Subtype.val : L.Face → Finset V)) Subtype.val_injective.injOn
  simpa [Set.preimage] using h

/-- A closed set in a subcomplex remains closed in the ambient weak realization. -/
theorem isClosedMap_inclusion (hLK : L.faces ⊆ K.faces) :
    IsClosedMap (inclusion hLK) := by
  intro A hA
  rw [K.isClosed_iff]
  intro s
  let C (t : L.Face) : Set K.Realization :=
    K.faceInclusion ⟨t.1, hLK t.2⟩ '' (L.faceInclusion t ⁻¹' A)
  have hC (t : L.Face) : IsClosed (C t) :=
    (K.isClosedEmbedding_faceInclusion ⟨t.1, hLK t.2⟩).isClosedMap _
      (hA.preimage (L.continuous_faceInclusion t))
  have heq : K.faceInclusion s ⁻¹' (inclusion hLK '' A) =
      K.faceInclusion s ⁻¹' (⋃ t ∈ {t : L.Face | t.1 ⊆ s.1}, C t) := by
    ext w
    constructor
    · rintro ⟨x, hxA, hx⟩
      have hxs : x.1.weights.support ⊆ s.1 := by
        have he : x.1 = (w.map (Subtype.val : s.1 → V)) :=
          congrArg (fun y : K.Realization ↦ y.1) hx
        rw [he]
        exact support_map_val_subset s.1 w
      let t : L.Face := ⟨x.1.weights.support, x.2⟩
      obtain ⟨z, hz⟩ := (L.mem_range_faceInclusion t x).2 (by exact Finset.Subset.refl _)
      apply Set.mem_iUnion.mpr
      refine ⟨t, Set.mem_iUnion.mpr ⟨hxs, ?_⟩⟩
      refine ⟨z, ?_, ?_⟩
      · change L.faceInclusion t z ∈ A
        simpa only [hz] using hxA
      · simpa only [← inclusion_faceInclusion hLK t, hz] using hx
    · intro hw
      obtain ⟨t, hw⟩ := Set.mem_iUnion.mp hw
      obtain ⟨ht, z, hzA, hzw⟩ := Set.mem_iUnion.mp hw
      exact ⟨L.faceInclusion t z, hzA, by simpa only [inclusion_faceInclusion] using hzw⟩
  rw [heq]
  exact ((finite_faces_subset L s.1).isClosed_biUnion (fun t _ ↦ hC t)).preimage
    (K.continuous_faceInclusion s)

/-- Every subcomplex is a closed embedded subspace for the weak topology. -/
theorem isClosedEmbedding_inclusion (hLK : L.faces ⊆ K.faces) :
    IsClosedEmbedding (inclusion hLK) :=
  .of_continuous_injective_isClosedMap (continuous_inclusion hLK)
    (inclusion_injective hLK) (isClosedMap_inclusion hLK)

theorem isClosed_range_inclusion (hLK : L.faces ⊆ K.faces) :
    IsClosed (Set.range (inclusion hLK)) :=
  (isClosedEmbedding_inclusion hLK).isClosed_range

theorem isClosed_subcomplex (hLK : L.faces ⊆ K.faces) :
    IsClosed {x : K.Realization | x.1.weights.support ∈ L.faces} := by
  have h : Set.range (inclusion hLK) =
      {x : K.Realization | x.1.weights.support ∈ L.faces} := by
    ext x
    exact mem_range_inclusion hLK x
  rw [← h]
  exact isClosed_range_inclusion hLK

end Topo.Complex
