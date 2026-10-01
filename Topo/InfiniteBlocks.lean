/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.BlockGluing
import Topo.ConeRelative
import Mathlib.Topology.LocallyFinite

/-!
# A non-locally-finite countable bouquet of triangles

The vertices are an apex and two separate vertices for every natural number.
The n-th closed triangle shares only the apex with every other triangle. The
one-layer theorem, with an actually infinite index set, retracts the bouquet
strongly onto the apex.
-/

noncomputable section

open Topology Convexity
open Topo.Complex

namespace Topo.InfiniteBlocks

abbrev Vertex := Option (ℕ × Bool)

/-- Three distinct vertices of the n-th triangle. -/
def triangle (n : ℕ) : Finset Vertex := {none, some (n, false), some (n, true)}

@[simp] theorem apex_mem_triangle (n : ℕ) : none ∈ triangle n := by simp [triangle]

@[simp] theorem mem_triangle_some (n i : ℕ) (b : Bool) :
    some (n, b) ∈ triangle i ↔ n = i := by
  cases b <;> simp [triangle]

theorem triangle_card (n : ℕ) : (triangle n).card = 3 := by simp [triangle]

theorem triangle_injective : Function.Injective triangle := by
  intro i j h
  have hi : some (i, false) ∈ triangle j := by rw [← h]; simp
  exact (mem_triangle_some i j false).mp hi

/-- The n-th block is the whole closed 2-simplex, with all its subfaces. -/
def block (n : ℕ) : Topo.Complex Vertex := simplexOn (triangle n)

/-- The common fixed target. -/
def target : Topo.Complex Vertex := pointComplex none

/-- The union of all the triangles, including their subfaces. -/
def bouquet : Topo.Complex Vertex where
  faces := {s | ∃ n, s ⊆ triangle n}
  empty_mem := ⟨0, Finset.empty_subset _⟩
  downward hst ht := by
    obtain ⟨n, hn⟩ := ht
    exact ⟨n, hst.trans hn⟩

theorem triangle_mem_bouquet (n : ℕ) : triangle n ∈ bouquet.faces :=
  ⟨n, Finset.Subset.refl _⟩

/-- The overlap and coverage hypotheses are verified combinatorially. -/
theorem cover : BlockCover bouquet target block where
  target_subset := by
    intro s hs
    exact ⟨0, hs.trans (Finset.singleton_subset_iff.mpr (apex_mem_triangle 0))⟩
  block_subset i _ hs := ⟨i, hs⟩
  cover s hs := Or.inr hs
  overlap := by
    intro i j hij s hs v hv
    cases v with
    | none => simp
    | some p =>
      obtain ⟨n, b⟩ := p
      have hni : n = i := (mem_triangle_some n i b).mp (hs.1 hv)
      have hnj : n = j := (mem_triangle_some n j b).mp (hs.2 hv)
      exact False.elim (hij (hni.symm.trans hnj))

theorem block_coneVertex (n : ℕ) : (block n).IsConeVertex none := by
  classical
  let : DecidableEq Vertex := fun a b ↦ Classical.propDecidable (a = b)
  intro s hs
  exact Finset.insert_subset (apex_mem_triangle n) hs

/-- Each actual triangle strongly retracts onto its intersection with the target. -/
def localDeformation (n : ℕ) : StrongDeformationRetract
    (inter_subset_left : ((block n).inter target).faces ⊆ (block n).faces) :=
  strongDeformationRetract_of_coneVertex inter_subset_left (block_coneVertex n)
    ⟨Finset.singleton_subset_iff.mpr (apex_mem_triangle n), Finset.Subset.refl _⟩
    (fun _ hs ↦ hs.2)

/-- The requested infinite, non-locally-finite specialization of the gluing theorem. -/
def strongDeformation : StrongDeformationRetract cover.target_subset :=
  cover.strongDeformationRetract localDeformation

theorem contractible_bouquet : ContractibleSpace bouquet.Realization :=
  by
    have : ContractibleSpace target.Realization := by
      change ContractibleSpace (pointComplex (none : Vertex)).Realization
      infer_instance
    exact cover.contractible localDeformation

/-- The apex belongs to infinitely many distinct 2-faces. This is the standard
combinatorial failure of local finiteness at a vertex. -/
theorem infinite_incident_faces :
    Set.Infinite {s : Finset Vertex | s ∈ bouquet.faces ∧ none ∈ s} := by
  apply (Set.infinite_range_of_injective triangle_injective).mono
  rintro s ⟨n, rfl⟩
  exact ⟨triangle_mem_bouquet n, apex_mem_triangle n⟩

/-- Even restricting to actual triangles, infinitely many faces contain the apex. -/
theorem infinite_incident_triangles :
    Set.Infinite {s : Finset Vertex | s ∈ bouquet.faces ∧ none ∈ s ∧ s.card = 3} := by
  apply (Set.infinite_range_of_injective triangle_injective).mono
  rintro s ⟨n, rfl⟩
  exact ⟨triangle_mem_bouquet n, apex_mem_triangle n, triangle_card n⟩

/-- The common apex as a point of the whole realization. -/
def apex : bouquet.Realization := bouquet.vertex none
  ⟨0, Finset.singleton_subset_iff.mpr (apex_mem_triangle 0)⟩

@[simp] theorem apex_mem_blockRange (n : ℕ) :
    apex ∈ Set.range (inclusion (cover.block_subset n)) := by
  refine ⟨(block n).vertex none
    (Finset.singleton_subset_iff.mpr (apex_mem_triangle n)), ?_⟩
  exact Subtype.ext rfl

/-- The closed block images fail topological local finiteness as well: every
neighborhood of the apex meets every block. -/
theorem not_locallyFinite_blockRanges :
    ¬ LocallyFinite (fun n : ℕ ↦ Set.range (inclusion (cover.block_subset n))) := by
  intro h
  have hf := h.point_finite apex
  have he : {n : ℕ | apex ∈ Set.range (inclusion (cover.block_subset n))} = Set.univ :=
    Set.eq_univ_of_forall apex_mem_blockRange
  rw [he] at hf
  exact (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) hf

/-- The block images are exactly the closed simplex images, not a different
notion of subset of the realization. -/
theorem blockRange_eq_triangleRange (n : ℕ) :
    Set.range (inclusion (cover.block_subset n)) =
      Set.range (bouquet.faceInclusion ⟨triangle n, triangle_mem_bouquet n⟩) := by
  ext x
  rw [mem_range_inclusion, bouquet.mem_range_faceInclusion]
  rfl

theorem not_locallyFinite_triangleRanges :
    ¬ LocallyFinite (fun n : ℕ ↦
      Set.range (bouquet.faceInclusion ⟨triangle n, triangle_mem_bouquet n⟩)) := by
  have he : (fun n : ℕ ↦
      Set.range (bouquet.faceInclusion ⟨triangle n, triangle_mem_bouquet n⟩)) =
      (fun n : ℕ ↦ Set.range (inclusion (cover.block_subset n))) :=
    funext fun n ↦ (blockRange_eq_triangleRange n).symm
  rw [he]
  exact not_locallyFinite_blockRanges

end Topo.InfiniteBlocks
