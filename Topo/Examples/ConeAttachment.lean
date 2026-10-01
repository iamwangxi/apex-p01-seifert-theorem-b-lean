/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.ConeBase
import Topo.FlagSuccessor

/-! A contractible base with no cone vertex: the three-edge path `0--1--2--3`.
The old complex is its cone at 4; attaching a second cone at 5 gives an actual
nontrivial successor deformation along a proper subcomplex. -/

noncomputable section
open Topology Convexity ContinuousMap
namespace Topo.Examples.ConeAttachment
open Topo.Complex

abbrev Vertex := Fin 6

def path : Topo.Complex Vertex where
  faces := {s | s ⊆ {0, 1} ∨ s ⊆ {1, 2} ∨ s ⊆ {2, 3}}
  empty_mem := Or.inl (Finset.empty_subset _)
  downward hst ht := ht.elim (fun h ↦ Or.inl (hst.trans h))
    (fun h ↦ Or.inr (h.elim (fun h ↦ Or.inl (hst.trans h))
      (fun h ↦ Or.inr (hst.trans h))))

def middle : Topo.Complex Vertex := simplexOn {1, 2}

def block : Bool → Topo.Complex Vertex
  | false => simplexOn {0, 1}
  | true => simplexOn {2, 3}

theorem cover : BlockCover path middle block where
  target_subset _ h := Or.inr (Or.inl h)
  block_subset i := by
    cases i
    · exact fun _ h ↦ Or.inl h
    · exact fun _ h ↦ Or.inr (Or.inr h)
  cover _ h := by
    rcases h with hl | hm | hr
    · exact Or.inr ⟨false, hl⟩
    · exact Or.inl hm
    · exact Or.inr ⟨true, hr⟩
  overlap i j hij := by
    cases i <;> cases j
    · exact (hij rfl).elim
    · intro s hs u hu
      have h₀ := hs.1 hu
      have h₁ := hs.2 hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at h₀ h₁
      rcases h₀ with rfl | rfl <;> norm_num at h₁
    · intro s hs u hu
      have h₀ := hs.1 hu
      have h₁ := hs.2 hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at h₀ h₁
      rcases h₀ with rfl | rfl <;> norm_num at h₁
    · exact (hij rfl).elim

theorem simplexOn_coneVertex {s : Finset Vertex} {a : Vertex} (ha : a ∈ s) :
    (simplexOn s).IsConeVertex a := by
  let : DecidableEq Vertex := fun a b ↦ Classical.propDecidable (a = b)
  intro t ht
  exact Finset.insert_subset_iff.mpr ⟨ha, ht⟩

def localDeformation (i : Bool) : StrongDeformationRetract
    (inter_subset_left : ((block i).inter middle).faces ⊆ (block i).faces) := by
  cases i
  · apply strongDeformationRetract_of_coneVertex inter_subset_left
      (a := (1 : Vertex)) (simplexOn_coneVertex (by simp))
    · simp [middle, mem_inter]
    · intro s hs u hu
      have hl : u = 0 ∨ u = 1 := by simpa using hs.1 hu
      have hm : u = 1 ∨ u = 2 := by simpa using hs.2 hu
      rcases hl with h₀ | h₁
      · subst u
        norm_num at hm
      · simpa using h₁
  · apply strongDeformationRetract_of_coneVertex inter_subset_left
      (a := (2 : Vertex)) (simplexOn_coneVertex (by simp))
    · simp [middle, mem_inter]
    · intro s hs u hu
      have hr : u = 2 ∨ u = 3 := by simpa using hs.1 hu
      have hm : u = 1 ∨ u = 2 := by simpa using hs.2 hu
      rcases hr with h₂ | h₃
      · simpa using h₂
      · subst u
        norm_num at hm

instance middleContractible : ContractibleSpace middle.Realization :=
  middle.contractible_of_coneVertex (simplexOn_coneVertex (a := 1) (by simp))

instance pathContractible : ContractibleSpace path.Realization :=
  cover.contractible localDeformation

instance pathNonempty : Nonempty path.Realization :=
  ⟨path.vertex 0 (by simp [path])⟩

theorem path_no_cone_vertex : ¬ ∃ a, path.IsConeVertex a := by
  rintro ⟨a, ha⟩
  fin_cases a
  · have h := ha {2, 3} (by simp [path, Finset.insert_subset_iff])
    simp [path, Finset.insert_subset_iff] at h
  · have h := ha {2, 3} (by simp [path, Finset.insert_subset_iff])
    simp [path, Finset.insert_subset_iff] at h
  · have h := ha {0, 1} (by simp [path, Finset.insert_subset_iff])
    simp [path, Finset.insert_subset_iff] at h
  · have h := ha {0, 1} (by simp [path, Finset.insert_subset_iff])
    simp [path, Finset.insert_subset_iff] at h
  · have h := ha {0, 1} (by simp [path, Finset.insert_subset_iff])
    simp [path, Finset.insert_subset_iff] at h
  · have h := ha {0, 1} (by simp [path, Finset.insert_subset_iff])
    simp [path, Finset.insert_subset_iff] at h

def oldComplex : Topo.Complex Vertex := path.coneAt 4
def successor : Topo.Complex Vertex := oldComplex.attachCone path 5

theorem path_subset_old : path.faces ⊆ oldComplex.faces := path.subset_coneAt 4
theorem apex_fresh : oldComplex.Fresh 5 := by
  simp [oldComplex, Fresh, mem_coneAt, path]

instance oldContractible : ContractibleSpace oldComplex.Realization :=
  oldComplex.contractible_of_coneVertex (path.coneAt_isConeVertex 4)

def successorDeformation : StrongDeformationRetract (oldComplex.subset_attachCone path 5) :=
  oldComplex.strongDeformationRetract_attachCone path 5 path_subset_old apex_fresh

theorem successor_contractible : ContractibleSpace successor.Realization :=
  oldComplex.contractible_attachCone path 5 path_subset_old apex_fresh

theorem proper_base : ∃ s, s ∈ oldComplex.faces ∧ s ∉ path.faces := by
  refine ⟨{0, 1, 4}, ?_, by simp [path, Finset.insert_subset_iff]⟩
  change _ ∈ (path.coneAt 4).faces
  rw [mem_coneAt]
  left
  intro u hu
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with ⟨hne, h₀ | h₁ | h₄⟩
  · simp [h₀]
  · simp [h₁]
  · exact (hne h₄).elim

theorem new_face : ∃ s, s ∈ successor.faces ∧ s ∉ oldComplex.faces := by
  refine ⟨{0, 1, 5}, ?_, by simp [oldComplex, mem_coneAt, path, Finset.insert_subset_iff]⟩
  right
  rw [mem_coneAt]
  left
  intro u hu
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with ⟨hne, h₀ | h₁ | h₅⟩
  · simp [h₀]
  · simp [h₁]
  · exact (hne h₅).elim

/-- A simultaneous witness of non-vacuity, including a genuinely new face. -/
theorem nonvacuous : Nonempty path.Realization ∧ ContractibleSpace path.Realization ∧
    (¬ ∃ a, path.IsConeVertex a) ∧
    (∃ s, s ∈ oldComplex.faces ∧ s ∉ path.faces) ∧
    (∃ s, s ∈ successor.faces ∧ s ∉ oldComplex.faces) ∧
    Nonempty (StrongDeformationRetract (oldComplex.subset_attachCone path 5)) ∧
    ContractibleSpace successor.Realization :=
  ⟨inferInstance, inferInstance, path_no_cone_vertex, proper_base, new_face,
    ⟨successorDeformation⟩, successor_contractible⟩

end Topo.Examples.ConeAttachment
