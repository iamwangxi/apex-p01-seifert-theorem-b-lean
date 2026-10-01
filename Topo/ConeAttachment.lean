/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.RelativeConeDeformation
import Topo.ConeBase
import Topo.BlockGluing

/-! Attach a cone along a contractible subcomplex and preserve the homotopy type. -/

noncomputable section
open Topology Convexity ContinuousMap
namespace Topo.Complex
universe u
variable {V : Type u}
local instance t5AttachmentDecidableEq : DecidableEq V := Classical.decEq V

def union (X Y : Topo.Complex V) : Topo.Complex V where
  faces := X.faces ∪ Y.faces
  empty_mem := Or.inl X.empty_mem
  downward hst ht := ht.elim (fun h ↦ Or.inl (X.downward hst h))
    (fun h ↦ Or.inr (Y.downward hst h))

@[simp] theorem mem_union (X Y : Topo.Complex V) (s : Finset V) :
    s ∈ (X.union Y).faces ↔ s ∈ X.faces ∨ s ∈ Y.faces := Iff.rfl

/-- The successor complex, using a fresh vertex in the common ambient type. -/
def attachCone (X L : Topo.Complex V) (a : V) : Topo.Complex V := X.union (L.coneAt a)

theorem subset_attachCone (X L : Topo.Complex V) (a : V) :
    X.faces ⊆ (X.attachCone L a).faces := fun _ h ↦ Or.inl h

theorem cone_subset_attachCone (X L : Topo.Complex V) (a : V) :
    (L.coneAt a).faces ⊆ (X.attachCone L a).faces := fun _ h ↦ Or.inr h

theorem coneAt_inter_faces (X L : Topo.Complex V) (a : V)
    (hLX : L.faces ⊆ X.faces) (ha : X.Fresh a) :
    ((L.coneAt a).inter X).faces = L.faces := by
  ext s
  constructor
  · rintro ⟨hc, hx⟩
    change s.erase a ∈ L.faces at hc
    simpa [Finset.erase_eq_of_notMem (ha.not_mem hx)] using hc
  · intro hl
    exact ⟨L.subset_coneAt a hl, hLX hl⟩

theorem attachmentCover (X L : Topo.Complex V) (a : V) :
    BlockCover (X.attachCone L a) X (fun _ : Unit ↦ L.coneAt a) where
  target_subset := X.subset_attachCone L a
  block_subset _ := X.cone_subset_attachCone L a
  cover _ hs := hs.elim Or.inl (fun h ↦ Or.inr ⟨(), h⟩)
  overlap i j h := (h (Subsingleton.elim i j)).elim

/-- Local relative cone contraction, retargeted to the block/old-complex intersection. -/
def attachmentLocal (X L : Topo.Complex V) (a : V)
    (hLX : L.faces ⊆ X.faces) (ha : X.Fresh a) [ContractibleSpace L.Realization] :
    StrongDeformationRetract
      (inter_subset_left : ((L.coneAt a).inter X).faces ⊆ (L.coneAt a).faces) := by
  let D := L.strongDeformationRetract_coneAt a (fun h ↦ ha (hLX h))
  exact {
    homotopy := D.homotopy
    continuous := D.continuous
    at_zero := D.at_zero
    at_one := fun x ↦ ⟨L.subset_coneAt a (D.at_one x), hLX (D.at_one x)⟩
    fixed := fun x t ↦ D.fixed_of_mem _ (by
      rw [← coneAt_inter_faces X L a hLX ha]
      exact x.2) t }

/-- Main successor step, including continuity for infinite non-locally-finite complexes. -/
def strongDeformationRetract_attachCone (X L : Topo.Complex V) (a : V)
    (hLX : L.faces ⊆ X.faces) (ha : X.Fresh a) [ContractibleSpace L.Realization] :
    StrongDeformationRetract (X.subset_attachCone L a) :=
  (X.attachmentCover L a).strongDeformationRetract (fun _ ↦ X.attachmentLocal L a hLX ha)

theorem nonempty_strongDeformationRetract_attachCone (X L : Topo.Complex V) (a : V)
    (hLX : L.faces ⊆ X.faces) (ha : X.Fresh a) [ContractibleSpace L.Realization] :
    Nonempty (StrongDeformationRetract (X.subset_attachCone L a)) :=
  ⟨X.strongDeformationRetract_attachCone L a hLX ha⟩

def homotopyEquiv_attachCone (X L : Topo.Complex V) (a : V)
    (hLX : L.faces ⊆ X.faces) (ha : X.Fresh a) [ContractibleSpace L.Realization] :
    (X.attachCone L a).Realization ≃ₕ X.Realization :=
  (X.strongDeformationRetract_attachCone L a hLX ha).homotopyEquiv

theorem contractible_attachCone (X L : Topo.Complex V) (a : V)
    (hLX : L.faces ⊆ X.faces) (ha : X.Fresh a)
    [ContractibleSpace L.Realization] [ContractibleSpace X.Realization] :
    ContractibleSpace (X.attachCone L a).Realization :=
  (X.strongDeformationRetract_attachCone L a hLX ha).contractible

/-- A fresh apex is available canonically, even if all original vertices are used. -/
def newVertexAttachment (X L : Topo.Complex V) : Topo.Complex (Option V) :=
  X.coneBase.attachCone L.coneBase none

theorem coneBase_mono {X L : Topo.Complex V} (hLX : L.faces ⊆ X.faces) :
    L.coneBase.faces ⊆ X.coneBase.faces := fun _ h ↦ ⟨h.1, hLX h.2⟩

theorem newVertexAttachment_eq_union (X L : Topo.Complex V) :
    X.newVertexAttachment L = X.coneBase.union L.cone := by
  unfold newVertexAttachment attachCone
  rw [L.coneBase_coneAt]

theorem subset_newVertexAttachment (X L : Topo.Complex V) :
    X.coneBase.faces ⊆ (X.newVertexAttachment L).faces :=
  X.coneBase.subset_attachCone L.coneBase none

def strongDeformationRetract_newVertexAttachment (X L : Topo.Complex V)
    (hLX : L.faces ⊆ X.faces) [ContractibleSpace L.Realization] :
    StrongDeformationRetract (X.subset_newVertexAttachment L) := by
  let : ContractibleSpace L.coneBase.Realization :=
    L.coneBaseHomeomorph.symm.contractibleSpace
  exact X.coneBase.strongDeformationRetract_attachCone L.coneBase none
    (coneBase_mono hLX) X.coneBase_fresh

def homotopyEquiv_newVertexAttachment (X L : Topo.Complex V)
    (hLX : L.faces ⊆ X.faces) [ContractibleSpace L.Realization] :
    (X.newVertexAttachment L).Realization ≃ₕ X.Realization :=
  (X.strongDeformationRetract_newVertexAttachment L hLX).homotopyEquiv.trans
    X.coneBaseHomeomorph.symm.toHomotopyEquiv

theorem contractible_newVertexAttachment (X L : Topo.Complex V)
    (hLX : L.faces ⊆ X.faces) [ContractibleSpace L.Realization]
    [ContractibleSpace X.Realization] : ContractibleSpace (X.newVertexAttachment L).Realization :=
  (X.homotopyEquiv_newVertexAttachment L hLX).contractibleSpace

end Topo.Complex
