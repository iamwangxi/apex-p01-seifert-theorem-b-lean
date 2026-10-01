/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.StrongDeformation

/-!
# One-layer gluing of arbitrarily many strong deformation retractions

Every face belongs to the fixed target or to a single block. Distinct blocks
intersect only in the target. There is no finiteness assumption on the index type.
Continuity is proved face by face, then descended on the product with the locally
compact unit interval using `continuous_prod_iff`.
-/

noncomputable section

open Topology Convexity

namespace Topo.Complex

universe u v
variable {V : Type u} {ι : Type v} {K L : Topo.Complex V} {B : ι → Topo.Complex V}

/-- The combinatorial hypotheses of the one-layer gluing theorem. -/
structure BlockCover (K L : Topo.Complex V) (B : ι → Topo.Complex V) : Prop where
  target_subset : L.faces ⊆ K.faces
  block_subset : ∀ i, (B i).faces ⊆ K.faces
  cover : ∀ s ∈ K.faces, s ∈ L.faces ∨ ∃ i, s ∈ (B i).faces
  overlap : ∀ i j, i ≠ j → ((B i).inter (B j)).faces ⊆ L.faces

namespace BlockCover

variable (C : BlockCover K L B)
variable (D : ∀ i, StrongDeformationRetract
  (inter_subset_left : ((B i).inter L).faces ⊆ (B i).faces))

include C in
theorem exists_block (x : K.Realization) (hx : x.1.weights.support ∉ L.faces) :
    ∃ i, x.1.weights.support ∈ (B i).faces :=
  (C.cover _ x.2).resolve_left hx

/-- A block containing a point outside the target. The overlap condition will
prove that this choice is unique whenever it is used. -/
def index (x : K.Realization) (hx : x.1.weights.support ∉ L.faces) : ι :=
  Classical.choose (C.exists_block x hx)

theorem index_mem (x : K.Realization) (hx : x.1.weights.support ∉ L.faces) :
    x.1.weights.support ∈ (B (C.index x hx)).faces :=
  Classical.choose_spec (C.exists_block x hx)

open Classical in
/-- Fix the target, and use the local deformation on the unique outside block. -/
def gluedHomotopy (p : K.Realization × unitInterval) : K.Realization :=
  if hx : p.1.1.weights.support ∈ L.faces then p.1
  else inclusion (C.block_subset (C.index p.1 hx))
    ((D (C.index p.1 hx)).homotopy (⟨p.1.1, C.index_mem p.1 hx⟩, p.2))

theorem glued_fixed (x : K.Realization) (hx : x.1.weights.support ∈ L.faces)
    (t : unitInterval) : C.gluedHomotopy D (x, t) = x := by
  simp only [gluedHomotopy, dite_eq_left hx]

/-- The global formula agrees with every local formula, including on overlaps. -/
theorem glued_on_block (i : ι) (x : (B i).Realization) (t : unitInterval) :
    C.gluedHomotopy D (inclusion (C.block_subset i) x, t) =
      inclusion (C.block_subset i) ((D i).homotopy (x, t)) := by
  let y := inclusion (C.block_subset i) x
  by_cases hy : y.1.weights.support ∈ L.faces
  · have hfix := (D i).fixed_of_mem x ⟨x.2, hy⟩ t
    rw [hfix]
    exact C.glued_fixed D y hy t
  · have hi : C.index y hy = i := by
      by_contra hne
      exact hy (C.overlap (C.index y hy) i hne ⟨C.index_mem y hy, x.2⟩)
    change C.gluedHomotopy D (y, t) = _
    simp only [gluedHomotopy, dite_eq_right hy]
    have he (j : ι) (hji : j = i) (hjx : y.1.weights.support ∈ (B j).faces) :
        inclusion (C.block_subset j) ((D j).homotopy (⟨y.1, hjx⟩, t)) =
          inclusion (C.block_subset i) ((D i).homotopy (x, t)) := by
      subst j
      rfl
    exact he (C.index y hy) hi (C.index_mem y hy)

/-- Joint continuity on the ordinary product topology, even for infinitely many
blocks. Each finite face is checked using just one block or the fixed target. -/
theorem continuous_gluedHomotopy : Continuous (C.gluedHomotopy D) := by
  rw [K.continuous_prod_iff]
  intro s
  rcases C.cover s.1 s.2 with hsL | ⟨i, hsi⟩
  · have heq : (fun p : StdSimplex ℝ s.1 × unitInterval ↦
        C.gluedHomotopy D (K.faceInclusion s p.1, p.2)) =
        K.faceInclusion s ∘ Prod.fst := by
      funext p
      exact C.glued_fixed D _ (L.downward (support_map_val_subset s.1 p.1) hsL) _
    rw [heq]
    exact (K.continuous_faceInclusion s).comp continuous_fst
  · let si : (B i).Face := ⟨s.1, hsi⟩
    have heq : (fun p : StdSimplex ℝ s.1 × unitInterval ↦
        C.gluedHomotopy D (K.faceInclusion s p.1, p.2)) =
        inclusion (C.block_subset i) ∘ (D i).homotopy ∘
          (fun p ↦ ((B i).faceInclusion si p.1, p.2)) := by
      funext p
      exact C.glued_on_block D i ((B i).faceInclusion si p.1) p.2
    rw [heq]
    exact (continuous_inclusion (C.block_subset i)).comp
      ((D i).continuous.comp
        (((B i).continuous_faceInclusion si).comp continuous_fst |>.prodMk continuous_snd))

theorem glued_zero (x : K.Realization) : C.gluedHomotopy D (x, 0) = x := by
  by_cases hx : x.1.weights.support ∈ L.faces
  · exact C.glued_fixed D x hx 0
  · simp only [gluedHomotopy, dite_eq_right hx]
    exact congrArg (inclusion (C.block_subset (C.index x hx)))
      ((D (C.index x hx)).at_zero ⟨x.1, C.index_mem x hx⟩)

theorem glued_one_mem (x : K.Realization) :
    (C.gluedHomotopy D (x, 1)).1.weights.support ∈ L.faces := by
  by_cases hx : x.1.weights.support ∈ L.faces
  · rw [C.glued_fixed D x hx 1]
    exact hx
  · simp only [gluedHomotopy, dite_eq_right hx, inclusion_val]
    exact ((D (C.index x hx)).at_one _).2

/-- The one-layer gluing theorem, with arbitrary index type and no local
finiteness assumption. -/
def strongDeformationRetract : StrongDeformationRetract C.target_subset where
  homotopy := C.gluedHomotopy D
  continuous := C.continuous_gluedHomotopy D
  at_zero := C.glued_zero D
  at_one := C.glued_one_mem D
  fixed x t := C.glued_fixed D _ x.2 t

/-- Propositional form: existence of a local deformation on each block is enough. -/
theorem nonempty_strongDeformationRetract
    (hD : ∀ i, Nonempty (StrongDeformationRetract
      (inter_subset_left : ((B i).inter L).faces ⊆ (B i).faces))) :
    Nonempty (StrongDeformationRetract C.target_subset) :=
  ⟨C.strongDeformationRetract (fun i ↦ Classical.choice (hD i))⟩

include C D in
theorem contractible [ContractibleSpace L.Realization] : ContractibleSpace K.Realization :=
  (C.strongDeformationRetract D).contractible

include C in
theorem contractible_of_nonempty [ContractibleSpace L.Realization]
    (hD : ∀ i, Nonempty (StrongDeformationRetract
      (inter_subset_left : ((B i).inter L).faces ⊆ (B i).faces))) :
    ContractibleSpace K.Realization :=
  C.contractible (fun i ↦ Classical.choice (hD i))

end BlockCover
end Topo.Complex
