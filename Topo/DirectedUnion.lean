/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.FiniteNullContractible
import Mathlib.Order.Directed

/-! # Contractibility of directed unions of subcomplexes -/

noncomputable section
open Topology Convexity
namespace Topo.Complex
universe u v
variable {V : Type u} {ι : Type v} [Nonempty ι]

def unionFamily (B : ι → Topo.Complex V) : Topo.Complex V where
  faces := {s | ∃ i, s ∈ (B i).faces}
  empty_mem := ⟨Classical.choice inferInstance, (B _).empty_mem⟩
  downward hst ht := by
    obtain ⟨i, hi⟩ := ht
    exact ⟨i, (B i).downward hst hi⟩

theorem subset_unionFamily (B : ι → Topo.Complex V) (i : ι) :
    (B i).faces ⊆ (unionFamily B).faces := fun _ hs ↦ ⟨i, hs⟩

/-- Finite families of faces in a directed union all occur in one stage. -/
theorem finite_subcomplex_subset_stage (B : ι → Topo.Complex V)
    (hdir : Directed (fun L M : Topo.Complex V ↦ L.faces ⊆ M.faces) B)
    (F : Topo.Complex V) (hF : F.faces ⊆ (unionFamily B).faces) (hfin : F.faces.Finite) :
    ∃ i, F.faces ⊆ (B i).faces := by
  classical
  have haux (S : Finset (Finset V)) :
      (∀ s ∈ S, ∃ i, s ∈ (B i).faces) → ∃ i, ∀ s ∈ S, s ∈ (B i).faces := by
    induction S using Finset.induction_on with
    | empty => exact fun _ ↦ ⟨Classical.choice inferInstance, by simp⟩
    | @insert s S hs ih =>
      intro hS
      obtain ⟨i, hi⟩ := hS s (Finset.mem_insert_self _ _)
      obtain ⟨j, hj⟩ := ih (fun t ht ↦ hS t (Finset.mem_insert_of_mem ht))
      obtain ⟨k, hik, hjk⟩ := hdir i j
      refine ⟨k, ?_⟩
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hik hi
      · exact hjk (hj t ht)
  obtain ⟨i, hi⟩ := haux hfin.toFinset (fun s hs ↦ hF (hfin.mem_toFinset.mp hs))
  exact ⟨i, fun s hs ↦ hi s (hfin.mem_toFinset.mpr hs)⟩

/-- A directed union of contractible weak realizations is contractible. -/
theorem contractible_unionFamily (B : ι → Topo.Complex V)
    (hdir : Directed (fun L M : Topo.Complex V ↦ L.faces ⊆ M.faces) B)
    (hB : ∀ i, ContractibleSpace (B i).Realization) :
    ContractibleSpace (unionFamily B).Realization :=
  (unionFamily B).contractible_of_cofinal_contractible B (subset_unionFamily B) hB
    (finite_subcomplex_subset_stage B hdir)

/-- The same limit theorem for an ambient complex specified by its face-wise union. -/
theorem contractible_of_directed_union (K : Topo.Complex V) (B : ι → Topo.Complex V)
    (hdir : Directed (fun L M : Topo.Complex V ↦ L.faces ⊆ M.faces) B)
    (hunion : ∀ s, s ∈ K.faces ↔ ∃ i, s ∈ (B i).faces)
    (hB : ∀ i, ContractibleSpace (B i).Realization) : ContractibleSpace K.Realization := by
  have hBK (i : ι) : (B i).faces ⊆ K.faces := fun s hs ↦ (hunion s).mpr ⟨i, hs⟩
  apply K.contractible_of_cofinal_contractible B hBK hB
  intro F hF hfin
  exact finite_subcomplex_subset_stage B hdir F (fun s hs ↦ (hunion s).mp (hF hs)) hfin

/-- Increasing families over any nonempty directed preorder, including well orders. -/
theorem contractible_of_increasing_union [Preorder ι] [IsDirectedOrder ι]
    (K : Topo.Complex V) (B : ι → Topo.Complex V)
    (hmono : ∀ i j, i ≤ j → (B i).faces ⊆ (B j).faces)
    (hunion : ∀ s, s ∈ K.faces ↔ ∃ i, s ∈ (B i).faces)
    (hB : ∀ i, ContractibleSpace (B i).Realization) : ContractibleSpace K.Realization :=
  contractible_of_directed_union K B (directed_of_isDirected_le (fun {i j} hij ↦ hmono i j hij))
    hunion hB

end Topo.Complex
