/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.DirectedUnion
import Topo.ConeRelative
import Mathlib.Topology.LocallyFinite

/-! # An infinite simplex of unbounded dimension: a non-locally-finite example -/

noncomputable section
open Topology Convexity Topo.Complex
namespace Topo.Examples.InfiniteSimplex

def infiniteSimplex : Topo.Complex ℕ where
  faces := Set.univ
  empty_mem := Set.mem_univ _
  downward _ _ := Set.mem_univ _

def stage (n : ℕ) : Topo.Complex ℕ := simplexOn (Finset.range (n + 1))

theorem stage_mono (i j : ℕ) (hij : i ≤ j) : (stage i).faces ⊆ (stage j).faces := by
  intro s hs
  exact hs.trans (Finset.range_mono (by omega))

theorem stage_finite (n : ℕ) : (stage n).faces.Finite := by
  have he : (stage n).faces = (↑(Finset.range (n + 1)).powerset : Set (Finset ℕ)) := by
    ext t
    exact Finset.mem_powerset.symm
  rw [he]
  exact (Finset.range (n + 1)).powerset.finite_toSet

theorem stage_contractible (n : ℕ) : ContractibleSpace (stage n).Realization := by
  classical
  apply (stage n).contractible_of_coneVertex (a := 0)
  let : DecidableEq ℕ := fun a b ↦ Classical.propDecidable (a = b)
  intro s hs
  exact Finset.insert_subset (Finset.mem_range.mpr (by omega)) hs

theorem union_stages (s : Finset ℕ) : s ∈ infiniteSimplex.faces ↔ ∃ n, s ∈ (stage n).faces := by
  constructor
  · intro _
    refine ⟨s.sup id, ?_⟩
    intro v hv
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hv))
  · intro _
    exact Set.mem_univ _

/-- This uses the finite-subcomplex limit theorem and the finite contractible stages. -/
theorem contractible_infiniteSimplex : ContractibleSpace infiniteSimplex.Realization :=
  contractible_of_increasing_union infiniteSimplex stage stage_mono union_stages stage_contractible

theorem faces_injective : Function.Injective (fun n : ℕ ↦ Finset.range (n + 1)) := by
  intro i j h
  have he := congrArg Finset.card h
  simpa only [Finset.card_range, Nat.add_right_cancel_iff] using he

/-- There are infinitely many faces incident to vertex zero, with no dimension bound. -/
theorem infinite_incident_faces :
    Set.Infinite {s : Finset ℕ | s ∈ infiniteSimplex.faces ∧ 0 ∈ s} := by
  apply (Set.infinite_range_of_injective faces_injective).mono
  rintro s ⟨n, rfl⟩
  exact ⟨Set.mem_univ _, Finset.mem_range.mpr (by omega)⟩

def zeroVertex : infiniteSimplex.Realization := infiniteSimplex.vertex 0 (Set.mem_univ _)

/-- The actual closed simplex images fail topological local finiteness at vertex zero. -/
theorem not_locallyFinite_faces : ¬ LocallyFinite (fun n : ℕ ↦
    Set.range (infiniteSimplex.faceInclusion ⟨Finset.range (n + 1), Set.mem_univ _⟩)) := by
  intro h
  have hf := h.point_finite zeroVertex
  have he : {n : ℕ | zeroVertex ∈ Set.range
      (infiniteSimplex.faceInclusion ⟨Finset.range (n + 1), Set.mem_univ _⟩)} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro n
    apply (infiniteSimplex.mem_range_faceInclusion _ zeroVertex).mpr
    change (StdSimplex.single (0 : ℕ)).weights.support ⊆ Finset.range (n + 1)
    simp
  rw [he] at hf
  exact (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) hf

end Topo.Examples.InfiniteSimplex
