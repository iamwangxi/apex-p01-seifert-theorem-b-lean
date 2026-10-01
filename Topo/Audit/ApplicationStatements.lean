/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import ApplicationStatements
import Topo.SurfaceTruncation

/-! Definition-by-definition audit, then proofs of the standalone conditional A and C. -/

noncomputable section
universe u
namespace SeifertApplicationAudit
variable {V : Type u}

/-- Both coordinates and the lexicographic order agree literally. -/
theorem complexity_eq (g : V → ℕ) (A : V → ℝ) :
    Seifert.Application.complexity g A = SeifertApplicationStatement.complexity g A := rfl

theorem values_eq (g : V → ℕ) (A : V → ℝ) :
    Seifert.Application.Values g A = SeifertApplicationStatement.Values g A := rfl

theorem outputs_iff (G : SimpleGraph V) (g : V → ℕ) (A : V → ℝ) (x u w p q : V) :
    Seifert.Application.Outputs G g A x u w p q ↔
      SeifertApplicationStatement.Outputs G g A x u w p q := by
  constructor <;> intro h <;> exact ⟨h.a_up, h.a_down, h.b, h.c, h.d⟩

/-- No geometric assumption is added, omitted, or hidden in the bridge. -/
theorem surfaceSystem_iff (G : SimpleGraph V) (g : V → ℕ) (A : V → ℝ) :
    Seifert.Application.SurfaceSystem G g A ↔
      SeifertApplicationStatement.SurfaceSystem G g A := by
  constructor
  · intro h
    refine ⟨h.positive, h.connected, h.wellFounded, ?_⟩
    intro x u w hxu hxw huw
    obtain ⟨p, q, hpq⟩ := h.outputs x u w hxu hxw huw
    exact ⟨p, q, (outputs_iff G g A x u w p q).mp hpq⟩
  · intro h
    refine ⟨h.positive, h.connected, h.wellFounded, ?_⟩
    intro x u w hxu hxw huw
    obtain ⟨p, q, hpq⟩ := h.outputs x u w hxu hxw huw
    exact ⟨p, q, (outputs_iff G g A x u w p q).mpr hpq⟩

theorem cliqueComplex_eq (G : SimpleGraph V) :
    (Seifert.cliqueComplex G).faces = SeifertApplicationStatement.cliqueComplex G := rfl

theorem realization_eq (G : SimpleGraph V) :
    (Seifert.cliqueComplex G).Realization = SeifertApplicationStatement.WeakRealization G := rfl

/-- Equality of the weak topology itself. -/
theorem weakTopology_eq (G : SimpleGraph V) :
    Topo.Complex.realizationTopology (Seifert.cliqueComplex G) =
      SeifertApplicationStatement.weakTopology G := rfl

def realizationHomeomorph (G : SimpleGraph V) :
    (Seifert.cliqueComplex G).Realization ≃ₜ SeifertApplicationStatement.WeakRealization G :=
  Homeomorph.refl _

theorem fullComplex_eq (G : SimpleGraph V) (D : Set V) :
    ((Seifert.cliqueComplex G).full D).faces =
      SeifertApplicationStatement.fullComplex G D := rfl

theorem fullRealization_eq (G : SimpleGraph V) (D : Set V) :
    ((Seifert.cliqueComplex G).full D).Realization =
      SeifertApplicationStatement.FullRealization G D := rfl

theorem fullWeakTopology_eq (G : SimpleGraph V) (D : Set V) :
    Topo.Complex.realizationTopology ((Seifert.cliqueComplex G).full D) =
      SeifertApplicationStatement.fullWeakTopology G D := rfl

/-- Includes the topology and both graph metrics, not just set-level identification. -/
theorem fullConclusion_iff (G : SimpleGraph V) (D : Set V) :
    Seifert.Application.FullConclusion G D ↔
      SeifertApplicationStatement.FullConclusion G D := Iff.rfl

theorem genusSet_eq (g : V → ℕ) (ℓ : ℕ) :
    Seifert.Application.GenusSet g ℓ = SeifertApplicationStatement.GenusSet g ℓ := rfl

theorem areaSet_eq (g : V → ℕ) (A : V → ℝ) (ℓ : ℕ) (a₀ : ℝ) :
    Seifert.Application.AreaSet g A ℓ a₀ = SeifertApplicationStatement.AreaSet g A ℓ a₀ := rfl

/-- Standalone conditional Theorem A, obtained from the project theorem. -/
theorem theoremA_verified : SeifertApplicationStatement.TheoremA.{u} := by
  intro V G g A h
  let := Seifert.Application.theoremA ((surfaceSystem_iff G g A).mpr h)
  exact (realizationHomeomorph G).symm.contractibleSpace

/-- Standalone conditional Theorem C, genus truncation. -/
theorem theoremC_genus_verified : SeifertApplicationStatement.TheoremC_genus.{u} := by
  intro V G g A h ℓ hne
  exact (fullConclusion_iff G _).mp
    (Seifert.Application.theoremC_genus ((surfaceSystem_iff G g A).mpr h) ℓ hne)

/-- Standalone conditional Theorem C, §6.2 area truncation. -/
theorem theoremC_area_verified : SeifertApplicationStatement.TheoremC_area.{u} := by
  intro V G g A h ℓ a₀ hne
  exact (fullConclusion_iff G _).mp
    (Seifert.Application.theoremC_area ((surfaceSystem_iff G g A).mpr h) ℓ a₀ hne)

end SeifertApplicationAudit
