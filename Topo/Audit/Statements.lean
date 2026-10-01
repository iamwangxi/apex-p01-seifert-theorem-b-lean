/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Statements
import Topo.ExchangeContractible

/-! Exact comparison with the independent Mathlib-only statement. -/
noncomputable section
open Topology Convexity
universe u w
namespace SeifertAudit
variable {V : Type u} {W : Type w} [LinearOrder W] [WellFoundedLT W]

/-- The two face predicates agree, including the empty face. -/
theorem cliqueComplex_eq (G : SimpleGraph V) :
    (Seifert.cliqueComplex G).faces = SeifertStatement.cliqueComplex G := rfl

/-- These are the same barycentric points, without a change of geometric model. -/
theorem realization_eq (G : SimpleGraph V) :
    (Seifert.cliqueComplex G).Realization = SeifertStatement.WeakRealization G := rfl

/-- The topology itself agrees, not just the underlying sets. -/
theorem weakTopology_eq (G : SimpleGraph V) :
    Topo.Complex.realizationTopology (Seifert.cliqueComplex G) =
      SeifertStatement.weakTopology G := rfl

/-- An explicit homeomorphism records both points and their weak topology. -/
def realizationHomeomorph (G : SimpleGraph V) :
    (Seifert.cliqueComplex G).Realization ≃ₜ SeifertStatement.WeakRealization G :=
  Homeomorph.refl _

theorem twoInterval_eq (G : SimpleGraph V) (u v : V) :
    Seifert.TwoInterval G u v = SeifertStatement.TwoInterval G u v := rfl

theorem isApex_iff (G : SimpleGraph V) (u v x : V) :
    Seifert.IsApex G u v x ↔ SeifertStatement.IsApex G u v x := Iff.rfl

/-- Distance-two witnesses, N1 and N2 agree with the paper's metric formulation. -/
theorem exchangeStructure_iff (G : SimpleGraph V) (c : V → W) :
    Seifert.ExchangeStructure G c ↔ SeifertStatement.ExchangeStructure G c := by
  constructor
  · intro h
    exact ⟨fun u v huv => h.n1 u v ((Seifert.distanceTwo_iff_edist G u v).mpr huv),
      fun u v huv => h.n2 u v ((Seifert.distanceTwo_iff_edist G u v).mpr huv)⟩
  · intro h
    exact ⟨fun u v huv => h.n1 u v ((Seifert.distanceTwo_iff_edist G u v).mp huv),
      fun u v huv => h.n2 u v ((Seifert.distanceTwo_iff_edist G u v).mp huv)⟩

/-- Graph connectedness in the project includes exactly the explicit nonemptiness here. -/
theorem exchangeComplex_iff (G : SimpleGraph V) (c : V → W) :
    Seifert.ExchangeComplex G c ↔ SeifertStatement.ExchangeComplex G c := by
  constructor
  · intro h
    exact ⟨h.connected.nonempty, h.connected.preconnected,
      (exchangeStructure_iff G c).mp h.toExchangeStructure⟩
  · rintro ⟨hne, hconnected, hs⟩
    let := hne
    exact { (exchangeStructure_iff G c).mpr hs with connected := ⟨hconnected⟩ }

/-- The independent Theorem B is discharged by the project theorem, with no extra assumptions. -/
theorem theoremB_verified : SeifertStatement.TheoremB.{u, w} := by
  intro V W _ _ G c h
  let := Seifert.theoremB ((exchangeComplex_iff G c).mpr h)
  exact (realizationHomeomorph G).symm.contractibleSpace

end SeifertAudit
