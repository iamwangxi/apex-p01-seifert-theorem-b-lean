/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.SurfaceFiniteness
import Topo.Audit.ApplicationStatements

/-!
# Conditional applications with Lemma 4.8(i) as the finiteness input

These conclusions use the independent statement's definitions, including its weak
topology and both graph distances. Only the well-foundedness premise is replaced:
positive area, connectedness and the exact Theorem 5.1(a)-(d) quantifiers are retained.
Flagness is represented by the finite clique complex, as in the original statements.

Theorem D adds no geometric proof. Section 6.3 supplies the link-version inputs and
ends by obtaining N1 and N2 "exactly as in the proof of Theorem A", then applying B.
The abstract application is polymorphic in the vertex type, so the same conditional
implication applies when those link-version geometric inputs are given.
-/

noncomputable section
universe u
namespace SeifertApplicationStatement
variable {V : Type u} {G : SimpleGraph V} {g : V → ℕ} {A : V → ℝ}

/-- The independent geometric premises with Lemma 4.8(i) in place of (iii).
No apex, descent, countability, order embedding or contractibility is assumed. -/
structure SurfaceSystemOfFiniteFibres (G : SimpleGraph V) (g : V → ℕ) (A : V → ℝ) : Prop where
  positive : ∀ v, 0 < A v
  connected : G.Connected
  finiteFibres : FiniteFibres g A
  outputs : ∀ x u w, G.Adj x u → G.Adj x w → G.edist u w = 2 →
    ∃ p q, Outputs G g A x u w p q

/-- Discharge precisely the original independent well-foundedness premise by (i). -/
theorem SurfaceSystemOfFiniteFibres.toSurfaceSystem (h : SurfaceSystemOfFiniteFibres G g A) :
    SurfaceSystem G g A :=
  ⟨h.positive, h.connected, values_wellFounded h.finiteFibres, h.outputs⟩

/-- Conditional Theorem A (§6.1), using Lemma 4.8(i); all other premises are unchanged. -/
theorem theoremA_of_finiteFibres (h : SurfaceSystemOfFiniteFibres G g A) :
    ContractibleSpace (WeakRealization G) :=
  SeifertApplicationAudit.theoremA_verified V G g A h.toSurfaceSystem

/-- Conditional Theorem C (§6.2), genus family, with the original nonempty condition. -/
theorem theoremC_genus_of_finiteFibres (h : SurfaceSystemOfFiniteFibres G g A)
    (ℓ : ℕ) (hne : ∃ v, g v ≤ ℓ) : FullConclusion G (GenusSet g ℓ) :=
  SeifertApplicationAudit.theoremC_genus_verified V G g A h.toSurfaceSystem ℓ hne

/-- Conditional Theorem C (§6.2), area bounded only in the top genus.
The cutoff may be any real number, and the truncated set must remain nonempty. -/
theorem theoremC_area_of_finiteFibres (h : SurfaceSystemOfFiniteFibres G g A)
    (ℓ : ℕ) (a₀ : ℝ) (hne : (AreaSet g A ℓ a₀).Nonempty) :
    FullConclusion G (AreaSet g A ℓ a₀) :=
  SeifertApplicationAudit.theoremC_area_verified V G g A h.toSurfaceSystem ℓ a₀ hne

/-- Conditional Theorem D (§6.3) in the independent model, assuming the link-version
connectedness, positive area, Lemma 4.8(i), and Theorem 5.1 outputs. The finite clique
complex models flagness. The link geometry establishing these premises is not proved. -/
theorem theoremD_of_finiteFibres (h : SurfaceSystemOfFiniteFibres G g A) :
    ContractibleSpace (WeakRealization G) :=
  theoremA_of_finiteFibres h

end SeifertApplicationStatement

namespace Seifert.Application
variable {V : Type u} {G : SimpleGraph V} {g : V → ℕ} {A : V → ℝ}

/-- Conditional Theorem D (§6.3), directly reusing Theorem A for arbitrary vertex types.
`h` means the corresponding link-version geometric inputs: positive relative area,
connectedness, well-founded attained values and Theorem 5.1(a)-(d). Flagness is modeled
by the clique complex. This alias proves no link geometry or identification of vertices. -/
theorem theoremD (h : SurfaceSystem G g A) :
    ContractibleSpace (Seifert.cliqueComplex G).Realization :=
  theoremA h

end Seifert.Application
