/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.SurfaceSystem

/-! Conditional Theorem C, following §6.2: tie refinement, Corollary 2.3, Lemma 2.4(1), B. -/

noncomputable section
universe u w
namespace Seifert.Application
variable {V : Type u} {W : Type w} [LinearOrder W] [WellFoundedLT W]

omit [WellFoundedLT W] in
/-- Refining ties cannot reverse the old weak inequality. -/
theorem tie_le_original [LinearOrder V] {c : V → W} {u v : V}
    (h : Seifert.tieComplexity c u ≤ Seifert.tieComplexity c v) : c u ≤ c v := by
  rcases Prod.Lex.toLex_le_toLex.mp h with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

omit [WellFoundedLT W] in
/-- A union of old complexity fibres remains downward closed after Lemma 2.2. -/
theorem downward_tie [LinearOrder V] {c : V → W} {D : Set V}
    (hD : Seifert.DownwardClosed c D) :
    Seifert.DownwardClosed (Seifert.tieComplexity c) D := by
  intro u v hv huv
  exact hD hv (tie_le_original huv)

/-- Full subcomplex conclusion with both natural and extended edge distances. -/
def FullConclusion (G : SimpleGraph V) (D : Set V) : Prop :=
  (G.induce D).Connected ∧
    (∀ s t : D, (G.induce D).dist s t = G.dist s.val t.val) ∧
    (∀ s t : D, (G.induce D).edist s t = G.edist s.val t.val) ∧
    ContractibleSpace ((Seifert.cliqueComplex G).full D).Realization

/-- A nonempty downward full subcomplex, without an injectivity assumption on the old c. -/
theorem downward_fullConclusion {G : SimpleGraph V} {c : V → W}
    (h : Seifert.ExchangeComplex G c) {D : Set V}
    (hD : Seifert.DownwardClosed c D) (hne : D.Nonempty) : FullConclusion G D := by
  obtain ⟨order, wf⟩ := exists_wellFoundedLT V
  let := order
  let := wf
  let d := Seifert.tieComplexity c
  have hd : Seifert.InjectiveExchangeComplex G d :=
    { Seifert.tieComplexity_exchangeStructure h.toExchangeStructure with
      connected := h.connected
      injective := Seifert.tieComplexity_injective c }
  have hD' : Seifert.DownwardClosed d D := downward_tie hD
  have hi := Seifert.downward_injectiveExchangeComplex hd hD' hne
  let := Seifert.theoremB hi.toExchangeComplex
  exact ⟨hi.connected, Seifert.downward_dist_eq hd hD',
    Seifert.downward_edist_eq hd hD',
    (Seifert.fullInduceHomeomorph G D).symm.contractibleSpace⟩

variable {G : SimpleGraph V} {g : V → ℕ} {A : V → ℝ}

/-- Definition 4.1, genus truncation. -/
def GenusSet (g : V → ℕ) (ℓ : ℕ) : Set V := {v | g v ≤ ℓ}

/-- The second family as written in §6.2: the area cutoff only applies in top genus ℓ. -/
def AreaSet (g : V → ℕ) (A : V → ℝ) (ℓ : ℕ) (a₀ : ℝ) : Set V :=
  {v | g v < ℓ ∨ g v = ℓ ∧ A v ≤ a₀}

/-- Genus truncations are downward closed for the original attained complexity. -/
theorem genus_downward (ℓ : ℕ) : Seifert.DownwardClosed (value g A) (GenusSet g ℓ) := by
  intro u v hv huv
  exact le_trans (genus_le_of_complexity_le huv) hv

/-- The top-genus area cutoff is also downward closed, including equality of old complexity. -/
theorem area_downward (ℓ : ℕ) (a₀ : ℝ) :
    Seifert.DownwardClosed (value g A) (AreaSet g A ℓ a₀) := by
  intro u v hv huv
  have hg := genus_le_of_complexity_le huv
  rcases hv with hv | ⟨hv, ha⟩
  · exact Or.inl (lt_of_le_of_lt hg hv)
  · by_cases hu : g u < ℓ
    · exact Or.inl hu
    · have he : g u = g v := by omega
      exact Or.inr ⟨he.trans hv, le_trans (area_le_of_complexity_le huv he) ha⟩

omit [LinearOrder W] [WellFoundedLT W] in
/-- Conditional Theorem C, genus family, with precisely the explicit nonempty condition. -/
theorem theoremC_genus (h : SurfaceSystem G g A) (ℓ : ℕ) (hne : ∃ v, g v ≤ ℓ) :
    FullConclusion G (GenusSet g ℓ) := by
  let : WellFoundedLT (Values g A) := h.wellFounded
  exact downward_fullConclusion (exchangeComplex h) (genus_downward ℓ) hne

omit [LinearOrder W] [WellFoundedLT W] in
/-- Conditional Theorem C, §6.2's second family, whenever it is nonempty.
This conclusion works for any real cutoff; in particular for the paper's a₀ > 0. -/
theorem theoremC_area (h : SurfaceSystem G g A) (ℓ : ℕ) (a₀ : ℝ)
    (hne : (AreaSet g A ℓ a₀).Nonempty) : FullConclusion G (AreaSet g A ℓ a₀) := by
  let : WellFoundedLT (Values g A) := h.wellFounded
  exact downward_fullConclusion (exchangeComplex h) (area_downward ℓ a₀) hne

end Seifert.Application
