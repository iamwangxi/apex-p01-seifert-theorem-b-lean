/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.Exchange
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Data.Prod.Lex

/-! Lemma 2.2: lexicographic refinement breaks ties while preserving N2. -/

noncomputable section
universe u w
namespace Seifert
variable {V : Type u} {W : Type w} [LinearOrder W] [WellFoundedLT W]

/-- The arbitrary auxiliary well order is used only inside old complexity fibres. -/
def tieComplexity [LinearOrder V] (c : V → W) (v : V) : W ×ₗ V := toLex (c v, v)

omit [LinearOrder W] [WellFoundedLT W] in
theorem tieComplexity_injective [LinearOrder V] (c : V → W) :
    Function.Injective (tieComplexity c) := by
  intro a b he
  exact congrArg (fun p : W ×ₗ V => (ofLex p).2) he

/-- Pulling back the refined strict order gives a well order on the vertices themselves. -/
theorem tieComplexity_wellOrdersVertices [LinearOrder V] [WellFoundedLT V] (c : V → W) :
    IsWellOrder V (fun u v => tieComplexity c u < tieComplexity c v) :=
  (tieComplexity_injective c).isWellOrder ((· < ·) : W ×ₗ V → W ×ₗ V → Prop)

theorem tieComplexity_exchangeStructure [LinearOrder V] [WellFoundedLT V]
    {G : SimpleGraph V} {c : V → W} (h : ExchangeStructure G c) :
    ExchangeStructure G (tieComplexity c) := by
  refine ⟨h.n1, ?_⟩
  intro u v huv
  obtain ⟨x, hx, hcx⟩ := h.n2 u v huv
  refine ⟨x, hx, ?_⟩
  rcases lt_max_iff.mp hcx with hu | hv
  · exact lt_of_lt_of_le (Prod.Lex.toLex_lt_toLex.mpr (Or.inl hu)) (le_max_left _ _)
  · exact lt_of_lt_of_le (Prod.Lex.toLex_lt_toLex.mpr (Or.inl hv)) (le_max_right _ _)

/-- Lemma 2.2, even without nonemptiness or connectedness of the graph.
The resulting codomain is a lexicographic product of two well orders. -/
theorem ties_may_be_broken {G : SimpleGraph V} {c : V → W}
    (h : ExchangeStructure G c) :
    ∃ order : LinearOrder V, letI := order;
      ∃ wf : WellFoundedLT V, letI := wf;
        ∃ d : V → W ×ₗ V, Function.Injective d ∧ ExchangeStructure G d := by
  obtain ⟨order, wf⟩ := exists_wellFoundedLT V
  let := order
  let := wf
  exact ⟨order, wf, tieComplexity c, tieComplexity_injective c,
    tieComplexity_exchangeStructure h⟩

/-- The same graph, with all exchange-complex data retained. -/
theorem exchangeComplex_ties_may_be_broken {G : SimpleGraph V} {c : V → W}
    (h : ExchangeComplex G c) :
    ∃ order : LinearOrder V, letI := order;
      ∃ wf : WellFoundedLT V, letI := wf;
        ∃ d : V → W ×ₗ V, InjectiveExchangeComplex G d := by
  obtain ⟨order, wf, d, hd, hs⟩ := ties_may_be_broken h.toExchangeStructure
  let := order
  let := wf
  exact ⟨order, wf, d, { hs with connected := h.connected, injective := hd }⟩

end Seifert
