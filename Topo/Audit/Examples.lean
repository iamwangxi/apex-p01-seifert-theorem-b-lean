/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.Audit.Statements
import Topo.ExchangeSeven
import Topo.Examples.Exchange

/-! Audit the scope and degeneracy of the project's positive examples. -/
noncomputable section
open Topology Convexity
namespace AdversarialAudit

/-- Seven.graph itself is a cone; contractibility of this graph alone is an easy special case. -/
theorem seven_is_cone : (Seifert.cliqueComplex Seifert.Seven.graph).IsConeVertex 6 := by
  classical
  intro s hs
  simp only [Seifert.mem_cliqueComplex, Finset.coe_insert] at hs ⊢
  exact hs.insert (fun b _ hne => ⟨hne, Or.inl rfl⟩)

/-- The genuinely non-cone six-vertex descending graph satisfies the independent hypotheses. -/
theorem lower_six_statement_exchange :
    SeifertStatement.ExchangeComplex
      (Seifert.Seven.graph.induce (Seifert.DescendingLink Seifert.Seven.graph id 6))
      (fun u : Seifert.DescendingLink Seifert.Seven.graph id 6 => u.val) := by
  exact (SeifertAudit.exchangeComplex_iff _ _).mp
    Seifert.Seven.descendingLink_exchangeComplex.toExchangeComplex

theorem lower_six_not_cone :
    ¬ Seifert.HasConeVertex (Seifert.flagComplex
      (Seifert.Seven.graph.induce (Seifert.DescendingLink Seifert.Seven.graph id 6))) :=
  Seifert.Seven.descendingFlagComplex_not_cone

theorem lower_six_contractible :
    ContractibleSpace (SeifertStatement.WeakRealization
      (Seifert.Seven.graph.induce (Seifert.DescendingLink Seifert.Seven.graph id 6))) :=
  SeifertAudit.theoremB_verified _ _ _ _ lower_six_statement_exchange

/-- A single vertex is allowed; distance-two clauses are vacuous there by design. -/
theorem singleton_statement_exchange :
    SeifertStatement.ExchangeComplex (⊥ : SimpleGraph Unit) (fun _ : Unit => (0 : ℕ)) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · intro u v
    have he : u = v := Subsingleton.elim _ _
    subst v
    exact SimpleGraph.Reachable.refl _
  · have htwo : ∀ u v : Unit, ¬ (⊥ : SimpleGraph Unit).edist u v = 2 := by
      intro u v
      have he : u = v := Subsingleton.elim _ _
      subst v
      simp
    exact ⟨fun u v h => (htwo u v h).elim, fun u v h => (htwo u v h).elim⟩

/-- Empty W cannot make an actual exchange complex; the map c forces W nonempty. -/
theorem complexity_nonempty {V W : Type*} [LinearOrder W] [WellFoundedLT W]
    (G : SimpleGraph V) (c : V → W) (h : SeifertStatement.ExchangeComplex G c) :
    Nonempty W := by
  obtain ⟨v⟩ := h.1
  exact ⟨c v⟩

/-- The empty vertex set has no realization point, independent of any exchange axioms. -/
theorem empty_realization (G : SimpleGraph Empty) :
    IsEmpty (SeifertStatement.WeakRealization G) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨v, _⟩ := x.1.support_weights_nonempty
  exact Empty.elim v

theorem empty_not_contractible (G : SimpleGraph Empty) :
    ¬ ContractibleSpace (SeifertStatement.WeakRealization G) := by
  intro h
  let := h
  let := empty_realization G
  obtain ⟨x⟩ := (inferInstance : Nonempty (SeifertStatement.WeakRealization G))
  exact isEmptyElim x

/-- The exchange example’s non-locally-finite infinite star remains a cone as well. -/
theorem omega_star_is_cone :
    (Seifert.cliqueComplex Seifert.OmegaStar.graph).IsConeVertex 0 := by
  classical
  intro s hs
  simp only [Seifert.mem_cliqueComplex, Finset.coe_insert] at hs ⊢
  exact hs.insert (fun b _ hne => SimpleGraph.starGraph_adj.mpr ⟨hne, Or.inl rfl⟩)

#print axioms seven_is_cone
#print axioms lower_six_statement_exchange
#print axioms lower_six_not_cone
#print axioms lower_six_contractible
#print axioms singleton_statement_exchange
#print axioms complexity_nonempty
#print axioms empty_realization
#print axioms empty_not_contractible
#print axioms omega_star_is_cone
end AdversarialAudit
