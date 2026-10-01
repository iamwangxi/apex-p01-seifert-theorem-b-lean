/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.ExchangeContractible
import Topo.ExchangeSeven
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Data.Sum.Order
import Mathlib.SetTheory.Ordinal.Basic

/-! A finite application and a non-locally-finite example of order type ω + 1. -/
noncomputable section
open Topology Convexity
namespace Seifert

/-- The seven-vertex example is an actual application of the general Theorem B. -/
theorem seven_contractible : ContractibleSpace (cliqueComplex Seven.graph).Realization :=
  theoremB Seven.injectiveExchangeComplex.toExchangeComplex

theorem seven_nonempty : Nonempty (cliqueComplex Seven.graph).Realization :=
  ⟨(cliqueComplex Seven.graph).vertex 0 (singleton_cliqueComplex Seven.graph 0)⟩

namespace OmegaStar

/-- Natural-number leaves, one extra last leaf, and centre zero. -/
abbrev Vertex := WithTop ℕ

def graph : SimpleGraph Vertex := SimpleGraph.starGraph 0

theorem nonempty_realization : Nonempty (cliqueComplex graph).Realization :=
  ⟨(cliqueComplex graph).vertex 0 (singleton_cliqueComplex graph 0)⟩

/-- Nonvacuous exchange axioms: each pair of different noncentral leaves has apex zero. -/
theorem exchange : InjectiveExchangeComplex graph (id : Vertex → Vertex) := by
  have n2 : ∀ u v : Vertex, DistanceTwo graph u v →
      ∃ x, IsApex graph u v x ∧ x < max u v := by
    intro u v huv
    have hu : u ≠ 0 := fun he => huv.2.1
      (SimpleGraph.starGraph_adj.mpr ⟨huv.1, Or.inl he⟩)
    have hv : v ≠ 0 := fun he => huv.2.1
      (SimpleGraph.starGraph_adj.mpr ⟨huv.1, Or.inr he⟩)
    refine ⟨0, ⟨⟨SimpleGraph.starGraph_center_adj' hu.symm,
      SimpleGraph.starGraph_center_adj' hv.symm⟩, ?_⟩, ?_⟩
    · intro y hy
      have h := SimpleGraph.starGraph_adj.mp hy.1
      exact Or.inl ((h.2.resolve_left hu).symm)
    · exact lt_of_lt_of_le (by simpa using (bot_lt_iff_ne_bot.mpr hu)) (le_max_left u v)
  exact {
    n1 := n1_of_n2 graph id n2
    n2 := n2
    connected := SimpleGraph.connected_starGraph 0
    injective := Function.injective_id }

/-- The attained complexities have order type ω + 1, not merely an ordinal-valued label. -/
theorem complexity_orderType : Ordinal.type ((· < ·) : Vertex → Vertex → Prop) =
    Ordinal.omega0 + 1 := by
  let e : Vertex ≃o ℕ ⊕ₗ PUnit := WithTop.orderIsoSumLexPUnit
  let : WellFoundedLT (ℕ ⊕ₗ PUnit) := e.symm.toRelIsoLT.toRelEmbedding.wellFounded wellFounded_lt
  rw [e.toRelIsoLT.ordinalType_congr]
  change Ordinal.type (Sum.Lex ((· < ·) : ℕ → ℕ → Prop)
    ((· < ·) : PUnit → PUnit → Prop)) = _
  rw [Ordinal.type_sum_lex, Ordinal.type_nat_lt, Ordinal.type_eq_one_of_unique]

/-- A genuine distance-two pair, so N2 is not vacuous. -/
theorem distanceTwo_one_top : DistanceTwo graph (1 : Vertex) ⊤ := by
  refine ⟨by simp, ?_, ⟨0, ?_, ?_⟩⟩
  · simp [graph, SimpleGraph.starGraph_adj]
  · simp [graph]
  · simp [graph]

/-- The centre has infinitely many neighbours, hence the graph is not locally finite. -/
theorem infinite_neighbors : (graph.neighborSet 0).Infinite := by
  let f : ℕ → Vertex := fun n => ((n + 1 : ℕ) : Vertex)
  have hf : Function.Injective f := by
    intro n m h
    exact Nat.add_right_cancel (WithTop.coe_injective h)
  apply (Set.infinite_range_of_injective hf).mono
  rintro _ ⟨n, rfl⟩
  change (SimpleGraph.starGraph (0 : Vertex)).Adj 0 ((n + 1 : ℕ) : Vertex)
  rw [SimpleGraph.starGraph_adj_center_iff]
  exact_mod_cast Nat.zero_ne_add_one n

theorem not_locallyFinite : ¬ Nonempty graph.LocallyFinite := by
  rintro ⟨h⟩
  let := h
  exact infinite_neighbors (Set.toFinite (graph.neighborSet 0))

/-- The required application of Theorem B to this infinite example. -/
theorem contractible : ContractibleSpace (cliqueComplex graph).Realization :=
  theoremB exchange.toExchangeComplex


/-- No stage below the final leaf is last: this is a genuine limit, rather than a finite union. -/
theorem limit_stage_no_largest (u : Vertex) (hu : u < ⊤) :
    ∃ v : Vertex, v < ⊤ ∧ u < v := by
  obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hu)
  exact ⟨((n + 1 : ℕ) : Vertex), by simp, WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)⟩

/-- The stage before the last vertex is assembled by the finite-subcomplex
limit argument. -/
theorem limit_stage_contractible :
    ContractibleSpace ((cliqueComplex graph).strictSublevel id (⊤ : Vertex)).Realization := by
  let D : Set Vertex := {u | u < ⊤}
  have : Nonempty D := ⟨⟨0, by simp [D]⟩⟩
  have hD : D.Nonempty := ⟨0, by simp [D]⟩
  have hG := strictSublevel_injectiveExchangeComplex exchange (⊤ : Vertex) hD
  let : ContractibleSpace (cliqueComplex (graph.induce D)).Realization :=
    contractible_of_sublevels (graph.induce D) (fun u : D => u.val) (fun u =>
      injective_sublevel_contractible u.val D (graph.induce D) (fun u : D => u.val) hG u rfl)
  exact (fullInduceHomeomorph graph D).symm.contractibleSpace

/-- A separate proof explicitly uses the successor step after the infinite limit stage. -/
theorem successor_after_limit_contractible :
    ContractibleSpace (cliqueComplex graph).Realization := by
  let := limit_stage_contractible
  have hLne := descendingLink_nonempty exchange (⊤ : Vertex) (by
    intro hleast
    have h := hleast 0
    simp at h)
  have hG := descending_injectiveExchangeComplex exchange (⊤ : Vertex) hLne
  let : ContractibleSpace (cliqueComplex
      (graph.induce (DescendingLink graph id (⊤ : Vertex)))).Realization :=
    injective_exchangeComplex_contractible hG
  have hL : ContractibleSpace
      ((cliqueComplex graph).descendingLink id (⊤ : Vertex)).Realization := by
    rw [descendingLink_cliqueComplex]
    exact (fullInduceHomeomorph graph (DescendingLink graph id (⊤ : Vertex))).symm.contractibleSpace
  let := hL
  exact (cliqueComplex graph).contractible_of_largest_vertex (cliqueComplex_isFlag graph)
    id Function.injective_id ⊤ (singleton_cliqueComplex graph ⊤) (fun _ _ => le_top)

end OmegaStar
end Seifert
