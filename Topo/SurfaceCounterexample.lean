/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.SurfaceSystem
import Mathlib.Data.Fintype.Card
import Mathlib.Topology.Connected.Clopen

/-! Removing §4.1 connectedness really invalidates the contractibility conclusion. -/

noncomputable section
namespace Seifert.Application.DisconnectedTwo
open Topology Convexity

/-- Two isolated vertices. Nonemptiness is retained, only connectedness is removed. -/
def graph : SimpleGraph (Fin 2) := ⊥
def genus (_ : Fin 2) : ℕ := 0
def area (_ : Fin 2) : ℝ := 1

theorem positive : ∀ v, 0 < area v := by intro v; norm_num [area]

theorem values_wellFounded :
    WellFounded ((· < ·) : Values genus area → Values genus area → Prop) := by
  let : Finite (Values genus area) := (Set.finite_range (complexity genus area)).to_subtype
  exact wellFounded_lt

/-- All output requirements remain true because this graph has no adjacent pairs. -/
theorem hasOutputs : HasOutputs graph genus area := by
  intro x u w hxu
  exact False.elim hxu

theorem not_connected : ¬ graph.Connected := by
  intro h
  have he : (0 : Fin 2) = 1 := by
    simpa only [graph, SimpleGraph.reachable_bot] using h 0 1
  norm_num at he

/-- Each point is concentrated at one of the two isolated vertices. -/
theorem coordinate_dichotomy (x : (Seifert.cliqueComplex graph).Realization) :
    x.val.weights 0 = 0 ∨ x.val.weights 0 = 1 := by
  by_cases hz : x.val.weights 0 = 0
  · exact Or.inl hz
  · have h1 : x.val.weights 1 = 0 := by
      by_contra h1
      have hs : (x.val.weights.support : Set (Fin 2)).Subsingleton :=
        SimpleGraph.isClique_bot_iff.mp x.property
      have he : (0 : Fin 2) = 1 := hs (Finsupp.mem_support_iff.mpr hz)
        (Finsupp.mem_support_iff.mpr h1)
      norm_num at he
    have ht := x.val.total_fin_two
    exact Or.inr (by linarith)

/-- Two isolated realization points are not contractible, proved with the actual weak topology. -/
theorem not_contractible : ¬ ContractibleSpace (Seifert.cliqueComplex graph).Realization := by
  intro h
  let := h
  let K := Seifert.cliqueComplex graph
  let D : Set K.Realization := {x | x.val.weights 0 = 0}
  have hc0 : IsClosed D := isClosed_eq (K.continuous_coordinate 0) continuous_const
  have hc1 : IsClosed {x : K.Realization | x.val.weights 0 = 1} :=
    isClosed_eq (K.continuous_coordinate 0) continuous_const
  have hcomp : Dᶜ = {x : K.Realization | x.val.weights 0 = 1} := by
    ext x
    change (¬ x.val.weights 0 = 0) ↔ x.val.weights 0 = 1
    constructor
    · intro hn
      exact (coordinate_dichotomy x).resolve_left hn
    · intro he hz
      linarith
  have hco : IsClosed Dᶜ := by rw [hcomp]; exact hc1
  have hcl : IsClopen D := ⟨hc0, isClosed_compl_iff.mp hco⟩
  let p₀ : K.Realization := K.vertex 0 (Seifert.singleton_cliqueComplex graph 0)
  let p₁ : K.Realization := K.vertex 1 (Seifert.singleton_cliqueComplex graph 1)
  have hp₁ : p₁ ∈ D := by
    change (StdSimplex.single (1 : Fin 2) : StdSimplex ℝ (Fin 2)).weights 0 = 0
    norm_num [StdSimplex.single]
  have hu : D = Set.univ := hcl.eq_univ ⟨p₁, hp₁⟩
  have hp₀ : p₀ ∈ D := hu ▸ Set.mem_univ p₀
  change (StdSimplex.single (0 : Fin 2) : StdSimplex ℝ (Fin 2)).weights 0 = 0 at hp₀
  norm_num [StdSimplex.single] at hp₀

/-- All remaining premises, together with failure of Theorem A's conclusion. -/
theorem counterexample : Nonempty (Fin 2) ∧ (∀ v, 0 < area v) ∧
    WellFounded ((· < ·) : Values genus area → Values genus area → Prop) ∧
    HasOutputs graph genus area ∧
    ¬ ContractibleSpace (Seifert.cliqueComplex graph).Realization :=
  ⟨inferInstance, positive, values_wellFounded, hasOutputs, not_contractible⟩

end Seifert.Application.DisconnectedTwo
