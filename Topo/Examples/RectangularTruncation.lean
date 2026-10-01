/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.Audit.ApplicationStatements
import Mathlib.Data.Fintype.Card

/-!
# The rectangular cutoff differs from the area family proved in §6.2

The path u—x—w has genera (1,0,1) and positive relative areas (1,2,1).
It satisfies every premise of the independent `SeifertApplicationStatement.SurfaceSystem`.
For ℓ = a₀ = 1 the introduction's literal rectangular set contains only u and w,
so its full subcomplex is disconnected. The lexicographic `AreaSet` used in §6.2
contains all three vertices and satisfies the conditional Theorem C conclusion.

This is a counterexample to deriving the literal rectangular conclusion from the
abstract premises used by the paper's proof. It is not a counterexample involving
actual knots or Seifert surfaces: no geometric realization of this system is asserted.
-/

noncomputable section
namespace Seifert.Application.RectangularTruncation

abbrev u : Fin 3 := 0
abbrev x : Fin 3 := 1
abbrev w : Fin 3 := 2

/-- The three-vertex path u—x—w. -/
def Adjacent (a b : Fin 3) : Prop := a.val + 1 = b.val ∨ b.val + 1 = a.val

instance (a b : Fin 3) : Decidable (Adjacent a b) := by unfold Adjacent; infer_instance

def graph : SimpleGraph (Fin 3) where
  Adj := Adjacent
  symm := ⟨by intro a b h; exact h.symm⟩
  loopless := ⟨by intro a h; unfold Adjacent at h; omega⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (Adjacent _ _))

def genus (v : Fin 3) : ℕ := if v = x then 0 else 1

def area (v : Fin 3) : ℝ := if v = x then 2 else 1

/-- These are precisely the requested numerical data, in path order. -/
theorem numerical_data :
    (genus u, genus x, genus w) = (1, 0, 1) ∧
    (area u, area x, area w) = (1, 2, 1) := by
  norm_num [genus, area, u, x, w]

/-- The only distance-two configuration, up to interchanging the endpoints. -/
theorem distance_two_configurations : ∀ m a b : Fin 3,
    graph.Adj m a → graph.Adj m b → graph.edist a b = 2 →
      m = x ∧ (a = u ∧ b = w ∨ a = w ∧ b = u) := by
  intro m a b hma hmb hab
  fin_cases m <;> fin_cases a <;> fin_cases b <;>
    simp_all [graph, Adjacent, u, x, w]

/-- The distance-two premise is actually attained. -/
theorem distance_two : graph.edist u w = 2 := by
  apply (Seifert.distanceTwo_iff_edist graph u w).mp
  exact ⟨by decide, by decide, ⟨x, by decide, by decide⟩⟩

/-- Both outputs are x, fixed before clause (b)'s universally quantified vertex. -/
theorem midpoint_outputs : ∀ m a b : Fin 3,
    graph.Adj m a → graph.Adj m b → graph.edist a b = 2 →
      SeifertApplicationStatement.Outputs graph genus area m a b x x := by
  intro m a b hma hmb hab
  obtain ⟨hm, he⟩ := distance_two_configurations m a b hma hmb hab
  have ha : SeifertApplicationStatement.EqAdj graph x m ∧
      SeifertApplicationStatement.EqAdj graph x a ∧
      SeifertApplicationStatement.EqAdj graph x b := by
    subst m
    exact ⟨Or.inl rfl, Or.inr hma, Or.inr hmb⟩
  have hb : ∀ z : Fin 3, SeifertApplicationStatement.EqAdj graph z x := by
    simp only [SeifertApplicationStatement.EqAdj]
    decide
  have hc : genus x + genus x < genus a + genus b := by
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  exact ⟨ha, ha, fun z _ _ => ⟨hb z, hb z⟩, le_of_lt hc,
    fun heq => False.elim ((Nat.ne_of_lt hc) heq)⟩

theorem positive : ∀ v, 0 < area v := by
  intro v
  fin_cases v <;> norm_num [area, x]

theorem connected : graph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨x, fun v => ?_⟩
  fin_cases v
  · exact (show graph.Adj x u by decide).reachable
  · exact SimpleGraph.Reachable.refl _
  · exact (show graph.Adj x w by decide).reachable

/-- The induced order on the actual values is well-founded because their range is finite. -/
theorem values_wellFounded :
    WellFounded ((· < ·) : SeifertApplicationStatement.Values genus area →
      SeifertApplicationStatement.Values genus area → Prop) := by
  let : Finite (SeifertApplicationStatement.Values genus area) :=
    (Set.finite_range (SeifertApplicationStatement.complexity genus area)).to_subtype
  exact wellFounded_lt

/-- All abstract geometric premises of the independent application statement. -/
theorem system : SeifertApplicationStatement.SurfaceSystem graph genus area :=
  ⟨positive, connected, values_wellFounded,
    fun m a b hma hmb hab => ⟨x, x, midpoint_outputs m a b hma hmb hab⟩⟩

/-- The introduction's literal set at ℓ = 1 and a₀ = 1. -/
def rectangle : Set (Fin 3) := {v | genus v ≤ 1 ∧ area v ≤ 1}

theorem rectangle_eq : rectangle = {u, w} := by
  ext v
  fin_cases v <;> norm_num [rectangle, genus, area, u, x, w]

theorem rectangle_nonempty : rectangle.Nonempty := by
  rw [rectangle_eq]
  exact ⟨u, by simp⟩

/-- The full induced graph on the rectangular cutoff has no edges. -/
theorem rectangle_induce_eq_bot : graph.induce rectangle = ⊥ := by
  ext a b
  have ha : a.val = u ∨ a.val = w := by
    simpa only [rectangle_eq, Set.mem_insert_iff, Set.mem_singleton_iff] using a.property
  have hb : b.val = u ∨ b.val = w := by
    simpa only [rectangle_eq, Set.mem_insert_iff, Set.mem_singleton_iff] using b.property
  change Adjacent a.val b.val ↔ False
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    norm_num [Adjacent, ha, hb, u, w]

theorem rectangle_not_connected : ¬ (graph.induce rectangle).Connected := by
  intro h
  let a : rectangle := ⟨u, by rw [rectangle_eq]; simp⟩
  let b : rectangle := ⟨w, by rw [rectangle_eq]; simp⟩
  have he : a = b := by
    simpa only [rectangle_induce_eq_bot, SimpleGraph.reachable_bot] using h a b
  have hv : u = w := congrArg Subtype.val he
  norm_num [u, w] at hv

theorem rectangle_not_fullConclusion :
    ¬ SeifertApplicationStatement.FullConclusion graph rectangle :=
  fun h => rectangle_not_connected h.1

/-- §6.2 keeps x because its genus is strictly below ℓ, despite its larger area. -/
theorem areaSet_eq_univ : SeifertApplicationStatement.AreaSet genus area 1 1 = Set.univ := by
  ext v
  fin_cases v <;> norm_num [SeifertApplicationStatement.AreaSet, genus, area, x]

/-- The independent conditional Theorem C applies to §6.2's area family. -/
theorem area_fullConclusion : SeifertApplicationStatement.FullConclusion graph
    (SeifertApplicationStatement.AreaSet genus area 1 1) := by
  apply SeifertApplicationAudit.theoremC_area_verified (Fin 3) graph genus area system 1 1
  rw [areaSet_eq_univ]
  exact ⟨x, Set.mem_univ x⟩

/-- A single witness separating the literal rectangular claim from the proved area claim. -/
theorem separation :
    SeifertApplicationStatement.SurfaceSystem graph genus area ∧
    rectangle.Nonempty ∧ ¬ (graph.induce rectangle).Connected ∧
    ¬ SeifertApplicationStatement.FullConclusion graph rectangle ∧
    SeifertApplicationStatement.AreaSet genus area 1 1 = Set.univ ∧
    SeifertApplicationStatement.FullConclusion graph
      (SeifertApplicationStatement.AreaSet genus area 1 1) :=
  ⟨system, rectangle_nonempty, rectangle_not_connected, rectangle_not_fullConclusion,
    areaSet_eq_univ, area_fullConclusion⟩

end Seifert.Application.RectangularTruncation
