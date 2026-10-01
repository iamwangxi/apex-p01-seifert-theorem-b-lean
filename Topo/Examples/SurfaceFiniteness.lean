/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.SurfaceFiniteness

/-! Regression for Lemma 4.8: infinitely many vertices, tied values, and negative area.
The ordinal bound and countability must not require positive area or injectivity. -/

noncomputable section
namespace SeifertApplicationStatement.FinitenessRegression

def genus (_ : ℕ × Bool) : ℕ := 0

def area (v : ℕ × Bool) : ℝ := v.1 - 1

/-- Each cutoff has finitely many vertices, despite infinitely many genus-zero vertices. -/
theorem finiteFibres : FiniteFibres genus area := by
  intro h a
  obtain ⟨m, hm⟩ := exists_nat_ge (a + 1)
  apply ((Set.finite_Iic m).prod (Set.finite_univ : (Set.univ : Set Bool).Finite)).subset
  rintro ⟨n, b⟩ ⟨_, ha⟩
  refine ⟨?_, Set.mem_univ b⟩
  change n ≤ m
  have hn : (n : ℝ) ≤ m := by
    change (n : ℝ) - 1 ≤ a at ha
    linarith
  exact_mod_cast hn

/-- The two Boolean labels give distinct vertices with exactly the same complexity. -/
theorem tied_values (n : ℕ) :
    (n, false) ≠ (n, true) ∧
      complexity genus area (n, false) = complexity genus area (n, true) := by
  exact ⟨by simp, rfl⟩

/-- Positivity is false, but the conclusions below still apply. -/
theorem negative_area : area (0, false) < 0 := by
  norm_num [area]

/-- The induced attained-value order embeds into omega squared. -/
def valuesEmbedding : Values genus area ↪o ℕ ×ₗ ℕ :=
  values_orderEmbedding finiteFibres

theorem wellFounded : WellFounded ((· < ·) : Values genus area → Values genus area → Prop) :=
  values_wellFounded finiteFibres

theorem countable_vertices : Countable (ℕ × Bool) :=
  vertices_countable finiteFibres

end SeifertApplicationStatement.FinitenessRegression
