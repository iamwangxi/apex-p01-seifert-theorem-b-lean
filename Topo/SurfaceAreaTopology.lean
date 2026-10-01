/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.SurfaceFiniteness

/-!
# The topological part of Lemma 4.8(ii)

The finite bounded intersections proved from Lemma 4.8(i) imply that each set of
attained area values is closed in the real line and has the discrete subspace
topology. Neither conclusion needs positivity or injectivity of area. With positive
areas, the final theorem states both conclusions in the positive-real subspace.
-/

noncomputable section
universe u
namespace SeifertApplicationStatement
variable {V : Type u} {g : V → ℕ} {A : V → ℝ}

/-- Lemma 4.8(ii): the attained areas of a fixed genus form a closed set in `ℝ`.
Around any real point, the values below that point plus one form a finite closed set. -/
theorem areaValues_isClosed (hf : FiniteFibres g A) (h : ℕ) :
    IsClosed (AreaValues g A h) := by
  apply isOpen_compl_iff.mp
  rw [isOpen_iff_mem_nhds]
  intro x hx
  refine Filter.mem_of_superset
    ((isOpen_Iio.sdiff (areaValues_finite_Iic hf h (x + 1)).isClosed).mem_nhds
      ⟨lt_add_one x, fun ht => hx ht.1⟩) ?_
  intro y hy hyW
  exact hy.2 ⟨hyW, show y ≤ x + 1 from le_of_lt hy.1⟩

/-- Lemma 4.8(ii): the usual subspace topology on the attained areas is discrete.
An open interval with the other finitely many bounded values removed isolates each value. -/
theorem areaValues_discreteTopology (hf : FiniteFibres g A) (h : ℕ) :
    DiscreteTopology (AreaValues g A h) := by
  apply discreteTopology_subtype_iff'.mpr
  intro x hx
  refine ⟨Set.Iio (x + 1) \ ((AreaValues g A h ∩ Set.Iic (x + 1)) \ {x}),
    isOpen_Iio.sdiff
      ((areaValues_finite_Iic hf h (x + 1)).subset Set.sdiff_subset).isClosed, ?_⟩
  ext y
  constructor
  · intro hy
    by_contra hne
    exact hy.1.2 ⟨⟨hy.2, show y ≤ x + 1 from le_of_lt hy.1.1⟩, hne⟩
  · intro hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact ⟨⟨lt_add_one y, fun ht => ht.2 rfl⟩, hx⟩

/-- Lemma 4.8(ii) in the paper's ambient space `ℝ_{>0}`. Positive area puts all
attained values in `Set.Ioi 0`; their preimage under the subtype inclusion is closed
and carries the discrete subspace topology inherited from that positive-real space. -/
theorem areaValues_closed_discrete_positive (hf : FiniteFibres g A)
    (hpos : ∀ v, 0 < A v) (h : ℕ) :
    AreaValues g A h ⊆ Set.Ioi 0 ∧
      IsClosed (((↑) : Set.Ioi (0 : ℝ) → ℝ) ⁻¹' AreaValues g A h) ∧
      DiscreteTopology (((↑) : Set.Ioi (0 : ℝ) → ℝ) ⁻¹' AreaValues g A h) := by
  refine ⟨?_, (areaValues_isClosed hf h).preimage continuous_subtype_val, ?_⟩
  · rintro a ⟨v, _, rfl⟩
    exact hpos v
  · have hd : IsDiscrete (AreaValues g A h) := ⟨areaValues_discreteTopology hf h⟩
    exact (hd.preimage continuous_subtype_val.continuousOn Subtype.val_injective).to_subtype

end SeifertApplicationStatement
