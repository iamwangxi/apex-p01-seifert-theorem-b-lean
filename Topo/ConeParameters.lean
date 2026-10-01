/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic

/-! Resolve the single corner singularity of a relative cone homotopy by a
compact graph. This avoids a local compactness assumption on the cone base. -/

noncomputable section
open Topology

namespace Topo.ConeParameters

def denominator (s t : unitInterval) : ℝ := 1 - s + (s : ℝ) * t

theorem denominator_nonneg (s t : unitInterval) : 0 ≤ denominator s t := by
  dsimp [denominator]
  have := s.2.2
  have := mul_nonneg s.2.1 t.2.1
  linarith

def parameter (s t : unitInterval) : unitInterval :=
  ⟨(s : ℝ) * t / denominator s t, by
    refine ⟨div_nonneg (mul_nonneg s.2.1 t.2.1) (denominator_nonneg s t), ?_⟩
    by_cases hd : denominator s t = 0
    · simp [hd]
    · apply (div_le_one (lt_of_le_of_ne (denominator_nonneg s t) (Ne.symm hd))).mpr
      dsimp [denominator]
      linarith [s.2.2]⟩

def height (s t : unitInterval) : unitInterval :=
  ⟨(s : ℝ) * (1 - t), by
    constructor
    · exact mul_nonneg s.2.1 (sub_nonneg.mpr t.2.2)
    · nlinarith [s.2.1, s.2.2, t.2.1, t.2.2]⟩

@[fun_prop] theorem continuous_height :
    Continuous (fun p : unitInterval × unitInterval ↦ height p.1 p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : unitInterval × unitInterval ↦ (p.1 : ℝ) * (1 - p.2))
  fun_prop

theorem parameter_equation (s t : unitInterval) :
    (parameter s t : ℝ) * denominator s t = (s : ℝ) * t := by
  by_cases hd : denominator s t = 0
  · have hz : (s : ℝ) * t = 0 := by
      have hm := mul_nonneg s.2.1 t.2.1
      dsimp [denominator] at hd
      linarith [s.2.2]
    simp [parameter, hd, hz]
  · exact div_mul_cancel₀ _ hd

theorem height_eq_one_of_denominator_zero {s t : unitInterval}
    (hd : denominator s t = 0) : height s t = 1 := by
  apply Subtype.ext
  have hm := mul_nonneg s.2.1 t.2.1
  dsimp [denominator] at hd
  change (s : ℝ) * (1 - t) = 1
  nlinarith [s.2.2]

@[simp] theorem parameter_zero_left (t : unitInterval) : parameter 0 t = 0 := by
  apply Subtype.ext
  simp [parameter]

@[simp] theorem parameter_zero_right (s : unitInterval) : parameter s 0 = 0 := by
  apply Subtype.ext
  simp [parameter]

@[simp] theorem parameter_one_right (s : unitInterval) : parameter s 1 = s := by
  apply Subtype.ext
  simp [parameter, denominator]

theorem parameter_one_left {t : unitInterval} (ht : t ≠ 0) : parameter 1 t = 1 := by
  apply Subtype.ext
  have ht' : (t : ℝ) ≠ 0 := fun h ↦ ht (Subtype.ext h)
  simp [parameter, denominator, ht']

@[simp] theorem height_zero_left (t : unitInterval) : height 0 t = 0 := by
  apply Subtype.ext
  simp [height]
@[simp] theorem height_zero_right (s : unitInterval) : height s 0 = s := by
  apply Subtype.ext
  simp [height]
@[simp] theorem height_one_right (s : unitInterval) : height s 1 = 0 := by
  apply Subtype.ext
  simp [height]

/-- Continuity after resolving the corner, on any compact Hausdorff source `X`.
The auxiliary coordinate is unconstrained only at the corner mapped to the apex. -/
theorem continuous_resolved {X Z : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TopologicalSpace Z]
    (Q : X × (unitInterval × unitInterval) → Z) (hQ : Continuous Q)
    (z : Z) (hQtop : ∀ x r, Q (x, r, 1) = z) :
    Continuous (fun p : X × (unitInterval × unitInterval) ↦
      Q (p.1, parameter p.2.1 p.2.2, height p.2.1 p.2.2)) := by
  let E : Set ((X × (unitInterval × unitInterval)) × unitInterval) :=
    {p | (p.2 : ℝ) * denominator p.1.2.1 p.1.2.2 =
      (p.1.2.1 : ℝ) * p.1.2.2}
  have hE : IsClosed E := by
    exact isClosed_eq (by dsimp only [denominator]; fun_prop) (by fun_prop)
  let : CompactSpace E := isCompact_iff_compactSpace.mp hE.isCompact
  let π : E → X × (unitInterval × unitInterval) := fun p ↦ p.1.1
  have hπc : Continuous π := continuous_fst.comp continuous_subtype_val
  have hπs : Function.Surjective π := by
    intro p
    exact ⟨⟨(p, parameter p.2.1 p.2.2), parameter_equation _ _⟩, rfl⟩
  apply (IsQuotientMap.of_surjective_continuous hπs hπc).continuous_iff.mpr
  have he : (fun p : E ↦ Q ((π p).1, parameter (π p).2.1 (π p).2.2,
      height (π p).2.1 (π p).2.2)) =
      (fun p : E ↦ Q (p.1.1.1, p.1.2, height p.1.1.2.1 p.1.1.2.2)) := by
    funext p
    by_cases hd : denominator p.1.1.2.1 p.1.1.2.2 = 0
    · simp only [π, height_eq_one_of_denominator_zero hd, hQtop]
    · have hr : parameter p.1.1.2.1 p.1.1.2.2 = p.1.2 := by
        apply Subtype.ext
        exact mul_right_cancel₀ hd ((parameter_equation _ _).trans p.2.symm)
      simp only [π, hr]
  change Continuous (fun p : E ↦ Q ((π p).1,
    parameter (π p).2.1 (π p).2.2, height (π p).2.1 (π p).2.2))
  rw [he]
  apply hQ.comp
  apply Continuous.prodMk
  · exact continuous_fst.comp (continuous_fst.comp continuous_subtype_val)
  · apply Continuous.prodMk
    · exact continuous_snd.comp continuous_subtype_val
    · exact continuous_height.comp
        (continuous_snd.comp (continuous_fst.comp continuous_subtype_val))

end Topo.ConeParameters
