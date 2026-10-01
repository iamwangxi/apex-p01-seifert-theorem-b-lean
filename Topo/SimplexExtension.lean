/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Data.Fintype.Lattice
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Extending a nullhomotopic map on the boundary of a finite simplex

The simplex is exhibited as a quotient of its boundary times the unit interval.
No cellular or Whitehead theorem is used.
-/

noncomputable section
open Topology Convexity

namespace Topo.SimplexExtension
universe u v
variable {T : Type u}

def boundary : Set (StdSimplex ℝ T) := {w | ∃ i, w.weights i = 0}

theorem isClosed_boundary [Finite T] : IsClosed (boundary (T := T)) := by
  have he : boundary (T := T) = ⋃ i : T, {w : StdSimplex ℝ T | w.weights i = 0} := by
    ext w
    simp [boundary]
  rw [he]
  exact isClosed_iUnion_of_finite fun i ↦
    isClosed_eq (StdSimplex.continuous_weights_apply ℝ i) continuous_const

instance boundaryCompactSpace [Finite T] : CompactSpace (boundary (T := T)) :=
  isCompact_iff_compactSpace.mp isClosed_boundary.isCompact

instance simplexT2Space [Finite T] : T2Space (StdSimplex ℝ T) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ T).t2Space

section Nontrivial
variable [Fintype T] [Nontrivial T]

def center : StdSimplex ℝ T where
  weights := Finsupp.equivFunOnFinite.symm (fun _ ↦ (Fintype.card T : ℝ)⁻¹)
  nonneg _ := by simp
  total := by
    classical
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp [Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)]

@[simp] theorem center_weights (i : T) : (center (T := T)).weights i =
    (Fintype.card T : ℝ)⁻¹ := by simp [center]

theorem center_pos (i : T) : 0 < (center (T := T)).weights i := by
  simp [inv_pos, Nat.cast_pos, Fintype.card_pos]

omit [Fintype T] in
theorem boundary_nonempty : (boundary (T := T)).Nonempty := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne T
  refine ⟨StdSimplex.single i, j, ?_⟩
  simp [Ne.symm hij]

def coneMap (p : boundary (T := T) × unitInterval) : StdSimplex ℝ T :=
  convexCombPair (R := ℝ) (unitInterval.symm p.2) p.2
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) p.1.1 center

theorem coneMap_weights (p : boundary (T := T) × unitInterval) (i : T) :
    (coneMap p).weights i = (1 - (p.2 : ℝ)) * p.1.1.weights i +
      (p.2 : ℝ) * center.weights i := by
  simp [coneMap, StdSimplex.weights_convexCombPair, unitInterval.coe_symm_eq]

@[simp] theorem coneMap_zero (b : boundary (T := T)) : coneMap (b, 0) = b.1 := by
  simp [coneMap]

@[simp] theorem coneMap_one (b : boundary (T := T)) : coneMap (b, 1) = center := by
  simp [coneMap]

theorem continuous_coneMap : Continuous (coneMap (T := T)) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ T).continuous_iff]
  apply continuous_pi
  intro i
  simp only [Function.comp_def, coneMap_weights]
  exact (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
    ((StdSimplex.continuous_weights_apply ℝ i).comp
      (continuous_subtype_val.comp continuous_fst)) |>.add
    ((continuous_subtype_val.comp continuous_snd).mul continuous_const)

theorem coneMap_surjective : Function.Surjective (coneMap (T := T)) := by
  classical
  intro w
  obtain ⟨i, hi⟩ := Finite.exists_min (fun i : T ↦ w.weights i / center.weights i)
  let m : ℝ := w.weights i / center.weights i
  have hc (j : T) : 0 < (center (T := T)).weights j := center_pos j
  have hm0 : 0 ≤ m := div_nonneg (w.weights_nonneg i) (hc i).le
  have hmin (j : T) : m * center.weights j ≤ w.weights j := by
    exact (le_div_iff₀ (hc j)).mp (hi j)
  have hm1 : m ≤ 1 := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hmin j)
    simpa only [← Finset.mul_sum, StdSimplex.total_of_fintype, mul_one] using hsum
  by_cases hm : m = 1
  · obtain ⟨b, hb⟩ := boundary_nonempty (T := T)
    refine ⟨(⟨b, hb⟩, 1), ?_⟩
    rw [coneMap_one]
    apply StdSimplex.ext
    apply Finsupp.ext
    intro j
    have hle (k : T) : center.weights k ≤ w.weights k := by simpa [hm] using hmin k
    have heq := Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun k _ ↦ hle k)
    exact ((heq.mp (by simp)) j (Finset.mem_univ j))
  · have hmlt : m < 1 := lt_of_le_of_ne hm1 hm
    have hd : 0 < 1 - m := sub_pos.mpr hmlt
    let B : T → ℝ := fun j ↦ (w.weights j - m * center.weights j) / (1 - m)
    have hB0 (j : T) : 0 ≤ B j := div_nonneg (sub_nonneg.mpr (hmin j)) hd.le
    have hBsum : ∑ j, B j = 1 := by
      simp only [B, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
        StdSimplex.total_of_fintype, mul_one]
      exact div_self (ne_of_gt hd)
    obtain ⟨b, hb⟩ := (StdSimplex.range_toFun_comp_weights (R := ℝ) (X := T)).symm ▸
      (show B ∈ (⋂ j : T, {s : T → ℝ | 0 ≤ s j}) ∩ {s | ∑ j, s j = 1} from
        ⟨by simpa using hB0, hBsum⟩)
    have hbi : b.weights i = 0 := by
      have hmi : m * center.weights i = w.weights i := by
        exact div_mul_cancel₀ _ (ne_of_gt (hc i))
      have h := congr_fun hb i
      change b.weights i = B i at h
      rw [h]
      change (w.weights i - m * center.weights i) / (1 - m) = 0
      rw [hmi, sub_self, zero_div]
    refine ⟨(⟨b, ⟨i, hbi⟩⟩, ⟨m, hm0, hm1⟩), ?_⟩
    apply StdSimplex.ext
    apply Finsupp.ext
    intro j
    rw [coneMap_weights]
    change (1 - m) * b.weights j + m * center.weights j = w.weights j
    have hbj : b.weights j = B j := congr_fun hb j
    rw [hbj]
    dsimp [B]
    field_simp
    ring

theorem coneMap_fibers {p q : boundary (T := T) × unitInterval}
    (hpq : coneMap p = coneMap q) : p.2 = q.2 ∧ (p.2 = 1 ∨ p.1 = q.1) := by
  obtain ⟨i, hi⟩ := p.1.2
  obtain ⟨j, hj⟩ := q.1.2
  have he (k : T) := congrArg (fun w : StdSimplex ℝ T ↦ w.weights k) hpq
  simp only [coneMap_weights] at he
  have hpi := p.1.1.weights_nonneg j
  have hqj := q.1.1.weights_nonneg i
  have hci := center_pos (T := T) i
  have hcj := center_pos (T := T) j
  have ht0 := unitInterval.nonneg p.2
  have ht1 := unitInterval.le_one p.2
  have hu0 := unitInterval.nonneg q.2
  have hu1 := unitInterval.le_one q.2
  have ht : (p.2 : ℝ) = (q.2 : ℝ) := by
    have hei := he i
    have hej := he j
    rw [hi, mul_zero, zero_add] at hei
    rw [hj, mul_zero, zero_add] at hej
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hpi,
      mul_nonneg (sub_nonneg.mpr hu1) hqj]
  have htu : p.2 = q.2 := Subtype.ext ht
  refine ⟨htu, ?_⟩
  by_cases h : p.2 = 1
  · exact Or.inl h
  · right
    apply Subtype.ext
    apply StdSimplex.ext
    apply Finsupp.ext
    intro k
    have hk := he k
    rw [← ht] at hk
    have hne : 1 - (p.2 : ℝ) ≠ 0 := by
      intro hz
      apply h
      apply Subtype.ext
      change (p.2 : ℝ) = 1
      linarith
    exact (mul_left_cancel₀ hne) (by linarith)

theorem isQuotientMap_coneMap : IsQuotientMap (coneMap (T := T)) :=
  .of_surjective_continuous coneMap_surjective continuous_coneMap

end Nontrivial

variable {Y : Type v} [TopologicalSpace Y]

/-- A boundary map homotopic to a constant extends over the whole closed simplex. -/
theorem exists_extension [Finite T] (f : C(boundary (T := T), Y)) (hf : f.Nullhomotopic) :
    ∃ g : C(StdSimplex ℝ T, Y), ∀ b : boundary (T := T), g b.1 = f b := by
  classical
  let : Fintype T := Fintype.ofFinite T
  obtain ⟨y, ⟨H⟩⟩ := hf
  rcases subsingleton_or_nontrivial T with hT | hT
  · let := hT
    refine ⟨ContinuousMap.const _ y, ?_⟩
    rintro ⟨b, i, hi⟩
    simp at hi
  · let := hT
    let q : C(boundary (T := T) × unitInterval, StdSimplex ℝ T) :=
      ⟨coneMap, continuous_coneMap⟩
    let h : C(boundary (T := T) × unitInterval, Y) := H.toContinuousMap.comp
      ⟨Prod.swap, continuous_swap⟩
    have hfactor : Function.FactorsThrough h q := by
      intro p r hpr
      obtain ⟨ht, hapex | hb⟩ := coneMap_fibers hpr
      · change H (p.2, p.1) = H (r.2, r.1)
        rw [← ht, hapex]
        simp
      · congr 1
        exact Prod.ext hb ht
    refine ⟨isQuotientMap_coneMap.lift h hfactor, ?_⟩
    intro b
    have he := congrArg (fun k : C(boundary (T := T) × unitInterval, Y) ↦ k (b, 0))
      (isQuotientMap_coneMap.lift_comp h hfactor)
    change (isQuotientMap_coneMap.lift h hfactor) (coneMap (b, 0)) = H (0, b) at he
    rw [coneMap_zero] at he
    exact he.trans (H.map_zero_left b)

end Topo.SimplexExtension
