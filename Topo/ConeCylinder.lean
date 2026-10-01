/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.ConeRelative
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Tactic

/-! A cone in the same ambient vertex type, and its cylinder quotient model. -/

noncomputable section
open Topology Convexity

namespace Topo.Complex
universe u
variable {V : Type u}
local instance t5ModelDecidableEq : DecidableEq V := Classical.decEq V

@[ext] theorem ext_faces {K M : Topo.Complex V} (h : K.faces = M.faces) : K = M := by
  cases K
  cases M
  cases h
  rfl

/-- Adjoin an apex `a`. Freshness is imposed by the theorems, not the definition. -/
def coneAt (L : Topo.Complex V) (a : V) : Topo.Complex V where
  faces := {s | s.erase a ∈ L.faces}
  empty_mem := by classical simpa using L.empty_mem
  downward := by
    classical
    intro s t hst ht
    exact L.downward (Finset.erase_subset_erase a hst) ht

@[simp] theorem mem_coneAt (L : Topo.Complex V) (a : V) (s : Finset V) :
    s ∈ (L.coneAt a).faces ↔ s.erase a ∈ L.faces := Iff.rfl

theorem subset_coneAt (L : Topo.Complex V) (a : V) :
    L.faces ⊆ (L.coneAt a).faces := by
  classical
  exact fun s hs ↦ L.downward (Finset.erase_subset a s) hs

theorem coneAt_isConeVertex (L : Topo.Complex V) (a : V) :
    (L.coneAt a).IsConeVertex a := by
  classical
  intro s hs
  simpa using hs

/-- A vertex is fresh precisely when it occurs in no face. -/
def Fresh (L : Topo.Complex V) (a : V) : Prop := {a} ∉ L.faces

theorem Fresh.not_mem {L : Topo.Complex V} {a : V} (ha : L.Fresh a)
    {s : Finset V} (hs : s ∈ L.faces) : a ∉ s := by
  classical
  intro has
  exact ha (L.downward (Finset.singleton_subset_iff.mpr has) hs)

theorem Fresh.coordinate_zero {L : Topo.Complex V} {a : V} (ha : L.Fresh a)
    (x : L.Realization) : x.1.weights a = 0 :=
  Finsupp.notMem_support_iff.mp (ha.not_mem x.2)

/-- The cylinder map: time zero is the base and time one is the apex. -/
def coneCylinder (L : Topo.Complex V) (a : V)
    (p : L.Realization × unitInterval) : (L.coneAt a).Realization :=
  (L.coneAt a).contraction (L.coneAt_isConeVertex a)
    (inclusion (L.subset_coneAt a) p.1, p.2)

@[fun_prop] theorem continuous_coneCylinder (L : Topo.Complex V) (a : V) :
    Continuous (L.coneCylinder a) :=
  ((L.coneAt a).continuous_contraction (L.coneAt_isConeVertex a)).comp
    ((continuous_inclusion (L.subset_coneAt a)).comp continuous_fst |>.prodMk continuous_snd)

@[simp] theorem coneCylinder_zero (L : Topo.Complex V) (a : V) (x : L.Realization) :
    L.coneCylinder a (x, 0) = inclusion (L.subset_coneAt a) x :=
  (L.coneAt a).contraction_zero _ _

@[simp] theorem coneCylinder_one (L : Topo.Complex V) (a : V) (x : L.Realization) :
    L.coneCylinder a (x, 1) = (L.coneAt a).vertex a
      (L.coneAt_isConeVertex a).singleton_mem :=
  (L.coneAt a).contraction_one _ _

theorem coneCylinder_coordinate {L : Topo.Complex V} {a : V} (ha : L.Fresh a)
    (x : L.Realization) (s : unitInterval) :
    (L.coneCylinder a (x, s)).1.weights a = s := by
  classical
  simp [coneCylinder, contraction, line_weights, ha.coordinate_zero x]

/-- Delete one coordinate and renormalize the remaining mass. -/
def awayFrom (w : StdSimplex ℝ V) (a : V) (h : w.weights a < 1) : StdSimplex ℝ V where
  weights := (1 - w.weights a)⁻¹ • w.weights.erase a
  nonneg := by
    classical
    intro v
    simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    apply mul_nonneg (inv_nonneg.mpr (by linarith))
    rw [Finsupp.erase_apply]
    split_ifs <;> simp
  total := by
    classical
    have he : (w.weights.erase a).sum (fun _ r ↦ r) = 1 - w.weights a := by
      have ht := Finsupp.add_sum_erase' w.weights a (fun _ r ↦ r) (fun _ ↦ rfl)
      rw [w.total] at ht
      linarith
    change ((1 - w.weights a)⁻¹ • w.weights.erase a).sum (fun _ r ↦ r) = 1
    rw [Finsupp.sum_smul_index (fun _ ↦ rfl)]
    change (∑ v ∈ (w.weights.erase a).support,
      (1 - w.weights a)⁻¹ * (w.weights.erase a) v) = 1
    rw [← Finset.mul_sum]
    change (1 - w.weights a)⁻¹ * (w.weights.erase a).sum (fun _ r ↦ r) = 1
    rw [he]
    exact inv_mul_cancel₀ (by linarith)

theorem support_awayFrom_subset (w : StdSimplex ℝ V) (a : V) (h : w.weights a < 1) :
    (awayFrom w a h).weights.support ⊆ w.weights.support.erase a := by
  classical
  exact Finsupp.support_smul.trans (by simp)

theorem line_awayFrom (w : StdSimplex ℝ V) (a : V) (h : w.weights a < 1) :
    line (awayFrom w a h) a ⟨w.weights a, w.weights_nonneg a, w.weights_apply_le_one a⟩ = w := by
  classical
  apply StdSimplex.ext
  ext v
  rw [line_weights]
  simp only [awayFrom, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Finsupp.erase_apply]
  by_cases hv : v = a
  · subst v
    simp
  · simp [hv, Finsupp.single_eq_of_ne hv]
    field_simp [show 1 - w.weights a ≠ 0 by linarith]

theorem eq_single_of_coordinate_one (w : StdSimplex ℝ V) (a : V)
    (h : w.weights a = 1) : w = .single a := by
  classical
  apply eq_single_of_support_subset w a
  intro v hv
  by_contra hn
  have hva : v ≠ a := by simpa using hn
  have hs : w.weights a + w.weights v ≤ 1 := by
    rw [← w.total]
    have he : ∑ i ∈ ({a, v} : Finset V), w.weights i = w.weights a + w.weights v := by
      simp [Ne.symm hva]
    rw [← he]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl
          · simp [Finsupp.mem_support_iff, h]
          · exact hv)
      (fun i _ _ ↦ w.weights_nonneg i)
  have hp : 0 < w.weights v := lt_of_le_of_ne (w.weights_nonneg v)
    (Ne.symm (Finsupp.mem_support_iff.mp hv))
  simpa [h] using (show False by linarith)

theorem coneCylinder_surjective (L : Topo.Complex V) (a : V)
    [Nonempty L.Realization] : Function.Surjective (L.coneCylinder a) := by
  intro x
  by_cases hx : x.1.weights a = 1
  · refine ⟨(Classical.arbitrary L.Realization, 1), ?_⟩
    rw [coneCylinder_one]
    exact Subtype.ext (eq_single_of_coordinate_one x.1 a hx).symm
  · have hlt := lt_of_le_of_ne (x.1.weights_apply_le_one a) hx
    let y : L.Realization := ⟨awayFrom x.1 a hlt,
      L.downward (support_awayFrom_subset x.1 a hlt) x.2⟩
    refine ⟨(y, ⟨x.1.weights a, x.1.weights_nonneg a, x.1.weights_apply_le_one a⟩), ?_⟩
    exact Subtype.ext (line_awayFrom x.1 a hlt)

/-- Each closed cone simplex is covered by a compact base simplex times `I`. -/
theorem face_subset_cylinder_range (L : Topo.Complex V) (a : V)
    (s : (L.coneAt a).Face) (t : L.Face) (ht : t.1.Nonempty)
    (hst : s.1.erase a ⊆ t.1) :
    Set.range ((L.coneAt a).faceInclusion s) ⊆
      Set.range (fun p : StdSimplex ℝ t.1 × unitInterval ↦
        L.coneCylinder a (L.faceInclusion t p.1, p.2)) := by
  rintro x ⟨w, rfl⟩
  let x := (L.coneAt a).faceInclusion s w
  by_cases hx : x.1.weights a = 1
  · obtain ⟨b, hb⟩ := ht
    refine ⟨(.single ⟨b, hb⟩, 1), ?_⟩
    change L.coneCylinder a (L.faceInclusion t (.single ⟨b, hb⟩), 1) = x
    rw [coneCylinder_one]
    exact Subtype.ext (eq_single_of_coordinate_one x.1 a hx).symm
  · have hlt := lt_of_le_of_ne (x.1.weights_apply_le_one a) hx
    have hy : (awayFrom x.1 a hlt).weights.support ⊆ t.1 :=
      (support_awayFrom_subset x.1 a hlt).trans
        ((Finset.erase_subset_erase a (support_map_val_subset s.1 w)).trans hst)
    let y : L.Realization := ⟨awayFrom x.1 a hlt, L.downward hy t.2⟩
    obtain ⟨z, hz⟩ := (L.mem_range_faceInclusion t y).mpr hy
    refine ⟨(z, ⟨x.1.weights a, x.1.weights_nonneg a, x.1.weights_apply_le_one a⟩), ?_⟩
    change L.coneCylinder a (L.faceInclusion t z,
      ⟨x.1.weights a, x.1.weights_nonneg a, x.1.weights_apply_le_one a⟩) = x
    rw [hz]
    exact Subtype.ext (line_awayFrom x.1 a hlt)

/-- The weak cone really is the cylinder with its top collapsed, for nonempty base.
No local finiteness or local compactness of the base is required. -/
theorem isQuotientMap_coneCylinder (L : Topo.Complex V) (a : V)
    [Nonempty L.Realization] : IsQuotientMap (L.coneCylinder a) := by
  rw [isQuotientMap_iff_isClosed]
  refine ⟨L.coneCylinder_surjective a, fun A ↦ ⟨fun h ↦
    h.preimage (L.continuous_coneCylinder a), fun h ↦ ?_⟩⟩
  rw [(L.coneAt a).isClosed_iff]
  intro s
  let b := Classical.arbitrary L.Realization
  let t : L.Face := if hs : (s.1.erase a).Nonempty then ⟨s.1.erase a, s.2⟩
    else ⟨b.1.weights.support, b.2⟩
  have ht : t.1.Nonempty := by
    dsimp [t]
    split_ifs with hs
    · exact hs
    · exact b.1.support_weights_nonempty
  have hst : s.1.erase a ⊆ t.1 := by
    dsimp [t]
    split_ifs with hs
    · exact Finset.Subset.refl _
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.empty_subset]
  let q : StdSimplex ℝ t.1 × unitInterval → (L.coneAt a).Realization :=
    fun p ↦ L.coneCylinder a (L.faceInclusion t p.1, p.2)
  have hc : Continuous q := (L.continuous_coneCylinder a).comp
    ((L.continuous_faceInclusion t).comp continuous_fst |>.prodMk continuous_snd)
  have hclosed : IsClosed (q ⁻¹' A) := h.preimage
    ((L.continuous_faceInclusion t).comp continuous_fst |>.prodMk continuous_snd)
  have he : (L.coneAt a).faceInclusion s ⁻¹' A =
      (L.coneAt a).faceInclusion s ⁻¹' (q '' (q ⁻¹' A)) := by
    ext w
    constructor
    · intro hw
      obtain ⟨p, hp⟩ := L.face_subset_cylinder_range a s t ht hst ⟨w, rfl⟩
      change q p = (L.coneAt a).faceInclusion s w at hp
      exact ⟨p, by simpa [hp] using hw, hp⟩
    · rintro ⟨p, hp, he⟩
      simpa [← he] using hp
  rw [he]
  exact (hc.isClosedMap _ hclosed).preimage ((L.coneAt a).continuous_faceInclusion s)

/-- Apart from the collapsed top, the cylinder map has singleton fibres. -/
theorem coneCylinder_fibre {L : Topo.Complex V} {a : V} (ha : L.Fresh a)
    {x y : L.Realization} {s r : unitInterval}
    (h : L.coneCylinder a (x, s) = L.coneCylinder a (y, r)) :
    s = r ∧ (s = 1 ∨ x = y) := by
  have hsr : s = r := by
    apply Subtype.ext
    simpa only [coneCylinder_coordinate ha] using
      congrArg (fun z : (L.coneAt a).Realization ↦ z.1.weights a) h
  subst r
  refine ⟨rfl, ?_⟩
  by_cases hs : s = 1
  · exact Or.inl hs
  · right
    have hn : 1 - (s : ℝ) ≠ 0 := by
      intro he
      apply hs
      apply Subtype.ext
      change (s : ℝ) = 1
      linarith
    apply Subtype.ext
    apply StdSimplex.ext
    ext v
    have hv := congrArg (fun z : (L.coneAt a).Realization ↦ z.1.weights v) h
    change (line x.1 a s).weights v = (line y.1 a s).weights v at hv
    simp only [line_weights, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at hv
    exact (mul_left_cancel₀ hn) (add_right_cancel hv)

end Topo.Complex
