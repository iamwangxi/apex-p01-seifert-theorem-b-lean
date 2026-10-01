/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.WeakRealization
import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Tactic.FunProp

/-!
# Cones are contractible in the weak topology

The global straight-line contraction is checked on each finite face times the
unit interval. Its image lies in the finite face obtained by adjoining the apex.
The parameterized final-topology criterion then proves joint continuity.
-/

noncomputable section

open Topology Convexity

namespace Topo.Complex

universe u
variable {V : Type u} (K : Topo.Complex V)

open Classical in
/-- Every face can be joined to `a`. -/
def IsConeVertex (a : V) : Prop := ∀ s ∈ K.faces, insert a s ∈ K.faces

lemma IsConeVertex.singleton_mem {a : V} (ha : K.IsConeVertex a) :
    {a} ∈ K.faces := by
  simpa using ha ∅ K.empty_mem

/-- A vertex viewed as a point of the realization. -/
def vertex (a : V) (ha : {a} ∈ K.faces) : K.Realization :=
  ⟨StdSimplex.single a, by simpa using ha⟩

/-- Straight-line interpolation toward a vertex in barycentric coordinates. -/
def line (w : StdSimplex ℝ V) (a : V) (t : unitInterval) : StdSimplex ℝ V :=
  convexCombPair (R := ℝ) (unitInterval.symm t) t
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) w (.single a)

lemma line_weights (w : StdSimplex ℝ V) (a : V) (t : unitInterval) :
    (line w a t).weights = (1 - (t : ℝ)) • w.weights + (t : ℝ) • Finsupp.single a 1 := by
  simp [line, StdSimplex.weights_convexCombPair, unitInterval.coe_symm_eq]

open Classical in
lemma support_line_subset (w : StdSimplex ℝ V) (a : V) (t : unitInterval) :
    (line w a t).weights.support ⊆ insert a w.weights.support := by
  rw [line, StdSimplex.weights_convexCombPair, StdSimplex.weights_single]
  refine Finsupp.support_add.trans (Finset.union_subset ?_ ?_)
  · exact Finsupp.support_smul.trans (Finset.subset_insert _ _)
  · exact Finsupp.support_smul.trans
      (Finsupp.support_single_subset.trans (by simp))

@[simp]
lemma line_zero (w : StdSimplex ℝ V) (a : V) : line w a 0 = w := by
  simp [line]

@[simp]
lemma line_one (w : StdSimplex ℝ V) (a : V) : line w a 1 = .single a := by
  simp [line]

@[simp]
lemma line_vertex (a : V) (t : unitInterval) :
    line (.single a) a t = .single a := by
  simp [line, convexCombPair_same]

open Classical in
/-- The straight-line contraction, with spatial variable first. -/
def contraction {a : V} (ha : K.IsConeVertex a) (p : K.Realization × unitInterval) :
    K.Realization :=
  ⟨line p.1.1 a p.2, K.downward (support_line_subset p.1.1 a p.2)
    (ha _ p.1.2)⟩

theorem contraction_weights {a : V} (ha : K.IsConeVertex a)
    (x : K.Realization) (t : unitInterval) :
    (K.contraction ha (x, t)).1.weights =
      (1 - (t : ℝ)) • x.1.weights + (t : ℝ) • Finsupp.single a 1 :=
  line_weights x.1 a t

@[simp]
lemma contraction_zero {a : V} (ha : K.IsConeVertex a) (x : K.Realization) :
    K.contraction ha (x, 0) = x := Subtype.ext (line_zero x.1 a)

@[simp]
lemma contraction_one {a : V} (ha : K.IsConeVertex a) (x : K.Realization) :
    K.contraction ha (x, 1) = K.vertex a ha.singleton_mem :=
  Subtype.ext (line_one x.1 a)

@[simp]
lemma contraction_vertex {a : V} (ha : K.IsConeVertex a) (t : unitInterval) :
    K.contraction ha (K.vertex a ha.singleton_mem, t) = K.vertex a ha.singleton_mem :=
  Subtype.ext (line_vertex a t)

open Classical in
/-- On a face `s`, the contraction factors through the finite simplex `insert a s`. -/
def faceLine (s : Finset V) (a : V) (p : StdSimplex ℝ s × unitInterval) :
    StdSimplex ℝ (insert a s : Finset V) :=
  line (p.1.map (fun v ↦ ⟨v.1, Finset.mem_insert_of_mem v.2⟩))
    ⟨a, Finset.mem_insert_self _ _⟩ p.2

open Classical in
lemma continuous_faceLine (s : Finset V) (a : V) : Continuous (faceLine s a) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (insert a s : Finset V)).continuous_iff]
  apply continuous_pi
  intro v
  simp only [Function.comp_def, faceLine, line, StdSimplex.weights_convexCombPair,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    unitInterval.coe_symm_eq]
  have hc : Continuous (fun p : StdSimplex ℝ s × unitInterval ↦
      (p.1.map (fun v ↦
        (⟨v.1, Finset.mem_insert_of_mem v.2⟩ : (insert a s : Finset V)))).weights v) :=
    (StdSimplex.continuous_weights_apply ℝ v).comp
      ((StdSimplex.continuous_map ℝ _).comp continuous_fst)
  fun_prop

open Classical in
lemma map_faceLine (s : Finset V) (a : V) (p : StdSimplex ℝ s × unitInterval) :
    (faceLine s a p).map (Subtype.val : ↥(insert a s : Finset V) → V) =
      line (p.1.map (Subtype.val : s → V)) a p.2 := by
  simpa [faceLine, line, StdSimplex.map_map] using
    (StdSimplex.isAffineMap_map ℝ (Subtype.val : ↥(insert a s : Finset V) → V)).map_convexCombPair
      (s := (unitInterval.symm p.2 : ℝ)) (t := (p.2 : ℝ))
      (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp)
      (p.1.map (fun v ↦ (⟨v.1, Finset.mem_insert_of_mem v.2⟩ : (insert a s : Finset V))))
      (.single ⟨a, Finset.mem_insert_self _ _⟩)

open Classical in
/-- Joint continuity on the actual product topology, using local compactness of `I`. -/
theorem continuous_contraction {a : V} (ha : K.IsConeVertex a) :
    Continuous (K.contraction ha) := by
  rw [K.continuous_prod_iff]
  intro s
  let s' : K.Face := ⟨insert a s.1, ha s.1 s.2⟩
  have h : (fun p : StdSimplex ℝ s.1 × unitInterval ↦
      K.contraction ha (K.faceInclusion s p.1, p.2)) =
      K.faceInclusion s' ∘ faceLine s.1 a := by
    funext p
    exact Subtype.ext (map_faceLine s.1 a p).symm
  rw [h]
  exact (K.continuous_faceInclusion s').comp (continuous_faceLine s.1 a)

/-- The explicit homotopy from the identity to the apex. -/
def contractionHomotopy {a : V} (ha : K.IsConeVertex a) :
    (ContinuousMap.id K.Realization).Homotopy
      (ContinuousMap.const K.Realization (K.vertex a ha.singleton_mem)) where
  toFun p := K.contraction ha (p.2, p.1)
  continuous_toFun := (K.continuous_contraction ha).comp continuous_swap
  map_zero_left := K.contraction_zero ha
  map_one_left := K.contraction_one ha

theorem contractible_of_coneVertex {a : V} (ha : K.IsConeVertex a) :
    ContractibleSpace K.Realization := by
  rw [contractible_iff_id_nullhomotopic]
  exact ⟨K.vertex a ha.singleton_mem, ⟨K.contractionHomotopy ha⟩⟩

/-- The abstract cone adds `none` as apex and uses `some v` for old vertices.
A set is a cone face exactly when its old vertices form a face of `K`. -/
def cone : Topo.Complex (Option V) where
  faces := {s | s.eraseNone ∈ K.faces}
  empty_mem := by simpa using K.empty_mem
  downward := by
    intro s t hst ht
    exact K.downward (Finset.eraseNone.monotone hst) ht

@[simp]
theorem mem_cone (s : Finset (Option V)) : s ∈ K.cone.faces ↔ s.eraseNone ∈ K.faces :=
  Iff.rfl

lemma eraseNone_insert_none [DecidableEq (Option V)] (s : Finset (Option V)) :
    (insert none s).eraseNone = s.eraseNone := by
  ext v
  simp

theorem cone_isConeVertex : K.cone.IsConeVertex none := by
  unfold IsConeVertex
  intro s hs
  simp only [cone, Set.mem_ofPred_eq] at hs ⊢
  simpa only [eraseNone_insert_none] using hs

open Classical in
@[simp]
theorem base_face_mem_cone (s : Finset V) : s.image some ∈ K.cone.faces ↔ s ∈ K.faces := by
  simp

open Classical in
@[simp]
theorem coned_face_mem_cone (s : Finset V) :
    insert none (s.image some) ∈ K.cone.faces ↔ s ∈ K.faces := by
  have h : (insert none (s.image some)).eraseNone = s := by ext v; simp
  simp [h]

/-- Any abstract simplicial complex has a contractible cone in the weak topology. -/
theorem contractible_cone : ContractibleSpace K.cone.Realization :=
  K.cone.contractible_of_coneVertex K.cone_isConeVertex

instance coneContractibleSpace : ContractibleSpace K.cone.Realization := K.contractible_cone

/-- The same theorem, directly accepting Mathlib's abstract complexes. -/
theorem contractible_cone_of_abstract (K : AbstractSimplicialComplex V) :
    ContractibleSpace (ofPreAbstract K.toPreAbstractSimplicialComplex).cone.Realization :=
  (ofPreAbstract K.toPreAbstractSimplicialComplex).contractible_cone

end Topo.Complex
