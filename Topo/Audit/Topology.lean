/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.Audit.Statements
import Topo.ExchangeSeven

/-! Independent adversarial topology sanity checks on the statement's own realization. -/
noncomputable section
open Topology Convexity
namespace AdversarialAudit
universe u

/-- This is proved directly from the independent statement's supremum, not assumed. -/
theorem statement_isOpen_iff {V : Type u} (G : SimpleGraph V)
    (A : Set (SeifertStatement.WeakRealization G)) :
    IsOpen A ↔ ∀ s : {s // s ∈ SeifertStatement.cliqueComplex G},
      IsOpen (SeifertStatement.closedSimplex G s ⁻¹' A) := by
  change IsOpen[⨆ s : {s // s ∈ SeifertStatement.cliqueComplex G},
    TopologicalSpace.coinduced (SeifertStatement.closedSimplex G s) inferInstance] A ↔ _
  simp only [isOpen_iSup_iff, isOpen_coinduced]

theorem statement_isClosed_iff {V : Type u} (G : SimpleGraph V)
    (A : Set (SeifertStatement.WeakRealization G)) :
    IsClosed A ↔ ∀ s : {s // s ∈ SeifertStatement.cliqueComplex G},
      IsClosed (SeifertStatement.closedSimplex G s ⁻¹' A) := by
  rw [← isOpen_compl_iff, statement_isOpen_iff]
  simp only [Set.preimage_compl, isOpen_compl_iff]

/-- Each closed-simplex parameter is a closed embedding, so preimages express
intersections. -/
theorem statement_closedSimplex_closedEmbedding {V : Type u} (G : SimpleGraph V)
    (s : {s // s ∈ SeifertStatement.cliqueComplex G}) :
    IsClosedEmbedding (SeifertStatement.closedSimplex G s) :=
  (Seifert.cliqueComplex G).isClosedEmbedding_faceInclusion s

/-- All realizations in the independent statement are Hausdorff. -/
theorem statement_hausdorff {V : Type u} (G : SimpleGraph V) :
    T2Space (SeifertStatement.WeakRealization G) :=
  (Seifert.cliqueComplex G).realizationT2Space

def statement_vertex {V : Type u} (G : SimpleGraph V) (v : V) :
    SeifertStatement.WeakRealization G :=
  ⟨StdSimplex.single v, by simp [SeifertStatement.cliqueComplex]⟩

theorem statement_vertex_injective {V : Type u} (G : SimpleGraph V) :
    Function.Injective (statement_vertex G) := by
  intro v w h
  exact StdSimplex.single_injective (congrArg Subtype.val h)

/-- A graph with no edges has a discrete realization, at every cardinality. -/
theorem edgeless_discrete (V : Type u) :
    DiscreteTopology (SeifertStatement.WeakRealization (⊥ : SimpleGraph V)) := by
  apply discreteTopology_iff_forall_isOpen.mpr
  intro A
  rw [statement_isOpen_iff]
  intro s
  have : Subsingleton s.1 := ⟨fun a b => Subtype.ext (by
    by_contra hne
    exact s.2 a.property b.property hne)⟩
  exact isOpen_discrete _

/-- Requested negative test: the realization of two isolated vertices is not contractible. -/
theorem two_isolated_not_contractible :
    ¬ ContractibleSpace (SeifertStatement.WeakRealization (⊥ : SimpleGraph (Fin 2))) := by
  intro h
  let := h
  let := edgeless_discrete (Fin 2)
  have := PreconnectedSpace.trivial_of_discrete
    (X := SeifertStatement.WeakRealization (⊥ : SimpleGraph (Fin 2)))
  have he := Subsingleton.elim
    (statement_vertex (⊥ : SimpleGraph (Fin 2)) 0) (statement_vertex ⊥ 1)
  exact (by decide : (0 : Fin 2) ≠ 1) (statement_vertex_injective ⊥ he)

/-- Requested positive test: a single edge has distinct endpoints. -/
theorem edge_endpoints_distinct :
    statement_vertex (⊤ : SimpleGraph (Fin 2)) 0 ≠ statement_vertex ⊤ 1 :=
  fun h => (by decide : (0 : Fin 2) ≠ 1) (statement_vertex_injective ⊤ h)

theorem edge_hausdorff :
    T2Space (SeifertStatement.WeakRealization (⊤ : SimpleGraph (Fin 2))) :=
  statement_hausdorff _

/-- Every barycentric point belongs to a simplex of the complete two-vertex graph. -/
def edgeSimplexEquiv :
    SeifertStatement.WeakRealization (⊤ : SimpleGraph (Fin 2)) ≃ StdSimplex ℝ (Fin 2) where
  toFun := Subtype.val
  invFun x := ⟨x, by simp [SeifertStatement.cliqueComplex]⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The inverse parametrization factors through the full finite closed simplex. -/
theorem edgeSimplexEquiv_continuous_inv : Continuous edgeSimplexEquiv.symm := by
  let s : {s // s ∈ SeifertStatement.cliqueComplex (⊤ : SimpleGraph (Fin 2))} :=
    ⟨Finset.univ, by simp [SeifertStatement.cliqueComplex]⟩
  let f : Fin 2 → s.1 := fun v => ⟨v, Finset.mem_univ v⟩
  have h : edgeSimplexEquiv.symm =
      SeifertStatement.closedSimplex ⊤ s ∘ StdSimplex.map f := by
    funext x
    apply Subtype.ext
    change x = (x.map f).map Subtype.val
    rw [StdSimplex.map_map]
    exact (StdSimplex.map_id x).symm
  rw [h]
  exact ((Seifert.cliqueComplex ⊤).continuous_faceInclusion s).comp
    (StdSimplex.continuous_map ℝ f)

def edgeSimplexHomeomorph :
    SeifertStatement.WeakRealization (⊤ : SimpleGraph (Fin 2)) ≃ₜ StdSimplex ℝ (Fin 2) where
  toEquiv := edgeSimplexEquiv
  continuous_toFun := by
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 2)).continuous_iff]
    exact continuous_pi fun v => (Seifert.cliqueComplex ⊤).continuous_coordinate v
  continuous_invFun := edgeSimplexEquiv_continuous_inv

/-- Stronger positive test: the edge is exactly the usual closed unit interval. -/
def edgeHomeomorphUnitInterval :
    SeifertStatement.WeakRealization (⊤ : SimpleGraph (Fin 2)) ≃ₜ unitInterval :=
  edgeSimplexHomeomorph.trans StdSimplex.homeomorphI

theorem edge_zero_mapped : edgeHomeomorphUnitInterval (statement_vertex ⊤ 0) = 0 :=
  StdSimplex.homeomorphI_single_zero

theorem edge_one_mapped : edgeHomeomorphUnitInterval (statement_vertex ⊤ 1) = 1 :=
  StdSimplex.homeomorphI_single_one

/-- Direct application of the actual independent predicate to the requested seven-vertex graph. -/
theorem seven_statement_exchange :
    SeifertStatement.ExchangeComplex Seifert.Seven.graph (id : Fin 7 → Fin 7) := by
  refine ⟨inferInstance, Seifert.Seven.connected.preconnected, ?_⟩
  refine ⟨?_, ?_⟩
  · intro u v hdist
    have htwo := (Seifert.distanceTwo_iff_edist Seifert.Seven.graph u v).mpr hdist
    exact ⟨Seifert.Seven.lowerApex u v, (Seifert.Seven.lowerApex_correct u v htwo).1⟩
  · intro u v hdist
    have htwo := (Seifert.distanceTwo_iff_edist Seifert.Seven.graph u v).mpr hdist
    exact ⟨Seifert.Seven.lowerApex u v, Seifert.Seven.lowerApex_correct u v htwo⟩

/-- At least one distance-two pair exists: N2 is not vacuous for this example. -/
theorem seven_distance_two : Seifert.Seven.graph.edist 1 3 = 2 := by
  rw [← Seifert.distanceTwo_iff_edist]
  exact ⟨by decide, by decide, ⟨2, by decide, by decide⟩⟩

theorem seven_lower_apex :
    SeifertStatement.IsApex Seifert.Seven.graph 1 3 2 ∧
      (2 : Fin 7) < max 1 3 := by
  change Seifert.IsApex Seifert.Seven.graph 1 3 2 ∧ _
  simpa [Seifert.Seven.lowerApex] using Seifert.Seven.lowerApex_correct 1 3
    ((Seifert.distanceTwo_iff_edist _ _ _).mpr seven_distance_two)

#print axioms statement_isOpen_iff
#print axioms statement_isClosed_iff
#print axioms statement_closedSimplex_closedEmbedding
#print axioms statement_hausdorff
#print axioms statement_vertex
#print axioms statement_vertex_injective
#print axioms edgeless_discrete
#print axioms two_isolated_not_contractible
#print axioms edge_endpoints_distinct
#print axioms edge_hausdorff
#print axioms edgeSimplexEquiv
#print axioms edgeSimplexEquiv_continuous_inv
#print axioms edgeSimplexHomeomorph
#print axioms edgeHomeomorphUnitInterval
#print axioms edge_zero_mapped
#print axioms edge_one_mapped
#print axioms seven_statement_exchange
#print axioms seven_distance_two
#print axioms seven_lower_apex
end AdversarialAudit
