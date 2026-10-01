/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Mathlib

/-! Self-contained conditional statements of Seifert's A and C; no project imports.
The surface geometry, minimal-area existence and Lemma 4.8 are explicit inputs.
The second family is precisely the set in §6.2. -/

noncomputable section
open Topology Convexity
universe u
namespace SeifertApplicationStatement
variable {V : Type u}

/-- Finite cliques, including the empty face (flagness models Lemma 4.3(1)). -/
def cliqueComplex (G : SimpleGraph V) : Set (Finset V) := {s | G.IsClique (s : Set V)}

/-- Barycentric realization of the flag complex. -/
def WeakRealization (G : SimpleGraph V) :=
  {x : StdSimplex ℝ V // x.weights.support ∈ cliqueComplex G}

/-- Inclusions of finite closed simplices. -/
def closedSimplex (G : SimpleGraph V) (s : {s // s ∈ cliqueComplex G})
    (x : StdSimplex ℝ s.1) : WeakRealization G :=
  ⟨x.map Subtype.val, s.2.subset (by
    intro v hv
    by_contra hn
    exact Finsupp.mem_support_iff.mp hv
      (Finsupp.mapDomain_of_notMem_range x.weights v (by simpa using hn)))⟩

/-- The weak topology, not a topology inherited from an infinite product. -/
instance weakTopology (G : SimpleGraph V) : TopologicalSpace (WeakRealization G) :=
  ⨆ s : {s // s ∈ cliqueComplex G},
    TopologicalSpace.coinduced (closedSimplex G s) inferInstance

/-- The full subcomplex on D in the original vertex type. -/
def fullComplex (G : SimpleGraph V) (D : Set V) : Set (Finset V) :=
  {s | G.IsClique (s : Set V) ∧ ∀ v ∈ s, v ∈ D}

/-- Its barycentric realization. -/
def FullRealization (G : SimpleGraph V) (D : Set V) :=
  {x : StdSimplex ℝ V // x.weights.support ∈ fullComplex G D}

/-- Full-subcomplex finite closed simplex inclusions. -/
def fullClosedSimplex (G : SimpleGraph V) (D : Set V)
    (s : {s // s ∈ fullComplex G D}) (x : StdSimplex ℝ s.1) : FullRealization G D := by
  have hs : (x.map (Subtype.val : s.1 → V)).weights.support ⊆ s.1 := by
    intro v hv
    by_contra hn
    exact Finsupp.mem_support_iff.mp hv
      (Finsupp.mapDomain_of_notMem_range x.weights v (by simpa using hn))
  exact ⟨x.map Subtype.val, s.2.1.subset (by exact_mod_cast hs),
    fun v hv => s.2.2 v (hs hv)⟩

/-- Again the weak topology of the full subcomplex itself. -/
instance fullWeakTopology (G : SimpleGraph V) (D : Set V) :
    TopologicalSpace (FullRealization G D) :=
  ⨆ s : {s // s ∈ fullComplex G D},
    TopologicalSpace.coinduced (fullClosedSimplex G D s) inferInstance

/-- Definition 4.7, with lexicographic order. -/
def complexity (g : V → ℕ) (A : V → ℝ) (v : V) : ℕ ×ₗ ℝ := toLex (g v, A v)

/-- W is exactly the set of actual values; its order is the subtype's induced order. -/
def Values (g : V → ℕ) (A : V → ℝ) := Set.range (complexity g A)

def EqAdj (G : SimpleGraph V) (u v : V) : Prop := u = v ∨ G.Adj u v

/-- Theorem 5.1(a)–(d), including its universally quantified (b). -/
structure Outputs (G : SimpleGraph V) (g : V → ℕ) (A : V → ℝ)
    (x u w p q : V) : Prop where
  a_up : EqAdj G p x ∧ EqAdj G p u ∧ EqAdj G p w
  a_down : EqAdj G q x ∧ EqAdj G q u ∧ EqAdj G q w
  b : ∀ z, EqAdj G z u → EqAdj G z w → EqAdj G z p ∧ EqAdj G z q
  c : g p + g q ≤ g u + g w
  d : g p + g q = g u + g w → A p + A q < A u + A w

/-- Geometric premises only. No exchange structure, apex, descent or contractibility is data. -/
structure SurfaceSystem (G : SimpleGraph V) (g : V → ℕ) (A : V → ℝ) : Prop where
  positive : ∀ v, 0 < A v
  connected : G.Connected -- §4.1: includes nonemptiness
  wellFounded : WellFounded ((· < ·) : Values g A → Values g A → Prop) -- Lemma 4.8(iii)
  outputs : ∀ x u w, G.Adj x u → G.Adj x w → G.edist u w = 2 →
    ∃ p q, Outputs G g A x u w p q -- fixed before z in (b)

/-- Definition 4.1. -/
def GenusSet (g : V → ℕ) (ℓ : ℕ) : Set V := {v | g v ≤ ℓ}

/-- §6.2: area is bounded only in genus ℓ. -/
def AreaSet (g : V → ℕ) (A : V → ℝ) (ℓ : ℕ) (a₀ : ℝ) : Set V :=
  {v | g v < ℓ ∨ g v = ℓ ∧ A v ≤ a₀}

/-- The edge-path isometry is stated in both natural and extended distances. -/
def FullConclusion (G : SimpleGraph V) (D : Set V) : Prop :=
  (G.induce D).Connected ∧
    (∀ s t : D, (G.induce D).dist s t = G.dist s.val t.val) ∧
    (∀ s t : D, (G.induce D).edist s t = G.edist s.val t.val) ∧
    ContractibleSpace (FullRealization G D)

/-- Conditional Theorem A. -/
def TheoremA : Prop := ∀ (V : Type u) (G : SimpleGraph V) (g : V → ℕ) (A : V → ℝ),
  SurfaceSystem G g A → ContractibleSpace (WeakRealization G)

/-- Conditional Theorem C, genus family, whenever it has a vertex. -/
def TheoremC_genus : Prop :=
  ∀ (V : Type u) (G : SimpleGraph V) (g : V → ℕ) (A : V → ℝ),
    SurfaceSystem G g A → ∀ ℓ : ℕ, (∃ v, g v ≤ ℓ) → FullConclusion G (GenusSet g ℓ)

/-- Conditional Theorem C, §6.2 area family, whenever nonempty. -/
def TheoremC_area : Prop :=
  ∀ (V : Type u) (G : SimpleGraph V) (g : V → ℕ) (A : V → ℝ),
    SurfaceSystem G g A → ∀ (ℓ : ℕ) (a₀ : ℝ),
      (AreaSet g A ℓ a₀).Nonempty → FullConclusion G (AreaSet g A ℓ a₀)

end SeifertApplicationStatement
