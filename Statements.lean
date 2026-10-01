/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Mathlib

/-! Standalone statement of Seifert, §2. No project definitions are imported. -/
noncomputable section
open Topology Convexity
universe u w
namespace SeifertStatement
variable {V : Type u}

/-- Finite cliques, including the empty face: the flag complex of the graph. -/
def cliqueComplex (G : SimpleGraph V) : Set (Finset V) :=
  {s | G.IsClique (s : Set V)}

/-- Barycentric points with finite, nonnegative, total-one weights on a clique. -/
def WeakRealization (G : SimpleGraph V) :=
  {x : StdSimplex ℝ V // x.weights.support ∈ cliqueComplex G}

/-- Inclusion of each finite closed simplex with its usual simplex topology. -/
def closedSimplex (G : SimpleGraph V) (s : {s // s ∈ cliqueComplex G})
    (x : StdSimplex ℝ s.1) : WeakRealization G :=
  ⟨x.map Subtype.val, s.2.subset (by
    intro v hv
    by_contra hn
    exact Finsupp.mem_support_iff.mp hv
      (Finsupp.mapDomain_of_notMem_range x.weights v (by simpa using hn)))⟩

/-- Weak topology: the final topology of all finite closed simplices. -/
instance weakTopology (G : SimpleGraph V) : TopologicalSpace (WeakRealization G) :=
  ⨆ s : {s // s ∈ cliqueComplex G},
    TopologicalSpace.coinduced (closedSimplex G s) inferInstance

/-- The common-neighbour two-interval I(u,v). -/
def TwoInterval (G : SimpleGraph V) (u v : V) : Set V :=
  {x | G.Adj u x ∧ G.Adj v x}

/-- An apex belongs to I(u,v) and equals or is adjacent to every member. -/
def IsApex (G : SimpleGraph V) (u v x : V) : Prop :=
  x ∈ TwoInterval G u v ∧ ∀ y ∈ TwoInterval G u v, x = y ∨ G.Adj x y

variable {W : Type w} [LinearOrder W] [WellFoundedLT W]

/-- Definition 2.1. Distance is the actual extended graph distance; only distance two is used. -/
structure ExchangeStructure (G : SimpleGraph V) (c : V → W) [WellFoundedLT W] : Prop where
  n1 : ∀ u v, G.edist u v = 2 → ∃ x, IsApex G u v x
  n2 : ∀ u v, G.edist u v = 2 →
    ∃ x, IsApex G u v x ∧ c x < max (c u) (c v)

/-- Nonempty connected flag complex carrying an exchange structure.
The flag condition is built into the clique complex. -/
def ExchangeComplex (G : SimpleGraph V) (c : V → W) : Prop :=
  Nonempty V ∧ G.Preconnected ∧ ExchangeStructure G c

end SeifertStatement

namespace SeifertStatement
/-- Theorem B: every exchange complex, with its weak topology, is contractible. -/
def TheoremB : Prop :=
  ∀ (V : Type u) (W : Type w) [LinearOrder W] [WellFoundedLT W]
    (G : SimpleGraph V) (c : V → W),
      ExchangeComplex G c → ContractibleSpace (WeakRealization G)
end SeifertStatement
