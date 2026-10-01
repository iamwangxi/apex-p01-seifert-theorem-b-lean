/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.ExchangeFlag
import Topo.ExchangeHeredity

/-!
# The paper's seven-vertex example

The competition version only mentions the example at lines 119–121. Its edge list is supplied
by the local companion Kakimizu-arXiv-v2.txt, Proposition 7.3, lines 2863–2876 (also identical
in github-kakimizu.txt, lines 2285–2295). All finite checks below are kernel-checked `decide`.
-/

namespace Seifert.Seven

/-- Six hexagon edges, then three chords. The spokes to vertex 6 are added in `Adjacent`. -/
def baseEdges : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0), (0, 2), (2, 4), (4, 0)]

def Adjacent (u v : Fin 7) : Prop :=
  u ≠ v ∧ (u = 6 ∨ v = 6 ∨ (u.val, v.val) ∈ baseEdges ∨ (v.val, u.val) ∈ baseEdges)

instance (u v : Fin 7) : Decidable (Adjacent u v) := by unfold Adjacent; infer_instance

def graph : SimpleGraph (Fin 7) where
  Adj := Adjacent
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, by rcases h.2 with h | h | h | h <;> tauto⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (Adjacent _ _))

/-- The actual lower-apex table in v2, lines 2872–2874, including both orders of each pair. -/
def lowerApex (u v : Fin 7) : Fin 7 :=
  if (u = 0 ∧ v = 3) ∨ (u = 3 ∧ v = 0) ∨
      (u = 1 ∧ v = 3) ∨ (u = 3 ∧ v = 1) then 2
  else if (u = 3 ∧ v = 5) ∨ (u = 5 ∧ v = 3) then 4
  else 0

theorem lowerApex_correct : ∀ u v : Fin 7, DistanceTwo graph u v →
    IsApex graph u v (lowerApex u v) ∧ lowerApex u v < max u v := by
  simp only [DistanceTwo, IsApex, TwoInterval, Set.mem_ofPred_eq, Set.Nonempty]
  decide

/-- Exhaustive list from v2 line 2873; ordering each pair avoids duplicates. -/
theorem nonadjacent_pairs : ∀ u v : Fin 7, u < v →
    (¬ graph.Adj u v ↔ (u.val, v.val) ∈
      ([(0, 3), (1, 3), (1, 4), (1, 5), (2, 5), (3, 5)] : List (ℕ × ℕ))) := by
  decide

theorem exchangeStructure : ExchangeStructure graph (id : Fin 7 → Fin 7) := by
  have n2 : ∀ u v, DistanceTwo graph u v →
      ∃ x, IsApex graph u v x ∧ x < max u v := by
    intro u v huv
    exact ⟨lowerApex u v, lowerApex_correct u v huv⟩
  exact ⟨n1_of_n2 _ _ n2, n2⟩

theorem connected : graph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨6, fun v => ?_⟩
  by_cases hv : v = 6
  · subst v; exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable ⟨Ne.symm hv, Or.inl rfl⟩

theorem injectiveExchangeComplex : InjectiveExchangeComplex graph (id : Fin 7 → Fin 7) :=
  { exchangeStructure with connected := connected, injective := Function.injective_id }

theorem descendingLink_top : DescendingLink graph (id : Fin 7 → Fin 7) 6 =
    {v | v.val < 6} := by
  ext v
  simp only [DescendingLink, Set.mem_ofPred_eq]
  fin_cases v <;> decide

theorem descendingLink_nonempty :
    (DescendingLink graph (id : Fin 7 → Fin 7) 6).Nonempty :=
  ⟨0, by change graph.Adj 6 0 ∧ (0 : Fin 7) < 6; decide⟩

theorem descendingLink_exchangeComplex :
    InjectiveExchangeComplex (graph.induce (DescendingLink graph (id : Fin 7 → Fin 7) 6))
      (fun u : DescendingLink graph (id : Fin 7 → Fin 7) 6 => u.val) :=
  descending_injectiveExchangeComplex injectiveExchangeComplex 6 descendingLink_nonempty

theorem descendingLink_not_cone :
    ¬ IsConeOn graph (DescendingLink graph (id : Fin 7 → Fin 7) 6) := by
  simp only [IsConeOn, DescendingLink, Set.mem_ofPred_eq]
  decide

/-- The same failure for Mathlib's actual abstract complex, with the face-insertion definition. -/
theorem descendingFlagComplex_not_cone :
    ¬ HasConeVertex (flagComplex (graph.induce
      (DescendingLink graph (id : Fin 7 → Fin 7) 6))) := by
  rw [hasConeVertex_induce_iff]
  exact descendingLink_not_cone

/-- Exact face description of the descending link: all nonempty subfaces of four triangles. -/
def triangles : List (Finset (Fin 7)) := [{0, 1, 2}, {2, 3, 4}, {4, 5, 0}, {0, 2, 4}]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
-- This kernel check enumerates all 128 finite subsets and the clique predicates on them.
theorem link_faces : ∀ s : Finset (Fin 7),
    (s.Nonempty ∧ graph.IsClique (s : Set (Fin 7)) ∧
      ∀ v ∈ s, v ∈ DescendingLink graph (id : Fin 7 → Fin 7) 6) ↔
    (s.Nonempty ∧ ∃ t ∈ triangles, s ⊆ t) := by
  simp only [SimpleGraph.IsClique, Set.Pairwise, DescendingLink, Set.mem_ofPred_eq,
    Finset.mem_coe]
  decide

end Seifert.Seven
