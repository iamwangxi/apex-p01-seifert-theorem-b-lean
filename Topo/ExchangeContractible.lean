/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.CliqueBridge
import Topo.ExchangeTies
import Topo.ExchangeHeredity
import Topo.DirectedUnion

/-! Seifert's Theorem B for weak realizations, in arbitrary universes. -/

noncomputable section
open Topology Convexity
universe u w
namespace Seifert
variable {V : Type u} {W : Type w} [LinearOrder W] [WellFoundedLT W]
local instance (priority := high) (α : Type*) : DecidableEq α :=
  fun a b => Classical.propDecidable (a = b)

omit [WellFoundedLT W] in
/-- The finite-cofinal limit argument, also used to assemble all stages at the end. -/
theorem contractible_of_sublevels (G : SimpleGraph V) (c : V → W) [Nonempty V]
    (h : ∀ v, ContractibleSpace ((cliqueComplex G).sublevel c v).Realization) :
    ContractibleSpace (cliqueComplex G).Realization := by
  classical
  apply Topo.Complex.contractible_of_directed_union (cliqueComplex G)
    (fun v => (cliqueComplex G).sublevel c v) ?_ ?_ h
  · intro u v
    rcases le_total (c u) (c v) with huv | hvu
    · exact ⟨v, fun _ hs => ⟨hs.1, fun x hx => le_trans (hs.2 x hx) huv⟩, fun _ hs => hs⟩
    · exact ⟨u, fun _ hs => hs, fun _ hs => ⟨hs.1, fun x hx => le_trans (hs.2 x hx) hvu⟩⟩
  · intro s
    constructor
    · intro hs
      by_cases hne : s.Nonempty
      · obtain ⟨v, _, hv⟩ := s.exists_max_image c hne
        exact ⟨v, hs, hv⟩
      · exact ⟨Classical.choice inferInstance, hs, by
          simp [Finset.not_nonempty_iff_eq_empty.mp hne]⟩
    · rintro ⟨_, hs, _⟩
      exact hs

omit [WellFoundedLT W] in
/-- Base case: with injective complexity, a least-vertex sublevel has just one vertex. -/
theorem contractible_sublevel_of_least (G : SimpleGraph V) (c : V → W)
    (hc : Function.Injective c) (v : V) (hv : IsLeastVertex c v) :
    ContractibleSpace ((cliqueComplex G).sublevel c v).Realization := by
  classical
  apply Topo.Complex.contractible_of_coneVertex (a := v)
  intro s hs
  have he : insert v s = {v} := by
    ext u
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | hu)
      · rfl
      · exact hc (le_antisymm (hs.2 u hu) (hv u))
    · exact Or.inl
  rw [he]
  exact ⟨singleton_cliqueComplex G v, by simp⟩

/-- Universal induction is essential: the lower link is a different exchange complex.
The induction parameter is an attained value, not an enumeration of the vertices. -/
theorem injective_sublevel_contractible (w₀ : W) :
    ∀ (U : Type u) (G : SimpleGraph U) (c : U → W),
      InjectiveExchangeComplex G c → ∀ v : U, c v = w₀ →
        ContractibleSpace ((cliqueComplex G).sublevel c v).Realization := by
  classical
  refine (wellFounded_lt (α := W)).induction
    (C := fun a => ∀ (U : Type u) (G : SimpleGraph U) (c : U → W),
      InjectiveExchangeComplex G c → ∀ v : U, c v = a →
        ContractibleSpace ((cliqueComplex G).sublevel c v).Realization) w₀ ?_
  intro w₀ ih U G c hG v hcv
  by_cases hleast : IsLeastVertex c v
  · exact contractible_sublevel_of_least G c hG.injective v hleast
  have hD : ({u | c u < c v} : Set U).Nonempty := by
    simpa only [Set.Nonempty, Set.mem_ofPred_eq, IsLeastVertex, not_forall, not_le] using hleast
  have hA : ContractibleSpace ((cliqueComplex G).strictSublevel c v).Realization := by
    let D : Set U := {u | c u < c v}
    have : Nonempty D := ⟨⟨hD.choose, hD.choose_spec⟩⟩
    have hGD := strictSublevel_injectiveExchangeComplex hG v hD
    let : ContractibleSpace (cliqueComplex (G.induce D)).Realization :=
      contractible_of_sublevels (G.induce D) (fun u : D => c u.val) (fun u =>
        ih (c u.val) (by simpa only [D, Set.mem_ofPred_eq, ← hcv] using u.property)
          D (G.induce D) (fun u : D => c u.val) hGD u rfl)
    exact (fullInduceHomeomorph G D).symm.contractibleSpace
  have hLne := descendingLink_nonempty hG v hleast
  have hL : ContractibleSpace ((cliqueComplex G).descendingLink c v).Realization := by
    let D : Set U := DescendingLink G c v
    have : Nonempty D := ⟨⟨hLne.choose, hLne.choose_spec⟩⟩
    have hGD := descending_injectiveExchangeComplex hG v hLne
    let : ContractibleSpace (cliqueComplex (G.induce D)).Realization :=
      contractible_of_sublevels (G.induce D) (fun u : D => c u.val) (fun u =>
        ih (c u.val) (by simpa only [← hcv] using u.property.2)
          D (G.induce D) (fun u : D => c u.val) hGD u rfl)
    rw [descendingLink_cliqueComplex]
    exact (fullInduceHomeomorph G D).symm.contractibleSpace
  let := hA
  let := hL
  exact (cliqueComplex G).contractible_sublevel (cliqueComplex_isFlag G) c hG.injective v
    (singleton_cliqueComplex G v)

/-- Theorem B with the temporary injectivity convention. -/
theorem injective_exchangeComplex_contractible {G : SimpleGraph V} {c : V → W}
    (h : InjectiveExchangeComplex G c) : ContractibleSpace (cliqueComplex G).Realization := by
  have : Nonempty V := h.connected.nonempty
  exact contractible_of_sublevels G c (fun v => injective_sublevel_contractible (c v) V G c h v rfl)

/-- **Theorem B. Every exchange complex is contractible.**
Only Definition 2.1 and a well-ordered complexity codomain are assumptions. -/
theorem theoremB {G : SimpleGraph V} {c : V → W} (h : ExchangeComplex G c) :
    ContractibleSpace (cliqueComplex G).Realization := by
  obtain ⟨order, wf, d, hd⟩ := exchangeComplex_ties_may_be_broken h
  let := order
  let := wf
  exact injective_exchangeComplex_contractible hd

end Seifert
