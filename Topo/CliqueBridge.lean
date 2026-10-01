/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.ExchangeFlag
import Topo.RealizationMap
import Topo.FlagSuccessor

/-! The graph clique complex, including the empty face, and vertex restriction. -/

noncomputable section
open Topology Convexity
universe u w
namespace Seifert
variable {V : Type u}
local instance (priority := high) (α : Type*) : DecidableEq α :=
  fun a b => Classical.propDecidable (a = b)

/-- All finite cliques, with the empty face included. -/
def cliqueComplex (G : SimpleGraph V) : Topo.Complex V where
  faces := {s | G.IsClique (s : Set V)}
  empty_mem := by simp
  downward hst ht := ht.subset (by exact_mod_cast hst)

@[simp] theorem mem_cliqueComplex (G : SimpleGraph V) (s : Finset V) :
    s ∈ (cliqueComplex G).faces ↔ G.IsClique (s : Set V) := Iff.rfl

@[simp] theorem singleton_cliqueComplex (G : SimpleGraph V) (v : V) :
    {v} ∈ (cliqueComplex G).faces := by simp

theorem cliqueComplex_isFlag (G : SimpleGraph V) : (cliqueComplex G).IsFlag := by
  intro s hs u hu v hv hne
  exact hs u hu v hv (by simp) (by simp) hne

theorem cliqueComplex_eq_ofPreAbstract (G : SimpleGraph V) :
    cliqueComplex G =
      Topo.Complex.ofPreAbstract (flagComplex G).toPreAbstractSimplicialComplex := by
  apply Topo.Complex.ext_faces
  ext s
  change G.IsClique (s : Set V) ↔ s = ∅ ∨ s.Nonempty ∧ G.IsClique (s : Set V)
  by_cases hs : s = ∅ <;> simp [hs, Finset.nonempty_iff_ne_empty]

@[simp] theorem pair_cliqueComplex (G : SimpleGraph V) (u v : V) :
    {u, v} ∈ (cliqueComplex G).faces ↔ u = v ∨ G.Adj u v := by
  rw [mem_cliqueComplex, Finset.coe_pair, SimpleGraph.isClique_pair]
  by_cases he : u = v <;> simp [he]

theorem descendingLink_cliqueComplex {W : Type w} [LinearOrder W]
    (G : SimpleGraph V) (c : V → W) (v : V) :
    (cliqueComplex G).descendingLink c v =
      (cliqueComplex G).full (DescendingLink G c v) := by
  apply Topo.Complex.ext_faces
  ext s
  simp only [Topo.Complex.descendingLink, Topo.Complex.mem_full, Set.mem_ofPred_eq,
    pair_cliqueComplex, DescendingLink]
  constructor
  · rintro ⟨hs, ht⟩
    refine ⟨hs, fun u hu => ?_⟩
    obtain ⟨hlt, he | ha⟩ := ht u hu
    · exact (ne_of_lt hlt (congrArg c he)).elim
    · exact ⟨ha.symm, hlt⟩
  · rintro ⟨hs, ht⟩
    exact ⟨hs, fun u hu => ⟨(ht u hu).2, Or.inr (ht u hu).1.symm⟩⟩

open Classical in
theorem clique_induce_face (G : SimpleGraph V) (D : Set V) (s : Finset D) :
    s.image Subtype.val ∈ ((cliqueComplex G).full D).faces ↔
      s ∈ (cliqueComplex (G.induce D)).faces := by
  constructor
  · rintro ⟨hs, _⟩ a ha b hb hne
    exact hs (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
      (Finset.mem_image.mpr ⟨b, hb, rfl⟩) (fun he => hne (Subtype.ext he))
  · intro hs
    refine ⟨?_, ?_⟩
    · intro x hx y hy hne
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      exact hs ha hb (fun he => hne (congrArg Subtype.val he))
    · intro u hu
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hu
      exact a.property

/-- Reindexing a full subcomplex by its vertex subtype preserves the weak topology.
The empty vertex set is allowed. -/
def fullInduceHomeomorph (G : SimpleGraph V) (D : Set V) :
    (cliqueComplex (G.induce D)).Realization ≃ₜ ((cliqueComplex G).full D).Realization := by
  classical
  by_cases hD : D.Nonempty
  · let a : D := ⟨hD.choose, hD.choose_spec⟩
    let g : V → D := fun v => if hv : v ∈ D then ⟨v, hv⟩ else a
    have hg (v : D) : g v.val = v := by simp [g, v.property]
    have hgv (v : V) (hv : v ∈ D) : (g v).val = v := by simp [g, hv]
    have hf : ∀ s ∈ (cliqueComplex (G.induce D)).faces,
        s.image Subtype.val ∈ ((cliqueComplex G).full D).faces :=
      fun s hs => (clique_induce_face G D s).mpr hs
    have hi : ∀ s ∈ ((cliqueComplex G).full D).faces,
        s.image g ∈ (cliqueComplex (G.induce D)).faces := by
      intro s hs x hx y hy hne
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      change G.Adj (g v).val (g w).val
      rw [hgv v (hs.2 v hv), hgv w (hs.2 w hw)]
      exact hs.1 hv hw (fun he => hne (congrArg g he))
    refine {
      toFun := Topo.Complex.realizationMap Subtype.val hf
      invFun := Topo.Complex.realizationMap g hi
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := Topo.Complex.continuous_realizationMap _ _
      continuous_invFun := Topo.Complex.continuous_realizationMap _ _ }
    · intro x
      apply Subtype.ext
      change (x.1.map Subtype.val).map g = x.1
      rw [StdSimplex.map_map]
      simp only [hg]
      change x.1.map id = x.1
      exact StdSimplex.map_id x.1
    · intro x
      apply Subtype.ext
      change (x.1.map g).map Subtype.val = x.1
      rw [StdSimplex.map_map]
      apply StdSimplex.ext
      change x.1.weights.mapDomain (fun v => (g v).val) = x.1.weights
      calc
        _ = x.1.weights.mapDomain id := Finsupp.mapDomain_congr (fun v hv => hgv v (x.2.2 v hv))
        _ = x.1.weights := Finsupp.mapDomain_id
  · have hE : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hD
    have hleft : IsEmpty (cliqueComplex (G.induce D)).Realization := by
      refine ⟨fun x => ?_⟩
      obtain ⟨v, _⟩ := x.1.support_weights_nonempty
      simpa [hE] using v.property
    have hright : IsEmpty ((cliqueComplex G).full D).Realization := by
      refine ⟨fun x => ?_⟩
      obtain ⟨v, hv⟩ := x.1.support_weights_nonempty
      simpa [hE] using x.2.2 v hv
    letI := hleft
    letI := hright
    exact { toEquiv := Equiv.equivOfIsEmpty _ _ }

end Seifert
