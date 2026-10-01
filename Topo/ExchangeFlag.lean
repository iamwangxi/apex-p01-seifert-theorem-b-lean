/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.Exchange

/-! Bridges from the graph interface to actual Mathlib abstract flag complexes. -/

universe u w

namespace Seifert

variable {V : Type u}

open Classical in
/-- A cone vertex in an abstract complex: it can be inserted into every face. -/
def HasConeVertex (K : AbstractSimplicialComplex V) : Prop :=
  ∃ x, ∀ s : Finset V, s ∈ K → insert x s ∈ K

/-- A cone apex in a full induced flag complex, with membership in its vertex set included. -/
def IsConeOn (G : SimpleGraph V) (D : Set V) : Prop :=
  ∃ x ∈ D, ∀ y ∈ D, x = y ∨ G.Adj x y

theorem hasConeVertex_flagComplex_iff (G : SimpleGraph V) :
    HasConeVertex (flagComplex G) ↔ ∃ x, ∀ y, x = y ∨ G.Adj x y := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, fun y => ?_⟩
    have hf := hx {y} ((flagComplex G).singleton_mem y)
    have hc := (mem_flagComplex G _).mp hf |>.2
    by_cases he : x = y
    · exact Or.inl he
    · exact Or.inr (hc (by simp) (by simp) he)
  · rintro ⟨x, hx⟩
    refine ⟨x, fun s hs => ?_⟩
    have hc := (mem_flagComplex G s).mp hs |>.2
    change (insert x s).Nonempty ∧ G.IsClique ((insert x s : Finset V) : Set V)
    refine ⟨Finset.insert_nonempty x s, ?_⟩
    rw [Finset.coe_insert]
    apply hc.insert
    intro y _ hne
    exact (hx y).resolve_left hne

theorem hasConeVertex_induce_iff (G : SimpleGraph V) (D : Set V) :
    HasConeVertex (flagComplex (G.induce D)) ↔ IsConeOn G D := by
  rw [hasConeVertex_flagComplex_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x.val, x.property, fun y hy => ?_⟩
    rcases hx ⟨y, hy⟩ with he | ha
    · exact Or.inl (congrArg Subtype.val he)
    · exact Or.inr ha
  · rintro ⟨x, hx, hc⟩
    refine ⟨⟨x, hx⟩, fun y => ?_⟩
    rcases hc y.val y.property with he | ha
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr ha

open Classical in
/-- Fullness: finite cliques in the induced graph are exactly ambient cliques on D. -/
theorem flagComplex_induce_face (G : SimpleGraph V) (D : Set V) (s : Finset D) :
    s ∈ flagComplex (G.induce D) ↔
      s.image Subtype.val ∈ flagComplex G := by
  classical
  simp only [mem_flagComplex, Finset.image_nonempty, Finset.coe_image,
    SimpleGraph.IsClique, Set.Pairwise]
  constructor
  · rintro ⟨hne, hc⟩
    refine ⟨hne, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    exact hc ha hb (fun he => hab (congrArg Subtype.val he))
  · rintro ⟨hne, hc⟩
    refine ⟨hne, ?_⟩
    intro a ha b hb hab
    exact hc ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ (fun he => hab (Subtype.ext he))

open Classical in
/-- In a flag complex, the descending link really is the full subcomplex on descending neighbors.
For any nonempty face s, adjoining v forms a simplex exactly when every vertex neighbors v. -/
theorem descending_face_iff {W : Type w} [LinearOrder W]
    (G : SimpleGraph V) (c : V → W) (v : V) (s : Finset V) (hs : s.Nonempty)
    (hc : ∀ u ∈ s, c u < c v) :
    (s ∈ flagComplex G ∧ ∀ u ∈ s, u ∈ DescendingLink G c v) ↔
      insert v s ∈ flagComplex G := by
  classical
  constructor
  · rintro ⟨hface, hlink⟩
    refine ⟨Finset.insert_nonempty _ _, ?_⟩
    rw [Finset.coe_insert]
    exact ((mem_flagComplex G s).mp hface).2.insert (fun u hu _ => (hlink u hu).1)
  · intro hface
    have hclique := ((mem_flagComplex G _).mp hface).2
    refine ⟨⟨hs, hclique.subset (by intro u hu; simpa using Finset.mem_insert_of_mem hu)⟩, ?_⟩
    intro u hu
    refine ⟨hclique (by simp) (by simp [hu]) ?_, hc u hu⟩
    intro he
    have hlt := hc u hu
    simp [he] at hlt

/-- An apex of a two-interval is precisely a cone vertex of its full flag subcomplex. -/
theorem apex_iff_coneOn (G : SimpleGraph V) (u w : V) :
    (∃ x, IsApex G u w x) ↔ IsConeOn G (TwoInterval G u w) := Iff.rfl

end Seifert
