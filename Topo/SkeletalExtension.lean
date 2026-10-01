/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.FaceBoundary

/-! # Compatible extension through the finite-dimensional skeleta

Maps remain literally equal on every earlier skeleton. The final map is evaluated
at the cardinality of the support; each closed face sees one fixed finite stage.
-/

noncomputable section
open Topology Convexity
namespace Topo.Complex
universe u v
variable {W : Type u} {Y : Type v} [TopologicalSpace Y]
variable (D A : Topo.Complex W) (f₀ : D.Realization → Y)

structure ExtensionStage (n : ℕ) where
  map : D.Realization → Y
  continuous_face : ∀ s : D.Face, s.1 ∈ A.faces ∨ s.1.card ≤ n →
    Continuous (map ∘ D.faceInclusion s)
  agrees : ∀ x : D.Realization, x.1.weights.support ∈ A.faces → map x = f₀ x

variable {D A f₀}

namespace ExtensionStage

theorem exists_next {n : ℕ} (S : ExtensionStage D A f₀ n) (y₀ : Y)
    (hext : ∀ s : D.Face, ∀ f : C(SimplexExtension.boundary (T := s.1), Y),
      ∃ g : C(StdSimplex ℝ s.1, Y), ∀ b, g b.1 = f b) :
    ∃ S' : ExtensionStage D A f₀ (n + 1),
      ∀ x : D.Realization, x.1.weights.support ∈ A.faces ∨ x.1.weights.support.card ≤ n →
        S'.map x = S.map x := by
  classical
  have hex (s : D.Face) : ∃ e : C(StdSimplex ℝ s.1, Y),
      s.1.card = n + 1 → s.1 ∉ A.faces →
        ∀ b : SimplexExtension.boundary (T := s.1), e b.1 = S.map (D.faceInclusion s b.1) := by
    by_cases hs : s.1.card = n + 1 ∧ s.1 ∉ A.faces
    · let f : C(SimplexExtension.boundary (T := s.1), Y) :=
        ⟨fun b ↦ S.map (D.faceInclusion s b.1), D.continuous_boundary s S.map (by
          intro t ht
          apply S.continuous_face t
          right
          have hlt := Finset.card_lt_card ht
          omega)⟩
      obtain ⟨e, he⟩ := hext s f
      exact ⟨e, fun _ _ b ↦ he b⟩
    · exact ⟨ContinuousMap.const _ y₀, fun h₁ h₂ ↦ (hs ⟨h₁, h₂⟩).elim⟩
  choose e he using hex
  let good (x : D.Realization) : Prop :=
    x.1.weights.support.card = n + 1 ∧ x.1.weights.support ∉ A.faces
  let f' (x : D.Realization) : Y :=
    if good x then e (D.supportFace x) (D.faceLift (D.supportFace x) x (Finset.Subset.refl _))
      else S.map x
  have hold (x : D.Realization)
      (hx : x.1.weights.support ∈ A.faces ∨ x.1.weights.support.card ≤ n) : f' x = S.map x := by
    have hn : ¬ good x := by
      rintro ⟨hc, hA⟩
      rcases hx with hx | hx
      · exact hA hx
      · omega
    simp only [f', ite_eq_right hn]
  have hface (s : D.Face) (hs : s.1.card = n + 1) (hA : s.1 ∉ A.faces) :
      f' ∘ D.faceInclusion s = e s := by
    funext w
    let x := D.faceInclusion s w
    have hsub : x.1.weights.support ⊆ s.1 := support_map_val_subset _ _
    by_cases hfull : x.1.weights.support = s.1
    · have hgood : good x := by simpa only [good, hfull] using And.intro hs hA
      change f' x = e s w
      simp only [f', ite_eq_left hgood]
      have hsupport : D.supportFace x = s := Subtype.ext hfull
      exact D.eval_supportFace (fun s ↦ e s) x s w hsupport rfl
    · have hproper : x.1.weights.support ⊂ s.1 :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hfull⟩
      have hlt := Finset.card_lt_card hproper
      have hsmall : x.1.weights.support.card ≤ n := by omega
      have hb : w ∈ SimplexExtension.boundary := (D.mem_boundary_iff s w).mpr hproper
      change f' x = e s w
      rw [hold x (Or.inr hsmall)]
      exact (he s hs hA ⟨w, hb⟩).symm
  refine ⟨⟨f', ?_, ?_⟩, hold⟩
  · intro s hs
    rcases hs with hA | hs
    · have heq : f' ∘ D.faceInclusion s = S.map ∘ D.faceInclusion s := by
        funext w
        exact hold _ (Or.inl (A.downward (support_map_val_subset _ _) hA))
      rw [heq]
      exact S.continuous_face s (Or.inl hA)
    · by_cases hlow : s.1.card ≤ n
      · have heq : f' ∘ D.faceInclusion s = S.map ∘ D.faceInclusion s := by
          funext w
          exact hold _ (Or.inr ((Finset.card_le_card (support_map_val_subset _ _)).trans hlow))
        rw [heq]
        exact S.continuous_face s (Or.inr hlow)
      · have heq : s.1.card = n + 1 := by omega
        by_cases hA : s.1 ∈ A.faces
        · have hfun : f' ∘ D.faceInclusion s = S.map ∘ D.faceInclusion s := by
            funext w
            exact hold _ (Or.inl (A.downward (support_map_val_subset _ _) hA))
          rw [hfun]
          exact S.continuous_face s (Or.inl hA)
        · rw [hface s heq hA]
          exact (e s).continuous
  · intro x hx
    exact (hold x (Or.inl hx)).trans (S.agrees x hx)

end ExtensionStage

/-- Extension over an arbitrary weak realization by compatible skeletal induction. -/
theorem exists_continuous_extension (D A : Topo.Complex W) (f₀ : D.Realization → Y)
    (y₀ : Y) (h₀ : ∀ s : D.Face, s.1 ∈ A.faces → Continuous (f₀ ∘ D.faceInclusion s))
    (hext : ∀ s : D.Face, ∀ f : C(SimplexExtension.boundary (T := s.1), Y),
      ∃ g : C(StdSimplex ℝ s.1, Y), ∀ b, g b.1 = f b) :
    ∃ f : C(D.Realization, Y), ∀ x : D.Realization,
      x.1.weights.support ∈ A.faces → f x = f₀ x := by
  classical
  let S₀ : ExtensionStage D A f₀ 0 :=
    { map := f₀
      continuous_face := by
        intro s hs
        rcases hs with hs | hs
        · exact h₀ s hs
        · have hempty : s.1 = ∅ := Finset.card_eq_zero.mp (by omega)
          let : IsEmpty s.1 := ⟨fun v ↦ by simpa only [hempty, Finset.notMem_empty] using v.2⟩
          let : IsEmpty (StdSimplex ℝ s.1) := ⟨fun w ↦ by
            obtain ⟨v⟩ := w.nonempty
            exact isEmptyElim v⟩
          exact continuous_of_discreteTopology
      agrees := fun _ _ ↦ rfl }
  let step (n : ℕ) (S : ExtensionStage D A f₀ n) : ExtensionStage D A f₀ (n + 1) :=
    (S.exists_next y₀ hext).choose
  let stages : (n : ℕ) → ExtensionStage D A f₀ n :=
    fun n ↦ Nat.rec (motive := fun n ↦ ExtensionStage D A f₀ n) S₀ step n
  have hstep (n : ℕ) (x : D.Realization)
      (hx : x.1.weights.support ∈ A.faces ∨ x.1.weights.support.card ≤ n) :
      (stages (n + 1)).map x = (stages n).map x :=
    ((stages n).exists_next y₀ hext).choose_spec x hx
  have hstable (m n : ℕ) (hmn : m ≤ n) (x : D.Realization)
      (hx : x.1.weights.support.card ≤ m) : (stages n).map x = (stages m).map x := by
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih => exact (hstep n x (Or.inr (hx.trans hmn))).trans ih
  let f (x : D.Realization) : Y := (stages x.1.weights.support.card).map x
  have hcont : Continuous f := by
    rw [D.continuous_iff]
    intro s
    have heq : f ∘ D.faceInclusion s = (stages s.1.card).map ∘ D.faceInclusion s := by
      funext w
      exact (hstable _ _ (Finset.card_le_card (support_map_val_subset _ _)) _ le_rfl).symm
    rw [heq]
    exact (stages s.1.card).continuous_face s (Or.inr le_rfl)
  exact ⟨⟨f, hcont⟩, fun x hx ↦ (stages _).agrees x hx⟩

/-- Continuous maps from a subcomplex extend when all finite simplex boundary maps extend. -/
theorem exists_extension_subcomplex (D A : Topo.Complex W) (hAD : A.faces ⊆ D.faces)
    (fA : C(A.Realization, Y)) (y₀ : Y)
    (hext : ∀ s : D.Face, ∀ f : C(SimplexExtension.boundary (T := s.1), Y),
      ∃ g : C(StdSimplex ℝ s.1, Y), ∀ b, g b.1 = f b) :
    ∃ f : C(D.Realization, Y),
      f.comp ⟨inclusion hAD, continuous_inclusion hAD⟩ = fA := by
  classical
  let f₀ (x : D.Realization) : Y :=
    if hx : x.1.weights.support ∈ A.faces then fA ⟨x.1, hx⟩ else y₀
  have h₀ (s : D.Face) (hs : s.1 ∈ A.faces) : Continuous (f₀ ∘ D.faceInclusion s) := by
    have heq : f₀ ∘ D.faceInclusion s = fA ∘ A.faceInclusion ⟨s.1, hs⟩ := by
      funext w
      have hx : (D.faceInclusion s w).1.weights.support ∈ A.faces :=
        A.downward (support_map_val_subset _ _) hs
      simp only [Function.comp_apply, f₀, dite_eq_left hx]
      rfl
    rw [heq]
    exact fA.continuous.comp (A.continuous_faceInclusion _)
  obtain ⟨f, hf⟩ := exists_continuous_extension D A f₀ y₀ h₀ hext
  refine ⟨f, ?_⟩
  ext x
  exact (hf (inclusion hAD x) x.2).trans (dite_eq_left x.2)

end Topo.Complex
