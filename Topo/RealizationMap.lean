/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.Cone
import Topo.Subcomplex

/-! # Maps induced by vertex maps, and the base of a simplicial cone -/

noncomputable section
open Topology Convexity
namespace Topo.Complex
universe u v
variable {V : Type u} {W : Type v} {K : Topo.Complex V} {L : Topo.Complex W}

open Classical in
def realizationMap (f : V → W) (hf : ∀ s ∈ K.faces, s.image f ∈ L.faces)
    (x : K.Realization) : L.Realization :=
  ⟨x.1.map f, by
    classical
    exact L.downward Finsupp.mapDomain_support (hf _ x.2)⟩

open Classical in
@[fun_prop] theorem continuous_realizationMap (f : V → W)
    (hf : ∀ s ∈ K.faces, s.image f ∈ L.faces) : Continuous (realizationMap f hf) := by
  classical
  rw [K.continuous_iff]
  intro s
  let t : L.Face := ⟨s.1.image f, hf s.1 s.2⟩
  let g : s.1 → t.1 := fun v ↦ ⟨f v.1, Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩
  have heq : realizationMap f hf ∘ K.faceInclusion s = L.faceInclusion t ∘ StdSimplex.map g := by
    funext w
    apply Subtype.ext
    change (w.map Subtype.val).map f = (w.map g).map Subtype.val
    rw [StdSimplex.map_map, StdSimplex.map_map]
  rw [heq]
  exact (L.continuous_faceInclusion t).comp (StdSimplex.continuous_map ℝ g)

variable (K)
local instance : DecidableEq (Option V) := Classical.decEq _

def coneBase : Topo.Complex (Option V) where
  faces := {s | none ∉ s ∧ s.eraseNone ∈ K.faces}
  empty_mem := ⟨by simp, by simpa using K.empty_mem⟩
  downward hst ht := ⟨fun hs ↦ ht.1 (hst hs),
    K.downward (Finset.eraseNone.monotone hst) ht.2⟩

theorem coneBase_subset : K.coneBase.faces ⊆ K.cone.faces := fun _ hs ↦ hs.2

open Classical in
theorem some_face_mem_coneBase (s : Finset V) (hs : s ∈ K.faces) :
    s.image some ∈ K.coneBase.faces := by
  classical
  exact ⟨by simp, by simpa using hs⟩

def intoConeBase : K.Realization → K.coneBase.Realization :=
  realizationMap some (by intro s hs; simpa using K.some_face_mem_coneBase s hs)

@[fun_prop] theorem continuous_intoConeBase : Continuous K.intoConeBase :=
  continuous_realizationMap _ _

def intoCone : K.Realization → K.cone.Realization :=
  inclusion K.coneBase_subset ∘ K.intoConeBase

@[fun_prop] theorem continuous_intoCone : Continuous K.intoCone :=
  (continuous_inclusion _).comp K.continuous_intoConeBase

open Classical in
theorem image_getD_eq_eraseNone (s : Finset (Option V)) (hn : none ∉ s) (a : V) :
    s.image (fun v ↦ v.getD a) = s.eraseNone := by
  classical
  ext v
  constructor
  · rintro hv
    obtain ⟨o, ho, hov⟩ := Finset.mem_image.mp hv
    cases o with
    | none => exact (hn ho).elim
    | some w =>
      simp only [Option.getD_some] at hov
      subst v
      exact Finset.mem_eraseNone.mpr ho
  · intro hv
    exact Finset.mem_image.mpr ⟨some v, Finset.mem_eraseNone.mp hv, rfl⟩

def fromConeBase (a : V) : K.coneBase.Realization → K.Realization :=
  realizationMap (fun v ↦ v.getD a) (by
    intro s hs
    rw [image_getD_eq_eraseNone s hs.1 a]
    exact hs.2)

@[fun_prop] theorem continuous_fromConeBase (a : V) : Continuous (K.fromConeBase a) :=
  continuous_realizationMap _ _

@[simp] theorem fromConeBase_intoConeBase (a : V) (x : K.Realization) :
    K.fromConeBase a (K.intoConeBase x) = x := by
  apply Subtype.ext
  change (x.1.map some).map (fun v ↦ v.getD a) = x.1
  rw [StdSimplex.map_map]
  change x.1.map id = x.1
  exact StdSimplex.map_id x.1

end Topo.Complex
