/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.RelativeConeDeformation
import Topo.RealizationMap

/-! Identify the old vertices of the explicit `Option` cone with the original base. -/

noncomputable section
open Topology Convexity ContinuousMap
namespace Topo.Complex
universe u v
variable {V : Type u} {W : Type v}
local instance t5BaseDecidableEqV : DecidableEq V := Classical.decEq V
local instance t5BaseDecidableEqW : DecidableEq W := Classical.decEq W
local instance (priority := 10000) t5BaseDecidableEqOption : DecidableEq (Option V) :=
  Classical.decEq _

def mapRealization {K : Topo.Complex V} {M : Topo.Complex W} (f : V → W)
    (hf : ∀ s ∈ K.faces, s.image f ∈ M.faces) (x : K.Realization) : M.Realization :=
  ⟨x.1.map f, M.downward Finsupp.mapDomain_support (hf _ x.2)⟩

theorem continuous_mapRealization {K : Topo.Complex V} {M : Topo.Complex W} (f : V → W)
    (hf : ∀ s ∈ K.faces, s.image f ∈ M.faces) : Continuous (mapRealization f hf) := by
  rw [K.continuous_iff]
  intro s
  let t : M.Face := ⟨s.1.image f, hf _ s.2⟩
  let g : s.1 → t.1 := fun x ↦ ⟨f x.1, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
  have he : mapRealization f hf ∘ K.faceInclusion s =
      M.faceInclusion t ∘ StdSimplex.map g := by
    funext x
    apply Subtype.ext
    simp [mapRealization, faceInclusion, StdSimplex.map_map, g]
  rw [he]
  exact (M.continuous_faceInclusion t).comp (StdSimplex.continuous_map ℝ g)

-- Integration note: `coneBase` is the identical definition from `Topo.RealizationMap`.

theorem coneBase_image_face (L : Topo.Complex V) (s : Finset V) (hs : s ∈ L.faces) :
    s.image some ∈ L.coneBase.faces := by
  simp [coneBase, hs]

def toConeBase (L : Topo.Complex V) : L.Realization → L.coneBase.Realization :=
  mapRealization some L.coneBase_image_face

theorem toConeBase_injective (L : Topo.Complex V) : Function.Injective L.toConeBase := by
  intro x y h
  apply Subtype.ext
  apply StdSimplex.ext
  apply Finsupp.mapDomain_injective (Option.some_injective V)
  exact congrArg (fun z : L.coneBase.Realization ↦ z.1.weights) h

theorem toConeBase_surjective (L : Topo.Complex V) : Function.Surjective L.toConeBase := by
  intro y
  obtain ⟨x, hx⟩ := (StdSimplex.mem_range_map_iff some y.1).mpr (by
    intro o ho
    cases o with
    | none => exact Finsupp.notMem_support_iff.mp y.2.1
    | some v => exact (ho ⟨v, rfl⟩).elim)
  have hxL : x.weights.support ∈ L.faces := by
    have hy := y.2.2
    rw [← hx, StdSimplex.weights_map,
      Finsupp.mapDomain_support_of_injective (Option.some_injective V)] at hy
    simpa using hy
  exact ⟨⟨x, hxL⟩, Subtype.ext hx⟩

def coneBaseEquiv (L : Topo.Complex V) : L.Realization ≃ L.coneBase.Realization :=
  Equiv.ofBijective L.toConeBase ⟨L.toConeBase_injective, L.toConeBase_surjective⟩

def coneBaseFaceDecode (L : Topo.Complex V) (s : L.coneBase.Face) (x : s.1) : s.1.eraseNone := by
  have hx : x.1 ≠ none := fun h ↦ s.2.1 (h ▸ x.2)
  let hv := Option.ne_none_iff_exists'.mp hx
  exact ⟨Classical.choose hv, Finset.mem_eraseNone.mpr (by
    rw [← Classical.choose_spec hv]
    exact x.2)⟩

theorem coneBaseFaceDecode_spec (L : Topo.Complex V) (s : L.coneBase.Face) (x : s.1) :
    some (L.coneBaseFaceDecode s x).1 = x.1 := by
  unfold coneBaseFaceDecode
  exact (Classical.choose_spec (Option.ne_none_iff_exists'.mp
    (show x.1 ≠ none from fun he ↦ s.2.1 (he ▸ x.2)))).symm

theorem continuous_coneBaseEquiv_symm (L : Topo.Complex V) :
    Continuous L.coneBaseEquiv.symm := by
  rw [L.coneBase.continuous_iff]
  intro s
  let t : L.Face := ⟨s.1.eraseNone, s.2.2⟩
  have he : L.coneBaseEquiv.symm ∘ L.coneBase.faceInclusion s =
      L.faceInclusion t ∘ StdSimplex.map (L.coneBaseFaceDecode s) := by
    funext w
    apply L.toConeBase_injective
    change L.coneBaseEquiv (L.coneBaseEquiv.symm _) = _
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    change w.map Subtype.val =
      ((w.map (L.coneBaseFaceDecode s)).map Subtype.val).map some
    simp only [StdSimplex.map_map]
    congr 1
    funext x
    exact (L.coneBaseFaceDecode_spec s x).symm
  rw [he]
  exact (L.continuous_faceInclusion t).comp
    (StdSimplex.continuous_map ℝ (L.coneBaseFaceDecode s))

def coneBaseHomeomorph (L : Topo.Complex V) : L.Realization ≃ₜ L.coneBase.Realization where
  toEquiv := L.coneBaseEquiv
  continuous_toFun := continuous_mapRealization some L.coneBase_image_face
  continuous_invFun := L.continuous_coneBaseEquiv_symm

theorem coneBase_fresh (L : Topo.Complex V) : L.coneBase.Fresh none := by
  simp [Fresh, coneBase]

theorem coneBase_coneAt (L : Topo.Complex V) : L.coneBase.coneAt none = L.cone := by
  apply ext_faces
  ext s
  have he : (s.erase none).eraseNone = s.eraseNone := by ext v; simp
  simp [mem_coneAt, coneBase, he]

theorem coneBase_subset_cone (L : Topo.Complex V) : L.coneBase.faces ⊆ L.cone.faces :=
  fun _ h ↦ h.2

/-- The explicit cone model, with the base identified homeomorphically. -/
theorem nonempty_strongDeformationRetract_cone (L : Topo.Complex V)
    [ContractibleSpace L.Realization] :
    Nonempty (StrongDeformationRetract L.coneBase_subset_cone) := by
  let : ContractibleSpace L.coneBase.Realization :=
    L.coneBaseHomeomorph.symm.contractibleSpace
  have h := L.coneBase.nonempty_strongDeformationRetract_coneAt none L.coneBase_fresh
  simpa only [L.coneBase_coneAt] using h

def strongDeformationRetract_cone (L : Topo.Complex V) [ContractibleSpace L.Realization] :
    StrongDeformationRetract L.coneBase_subset_cone :=
  Classical.choice L.nonempty_strongDeformationRetract_cone

def homotopyEquiv_cone_base (L : Topo.Complex V) [ContractibleSpace L.Realization] :
    L.cone.Realization ≃ₕ L.Realization :=
  L.strongDeformationRetract_cone.homotopyEquiv.trans L.coneBaseHomeomorph.symm.toHomotopyEquiv

end Topo.Complex
