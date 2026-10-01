/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.ConeAttachment

/-! The combinatorial successor decomposition used in Seifert, Theorem B. -/

noncomputable section
open Topology Convexity ContinuousMap
namespace Topo.Complex
universe u v
variable {V : Type u} {A : Type v}
local instance t5FlagDecidableEq : DecidableEq V := Classical.decEq V

/-- Full subcomplex on a specified vertex set, retaining only actual vertices of `K`. -/
def full (K : Topo.Complex V) (S : Set V) : Topo.Complex V where
  faces := {s | s ∈ K.faces ∧ ∀ u ∈ s, u ∈ S}
  empty_mem := ⟨K.empty_mem, by simp⟩
  downward hst ht := ⟨K.downward hst ht.1, fun u hu ↦ ht.2 u (hst hu)⟩

@[simp] theorem mem_full (K : Topo.Complex V) (S : Set V) (s : Finset V) :
    s ∈ (K.full S).faces ↔ s ∈ K.faces ∧ ∀ u ∈ s, u ∈ S := Iff.rfl

/-- Flagness, with diagonal pairs recording membership of vertices.
For distinct vertices the pair is an edge; for equal vertices it is a singleton. -/
def IsFlag (K : Topo.Complex V) : Prop :=
  ∀ s : Finset V, (∀ u ∈ s, ∀ w ∈ s, {u, w} ∈ K.faces) → s ∈ K.faces

theorem IsFlag.full {K : Topo.Complex V} (hK : K.IsFlag) (S : Set V) :
    (K.full S).IsFlag := by
  intro s hs
  refine ⟨hK s (fun u hu w hw ↦ (hs u hu w hw).1), ?_⟩
  intro u hu
  exact (hs u hu u hu).2 u (by simp)

/-- The ordinary simplicial link, expressed without reference to flagness. -/
def link (K : Topo.Complex V) (v : V) (hv : {v} ∈ K.faces) : Topo.Complex V where
  faces := {s | v ∉ s ∧ insert v s ∈ K.faces}
  empty_mem := ⟨by simp, by simpa using hv⟩
  downward hst ht := ⟨fun h ↦ ht.1 (hst h),
    K.downward (Finset.insert_subset_insert v hst) ht.2⟩

variable [LinearOrder A]

def strictSublevel (K : Topo.Complex V) (c : V → A) (v : V) : Topo.Complex V :=
  K.full {u | c u < c v}

def sublevel (K : Topo.Complex V) (c : V → A) (v : V) : Topo.Complex V :=
  K.full {u | c u ≤ c v}

/-- The descending link is explicitly a full subcomplex on the lower neighbours. -/
def descendingLink (K : Topo.Complex V) (c : V → A) (v : V) : Topo.Complex V :=
  K.full {u | c u < c v ∧ {u, v} ∈ K.faces}

theorem descendingLink_is_full (K : Topo.Complex V) (c : V → A) (v : V) :
    K.descendingLink c v = K.full {u | c u < c v ∧ {u, v} ∈ K.faces} := rfl

theorem descendingLink_subset_strict (K : Topo.Complex V) (c : V → A) (v : V) :
    (K.descendingLink c v).faces ⊆ (K.strictSublevel c v).faces :=
  fun _ h ↦ ⟨h.1, fun u hu ↦ (h.2 u hu).1⟩

theorem strictSublevel_fresh (K : Topo.Complex V) (c : V → A) (v : V) :
    (K.strictSublevel c v).Fresh v := by
  intro h
  exact (lt_irrefl (c v)) (h.2 v (by simp))

theorem descendingLink_fresh (K : Topo.Complex V) (c : V → A) (v : V) :
    (K.descendingLink c v).Fresh v :=
  fun h ↦ K.strictSublevel_fresh c v (K.descendingLink_subset_strict c v h)

/-- The usual link condition follows from full lower-neighbour membership by flagness. -/
theorem insert_mem_of_descendingLink {K : Topo.Complex V} (hK : K.IsFlag)
    (c : V → A) (v : V) (hv : {v} ∈ K.faces)
    {s : Finset V} (hs : s ∈ (K.descendingLink c v).faces) : insert v s ∈ K.faces := by
  apply hK
  intro u hu w hw
  rcases Finset.mem_insert.mp hu with huv | hus
  · subst u
    rcases Finset.mem_insert.mp hw with hwv | hws
    · subst w
      simpa using hv
    · simpa [Finset.pair_comm] using (hs.2 w hws).2
  · rcases Finset.mem_insert.mp hw with hwv | hws
    · subst w
      exact (hs.2 u hus).2
    · exact K.downward (by simp [Finset.insert_subset_iff, Finset.singleton_subset_iff,
        hus, hws]) hs.1

/-- Under flagness the full lower-neighbour complex really is the lower part of
the ordinary link, rather than merely a definition of a vertex subset. -/
theorem descendingLink_eq_full_link (K : Topo.Complex V) (hK : K.IsFlag)
    (c : V → A) (v : V) (hv : {v} ∈ K.faces) :
    K.descendingLink c v = (K.link v hv).full {u | c u < c v} := by
  apply ext_faces
  ext s
  constructor
  · intro hs
    refine ⟨⟨?_, insert_mem_of_descendingLink hK c v hv hs⟩,
      fun u hu ↦ (hs.2 u hu).1⟩
    intro hvs
    exact (lt_irrefl (c v)) (hs.2 v hvs).1
  · rintro ⟨⟨_, hins⟩, hlt⟩
    refine ⟨K.downward (Finset.subset_insert v s) hins, ?_⟩
    intro u hu
    refine ⟨hlt u hu, K.downward ?_ hins⟩
    simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hu]

/-- Exact equality of complexes, with injective complexity resolving the top level. -/
theorem sublevel_eq_attachCone (K : Topo.Complex V) (hK : K.IsFlag)
    (c : V → A) (hc : Function.Injective c) (v : V) (hv : {v} ∈ K.faces) :
    K.sublevel c v = (K.strictSublevel c v).attachCone (K.descendingLink c v) v := by
  apply ext_faces
  ext s
  constructor
  · rintro ⟨hs, hle⟩
    by_cases hvs : v ∈ s
    · right
      refine ⟨K.downward (Finset.erase_subset v s) hs, ?_⟩
      intro u hu
      have hum := Finset.mem_erase.mp hu
      refine ⟨lt_of_le_of_ne (hle u hum.2) (fun he ↦ hum.1 (hc he)), ?_⟩
      exact K.downward (by simp [Finset.insert_subset_iff, Finset.singleton_subset_iff,
        hum.2, hvs]) hs
    · left
      refine ⟨hs, fun u hu ↦ lt_of_le_of_ne (hle u hu) ?_⟩
      exact fun he ↦ hvs (hc he ▸ hu)
  · intro hs
    rcases hs with hs | hs
    · exact ⟨hs.1, fun u hu ↦ le_of_lt (hs.2 u hu)⟩
    · change s.erase v ∈ (K.descendingLink c v).faces at hs
      have hface : s ∈ K.faces := by
        by_cases hvs : v ∈ s
        · simpa [Finset.insert_erase hvs] using insert_mem_of_descendingLink hK c v hv hs
        · simpa [Finset.erase_eq_of_notMem hvs] using hs.1
      refine ⟨hface, ?_⟩
      intro u hu
      by_cases huv : u = v
      · simp [huv]
      · exact le_of_lt (hs.2 u (Finset.mem_erase.mpr ⟨huv, hu⟩)).1

theorem sublevel_cone_inter (K : Topo.Complex V) (c : V → A) (v : V) :
    (((K.descendingLink c v).coneAt v).inter (K.strictSublevel c v)).faces =
      (K.descendingLink c v).faces :=
  coneAt_inter_faces _ _ _ (K.descendingLink_subset_strict c v) (K.strictSublevel_fresh c v)

theorem strictSublevel_subset_sublevel (K : Topo.Complex V) (c : V → A) (v : V) :
    (K.strictSublevel c v).faces ⊆ (K.sublevel c v).faces :=
  fun _ h ↦ ⟨h.1, fun u hu ↦ le_of_lt (h.2 u hu)⟩

theorem sublevel_eq_self_of_largest (K : Topo.Complex V) (c : V → A) (v : V)
    (hmax : ∀ u, {u} ∈ K.faces → c u ≤ c v) : K.sublevel c v = K := by
  apply ext_faces
  ext s
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun u hu ↦
    hmax u (K.downward (Finset.singleton_subset_iff.mpr hu) h)⟩⟩

/-- Directly applicable to the successor case of Theorem B once the descending
link has been proved contractible by the universal induction hypothesis. -/
theorem nonempty_strongDeformationRetract_sublevel (K : Topo.Complex V) (hK : K.IsFlag)
    (c : V → A) (hc : Function.Injective c) (v : V) (hv : {v} ∈ K.faces)
    [ContractibleSpace (K.descendingLink c v).Realization] :
    Nonempty (StrongDeformationRetract (K.strictSublevel_subset_sublevel c v)) := by
  have h := (K.strictSublevel c v).nonempty_strongDeformationRetract_attachCone
    (K.descendingLink c v) v (K.descendingLink_subset_strict c v) (K.strictSublevel_fresh c v)
  simpa only [← K.sublevel_eq_attachCone hK c hc v hv] using h

theorem contractible_sublevel (K : Topo.Complex V) (hK : K.IsFlag)
    (c : V → A) (hc : Function.Injective c) (v : V) (hv : {v} ∈ K.faces)
    [ContractibleSpace (K.descendingLink c v).Realization]
    [ContractibleSpace (K.strictSublevel c v).Realization] :
    ContractibleSpace (K.sublevel c v).Realization :=
  (Classical.choice (K.nonempty_strongDeformationRetract_sublevel hK c hc v hv)).contractible

/-- The paper's largest-vertex successor case, with both induction inputs explicit. -/
theorem contractible_of_largest_vertex (K : Topo.Complex V) (hK : K.IsFlag)
    (c : V → A) (hc : Function.Injective c) (v : V) (hv : {v} ∈ K.faces)
    (hmax : ∀ u, {u} ∈ K.faces → c u ≤ c v)
    [ContractibleSpace (K.descendingLink c v).Realization]
    [ContractibleSpace (K.strictSublevel c v).Realization] :
    ContractibleSpace K.Realization := by
  have h := K.contractible_sublevel hK c hc v hv
  exact (K.sublevel_eq_self_of_largest c v hmax) ▸ h

end Topo.Complex
