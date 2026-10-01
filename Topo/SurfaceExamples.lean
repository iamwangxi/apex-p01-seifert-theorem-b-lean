/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.SurfaceTruncation
import Mathlib.Data.Fintype.Card

/-! A concrete four-vertex surface system. Distance-two and both numerical mechanisms occur. -/

noncomputable section
namespace Seifert.Application.StarFour

/-- Center 0, leaves 1,2,3. -/
def Adjacent (u v : Fin 4) : Prop := u ≠ v ∧ (u = 0 ∨ v = 0)

instance (u v : Fin 4) : Decidable (Adjacent u v) := by unfold Adjacent; infer_instance

def graph : SimpleGraph (Fin 4) where
  Adj := Adjacent
  symm := ⟨by intro u v h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (Adjacent _ _))

/-- Genus 0 at 0,1,2 and genus 1 at 3. -/
def genus (v : Fin 4) : ℕ := if v = 3 then 1 else 0

/-- Positive areas 1,2,2,3. Ties are intentionally present. -/
def areaWeight (v : Fin 4) : ℕ := if v = 0 then 1 else if v = 3 then 3 else 2

def area (v : Fin 4) : ℝ := areaWeight v

/-- Finite verification of the output choice p=q=0, including (b) for every z.
Numerical checking is over natural weights; real area is handled by a cast below. -/
theorem output_data : ∀ x u w : Fin 4,
    graph.Adj x u → graph.Adj x w → Seifert.DistanceTwo graph u w →
    (EqAdj graph 0 x ∧ EqAdj graph 0 u ∧ EqAdj graph 0 w) ∧
    (∀ z, EqAdj graph z u → EqAdj graph z w → EqAdj graph z 0) ∧
    genus 0 + genus 0 ≤ genus u + genus w ∧
    (genus 0 + genus 0 = genus u + genus w →
      areaWeight 0 + areaWeight 0 < areaWeight u + areaWeight w) := by
  simp only [Seifert.DistanceTwo, Seifert.TwoInterval, Set.mem_ofPred_eq, Set.Nonempty, EqAdj]
  decide

theorem hasOutputs : HasOutputs graph genus area := by
  intro x u w hxu hxw huw
  have hd := (Seifert.distanceTwo_iff_edist graph u w).mpr huw
  obtain ⟨ha, hb, hc, hd'⟩ := output_data x u w hxu hxw hd
  refine ⟨0, 0, ha, ha, fun z hzu hzw => ⟨hb z hzu hzw, hb z hzu hzw⟩, hc, ?_⟩
  intro he
  have hn := hd' he
  unfold area
  exact_mod_cast hn

theorem positive : ∀ v, 0 < area v := by
  intro v
  have hn : 0 < areaWeight v := by fin_cases v <;> decide
  unfold area
  exact_mod_cast hn

theorem connected : graph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  by_cases hv : v = 0
  · subst v; exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable ⟨Ne.symm hv, Or.inl rfl⟩

theorem values_wellFounded :
    WellFounded ((· < ·) : Values genus area → Values genus area → Prop) := by
  let : Finite (Values genus area) := (Set.finite_range (complexity genus area)).to_subtype
  exact wellFounded_lt

/-- All premises of the application, including the attained well-order and uniform outputs. -/
theorem system : SurfaceSystem graph genus area :=
  ⟨positive, connected, values_wellFounded, hasOutputs⟩

/-- N2 is not vacuous: the leaves 1 and 2 are at actual graph distance two. -/
theorem distance_two : graph.edist 1 2 = 2 := by
  apply (Seifert.distanceTwo_iff_edist graph 1 2).mp
  exact ⟨by decide, by decide, ⟨0, by decide, by decide⟩⟩

/-- The same example also has distance two between different genera. -/
theorem distance_two_mixed : graph.edist 1 3 = 2 := by
  apply (Seifert.distanceTwo_iff_edist graph 1 3).mp
  exact ⟨by decide, by decide, ⟨0, by decide, by decide⟩⟩

/-- At equal genus (c) is an equality and strict area gain in (d) really occurs. -/
theorem area_mechanism : genus 0 + genus 0 = genus 1 + genus 2 ∧
    area 0 + area 0 < area 1 + area 2 := by
  norm_num [genus, area, areaWeight]

/-- For the other pair, the genus inequality is strict. -/
theorem genus_mechanism : genus 0 + genus 0 < genus 1 + genus 3 := by decide

/-- W contains exactly three attained values, and vertex complexities have a genuine tie. -/
theorem values_description : Values genus area =
    ({toLex (0, 1), toLex (0, 2), toLex (1, 3)} : Set (ℕ ×ₗ ℝ)) := by
  ext t
  constructor
  · rintro ⟨v, rfl⟩
    fin_cases v <;> norm_num [complexity, genus, area, areaWeight]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num [complexity, genus, area, areaWeight]⟩
    · exact ⟨1, by norm_num [complexity, genus, area, areaWeight]⟩
    · exact ⟨3, by norm_num [complexity, genus, area, areaWeight]⟩

theorem genuine_tie : (1 : Fin 4) ≠ 2 ∧ complexity genus area 1 = complexity genus area 2 := by
  norm_num [complexity, genus, area, areaWeight]

theorem contractible : ContractibleSpace (Seifert.cliqueComplex graph).Realization :=
  theoremA system

/-- The genus-zero full subcomplex is a proper three-vertex path. -/
theorem genus_zero : FullConclusion graph (GenusSet genus 0) :=
  theoremC_genus system 0 ⟨0, by decide⟩

/-- The area-one cutoff in genus zero selects the center alone. -/
theorem area_one : FullConclusion graph (AreaSet genus area 0 1) :=
  theoremC_area system 0 1 ⟨0, by norm_num [AreaSet, genus, area, areaWeight]⟩

/-- In genus one, a cutoff of two leaves all lower-genus vertices in place and excludes 3. -/
theorem area_top_two : FullConclusion graph (AreaSet genus area 1 2) :=
  theoremC_area system 1 2 ⟨0, Or.inl (by decide)⟩

theorem proper_genus_truncation : (3 : Fin 4) ∉ GenusSet genus 0 := by
  change ¬ genus 3 ≤ 0
  decide

theorem proper_area_truncation : (3 : Fin 4) ∉ AreaSet genus area 1 2 := by
  norm_num [AreaSet, genus, area, areaWeight]

end Seifert.Application.StarFour
