/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.SurfaceTruncation
import Mathlib.Data.Fintype.Card

/-! A non-cone five-vertex path satisfying every geometric output premise. -/

noncomputable section
namespace Seifert.Application.PathFive

/-- The path 0—1—2—3—4. -/
def Adjacent (u v : Fin 5) : Prop := u.val + 1 = v.val ∨ v.val + 1 = u.val

instance (u v : Fin 5) : Decidable (Adjacent u v) := by unfold Adjacent; infer_instance

def graph : SimpleGraph (Fin 5) where
  Adj := Adjacent
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := ⟨by intro u h; unfold Adjacent at h; omega⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (Adjacent _ _))

/-- The endpoints have genus one, and the three interior vertices have genus zero. -/
def genus (v : Fin 5) : ℕ := if v = 0 ∨ v = 4 then 1 else 0

/-- Positive areas 4,2,1,2,4. -/
def areaWeight (v : Fin 5) : ℕ := if v = 2 then 1 else if v = 1 ∨ v = 3 then 2 else 4

def area (v : Fin 5) : ℝ := areaWeight v

/-- For every distance-two configuration, choose both outputs to be its unique midpoint x. -/
theorem output_data : ∀ x u w : Fin 5,
    graph.Adj x u → graph.Adj x w → Seifert.DistanceTwo graph u w →
    (EqAdj graph x x ∧ EqAdj graph x u ∧ EqAdj graph x w) ∧
    (∀ z, EqAdj graph z u → EqAdj graph z w → EqAdj graph z x) ∧
    genus x + genus x ≤ genus u + genus w ∧
    (genus x + genus x = genus u + genus w →
      areaWeight x + areaWeight x < areaWeight u + areaWeight w) := by
  simp only [Seifert.DistanceTwo, Seifert.TwoInterval, Set.mem_ofPred_eq, Set.Nonempty, EqAdj]
  decide

theorem hasOutputs : HasOutputs graph genus area := by
  intro x u w hxu hxw huw
  obtain ⟨ha, hb, hc, hd⟩ := output_data x u w hxu hxw
    ((Seifert.distanceTwo_iff_edist graph u w).mpr huw)
  refine ⟨x, x, ha, ha, fun z hzu hzw => ⟨hb z hzu hzw, hb z hzu hzw⟩, hc, ?_⟩
  intro he
  have hn := hd he
  unfold area
  exact_mod_cast hn

theorem positive : ∀ v, 0 < area v := by
  intro v
  have hn : 0 < areaWeight v := by fin_cases v <;> decide
  unfold area
  exact_mod_cast hn

theorem connected : graph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨2, fun v => ?_⟩
  have h01 : graph.Adj 0 1 := by decide
  have h12 : graph.Adj 1 2 := by decide
  have h23 : graph.Adj 2 3 := by decide
  have h34 : graph.Adj 3 4 := by decide
  fin_cases v
  · exact h12.symm.reachable.trans h01.symm.reachable
  · exact h12.symm.reachable
  · exact SimpleGraph.Reachable.refl _
  · exact h23.reachable
  · exact h23.reachable.trans h34.reachable

theorem values_wellFounded :
    WellFounded ((· < ·) : Values genus area → Values genus area → Prop) := by
  let : Finite (Values genus area) := (Set.finite_range (complexity genus area)).to_subtype
  exact wellFounded_lt

theorem system : SurfaceSystem graph genus area :=
  ⟨positive, connected, values_wellFounded, hasOutputs⟩

/-- This example has no universal vertex, so its clique complex is not a cone. -/
theorem no_cone_vertex : ¬ ∃ x, ∀ v, EqAdj graph x v := by
  simp only [EqAdj]
  decide

theorem distance_two : graph.edist 1 3 = 2 := by
  apply (Seifert.distanceTwo_iff_edist graph 1 3).mp
  exact ⟨by decide, by decide, ⟨2, by decide, by decide⟩⟩

theorem distance_two_mixed : graph.edist 0 2 = 2 := by
  apply (Seifert.distanceTwo_iff_edist graph 0 2).mp
  exact ⟨by decide, by decide, ⟨1, by decide, by decide⟩⟩

theorem area_mechanism : genus 2 + genus 2 = genus 1 + genus 3 ∧
    area 2 + area 2 < area 1 + area 3 := by
  norm_num [genus, area, areaWeight]

theorem genus_mechanism : genus 1 + genus 1 < genus 0 + genus 2 := by decide

theorem contractible : ContractibleSpace (Seifert.cliqueComplex graph).Realization :=
  theoremA system

theorem genus_zero : FullConclusion graph (GenusSet genus 0) :=
  theoremC_genus system 0 ⟨2, by decide⟩

theorem area_one : FullConclusion graph (AreaSet genus area 0 1) :=
  theoremC_area system 0 1 ⟨2, by norm_num [AreaSet, genus, area, areaWeight]⟩

theorem proper_genus_truncation : (0 : Fin 5) ∉ GenusSet genus 0 := by
  change ¬ genus 0 ≤ 0
  decide

end Seifert.Application.PathFive
