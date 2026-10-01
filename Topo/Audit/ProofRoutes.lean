/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.Audit.Statements

/-! Exact external interfaces for the three sampled proof stages. -/
noncomputable section
open Topology Convexity
namespace AdversarialAudit
universe u w
variable {V : Type u} {W : Type w} [LinearOrder W] [WellFoundedLT W]

/-- Lemma 2.2 including the well-order conclusion in the same existential witness. -/
theorem lemma22_full_conclusion {G : SimpleGraph V} {c : V → W}
    (h : SeifertStatement.ExchangeStructure G c) :
    ∃ order : LinearOrder V, letI := order;
      ∃ wf : WellFoundedLT V, letI := wf;
        ∃ d : V → W ×ₗ V, Function.Injective d ∧
          SeifertStatement.ExchangeStructure G d ∧
          IsWellOrder V (fun a b => d a < d b) := by
  have hs := (SeifertAudit.exchangeStructure_iff G c).mpr h
  obtain ⟨order, wf, d, hd, hex⟩ := Seifert.ties_may_be_broken hs
  let := order
  let := wf
  exact ⟨order, wf, d, hd, (SeifertAudit.exchangeStructure_iff G d).mp hex,
    hd.isWellOrder ((· < ·) : W ×ₗ V → W ×ₗ V → Prop)⟩

omit [WellFoundedLT W] in
/-- The successor interface consumes exactly the two induction inputs on the actual weak spaces. -/
theorem successor_interface (G : SimpleGraph V) (c : V → W)
    (hc : Function.Injective c) (v : V)
    (hA : ContractibleSpace ((Seifert.cliqueComplex G).strictSublevel c v).Realization)
    (hL : ContractibleSpace ((Seifert.cliqueComplex G).descendingLink c v).Realization) :
    ContractibleSpace ((Seifert.cliqueComplex G).sublevel c v).Realization := by
  let := hA
  let := hL
  exact (Seifert.cliqueComplex G).contractible_sublevel (Seifert.cliqueComplex_isFlag G)
    c hc v (Seifert.singleton_cliqueComplex G v)

/-- The finite-cofinal assembly has no countability, dimension, or local-finiteness parameter. -/
theorem limit_interface {ι : Type w} (K : Topo.Complex V)
    (B : ι → Topo.Complex V) (hBK : ∀ i, (B i).faces ⊆ K.faces)
    (hB : ∀ i, ContractibleSpace (B i).Realization)
    (hcofinal : ∀ F : Topo.Complex V, F.faces ⊆ K.faces → F.faces.Finite →
      ∃ i, F.faces ⊆ (B i).faces) : ContractibleSpace K.Realization :=
  K.contractible_of_cofinal_contractible B hBK hB hcofinal

#print axioms lemma22_full_conclusion
#print axioms successor_interface
#print axioms limit_interface
end AdversarialAudit
