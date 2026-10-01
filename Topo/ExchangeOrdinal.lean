/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.ExchangeHeredity
import Mathlib.SetTheory.Ordinal.Basic

/-! An infinite, ordinal-valued model validating that the interface has no finite/natural bound. -/

namespace Seifert

/-- The complete flag complex on all ordinals, with identity complexity, is an exchange complex.
Its vertex and complexity types are genuinely ordinal types, with no `Fintype` instance. -/
theorem ordinalComplete :
    InjectiveExchangeComplex (⊤ : SimpleGraph Ordinal) (id : Ordinal → Ordinal) := by
  have n2 : ∀ u v : Ordinal, DistanceTwo (⊤ : SimpleGraph Ordinal) u v →
      ∃ x, IsApex (⊤ : SimpleGraph Ordinal) u v x ∧ x < max u v := by
    intro u v huv
    exact False.elim (huv.2.1 huv.1)
  exact {
    n1 := n1_of_n2 _ _ n2
    n2 := n2
    connected := SimpleGraph.connected_top
    injective := Function.injective_id }

end Seifert
