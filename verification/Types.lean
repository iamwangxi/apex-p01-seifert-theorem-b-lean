/-
Copyright (c) 2026 Topo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Topo contributors
-/

import Topo.Audit.Statements
import Topo.Audit.ApplicationStatements

/-! Machine-readable documentation: unfold only the outer statement aliases. -/

open Lean Elab Command Meta in
run_cmd do
  for name in [``SeifertAudit.theoremB_verified, ``Seifert.theoremB,
      ``SeifertApplicationAudit.theoremA_verified,
      ``SeifertApplicationAudit.theoremC_genus_verified,
      ``SeifertApplicationAudit.theoremC_area_verified] do
    let info ← getConstInfo name
    let type ← liftTermElabM do whnf info.type
    logInfo m!"{info.name} : {type}"

#print SeifertStatement.ExchangeStructure
#print SeifertStatement.ExchangeComplex
#print SeifertApplicationStatement.Outputs
#print SeifertApplicationStatement.SurfaceSystem
#print SeifertApplicationStatement.GenusSet
#print SeifertApplicationStatement.AreaSet
#print SeifertApplicationStatement.FullConclusion
