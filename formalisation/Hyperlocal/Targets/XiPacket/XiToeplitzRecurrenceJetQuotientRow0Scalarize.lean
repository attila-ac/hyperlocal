/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0Scalarize.lean

  Thin re-export layer.

  Rationale:
  Some files want to import a module named `...Row0Scalarize` (row-0 scalar normal form).
  The actual implementation lives in `...Row0ConcreteProof.lean`.

  This file keeps that stable import name without duplicating content.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof

set_option autoImplicit false
noncomputable section
