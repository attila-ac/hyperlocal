/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientOperator.lean

  Option 2 (σ-sums): use the explicit symmetric-sum coefficient model.
  This file becomes a thin compatibility wrapper so downstream imports stay stable.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Transport.TACToeplitz

set_option autoImplicit false
noncomputable section

namespace Hyperlocal.Targets.XiPacket

open Hyperlocal.Transport

/-!
`JetQuotOp.aR`, `JetQuotOp.aRk1`, and `JetQuotOp.jetQuotToeplitzOp3`
are defined in `...OperatorDefs.lean` (σ-sum model).
This wrapper exists so older files can keep importing the “Operator” module name.
-/

end Hyperlocal.Targets.XiPacket
