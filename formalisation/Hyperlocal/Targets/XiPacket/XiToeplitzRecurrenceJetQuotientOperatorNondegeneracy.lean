/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientOperatorNondegeneracy.lean

  Cycle-safe nondegeneracy boundary:

  We assume the leading recurrence coefficient is nonzero:
    JetQuotOp.aRk1 s 0 ≠ 0.

  (In your development, this is equivalent to σ3 s ≠ 0 up to sign.)

  This file is intentionally tiny and cycle-safe.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Minimal nondegeneracy hypothesis for the Rec2→coords elimination. -/
axiom a0_ne_zero (s : OffSeed Xi) : JetQuotOp.aRk1 s 0 ≠ (0 : ℂ)

end XiPacket
end Targets
end Hyperlocal
