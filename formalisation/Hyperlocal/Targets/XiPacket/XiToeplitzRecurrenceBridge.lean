/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceBridge.lean

  This file is intentionally axiom-free:
  the single ξ-semantic statement lives in `XiToeplitzRecurrenceExtract.lean`,
  and here we only package it into the downstream `XiToeplitzEllOut` record.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOut
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceExtract
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport

/-- Convenience wrapper: convert the concrete extraction output into the `EllOut` record. -/
theorem xiToeplitzEllOut_fromRecurrence (s : Hyperlocal.OffSeed Xi) : XiToeplitzEllOut s := by
  rcases xiToeplitzRecExtractOut_fromRecurrence s with ⟨h2, h3⟩
  exact ⟨h2, h3⟩

end XiPacket
end Targets
end Hyperlocal
