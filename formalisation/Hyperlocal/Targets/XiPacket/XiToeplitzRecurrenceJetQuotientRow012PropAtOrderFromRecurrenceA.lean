/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012PropAtOrderFromRecurrenceA.lean

  Stable API: provides the manuscript-facing Prop-valued row012 payload at order.

  IMPORTANT:
  This file must be cycle-safe, so it MUST NOT import the analytic pipeline.
  For now it is axiomatic (until the analytic landing spot is fully theorem-level).
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012PropAtOrderDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/--
Cycle-safe placeholder for the manuscript-facing Prop-valued row012 constraints at order.

Once the analytic landing spot is discharged, replace this axiom by the real theorem,
*without* changing the exported name.
-/
axiom xiJetQuotRow012PropAtOrder_fromRecurrenceA (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow012PropAtOrder m s

end XiPacket
end Targets
end Hyperlocal
