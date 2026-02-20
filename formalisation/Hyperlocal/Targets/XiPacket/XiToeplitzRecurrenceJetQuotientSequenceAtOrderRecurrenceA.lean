/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA.lean
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/--
Cycle-safe recurrence API (Route–A boundary).

This module is an *upstream* node that must remain independent of the analytic pipeline.
Therefore it exports only the bundled padded-sequence recurrence payload
`XiJetQuotRec2AtOrder m s` under a stable name.

Current status: axiomatic.

When the true analytic extractor proof is wired into the Route–A chain, replace this axiom
by a theorem (without changing the exported name).
-/
axiom xiJetQuotRec2AtOrder_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRec2AtOrder m s

end XiPacket
end Targets
end Hyperlocal
