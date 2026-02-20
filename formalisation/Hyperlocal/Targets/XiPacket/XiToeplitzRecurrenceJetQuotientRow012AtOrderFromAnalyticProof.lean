/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderFromAnalyticProof.lean

  Cycle-safe placeholder proof module.

  This file exists only to provide the symbol
    xiJetQuotRow012AtOrder_fromAnalytic_proof

  without importing the analytic pipeline (which would reintroduce cycles).
  Later, replace the axiom by the real construction.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderRow012Target

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/--
Cycle-safe placeholder for the Type-valued analytic landing spot.

Replace this axiom by a real proof term once the analytic construction is
made independent of Row0Semantics / SequenceAtOrderRecurrenceA.
-/
axiom xiJetQuotRow012AtOrder_fromAnalytic_proof
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow012AtOrder m s

end XiPacket
end Targets
end Hyperlocal
