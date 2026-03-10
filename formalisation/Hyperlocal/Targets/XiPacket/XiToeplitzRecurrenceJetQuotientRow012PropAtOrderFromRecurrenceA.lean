/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012PropAtOrderFromRecurrenceA.lean

  Stable API: provides the manuscript-facing Prop-valued row012 payload at order.

  IMPORTANT:
  This file must be cycle-safe, so it MUST NOT import the analytic pipeline.
  It is theorem-level: we derive the Prop payload from the clean theorem-side recurrence API.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA_Theorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTheorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderTheorem
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012PropAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012FromSequenceBridge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/--
Prop-valued row012 payload at order, derived from the clean theorem-side recurrence API.
-/
theorem xiJetQuotRow012PropAtOrder_fromRecurrenceA (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow012PropAtOrder m s := by
  classical
  have Hrec : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_fromRecurrenceA_theorem (m := m) (s := s)
  exact xiJetQuotRow012PropAtOrder_of_rec2 (m := m) (s := s) Hrec

end XiPacket
end Targets
end Hyperlocal
