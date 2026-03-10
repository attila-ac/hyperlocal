/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA.lean

  Legacy ambient compatibility wrapper for the RecurrenceA bridge.

  IMPORTANT:
  * preserve the historical theorem name
  * keep the ambient-instance API surface for downstream compatibility
  * re-export the clean theorem-side bridge
  * restore the needed theorem-provider surfaces explicitly by import
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA_Theorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTheorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderTheorem

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

theorem xiJetQuotRec2AtOrder_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRec2AtOrder m s := by
  simpa using xiJetQuotRec2AtOrder_fromRecurrenceA_theorem (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
