/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderFromAnalyticExtractor.lean

  Legacy packaged Route-X endpoint (analytic -> recurrence) at order.

  IMPORTANT:
  * this file remains on the historical ambient/provider corridor
  * it is allowed to import the ambient installer surfaces needed for synthesis
  * do NOT retarget this wrapper directly onto the theorem-side gate yet
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromAnalyticExtractor
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTheorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderAxiom

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

theorem xiJetQuotRec2AtOrder_fromAnalyticExtractor
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRec2AtOrder m s := by
  exact xiJetQuotRec2AtOrder_provided (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
