/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderFromAnalyticExtractor.lean

  Legacy packaged Route-X endpoint (analytic -> recurrence) at order.

  CHANGE:
  * this historical endpoint is now a compatibility shim over the clean
    theorem-parametric endpoint
  * preserve the historical ambient-instance surface here
  * restore the required producer surfaces explicitly by import

  IMPORTANT:
  * this file remains the legacy convenience surface
  * the clean theorem corridor lives in
      XiToeplitzRecurrenceJetQuotientSequenceAtOrderFromAnalyticExtractor_Theorem
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderFromAnalyticExtractor_Theorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderTheorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderTheorem

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Legacy packaged endpoint, now re-exported from the clean theorem corridor. -/
theorem xiJetQuotRec2AtOrder_fromAnalyticExtractor
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRec2AtOrder m s := by
  simpa using xiJetQuotRec2AtOrder_fromAnalyticExtractor_theorem (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
