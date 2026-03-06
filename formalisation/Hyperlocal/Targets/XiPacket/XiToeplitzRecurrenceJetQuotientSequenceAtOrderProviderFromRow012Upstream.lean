/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012Upstream.lean

  Extractor-free provider for the at-order jet-quotient recurrence payload,
  built from the Row012 analytic-upstream proof spine.

  IMPORTANT:
  * This file must remain interface-parametric.
  * Do NOT import provider installers here.
  * Required upstream interfaces are:
      [XiAtOrderSigmaProvider]
      [XiAtOrderCoords01Provider]
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticProofUpstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012ToSequenceBridge

-- interface-only imports
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Sequence payload derived from the extractor-free Row012 upstream proof spine. -/
theorem xiJetQuotRec2AtOrder_fromRow012Upstream
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider] :
    XiJetQuotRec2AtOrder m s := by
  exact xiJetQuotRec2AtOrder_of_row012
    (m := m) (s := s)
    (xiJetQuotRow012AtOrder_analytic_upstream (m := m) (s := s))

/--
Provider instance for the at-order recurrence payload.

Crucially this instance is interface-parametric:
it does not install sigma/coords01 itself.
-/
instance (priority := 100)
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider] :
    XiJetQuotRec2AtOrderProvider where
  rec2AtOrder := by
    intro m s
    exact xiJetQuotRec2AtOrder_fromRow012Upstream (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
