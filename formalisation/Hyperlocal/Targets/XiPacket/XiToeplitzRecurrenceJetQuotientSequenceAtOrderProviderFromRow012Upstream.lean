/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012Upstream.lean

  Extractor-free provider for the at-order jet-quotient recurrence payload,
  built from the theorem-clean true-analytic Row012 upstream proof spine.

  IMPORTANT:
  * This file must remain interface-parametric.
  * Do NOT import ambient provider installers here.
  * Required upstream interfaces are now the honest theorem-side gates:
      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]

  2026-03-12 correction:
  * stop routing through `xiJetQuotRow012AtOrder_analytic_upstream`,
    which still depends on ambient sigma / coords providers
  * instead route through `xiJetQuotRow012AtOrder_trueAnalytic_upstream`
    together with the bridge
      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]
        ==> [XiRow012UpstreamTrueAnalytic]
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticProofUpstreamFromConvolutionTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012ToSequenceBridge

-- interface-only imports for the honest theorem-side gate
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets
import Hyperlocal.Targets.XiPacket.XiRow012UpstreamTrueAnalyticFromRec2TrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Complex
open Hyperlocal.Transport

/-- Sequence payload derived from the theorem-clean true-analytic Row012 upstream spine. -/
theorem xiJetQuotRec2AtOrder_fromRow012Upstream
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetQuotRec2AtOrder m s := by
  exact xiJetQuotRec2AtOrder_of_row012
    (m := m) (s := s)
    (xiJetQuotRow012AtOrder_trueAnalytic_upstream (m := m) (s := s))

/--
Provider instance for the at-order recurrence payload.

Crucially this instance is interface-parametric:
it does not install the theorem-side gate itself.
-/
instance (priority := 100)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetQuotRec2AtOrderProvider where
  rec2AtOrder := by
    intro m s
    exact xiJetQuotRec2AtOrder_fromRow012Upstream (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
