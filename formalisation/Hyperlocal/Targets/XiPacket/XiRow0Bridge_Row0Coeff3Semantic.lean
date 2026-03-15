/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row0Coeff3Semantic.lean

  MOVE–3 semantic payload (theorem-level, upstream-extracted).

  IMPORTANT:
  This layer must stay extractor-only and must NOT import
  Route-A stencil files, otherwise we create a cycle.

  Honest current status:
  * the upstream coeff-3 extractor is theorem-gated on the `wc` branch
  * therefore the `wc` semantic export must expose the same theorem-side gate
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0Coeff3Extractor
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Complex
open scoped BigOperators
open Hyperlocal.Cancellation

theorem row0ConvCoeff3_eq_zero_w0
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (w0 s)) 3 = 0 := by
  simpa using (row0ConvCoeff3_w0 s)

theorem row0ConvCoeff3_eq_zero_wc
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0 := by
  simpa using (row0ConvCoeff3_wc s hroute)

theorem row0ConvCoeff3_eq_zero_wp2
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2 s)) 3 = 0 := by
  simpa using (row0ConvCoeff3_wp2 s)

theorem row0ConvCoeff3_eq_zero_wp3
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3 s)) 3 = 0 := by
  simpa using (row0ConvCoeff3_wp3 s)

namespace Row0Coeff3SemanticExport
export _root_.Hyperlocal.Targets.XiPacket
  (row0ConvCoeff3_eq_zero_w0
   row0ConvCoeff3_eq_zero_wc
   row0ConvCoeff3_eq_zero_wp2
   row0ConvCoeff3_eq_zero_wp3)
end Row0Coeff3SemanticExport

end XiPacket
end Targets
end Hyperlocal
