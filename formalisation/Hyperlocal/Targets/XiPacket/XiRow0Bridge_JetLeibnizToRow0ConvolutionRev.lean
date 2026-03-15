/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetLeibnizToRow0ConvolutionRev.lean

  MOVE–3 (Route–C Row--0), theorem-side retarget.

  Honest current status:
  * the `wc` branch is theorem-gated on the Route-A scalar seam
  * the other three branches remain closed
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizToRow0ConvolutionRevCore
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0Coeff3Semantic
import Mathlib.Tactic

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

theorem row0ConvolutionAtRev_w0
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    Row0ConvolutionAtRev s (s.ρ) (w0 s) := by
  exact row0ConvolutionAtRev_w0_of_coeff3
    (s := s)
    (h3 := row0ConvCoeff3_eq_zero_w0 s)

theorem row0ConvolutionAtRev_wc
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    Row0ConvolutionAtRev s (1 - s.ρ) (wc s) := by
  exact row0ConvolutionAtRev_wc_of_coeff3
    (s := s)
    (h3 := row0ConvCoeff3_eq_zero_wc s hroute)

theorem row0ConvolutionAtRev_wp2
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    Row0ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2 s) := by
  exact row0ConvolutionAtRev_wp2_of_coeff3
    (s := s)
    (h3 := row0ConvCoeff3_eq_zero_wp2 s)

theorem row0ConvolutionAtRev_wp3
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    Row0ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3 s) := by
  exact row0ConvolutionAtRev_wp3_of_coeff3
    (s := s)
    (h3 := row0ConvCoeff3_eq_zero_wp3 s)

namespace JetLeibnizToRow0ConvolutionRevExport
export _root_.Hyperlocal.Targets.XiPacket
  (row0ConvolutionAtRev_w0
   row0ConvolutionAtRev_wc
   row0ConvolutionAtRev_wp2
   row0ConvolutionAtRev_wp3)
end JetLeibnizToRow0ConvolutionRevExport

end XiPacket
end Targets
end Hyperlocal
