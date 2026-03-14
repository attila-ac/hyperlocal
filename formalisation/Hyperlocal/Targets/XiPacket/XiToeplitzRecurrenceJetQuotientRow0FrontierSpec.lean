/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0FrontierSpec.lean

  Thin public `wc` frontier seam.

  IMPORTANT:
  * keep this file minimal
  * do NOT import proof modules here
  * do NOT route this file through the new stencil corridor
  * this seam must stay acyclic
-/

import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Transport.TACToeplitz
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcSigma2DeltaToToeplitzRow0Core
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcSigma2EqTwoDelta

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

theorem xiJetQuot_row0_wc_spec
  (s : OffSeed Xi)
  [XiJetQuotRec2AtOrderTrueAnalytic]
  [TAC.XiJetWindowEqAtOrderQuotProvider]
  [RouteAWcScalarProvider]
  (hroute :
    (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
      + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
      - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
  exact
    toeplitz_row0_wc_eq_zero_of_sigma2_eq_two_delta
      (s := s)
      (hσ2δ := sigma2_eq_two_delta (s := s) (hroute := hroute))

end XiPacket
end Targets
end Hyperlocal
