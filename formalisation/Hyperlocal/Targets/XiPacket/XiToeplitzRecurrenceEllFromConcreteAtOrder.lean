/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceEllFromConcreteAtOrder.lean

  Public wrapper for AtOrder ell-out.

  2026-03-13 honest post-axiom state:
  * the upstream proof is now theorem-gated
  * therefore this wrapper can no longer remain assumption-free
  * it must expose the honest theorem-side gate

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]
      [RouteAWcScalarProvider]

  plus the explicit Route-A scalar-zero payload required by the `wc` branch.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceOutAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrderProofUpstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_Theorem

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

/-- Route--B “AtOrder” ℓ-output (theorem-level; proof is upstream). -/
theorem xiToeplitzEllOutAt_fromRecurrenceC
    (m : ℕ) (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    XiToeplitzEllOutAt m s :=
  xiToeplitzEllOutAt_fromRecurrenceC_proof
    (m := m) (s := s) (hroute := hroute)

end XiPacket
end Targets
end Hyperlocal
