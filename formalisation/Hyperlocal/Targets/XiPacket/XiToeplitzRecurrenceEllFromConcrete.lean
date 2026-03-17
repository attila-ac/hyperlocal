import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrder
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open scoped Real
open Complex
open Hyperlocal.Transport

/--
2026-03-13 honest post-axiom state:
* the AtOrder theorem is now theorem-gated
* therefore this wrapper can no longer remain assumption-free
* it must expose the honest theorem-side gate
-/
theorem xiToeplitzEllOut_fromRecurrenceC
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * routeA_G s (1 - s.ρ) = 0) :
    XiToeplitzEllOut s := by
  let h0 := xiToeplitzEllOutAt_fromRecurrenceC (m := 0) (s := s) (hroute := hroute)
  refine ⟨?_, ?_⟩
  · simpa [w0At_zero (s := s), wp2At_zero (s := s)] using h0.hell2
  · simpa [w0At_zero (s := s), wp3At_zero (s := s)] using h0.hell3

end XiPacket
end Targets
end Hyperlocal
