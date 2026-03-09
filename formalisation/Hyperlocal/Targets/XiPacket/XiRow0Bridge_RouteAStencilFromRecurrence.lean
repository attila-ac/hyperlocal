import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcRouteAStencilZero

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Route-A stencil identity derived from the Route-A recurrence.
-/
theorem routeA_stencil_zero_fromRecurrence
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (hrec :
      2 * deriv (deriv (routeA_G s)) (1 - s.ρ)
        =
      (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        -
      (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ)) :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ)
        = 0 := by
  -- Rewrite the recurrence to isolate G''
  have hrec' :
      deriv (deriv (routeA_G s)) (1 - s.ρ)
        =
      ((JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ)) / 2 := by
    have := congrArg (fun x => x / 2) hrec
    simpa [two_mul] using this

  -- Substitute and simplify algebraically
  simp [hrec']
  ring

end XiPacket
end Targets
end Hyperlocal
