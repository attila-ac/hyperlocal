import Hyperlocal.Targets.XiPacket.XiRouteA_WcNormalization
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Exact remaining local scalar theorem, stated without class indirection.

This is the honest mathematical root now: once this is proved, the theorem-side
`RouteAWcScalarProvider` is available, and the higher Route-A / pair-{2,5}
endgame should become plumbing rather than new mathematics.
-/
def RouteAWcScalarNormalization : Prop :=
  ∀ s : OffSeed Xi,
    (routeA_G s) (1 - s.ρ) = 0 ∧
    deriv (routeA_G s) (1 - s.ρ) = (1 : ℂ) ∧
    deriv (deriv (routeA_G s)) (1 - s.ρ) = (XiTransport.delta s : ℂ)

/--
Turn the exact scalar theorem into the existing theorem-side provider payload.
-/
theorem routeA_wc_scalarProvider_of_normalization
    (h : RouteAWcScalarNormalization) :
    RouteAWcScalarProvider := by
  exact
    { routeA_G_at_one_sub_rho := fun s => (h s).1
      routeA_G_deriv_at_one_sub_rho := fun s => (h s).2.1
      routeA_G_deriv2_at_one_sub_rho := fun s => (h s).2.2 }

end XiPacket
end Targets
end Hyperlocal
