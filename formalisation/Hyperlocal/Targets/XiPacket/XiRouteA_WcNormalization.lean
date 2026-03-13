/-
  Hyperlocal/Targets/XiPacket/XiRouteA_WcNormalization.lean

  Tiny scalar normalization surface for the Route-A `wc` lane.

  IMPORTANT (2026-03-13):
  * this file is now only an interface + theorem wrappers
  * it no longer imports the residual `base` fallback
  * the fallback installer lives separately in
      `XiRow0Bridge_JetWindowEqFromRouteA_WcScalarProviderFromBase.lean`
-/

import Hyperlocal.Targets.XiPacket.XiRouteA_GDefs
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Tiny provider surface for the three scalar Route-A normalization facts.

This is the correct low seam below the `wc` jet theorem:
the theorem-side `wc` jet bridge can be parameterized over these three facts
without hardwiring the historical `base` fallback into the theorem constants.
-/
class RouteAWcScalarProvider : Prop where
  routeA_G_at_one_sub_rho :
    ∀ s : OffSeed Xi, (routeA_G s) (1 - s.ρ) = 0
  routeA_G_deriv_at_one_sub_rho :
    ∀ s : OffSeed Xi, deriv (routeA_G s) (1 - s.ρ) = (1 : ℂ)
  routeA_G_deriv2_at_one_sub_rho :
    ∀ s : OffSeed Xi,
      deriv (deriv (routeA_G s)) (1 - s.ρ) = (XiTransport.delta s : ℂ)

theorem routeA_G_at_one_sub_rho
    (s : OffSeed Xi)
    [RouteAWcScalarProvider] :
    (routeA_G s) (1 - s.ρ) = 0 :=
  RouteAWcScalarProvider.routeA_G_at_one_sub_rho s

theorem routeA_G_deriv_at_one_sub_rho
    (s : OffSeed Xi)
    [RouteAWcScalarProvider] :
    deriv (routeA_G s) (1 - s.ρ) = (1 : ℂ) :=
  RouteAWcScalarProvider.routeA_G_deriv_at_one_sub_rho s

theorem routeA_G_deriv2_at_one_sub_rho
    (s : OffSeed Xi)
    [RouteAWcScalarProvider] :
    deriv (deriv (routeA_G s)) (1 - s.ρ) = (XiTransport.delta s : ℂ) :=
  RouteAWcScalarProvider.routeA_G_deriv2_at_one_sub_rho s

end XiPacket
end Targets
end Hyperlocal
