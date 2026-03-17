import Hyperlocal.Targets.XiPacket.XiRouteA_WcScalarNormalizationTheorem
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/--
Typeclass-packaged version of the exact remaining local scalar theorem.

Why this file exists:
the theorem object `RouteAWcScalarNormalization` is mathematically right, but
plain theorem arguments do not participate in the instance DAG. Packaging it as
a Prop-class lets the existing Route-A theorem-side installers fire via `#synth`.
-/
class RouteAWcScalarNormalizationProvider : Prop where
  normalization : RouteAWcScalarNormalization

instance (priority := 1000)
    [RouteAWcScalarNormalizationProvider] :
    RouteAWcScalarProvider where
  routeA_G_at_one_sub_rho := by
    intro s
    exact (RouteAWcScalarNormalizationProvider.normalization s).1
  routeA_G_deriv_at_one_sub_rho := by
    intro s
    exact (RouteAWcScalarNormalizationProvider.normalization s).2.1
  routeA_G_deriv2_at_one_sub_rho := by
    intro s
    exact (RouteAWcScalarNormalizationProvider.normalization s).2.2

end XiPacket
end Targets
end Hyperlocal
