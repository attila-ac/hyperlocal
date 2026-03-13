/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_WcScalarProviderFromBase.lean

  Historical compatibility shim for the old scalar-provider-from-base path.

  IMPORTANT (2026-03-13):
  * this file no longer installs `RouteAWcScalarProvider`
  * the old fallback became circular after the theorem-backed wc surfaces
  * keep this file importable only, so legacy imports do not break
  * any real `RouteAWcScalarProvider` instance must now come from a genuine
    lower theorem lane, not from reusing the theorem wrappers that already
    require the class
-/

import Hyperlocal.Targets.XiPacket.XiRouteA_WcNormalization

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

end XiPacket
end Targets
end Hyperlocal
