/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetWindowEqFromRouteA_Discharge.lean

  High-priority Route–A coordinate provider instance.

  NOTE (current status in your repo):
  You already have theorem-level Route–A existence/jet facts for the *canonical* window
    `jet3 G z`
  in:
    XiRow0Bridge_JetPkgFromAnalyticInputs.lean

  But you do NOT yet have theorem-level lemmas identifying the definitional windows
    `w0At / wp2At / wp3At`
  as `jet3 (routeA_G s) ...` windows of the quotient.

  Therefore, the only thing we can honestly install today is a high-priority alias of the
  existing fallback instance from:
    XiRow0Bridge_JetWindowEqFromRouteA_Axioms.lean

  Once you prove the window=jet3 identifications, replace the `infer_instance` below with
  a constructive `refine { ... }` using those lemmas.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_CoordProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_Axioms

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/--
High-priority provider.

Right now this delegates to the fallback axiom provider.
Replace this with a real implementation once the window=jet3 lemmas exist.
-/
instance (priority := 1000) : RouteAJetCoordProvider := by
  infer_instance

end XiPacket
end Targets
end Hyperlocal
