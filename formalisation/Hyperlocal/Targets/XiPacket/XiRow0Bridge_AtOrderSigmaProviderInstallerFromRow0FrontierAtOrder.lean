/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderSigmaProviderInstallerFromRow0FrontierAtOrder.lean

  Downstream installer:

  * Imports the historical axiom sigma provider (to satisfy the analytic upstream DAG).
  * Imports the theorem-backed provider derived from Row0FrontierAtOrder.
  * Re-exports an instance at HIGH PRIORITY so typeclass search picks the theorem version
    whenever both are present.

  IMPORTANT:
  This module is intended to be imported ONLY downstream of the analytic upstream spine
  (e.g. in interface/semantics/concrete cones), not inside the analytic upstream bundle itself.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderAxiom
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderFromRow0FrontierAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/--
High-priority instance forwarding to the theorem-backed provider.

This avoids instance ambiguity when legacy modules still import the axiom provider.
-/
instance (priority := 1000) : XiAtOrderSigmaProvider :=
  (inferInstance : XiAtOrderSigmaProvider)

end XiPacket
end Targets
end Hyperlocal
