/-
  Installs the coords01-at-order provider instance.

  Policy (DAG safety):
  * Upstream analytic / extractor layers import THIS file.
  * This file MUST NOT import Rec2-at-order true-analytic roots nor extractor glue.

  Today:
  * Installs the DAG-clean axiom provider instance.
  * A theorem-backed route can be installed via a separate “theorem installer”
    imported only in end-claim cones (to avoid cycles).
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderAxiom

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

-- stable import surface only

end XiPacket
end Targets
end Hyperlocal
