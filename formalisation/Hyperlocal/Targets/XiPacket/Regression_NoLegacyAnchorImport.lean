/-
  Hyperlocal/Targets/XiPacket/Regression_NoLegacyAnchorImport.lean

  Tiny regression check:

  Import the final Stage-3 consumer (`OffSeedPhaseLockXiPayloadAtOrder`) and nothing else.

  This file is meant to stay on the *main* build path. If the Stage-3 consumer
  ever regresses to importing the legacy anchor-based nonvanishing modules,
  the dependency will show up immediately in the import graph (and can be caught
  by CI / `lake print-paths` style tooling).

  (Lean itself does not provide a stable, snapshot-robust “fail compilation if module X
  is imported” primitive, so this check is intentionally minimal.)
-/

import Hyperlocal.Targets.XiPacket.OffSeedPhaseLockXiPayloadAtOrder

set_option autoImplicit false

namespace Hyperlocal
namespace Targets
namespace XiPacket

-- Sanity: the consumer theorem is in scope.
#check Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.offSeedPhaseLock_Xi

end XiPacket
end Targets
end Hyperlocal
