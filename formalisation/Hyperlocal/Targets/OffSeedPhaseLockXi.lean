/-
  Hyperlocal/Targets/OffSeedPhaseLockXi.lean

  Stage-3 public entrypoint.

  NOTE:
  `Hyperlocal.Targets.OffSeedPhaseLockXiPayload` already defines
    * `Hyperlocal.Targets.Xi`
    * `Hyperlocal.Targets.offSeedPhaseLock_Xi`

  so this file must NOT redeclare them (otherwise Lean reports duplicate declarations).
-/

import Hyperlocal.Targets.OffSeedPhaseLockXiPayload

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

-- Nothing to do: importing the payload module installs the canonical Stage-3 theorem
-- in this namespace as `Targets.offSeedPhaseLock_Xi`.

end Targets
end Hyperlocal
