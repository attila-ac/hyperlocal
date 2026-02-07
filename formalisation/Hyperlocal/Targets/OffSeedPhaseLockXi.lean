/-
  Hyperlocal/Targets/OffSeedPhaseLockXi.lean

  Compatibility wrapper (Plan C++):
  Keep the old import path `Hyperlocal.Targets.OffSeedPhaseLockXi`
  but delegate the actual proof to `OffSeedPhaseLockXiPayload`.
-/

import Hyperlocal.Targets.OffSeedPhaseLockXiPayload

set_option autoImplicit false

noncomputable section

namespace Hyperlocal
namespace Targets
namespace OffSeedPhaseLockXi

/-- The ξ target (noncomputable). -/
abbrev Xi : ℂ → ℂ := Hyperlocal.xi

/-- Re-export the new Plan C++ endpoint under the old name. -/
theorem offSeedPhaseLock_Xi : Hyperlocal.Transport.OffSeedPhaseLock Xi :=
  Hyperlocal.Targets.OffSeedPhaseLockXiPayload.offSeedPhaseLock_Xi

end OffSeedPhaseLockXi
end Targets
end Hyperlocal
