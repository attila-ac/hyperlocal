/-
  Hyperlocal/Targets/XiPhaseLock.lean

  Targets-level stage-3 bridge surface.

  IMPORTANT:
  This file must not rely on `Xi` being in scope implicitly inside `Hyperlocal.Targets`.
  We import `XiWindowDefs` and refer to `Xi` as `Hyperlocal.Targets.XiPacket.Xi`.

  We also route `OffSeedPhaseLock Xi` through the axiom-free re-export
  `Hyperlocal.Targets.OffSeedPhaseLockXi`.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.OffSeedPhaseLockXi
import Hyperlocal.Transport.OffSeedBridge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

/-- The concrete ξ used in Targets-land. -/
abbrev Xi := Hyperlocal.Targets.XiPacket.Xi

/-- Axiom-free mainline: `OffSeedPhaseLock Xi`. -/
theorem xi_phaseLock : Hyperlocal.Transport.OffSeedPhaseLock Xi :=
  Hyperlocal.Targets.offSeedPhaseLock_Xi

/-- Stage-3 bridge: build `Conclusion.OffSeedToTAC.Stage3Bridge Xi`. -/
theorem Stage3Bridge :
    Hyperlocal.Conclusion.OffSeedToTAC.Stage3Bridge Xi :=
by
  -- `Stage3Bridge` has field `bridge` and is provided generically from a phase lock.
  exact Hyperlocal.Transport.stage3Bridge_of_phaseLock (H := Xi) xi_phaseLock

end Targets
end Hyperlocal
