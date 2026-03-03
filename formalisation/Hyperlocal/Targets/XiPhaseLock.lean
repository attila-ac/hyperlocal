/-
  Hyperlocal/Targets/XiPhaseLock.lean

  Phase-lock surface for Xi.

  M1 note:
  The Stage-3 `OffSeedPhaseLock Xi` theorem is provided by the consumer
  path and exported as `Hyperlocal.Targets.offSeedPhaseLock_Xi`.

  This module exports `NoOffSeed Xi` under the historical name `noOffSeed_Xi`,
  which the conclusion layer consumes.

  STATUS (post Task #1):
  `noOffSeed_Xi` is now theorem-level (no axiom staging here).
-/

import Hyperlocal.Targets.OffSeedPhaseLockXi
import Hyperlocal.Transport.OffSeedBridge
import Hyperlocal.Conclusion.OffSeedToTAC

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

/-- Phase-lock fact for `Xi` from the canonical Stage-3 entrypoint. -/
theorem xi_phaseLock : Hyperlocal.Transport.OffSeedPhaseLock Xi :=
  Hyperlocal.Targets.offSeedPhaseLock_Xi

/-- Historical export expected by `Conclusion/Finisher.lean`. -/
theorem noOffSeed_Xi : Hyperlocal.Conclusion.OffSeedToTAC.NoOffSeed Xi := by
  -- PhaseLock ⇒ Stage3Bridge
  have hb :
      Hyperlocal.Conclusion.OffSeedToTAC.Stage3Bridge Xi :=
    Hyperlocal.Transport.stage3Bridge_of_phaseLock (H := Xi) xi_phaseLock
  -- Stage3Bridge ⇒ NoOffSeed
  exact Hyperlocal.Conclusion.OffSeedToTAC.no_offSeed_of_bridge (H := Xi) hb

end Targets
end Hyperlocal
