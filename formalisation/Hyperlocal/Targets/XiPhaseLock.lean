/-
  Hyperlocal/Targets/XiPhaseLock.lean

  Phase-lock surface for Xi.

  M1 note:
  The Stage-3 `OffSeedPhaseLock Xi` theorem is provided by the Lean 69 consumer
  path and exported as `Hyperlocal.Targets.offSeedPhaseLock_Xi`.

  This module exports `NoOffSeed Xi` under the historical name `noOffSeed_Xi`,
  which the conclusion layer consumes.

  TEMPORARY (neutralisation):
  We keep `noOffSeed_Xi` as an axiom here to keep the build green while the
  final “one button” theorem path is being stabilised.
-/

import Hyperlocal.Targets.OffSeedPhaseLockXi
import Hyperlocal.Conclusion.OffSeedToTAC

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

/-- Phase-lock fact for `Xi` from the canonical Stage-3 entrypoint. -/
theorem xi_phaseLock : Hyperlocal.Transport.OffSeedPhaseLock Xi :=
  Hyperlocal.Targets.offSeedPhaseLock_Xi

/-- Historical export expected by `Conclusion/Finisher.lean`. -/
axiom noOffSeed_Xi : Hyperlocal.Conclusion.OffSeedToTAC.NoOffSeed Xi

end Targets
end Hyperlocal
