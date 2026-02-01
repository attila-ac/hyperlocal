/-
  Hyperlocal/Targets/XiPhaseLock.lean

  Glue file:
    OffSeedPhaseLockXi gives: OffSeedPhaseLock Xi
    OffSeedBridge gives:      Stage3Bridge Xi
    OffSeedToTAC gives:       NoOffSeed Xi
-/

import Hyperlocal.Targets.OffSeedPhaseLockXi
import Hyperlocal.Transport.OffSeedBridge
import Hyperlocal.Conclusion.OffSeedToTAC
import Hyperlocal.Targets.RiemannXi
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPhaseLock

open scoped Real

abbrev Xi : ℂ → ℂ := Hyperlocal.xi

/-- Pull the phase-lock package for ξ from `Hyperlocal.Targets.OffSeedPhaseLockXi`. -/
theorem offSeedPhaseLock_Xi : Hyperlocal.Transport.OffSeedPhaseLock Xi := by
  -- Avoid abbrev-mismatch headaches: first take it at `Hyperlocal.xi`, then rewrite.
  have h : Hyperlocal.Transport.OffSeedPhaseLock Hyperlocal.xi :=
    Hyperlocal.Targets.OffSeedPhaseLockXi.offSeedPhaseLock_Xi
  simpa [Xi] using h

/-- Convert phase-lock ⇒ Stage-3 bridge (pure glue). -/
theorem stage3Bridge_Xi :
    Hyperlocal.Conclusion.OffSeedToTAC.Stage3Bridge Xi :=
  Hyperlocal.Transport.stage3Bridge_of_phaseLock (H := Xi) offSeedPhaseLock_Xi

/-- Bridge ⇒ no off-seed (pure glue). -/
theorem noOffSeed_Xi :
    Hyperlocal.Conclusion.OffSeedToTAC.NoOffSeed Xi :=
  Hyperlocal.Conclusion.OffSeedToTAC.no_offSeed_of_bridge (H := Xi) stage3Bridge_Xi

end XiPhaseLock
end Targets
end Hyperlocal
