/-
  Hyperlocal/Targets/RH.lean

  Public-facing “RH for ζ” export:
  NoOffSeed ζ follows from the project’s NoOffSeed ξ endpoint plus ζ→ξ transfer.

  IMPORTANT:
  This file adds no new axioms. Any remaining axioms show up in
  `#print axioms Hyperlocal.Targets.noOffSeed_Zeta`.
-/

import Hyperlocal.Targets.XiPhaseLock
import Hyperlocal.Targets.ZetaTransfer

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

open Hyperlocal.Conclusion.OffSeedToTAC

/-- Final ζ-facing export (same notion of NoOffSeed as the conclusion layer). -/
theorem noOffSeed_Zeta : NoOffSeed Hyperlocal.zeta := by
  -- ZetaTransfer works with `Targets.ZetaTransfer.Zeta` abbrev, but definitional equality is fine.
  -- We just feed the xi-endpoint into the transfer lemma.
  simpa [Targets.ZetaTransfer.Zeta, Targets.ZetaTransfer.Xi] using
    (Targets.ZetaTransfer.noOffSeed_zeta_of_noOffSeed_xi (hxi := Targets.noOffSeed_Xi))

end Targets
end Hyperlocal
