/-
  Hyperlocal/All.lean

  One-stop import for the *current working* core pipeline.

  NOTE (temporary):
  The old ζ-facing conclusion wrapper (`Conclusion/Finisher`) is intentionally
  not exported right now while the conclusion layer is being stabilised.
-/

import Hyperlocal.Targets.OffSeedPhaseLockXi
import Hyperlocal.Targets.XiPhaseLock
import Hyperlocal.Targets.XiPacket.Regression_NoLegacyAnchorImport

-- Re-export stable Stage-3 surface (names exist today).
export Hyperlocal.Targets
  ( offSeedPhaseLock_Xi
    xi_phaseLock )
