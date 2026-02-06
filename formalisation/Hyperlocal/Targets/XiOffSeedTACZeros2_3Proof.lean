/-
  Hyperlocal/Targets/XiOffSeedTACZeros2_3Proof.lean

  Derived glue (no semantics):
    OffSeedPhaseLock Xi  →  Stage3System Xi  →  OffSeedTACZeros2_3 Xi.

  This file is OPTIONAL for the endgame, but keeping it green prevents
  accidental re-imports from reintroducing a `sorry`.
-/

import Hyperlocal.Targets.OffSeedPhaseLockXi
import Hyperlocal.Targets.Stage3SystemXiProof
import Hyperlocal.Transport.TACExtraction

noncomputable section

namespace Hyperlocal
namespace Targets

open scoped Real

abbrev Xi : ℂ → ℂ := Hyperlocal.xi

/-- Derived: Stage3System Xi from the phase-lock package (already proved in Stage3SystemXiProof). -/
theorem stage3System_xi :
    Hyperlocal.Transport.Stage3System (H := Xi) :=
  Hyperlocal.Targets.stage3System_xi_of_phaseLock
    (hlock := Hyperlocal.Targets.OffSeedPhaseLockXi.offSeedPhaseLock_Xi)

/-- Derived: OffSeedTACZeros2_3 Xi from Stage3System Xi. -/
theorem xi_offSeedTACZeros2_3 :
    Hyperlocal.Transport.OffSeedTACZeros2_3 (H := Xi) :=
  Hyperlocal.Transport.offSeedTACZeros2_3_of_stage3System (H := Xi) stage3System_xi

end Targets
end Hyperlocal
