/-
  Hyperlocal/Targets/OffSeedPhaseLockXi.lean

  Home of the final lemma for Xi:

      theorem offSeedPhaseLock_Xi : OffSeedPhaseLock Xi

  We isolate the single remaining semantic extraction as:

      xi_offSeedTACZeros2_3 : OffSeedTACZeros2_3 Xi

  and obtain phase-lock via PhaseLock2_3 glue.
-/

import Hyperlocal.Transport.PhaseLock2_3
import Hyperlocal.Transport.TACExtraction
import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Targets.XiOffSeedTACZeros2_3Proof
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal.Targets.OffSeedPhaseLockXi

open scoped Real

/-- Notation: our Xi target from `Hyperlocal.Targets.RiemannXi`. -/
abbrev Xi : ℂ → ℂ := Hyperlocal.xi

/--
**Only remaining semantic gap (transport/TAC, p = 2,3):**

Now sourced from `Hyperlocal.Targets.xi_offSeedTACZeros2_3` (the dedicated proof file).
-/
theorem xi_offSeedTACZeros2_3 :
    Hyperlocal.Transport.OffSeedTACZeros2_3 Xi := by
  -- Avoid abbrev-mismatch headaches: take it at `Hyperlocal.xi`, then rewrite.
  have h : Hyperlocal.Transport.OffSeedTACZeros2_3 Hyperlocal.xi :=
    Hyperlocal.Targets.xi_offSeedTACZeros2_3
  simpa [Xi] using h

/-- Immediate glue: TAC zeros at 2,3 ⇒ phase-lock. -/
theorem offSeedPhaseLock_Xi : Hyperlocal.Transport.OffSeedPhaseLock Xi :=
  Hyperlocal.Transport.offSeedPhaseLock_of_offSeedTACZeros2_3
    (H := Xi) xi_offSeedTACZeros2_3

end Hyperlocal.Targets.OffSeedPhaseLockXi
