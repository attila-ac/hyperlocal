/-
  Hyperlocal/Targets/XiOffSeedTACZeros2_3Proof.lean

  The ONLY remaining semantic cliff for the v4.x track:

    xi_offSeedTACZeros2_3 : OffSeedTACZeros2_3 Xi

  This file is where the ξ-specific window/transport recurrence must eventually
  be proved. Everything else downstream is glue (PhaseLock2_3, OffSeedBridge,
  OffSeedToTAC, Finisher).

  For now we leave exactly ONE hole (a single `sorry`) at the precise place
  where the operator/window semantics must enter.
-/

import Hyperlocal.Transport.TACExtraction
import Hyperlocal.Transport.TAC
import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Targets.XiTransportOp
import Hyperlocal.Targets.XiTransportToeplitz
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal.Targets

open scoped Real

/-- Notation: ξ target. -/
abbrev Xi : ℂ → ℂ := Hyperlocal.xi

/--
**ξ-specific semantic extraction (the remaining cliff):**

Produce TAC odd-part zeros at orders 2 and 3 for primes p=2,3, for every off-seed.

This is exactly the statement consumed by `PhaseLock2_3` glue.
The proof must ultimately be the ξ window/transport recurrence → stencil → TACZeros2_3.
-/
theorem xi_offSeedTACZeros2_3 :
    Hyperlocal.Transport.OffSeedTACZeros2_3 Xi := by
  intro s
  classical
  -- REAL WORK GOES HERE:
  --   (XiTransportOp + window recurrence + finite extraction) ⇒
  --     ∃ A B κ, EvenF A ∧ EvenF B ∧ κ≠0 ∧ oddPart(PhiPrime .. 2)=0 ∧ oddPart(PhiPrime .. 3)=0
  --
  -- Keep this as the *only* hole in the v4.x track.
  sorry

end Hyperlocal.Targets
