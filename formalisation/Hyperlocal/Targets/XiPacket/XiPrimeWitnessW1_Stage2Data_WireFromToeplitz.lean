/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1_Stage2Data_WireFromToeplitz.lean

  W1 Stage-2 wiring milestone (Option A):
  Provide the *data layer* for the W1 interface:
    * generator family c : PrimeIdx → Window 3
    * linear map F : Window 3 →ₗ[ℂ] Window 3

  Engineering:
  * Extractor-free.
  * Endpoint-free.
  * True-analytic-friendly imports only (no extractor/frontier).
  * Uses fallback-to-0 for primes other than 2 and 3.

  Concrete choices:
  * V = W = Transport.Window 3
  * F = JetQuotOp.jetQuotToeplitzOp3 s
  * c p = wp2At m s (if p=2), wp3At m s (if p=3), else 0
-/

import Hyperlocal.AdAbsurdumSetup
import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Interface
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs

import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace W1

/-- Concrete ξ target. -/
abbrev Xi : ℂ → ℂ := Hyperlocal.xi

section

/--
Stage-2 data (c,F) wired from the Toeplitz operator and the jet-pivot prime windows.

Parameter `m`:
we wire against the jet-pivot windows `wp2At m s` and `wp3At m s`.
-/
instance instXiPrimeWitnessW1Defs_xi_fromToeplitz
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    XiPrimeWitnessW1Defs (R := ℂ) (V := Hyperlocal.Transport.Window 3)
      (W := Hyperlocal.Transport.Window 3) (H := Xi) s where
  c := fun p =>
    if hp2 : (p.1 : ℕ) = 2 then
      -- p = 2 (as a Nat equality on the underlying value)
      by
        -- No `subst`: just rewrite `p.1` in the expression.
        simpa [hp2] using (wp2At m s)
    else if hp3 : (p.1 : ℕ) = 3 then
      -- p = 3
      by
        simpa [hp3] using (wp3At m s)
    else
      0
  F := JetQuotOp.jetQuotToeplitzOp3 (s := s)

end

end W1
end XiPacket
end Targets
end Hyperlocal
