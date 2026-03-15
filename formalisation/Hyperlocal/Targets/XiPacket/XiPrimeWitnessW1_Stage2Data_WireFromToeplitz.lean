/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1_Stage2Data_WireFromToeplitz.lean

  W1 Stage-2 wiring milestone (actual-prime family):

  Provide the *data layer* for the W1 interface:
    * generator family c : PrimeIdx → Window 3
    * linear map F : Window 3 →ₗ[ℂ] Window 3

  Engineering:
  * Extractor-free.
  * Endpoint-free.
  * True-analytic-friendly imports only (no extractor/frontier).

  Concrete choices:
  * V = W = Transport.Window 3
  * F = JetQuotOp.jetQuotToeplitzOp3 s
  * c p = wpAt m s p.1

  This is the honest W1 family: the actual prime windows, not the legacy
  `{2,3,0}` placeholder wiring.
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
Stage-2 data (c,F) wired from the Toeplitz operator and the actual jet-pivot
prime family `wpAt m s p`.
-/
instance instXiPrimeWitnessW1Defs_xi_fromToeplitz
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    XiPrimeWitnessW1Defs (R := ℂ) (V := Hyperlocal.Transport.Window 3)
      (W := Hyperlocal.Transport.Window 3) (H := Xi) s where
  c := fun p => wpAt m s p.1
  F := JetQuotOp.jetQuotToeplitzOp3 (s := s)

end

end W1
end XiPacket
end Targets
end Hyperlocal
