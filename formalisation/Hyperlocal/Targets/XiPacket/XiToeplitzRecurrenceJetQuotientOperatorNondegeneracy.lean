/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientOperatorNondegeneracy.lean

  Cycle-safe nondegeneracy boundary.

  Existing boundary:
    JetQuotOp.aRk1 s 0 ≠ 0.

  Added (needed by Stage-2 deterministic connector):
    det(aCoeff,bCoeff) at primes 2 and 3 is nonzero.

  This file is intentionally tiny and cycle-safe.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Transport.PrimeTrigPacket

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- Minimal nondegeneracy hypothesis for the Rec2→coords elimination. -/
axiom a0_ne_zero (s : OffSeed Xi) : JetQuotOp.aRk1 s 0 ≠ (0 : ℂ)

/--
Two-prime 2×2 nondegeneracy boundary for the W1 Stage-2 connector.

This is exactly the determinant needed to solve for `L(wc)` from the two window equations
at primes 2 and 3.
-/
axiom det_two_prime_ne_zero (s : OffSeed Xi) :
  (aCoeff (σ s) (t s) (2 : ℝ) : ℂ) * (bCoeff (σ s) (t s) (3 : ℝ) : ℂ)
    -
  (aCoeff (σ s) (t s) (3 : ℝ) : ℂ) * (bCoeff (σ s) (t s) (2 : ℝ) : ℂ) ≠ 0

end XiPacket
end Targets
end Hyperlocal
