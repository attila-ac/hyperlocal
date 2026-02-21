/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeart.lean

  Heart contract (cycle-safe admitted boundary).

  CHANGE (2026-02-21):
  The heart admits ONLY the three scalar Row0 goals (row0Sigma = 0) for the
  three AtOrder windows.

  Coordinate vanishings (w 0 = 0 and w 1 = 0) have been moved OUT of the heart,
  into a separate (cycle-safe) admitted boundary file and/or derived theorem-level
  from the analytic extractor.

  This keeps the heart small and avoids entangling it with the extractor loop.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchySemantics
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Heart output: the scalar Row0 goals (row0Sigma = 0) for the three AtOrder windows.

This file is cycle-safe and should remain independent of the analytic extractor stack.
-/
structure XiJetQuotRow0AtOrderHeartOut (m : ℕ) (s : OffSeed Xi) : Prop where
  hw0AtSigma  : row0Sigma s (w0At m s)  = 0
  hwp2AtSigma : row0Sigma s (wp2At m s) = 0
  hwp3AtSigma : row0Sigma s (wp3At m s) = 0

/--
Admitted heart output (current semantic cliff for the Route–B scalar goals).
-/
axiom xiJetQuotRow0AtOrderHeartOut
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow0AtOrderHeartOut m s

end XiPacket
end Targets
end Hyperlocal
