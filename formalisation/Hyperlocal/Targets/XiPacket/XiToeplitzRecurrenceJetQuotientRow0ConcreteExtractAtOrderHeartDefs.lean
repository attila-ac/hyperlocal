/-
  Heart defs-only layer (cycle-safe-ish, no analytic imports):

  Defines the Prop bundle `XiJetQuotRow0AtOrderHeartOut`:
    row0Sigma s (w0At/wp2At/wp3At) = 0.

  This file exists so we can have two proof providers:
  * general heart proof (may use global nondegeneracy boundary),
  * strip-only heart proof (uses `a0_ne_zero_of_strip`),
  without duplicating the structure or creating import dependence.
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

/-- Heart output: scalar Row0 goals (row0Sigma = 0) for the three AtOrder windows. -/
structure XiJetQuotRow0AtOrderHeartOut (m : ℕ) (s : OffSeed Xi) : Prop where
  hw0AtSigma  : row0Sigma s (w0At m s)  = 0
  hwp2AtSigma : row0Sigma s (wp2At m s) = 0
  hwp3AtSigma : row0Sigma s (wp3At m s) = 0

end XiPacket
end Targets
end Hyperlocal
