/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeartStrip.lean

  Non-cycle-safe *strip* export layer for the Row0 heart.

  Purpose:
  Provide the strip-specialised theorem-level heart output without exposing the
  global nondegeneracy axiom `a0_ne_zero`.

  Downstream strip-threaded modules should import this file (or the underlying
  heart file) and use `xiJetQuotRow0AtOrderHeartOut_strip`.
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeartFromAnalyticStrip

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Re-export: strip-specialised heart output. -/
theorem xiJetQuotRow0AtOrderHeartOut_fromAnalytic_strip
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi) :
    XiJetQuotRow0AtOrderHeartOut m (s : OffSeed Xi) :=
  xiJetQuotRow0AtOrderHeartOut_strip (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
