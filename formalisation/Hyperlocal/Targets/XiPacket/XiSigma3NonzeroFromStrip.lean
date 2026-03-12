/-
  Formalisation/Hyperlocal/Targets/XiPacket/XiSigma3NonzeroFromStrip.lean

  Strip-native nondegeneracy theorem for σ3.

  This is intentionally theorem-level only:
  `XiSigma3Nonzero` is a global class over all `OffSeed Xi`, so we do NOT try
  to install that class from strip data.
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiSigma3Nonzero
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorNondegeneracyFromStrip

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

theorem sigma3_ne_zero_of_strip
    (s : _root_.Hyperlocal.OffSeedStrip Xi) :
    (JetQuotOp.σ3 (s : OffSeed Xi) : ℂ) ≠ 0 := by
  have h : JetQuotOp.aRk1 (s : OffSeed Xi) 0 ≠ (0 : ℂ) := by
    simpa using (a0_ne_zero_of_strip (s := s))
  have hneg : (-(JetQuotOp.σ3 (s : OffSeed Xi) : ℂ)) ≠ 0 := by
    simpa [JetQuotOp.aRk1, JetQuotOp.aR] using h
  exact neg_ne_zero.mp hneg

end XiPacket
end Targets
end Hyperlocal
