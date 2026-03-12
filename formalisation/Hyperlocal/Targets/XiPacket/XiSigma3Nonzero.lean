/-
  Hyperlocal/Targets/XiPacket/XiSigma3Nonzero.lean

  Minimal nondegeneracy interface: σ3(s) ≠ 0.

  2026-03-12 policy:
  this file defines only the interface/class surface.
  It does NOT install any default instance.

  Concrete producers now live in separate files, e.g.
    * XiSigma3NonzeroFromTrueAnalytic
    * XiSigma3NonzeroFromA0Nonzero   (legacy compatibility)
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

/-- Minimal nondegeneracy interface for Tail345 coordinate kill: `σ3(s) ≠ 0`. -/
class XiSigma3Nonzero : Prop where
  sigma3_ne_zero : ∀ (s : OffSeed Xi), (JetQuotOp.σ3 s : ℂ) ≠ 0

end XiPacket
end Targets
end Hyperlocal
