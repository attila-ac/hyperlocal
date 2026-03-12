/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_A0NonzeroBoundary.lean

  Minimal boundary: `a0 := JetQuotOp.aRk1 s 0` is nonzero.

  Why this exists:
  Some pure-algebra closed forms for Row012 extra linear constraints divide by `a0`.
  We firewall that denominator as a small, explicit boundary so the rest of the
  route remains cycle-safe.

  2026-03-12 policy:
  this file now provides only the class surface.
  It does NOT install a global default instance.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

/-- Boundary typeclass: `JetQuotOp.aRk1 s 0 ≠ 0`. -/
class A0Nonzero (s : OffSeed Xi) : Prop where
  a0_ne_zero : JetQuotOp.aRk1 s 0 ≠ 0

end XiPacket
end Targets
end Hyperlocal
