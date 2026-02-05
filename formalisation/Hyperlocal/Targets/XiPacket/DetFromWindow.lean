/-
  Hyperlocal/Targets/XiPacket/DetFromWindow.lean

  Semantic cliff interface (refactored):

  We now isolate ξ-semantics at the *window* level:

    XiPacketCore (σ,t) := WindowPayload (σ,t)

  i.e. complex windows + prime decompositions + ell/kappa facts.

  Then conversion to the Stage-3 trig packet is pure algebra:

    WindowPayload.toPrimeTrigPacket
-/

import Hyperlocal.Targets.XiPacket.WindowPayload
import Hyperlocal.Targets.XiPacket.ToPrimeTrigPacket
import Hyperlocal.Transport.PrimeTrigPacket
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-- Minimal semantic output required from ξ-transport (window-level payload). -/
abbrev XiPacketCore (σ t : ℝ) : Type :=
  WindowPayload σ t

/-- Core contract → PrimeTrigPacket (pure conversion). -/
abbrev toPrimeTrigPacket {σ t : ℝ} (X : XiPacketCore σ t) :
    Hyperlocal.Transport.PrimeTrigPacket.Packet σ t :=
  X.toPrimeTrigPacket

end XiPacket
end Targets
end Hyperlocal
