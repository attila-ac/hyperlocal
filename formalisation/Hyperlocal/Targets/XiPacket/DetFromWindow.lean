/-
  Hyperlocal/Targets/XiPacket/DetFromWindow.lean

  Semantic cliff interface:
  exact data extracted from ξ Toeplitz/window recurrence,
  sufficient to build a PrimeTrigPacket.
-/

import Hyperlocal.Transport.PrimeTrigPacket
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/--
Minimal semantic output required from ξ-transport.

In the current refactor, this *is literally* the `PrimeTrigPacket.Packet` payload.
Keeping it as an alias avoids namespace/field duplication and stays green.
-/
abbrev XiPacketCore (σ t : ℝ) : Type :=
  Hyperlocal.Transport.PrimeTrigPacket.Packet σ t

/-- Core contract → PrimeTrigPacket (identity). -/
abbrev toPrimeTrigPacket {σ t : ℝ} (X : XiPacketCore σ t) :
    Hyperlocal.Transport.PrimeTrigPacket.Packet σ t :=
  X

end XiPacket
end Targets
end Hyperlocal
