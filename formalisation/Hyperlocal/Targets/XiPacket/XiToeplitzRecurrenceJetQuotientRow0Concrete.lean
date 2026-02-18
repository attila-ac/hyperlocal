/-
PATCH (EDIT) for:
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0Concrete.lean

Fix:
  `export Hyperlocal.Targets.XiPacket (...)` inside `namespace Hyperlocal.Targets.XiPacket`
  is a self-export (Lean rejects it).

Use the dedicated export namespace from the frontier file instead.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Frontier
-- keep the rest of your existing imports

namespace Hyperlocal.Targets.XiPacket

-- If you previously declared `axiom xiJetQuot_row0_*` here, DELETE those lines.

-- Re-export the frontier names *without* self-export:
export _root_.Hyperlocal.Targets.XiPacket.Row0FrontierExport
  (xiJetQuot_row0_w0 xiJetQuot_row0_wc xiJetQuot_row0_wp2 xiJetQuot_row0_wp3)

end Hyperlocal.Targets.XiPacket
