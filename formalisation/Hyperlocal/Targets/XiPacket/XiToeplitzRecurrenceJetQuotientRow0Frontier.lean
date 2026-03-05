/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0Frontier.lean

  Legacy row-0 frontier exports (Route–B canonical windows).

  IMPORTANT (stability + cycle safety in practice):
  * This file is a THIN EXPORT LAYER.
  * All canonical row0 facts live in `...Row0Concrete`.
  * This file re-exports those facts under the historical names, but does NOT
    redeclare/prove them (avoids duplicate declarations and accidental cycles).

  NOTE:
  If you later switch `wc` away from the historical Spec axiom, do it in the
  *Concrete* layer first, then this file will automatically inherit the change.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0Concrete

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-
Re-export the historical public surface.
These are defined in `...Row0Concrete` and remain in the root namespace, so
downstream files keep working.
-/

namespace Row0FrontierExport

export _root_.Hyperlocal.Targets.XiPacket
  (w0At_zero wp2At_zero wp3At_zero
   xiJetQuot_row0_w0 xiJetQuot_row0_wc xiJetQuot_row0_wp2 xiJetQuot_row0_wp3)

end Row0FrontierExport

end XiPacket
end Targets
end Hyperlocal
