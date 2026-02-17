/-
  Hyperlocal/Targets/XiPacket/XiJet3Defs.lean

  Single source of truth for jet-window predicates.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-- A length-3 jet window for a function `F` at center `z` (raw derivatives). -/
def IsJet3At (F : ℂ → ℂ) (z : ℂ) (w : Transport.Window 3) : Prop :=
  w 0 = F z ∧
  w 1 = deriv F z ∧
  w 2 = deriv (deriv F) z

end XiPacket
end Targets
end Hyperlocal
