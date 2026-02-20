/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderFromAnalytic.lean

  Analytic landing spot (heavy, allowed to import analytic material):

    xiJetQuotRow012AtOrder_fromAnalytic : ∀ m s, XiJetQuotRow012AtOrder m s

  For now, this is kept as ONE axiom in this file only.
  Everything downstream should depend on the *def* name, not the axiom.
-/

import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderRow012Target

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Temporary single analytic cliff (to be replaced by real proof). -/
axiom xiJetQuotRow012AtOrder_fromAnalytic_axiom
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow012AtOrder m s

/--
Stable name (Type-valued): downstream should use this `def`.

When the real proof lands, delete the axiom and redefine this `def` by the proof.
-/
noncomputable def xiJetQuotRow012AtOrder_fromAnalytic
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow012AtOrder m s :=
  xiJetQuotRow012AtOrder_fromAnalytic_axiom (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
