/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA.lean

  Step 2 (analytic recurrence statement, rewritten to reduce translation friction):

  Instead of axiomatizing the padded-sequence recurrence directly, we axiomatize
  the manuscript-facing finite-window Toeplitz row012 constraints and derive the
  padded recurrence bundle from it using the (pure algebra) bridge
  `xiJetQuotRec2AtOrder_of_row012`.

  Net effect:
    • the only remaining axiom matches the manuscript’s finite-window statement,
    • `xiJetQuotRec2AtOrder_fromRecurrenceA` becomes theorem-level.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientManuscriptRow012PropAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceToRow012Bridge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/--
Derived recurrence payload on the padded AtOrder sequences.

This is now theorem-level: it is obtained from the manuscript-facing row012 axiom
via `XiJetQuotRow012AtOrder.ofProp` and the converse bridge `xiJetQuotRec2AtOrder_of_row012`.
-/
theorem xiJetQuotRec2AtOrder_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRec2AtOrder m s := by
  classical
  have Hprop : XiJetQuotRow012PropAtOrder m s :=
    xiJetQuotRow012PropAtOrder_fromRecurrenceA (m := m) (s := s)
  have Hrow012 : XiJetQuotRow012AtOrder m s :=
    XiJetQuotRow012AtOrder.ofProp (m := m) (s := s) Hprop
  exact xiJetQuotRec2AtOrder_of_row012 (m := m) (s := s) Hrow012

end XiPacket
end Targets
end Hyperlocal
