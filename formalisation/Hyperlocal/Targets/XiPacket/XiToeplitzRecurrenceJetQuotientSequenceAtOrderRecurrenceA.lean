/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderRecurrenceA.lean
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012PropAtOrderFromRecurrenceA
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012ToSequenceBridge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/--
Derived recurrence payload on the padded AtOrder sequences.

Obtained from the manuscript-facing **Prop-valued** row012 axiom
via `xiJetQuotRec2AtOrder_of_row012Prop`.
-/
theorem xiJetQuotRec2AtOrder_fromRecurrenceA
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRec2AtOrder m s := by
  classical
  have Hprop : XiJetQuotRow012PropAtOrder m s :=
    xiJetQuotRow012PropAtOrder_fromRecurrenceA (m := m) (s := s)
  exact xiJetQuotRec2AtOrder_of_row012Prop (m := m) (s := s) Hprop

end XiPacket
end Targets
end Hyperlocal
