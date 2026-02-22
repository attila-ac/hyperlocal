/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider.lean

  DAG-clean interface: provide the Route–A recurrence payload at order:

    XiJetQuotRec2AtOrder m s

  This firewalls the remaining semantic cliff behind `xiJetQuotOpZeroAtOrder`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-- Provider of the AtOrder Rec2 payload. -/
class XiJetQuotRec2AtOrderProvider : Type where
  rec2AtOrder : ∀ (m : ℕ) (s : OffSeed Xi), XiJetQuotRec2AtOrder m s

/-- Canonical accessor. -/
theorem xiJetQuotRec2AtOrder_provided
    (m : ℕ) (s : OffSeed Xi) [XiJetQuotRec2AtOrderProvider] :
    XiJetQuotRec2AtOrder m s :=
  XiJetQuotRec2AtOrderProvider.rec2AtOrder (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
