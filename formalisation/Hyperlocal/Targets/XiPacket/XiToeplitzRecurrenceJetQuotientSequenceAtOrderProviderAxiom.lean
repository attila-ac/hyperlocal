/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderAxiom.lean

  DAG-clean placeholder instance: provides XiJetQuotRec2AtOrder by axiom.

  This is the *only* remaining semantic cliff once Row0SemanticsAtOrder is provider-based.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-- Placeholder (DAG-clean) Rec2AtOrder provider. Replace by theorem-level later. -/
axiom xiJetQuotRec2AtOrder_axiom
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRec2AtOrder m s

/-- Default instance installed by importing this file. -/
instance : XiJetQuotRec2AtOrderProvider where
  rec2AtOrder := xiJetQuotRec2AtOrder_axiom

end XiPacket
end Targets
end Hyperlocal
