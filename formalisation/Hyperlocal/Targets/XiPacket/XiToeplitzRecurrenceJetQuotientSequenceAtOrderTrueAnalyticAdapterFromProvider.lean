/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticAdapterFromProvider.lean

  Adapter (no refactor):
  Use the existing theorem-level true-analytic Rec2 lemmas to instantiate the
  new Prop-class interface `XiJetQuotRec2AtOrderTrueAnalytic`.

  This keeps downstream code free to depend on the class (interface),
  while you can keep the actual analytic proofs living where they already are.

  No axioms introduced.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-- Adapter: existing theorem-level true-analytic Rec2 lemmas ⇒ new interface class. -/
instance (priority := 1000) : XiJetQuotRec2AtOrderTrueAnalytic where
  rec2_w0At  := by intro m s; simpa using rec2_w0At_trueAnalytic (m := m) (s := s)
  rec2_wp2At := by intro m s; simpa using rec2_wp2At_trueAnalytic (m := m) (s := s)
  rec2_wp3At := by intro m s; simpa using rec2_wp3At_trueAnalytic (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
