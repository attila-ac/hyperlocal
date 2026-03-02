/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetIsJetAxiom.lean

  AXIOM-FREE installer:

  Previously this file staged `XiJetWindowIsJetAtOrderProvider` via axioms
  `jet_w0At_axiom / jet_wp2At_axiom / jet_wp3At_axiom`.

  Now we derive those jets theorem-level from the already-available
  window-equality provider `[XiJetWindowEqAtOrderProvider]` using the
  analytic-jet bundle `xiJetQuotRow012AtOrder_analyticJet`.

  Net effect:
  * importing this file never introduces axioms,
  * and you still get `XiJetWindowIsJetAtOrderProvider` wherever
    `XiJetWindowEqAtOrderProvider` is available.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC

/--
Axiom-free instance installer:

If `[XiJetWindowEqAtOrderProvider]` is available (the theorem-level window equalities),
then the jet predicates `IsJet3AtOrder` for `w0At/wp2At/wp3At` follow automatically
via `XiJetQuotRow012AtOrder_AnalyticJet.jet_*`.
-/
instance (priority := 1000)
    [XiJetWindowEqAtOrderProvider] : XiJetWindowIsJetAtOrderProvider where
  jet_w0At := by
    intro m s
    simpa using
      (XiJetQuotRow012AtOrder_AnalyticJet.jet_w0At
        (P := xiJetQuotRow012AtOrder_analyticJet (m := m) (s := s)))
  jet_wp2At := by
    intro m s
    simpa using
      (XiJetQuotRow012AtOrder_AnalyticJet.jet_wp2At
        (P := xiJetQuotRow012AtOrder_analyticJet (m := m) (s := s)))
  jet_wp3At := by
    intro m s
    simpa using
      (XiJetQuotRow012AtOrder_AnalyticJet.jet_wp3At
        (P := xiJetQuotRow012AtOrder_analyticJet (m := m) (s := s)))

end TAC

end XiPacket
end Targets
end Hyperlocal
