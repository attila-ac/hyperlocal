/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetIsJetAxiom.lean

  Stage-only installer (Step 4.5 staging):

  Installs `TAC.XiJetWindowIsJetAtOrderProvider` via axioms.

  Why:
  * The remaining analytic cliff is naturally expressed as jet predicates
      IsJet3AtOrder m (z_?At s) (?At m s)
    for w0/wp2/wp3.
  * Once these jets are proved theorem-level, the provider instance becomes theorem-level.
  * Until then, this file provides a *localized* staged instance to keep the DAG green.

  IMPORTANT:
  Prefer importing the provider surface:
    XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets.lean
  and only import THIS file when intentionally staging jets.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC

/-- Staged axiom: `w0At` is an order-m Jet3 window at the anchor `z_w0At`. -/
axiom jet_w0At_axiom (m : ℕ) (s : OffSeed Xi) :
  IsJet3AtOrder m (z_w0At s) (w0At m s)

/-- Staged axiom: `wp2At` is an order-m Jet3 window at the anchor `z_wp2At`. -/
axiom jet_wp2At_axiom (m : ℕ) (s : OffSeed Xi) :
  IsJet3AtOrder m (z_wp2At s) (wp2At m s)

/-- Staged axiom: `wp3At` is an order-m Jet3 window at the anchor `z_wp3At`. -/
axiom jet_wp3At_axiom (m : ℕ) (s : OffSeed Xi) :
  IsJet3AtOrder m (z_wp3At s) (wp3At m s)

/--
Stage-only instance installer:
`XiJetWindowIsJetAtOrderProvider` (and therefore `XiJetWindowEqAtOrderProvider`)
is now available wherever this file is imported.
-/
instance : XiJetWindowIsJetAtOrderProvider where
  jet_w0At  := jet_w0At_axiom
  jet_wp2At := jet_wp2At_axiom
  jet_wp3At := jet_wp3At_axiom

end TAC

end XiPacket
end Targets
end Hyperlocal
