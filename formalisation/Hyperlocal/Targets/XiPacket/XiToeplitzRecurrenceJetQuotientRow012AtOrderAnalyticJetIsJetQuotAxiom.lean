/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetIsJetQuotAxiom.lean

  YELLOW (Route E payload):
  Provide a NON-CIRCULAR global source of quotient-jet facts for the three pivot windows,
  i.e. an instance of:

      Hyperlocal.Targets.XiPacket.TAC.XiJetWindowIsJetAtOrderQuotProvider

  Once this exists, the pipeline becomes hands-free:

    [XiJetWindowIsJetAtOrderQuotProvider]
        ⇒ [XiJetWindowEqAtOrderQuotProvider]        (ProviderFromJets)
        ⇒ [JetQuotShiftBridge3AtOrderQuot ...]      (InstancesFromAnalyticExtractor)
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets
import Hyperlocal.Targets.XiPacket.XiJet3AtOrderQuotDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiRouteA_GDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

/-
  The three axioms are stated at the *canonical quotient anchors* already used by the
  provider/installer stack: `TAC.z_w0At/z_wp2At/z_wp3At`.

  IMPORTANT:
  We do NOT mention Rec2 or bridges here: this is the “payload source” that breaks the cycle.
-/

axiom jet_w0At_trueAnalytic_payload
    (m : ℕ) (s : OffSeed Xi) :
    IsJet3AtOrderQuot m s (TAC.z_w0At s) (w0At m s)

axiom jet_wp2At_trueAnalytic_payload
    (m : ℕ) (s : OffSeed Xi) :
    IsJet3AtOrderQuot m s (TAC.z_wp2At s) (wp2At m s)

axiom jet_wp3At_trueAnalytic_payload
    (m : ℕ) (s : OffSeed Xi) :
    IsJet3AtOrderQuot m s (TAC.z_wp3At s) (wp3At m s)

/-- Install the provider instance globally (this is what was missing). -/
instance : TAC.XiJetWindowIsJetAtOrderQuotProvider where
  jet_w0At  := jet_w0At_trueAnalytic_payload
  jet_wp2At := jet_wp2At_trueAnalytic_payload
  jet_wp3At := jet_wp3At_trueAnalytic_payload

end XiPacket
end Targets
end Hyperlocal
