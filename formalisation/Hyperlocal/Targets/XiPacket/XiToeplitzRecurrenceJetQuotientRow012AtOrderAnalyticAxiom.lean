/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticAxiom.lean

  Analytic landing for the Row012 target bundle.

  IMPORTANT (new graph discipline):
  * this file is interface-parametric
  * it must NOT import provider installers
  * it must NOT import historical theorem/axiom installer surfaces

  Reason:
  The analytic extractor is a downstream consumer of this file.
  If this file imports installed sigma/coords providers directly, it freezes those
  historical surfaces into the extractor cone and can create import cycles.

  The installed extractor-facing import surface lives in the separate file:

    XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticInstaller.lean

  2026-03-12 split:
  * keep the historical ambient endpoint
      `xiJetQuotRow012AtOrder_analytic`
    for legacy extractor users
  * add a theorem-gated endpoint
      `xiJetQuotRow012AtOrder_analytic_fromRec2TrueAnalytic`
    on the honest gate
      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]

  This creates an admissible downstream retarget point without disturbing the
  legacy ambient surface yet.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticProofUpstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticProofUpstreamFromConvolutionTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets
import Hyperlocal.Targets.XiPacket.XiRow012UpstreamTrueAnalyticFromRec2TrueAnalytic

-- legacy provider interfaces only
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Complex
open Hyperlocal.Transport

/--
Historical ambient analytic endpoint.

Keep this wrapper for legacy extractor users that still live on the
sigma/coords corridor.
-/
noncomputable def xiJetQuotRow012AtOrder_analytic
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider] :
    XiJetQuotRow012AtOrder m s :=
  xiJetQuotRow012AtOrder_analytic_upstream (m := m) (s := s)

/--
Theorem-gated analytic endpoint on the honest Rec2 true-analytic corridor.
-/
noncomputable def xiJetQuotRow012AtOrder_analytic_fromRec2TrueAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiJetQuotRow012AtOrder m s :=
  xiJetQuotRow012AtOrder_trueAnalytic_upstream (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
