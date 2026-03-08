/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractor.lean

  Route X extractor (analytic -> recurrence):
  derive the padded-sequence JetQuotRec2 triple from the analytic row012 target.

  IMPORTANT:
  * keep this theorem parametric in the provider surfaces
  * do NOT locally reinstall fallback axiom instances here
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticInstaller
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceToRow012Bridge
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

theorem xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [XiAtOrderCoords01Provider] :
    JetQuotRec2 s (padSeq3 (w0At m s)) ∧
    JetQuotRec2 s (padSeq3 (wp2At m s)) ∧
    JetQuotRec2 s (padSeq3 (wp3At m s)) := by
  classical
  have Hrow012 : XiJetQuotRow012AtOrder m s :=
    xiJetQuotRow012AtOrder_analytic (m := m) (s := s)

  have Hrec2 : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_of_row012 (m := m) (s := s) Hrow012

  exact ⟨Hrec2.h_w0At, Hrec2.h_wp2At, Hrec2.h_wp3At⟩

end XiPacket
end Targets
end Hyperlocal
