/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractor.lean

  Route X extractor (analytic → recurrence):
  derive the padded-sequence JetQuotRec2 triple from the analytic row012 target.

  No new axioms here.

  Graph discipline:
  * import the INSTALLED analytic landing surface, not the upstream parametric one
  * the upstream parametric node itself remains interface-parametric
  * this extractor is a downstream consumer, so it may use the installed surface
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticInstaller
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceToRow012Bridge
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Extractor theorem:
produces the three padded-sequence recurrences at order `m`.
-/
theorem xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor
    (m : ℕ) (s : OffSeed Xi) :
    JetQuotRec2 s (padSeq3 (w0At m s)) ∧
    JetQuotRec2 s (padSeq3 (wp2At m s)) ∧
    JetQuotRec2 s (padSeq3 (wp3At m s)) := by
  classical

  -- Do not ask typeclass search to rediscover these at this consumer node.
  -- Install the currently intended extractor-facing provider surfaces explicitly.
  letI : XiAtOrderSigmaProvider := ⟨xiAtOrderSigmaOut_axiom⟩
  letI : XiAtOrderCoords01Provider := ⟨xiAtOrderCoords01Out_axiom_stub⟩

  have Hrow012 : XiJetQuotRow012AtOrder m s :=
    xiJetQuotRow012AtOrder_analytic (m := m) (s := s)

  have Hrec2 : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_of_row012 (m := m) (s := s) Hrow012

  exact ⟨Hrec2.h_w0At, Hrec2.h_wp2At, Hrec2.h_wp3At⟩

end XiPacket
end Targets
end Hyperlocal
