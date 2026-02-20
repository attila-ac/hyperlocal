/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderFromAnalyticExtractor.lean

  Route–X endpoint (analytic → recurrence) at order.

  This module packages the three padded-sequence `JetQuotRec2` facts (for `w0At/wp2At/wp3At`)
  into the bundled payload `XiJetQuotRec2AtOrder m s`.

  Downstream discipline:
  * This file is intentionally downstream of the analytic row012 landing spot.
  * Once the analytic landing spot becomes truly analytic (axiom-free), this endpoint becomes
    analytic end-to-end without changing its interface.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderAnalyticExtractor

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Route–X (analytic → recurrence) packaged endpoint at order `m`. -/
theorem xiJetQuotRec2AtOrder_fromAnalyticExtractor
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRec2AtOrder m s := by
  classical
  rcases xiJetQuotRec2_padSeq3_triple_fromAnalyticExtractor (m := m) (s := s) with
    ⟨hw0, hwp2, hwp3⟩
  exact ⟨hw0, hwp2, hwp3⟩

end XiPacket
end Targets
end Hyperlocal
