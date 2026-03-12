/-
  Formalisation/Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ExtraLinAtOrderFromRec2AtOrderTrueAnalyticStrip.lean

  Strip-specialised theorem wrapper for the extra-lin bundle from the
  Rec2-at-order corridor.
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_A0NonzeroBoundary
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinAtOrderFromRec2AtOrderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorNondegeneracyFromStrip

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

theorem xiRow012ExtraLinAtOrderOut_fromRec2AtOrderTrueAnalytic_strip
    [XiJetQuotRec2AtOrderProvider]
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi) :
    XiRow012ExtraLinAtOrderOut m (s : OffSeed Xi) := by
  let s0 : OffSeed Xi := (s : OffSeed Xi)
  letI : A0Nonzero (s := s0) := ⟨by
    simpa [s0] using (a0_ne_zero_of_strip (s := s))
  ⟩
  simpa [s0] using
    (xiRow012ExtraLinAtOrderOut_fromRec2AtOrderTrueAnalytic (m := m) (s := s0))

end XiPacket
end Targets
end Hyperlocal
