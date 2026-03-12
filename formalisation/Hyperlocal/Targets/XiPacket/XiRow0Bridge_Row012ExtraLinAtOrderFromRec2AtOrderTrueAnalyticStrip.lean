/-
  Formalisation/Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ExtraLinAtOrderFromRec2AtOrderTrueAnalyticStrip.lean

  Strip-specialised theorem wrapper for the extra-lin bundle from the
  Rec2 true-analytic corridor.

  2026-03-12 cleanup:
  * do not call back into the global extra-lin wrapper
  * do not reinstall `A0Nonzero` here
  * derive extra-lin directly from the strip coords theorem
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromRec2AtOrderTrueAnalyticStrip
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinToCoords
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Transport

theorem xiRow012ExtraLinAtOrderOut_fromRec2AtOrderTrueAnalytic_strip
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi) :
    XiRow012ExtraLinAtOrderOut m (s : OffSeed Xi) := by
  letI : XiJetQuotRec2AtOrderProvider := inferInstance
  let s0 : OffSeed Xi := (s : OffSeed Xi)

  have HC : XiAtOrderCoords01Out m s0 :=
    xiAtOrderCoords01Out_fromRec2AtOrderTrueAnalytic_strip (m := m) (s := s)

  refine ⟨?_, ?_, ?_⟩
  · exact row012ExtraLin_of_coords (s := s0) (w := w0At m s0) HC.hw0At0 HC.hw0At1
  · exact row012ExtraLin_of_coords (s := s0) (w := wp2At m s0) HC.hwp2At0 HC.hwp2At1
  · exact row012ExtraLin_of_coords (s := s0) (w := wp3At m s0) HC.hwp3At0 HC.hwp3At1

end XiPacket
end Targets
end Hyperlocal
