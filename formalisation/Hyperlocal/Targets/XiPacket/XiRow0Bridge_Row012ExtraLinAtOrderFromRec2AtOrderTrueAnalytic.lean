/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ExtraLinAtOrderFromRec2AtOrderTrueAnalytic.lean

  Theorem-side coords01 -> extra-lin bridge from the ROOT-FREE Rec2-at-order corridor.

  IMPORTANT:
  * theorem-level only
  * requires the Rec2 provider gate explicitly
  * does NOT import the analytic extractor corridor
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderFromRec2AtOrderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinToCoords
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_A0NonzeroBoundary

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

theorem xiRow012ExtraLinAtOrderOut_fromRec2AtOrderTrueAnalytic
    [XiJetQuotRec2AtOrderProvider]
    (m : ℕ) (s : OffSeed Xi) [A0Nonzero (s := s)] :
    XiRow012ExtraLinAtOrderOut m s := by
  have HC : XiAtOrderCoords01Out m s :=
    xiAtOrderCoords01Out_fromRec2AtOrderTrueAnalytic (m := m) (s := s)

  refine ⟨?_, ?_, ?_⟩
  · exact row012ExtraLin_of_coords (s := s) (w := w0At m s) HC.hw0At0 HC.hw0At1
  · exact row012ExtraLin_of_coords (s := s) (w := wp2At m s) HC.hwp2At0 HC.hwp2At1
  · exact row012ExtraLin_of_coords (s := s) (w := wp3At m s) HC.hwp3At0 HC.hwp3At1

end XiPacket
end Targets
end Hyperlocal
