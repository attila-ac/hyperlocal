/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ExtraLinAtOrderFromProvidedCoords.lean

  Clean theorem-side Row012ExtraLin route from an abstract coords01 provider.

  IMPORTANT:
  * do NOT replace the historical FromHeart file in place
  * this file is the theorem-side sibling used only by consumers that already
    carry `[XiAtOrderCoords01Provider]`
  * keeps the historical analytic branch available for legacy/shared consumers
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinToCoords
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

theorem xiRow012ExtraLinAtOrderOut_fromProvidedCoords
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderCoords01Provider] :
    XiRow012ExtraLinAtOrderOut m s := by
  have HC : XiAtOrderCoords01Out m s :=
    xiAtOrderCoords01Out_provided (m := m) (s := s)

  refine ⟨?_, ?_, ?_⟩
  · exact row012ExtraLin_of_coords (s := s) (w := w0At m s) HC.hw0At0 HC.hw0At1
  · exact row012ExtraLin_of_coords (s := s) (w := wp2At m s) HC.hwp2At0 HC.hwp2At1
  · exact row012ExtraLin_of_coords (s := s) (w := wp3At m s) HC.hwp3At0 HC.hwp3At1

end XiPacket
end Targets
end Hyperlocal
