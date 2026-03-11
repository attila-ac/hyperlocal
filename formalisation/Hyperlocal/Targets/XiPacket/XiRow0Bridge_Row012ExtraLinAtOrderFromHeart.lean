/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ExtraLinAtOrderFromHeart.lean

  Pure projection from a coords01 payload.

  IMPORTANT:
  * stay theorem-level / cycle-safe
  * do NOT call the analytic coords extractor wrapper here
  * provide an explicit-coords theorem first
  * keep the historical provider-based wrapper for compatibility

  COMPAT NOTE:
  We keep `[A0Nonzero (s := s)]` in the signature to avoid downstream interface
  churn, even though the construction itself is now purely a projection from
  coords01.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
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

theorem xiRow012ExtraLinAtOrderOut_fromHeart_of_coords
    (m : ℕ) (s : OffSeed Xi)
    [A0Nonzero (s := s)]
    (HC : XiAtOrderCoords01Out m s) :
    XiRow012ExtraLinAtOrderOut m s := by
  refine ⟨?_, ?_, ?_⟩
  · exact row012ExtraLin_of_coords (s := s) (w := w0At m s) HC.hw0At0 HC.hw0At1
  · exact row012ExtraLin_of_coords (s := s) (w := wp2At m s) HC.hwp2At0 HC.hwp2At1
  · exact row012ExtraLin_of_coords (s := s) (w := wp3At m s) HC.hwp3At0 HC.hwp3At1

theorem xiRow012ExtraLinAtOrderOut_fromHeart
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderCoords01Provider] [A0Nonzero (s := s)] :
    XiRow012ExtraLinAtOrderOut m s := by
  have HC : XiAtOrderCoords01Out m s :=
    xiAtOrderCoords01Out_provided (m := m) (s := s)
  exact xiRow012ExtraLinAtOrderOut_fromHeart_of_coords
    (m := m) (s := s) HC

end XiPacket
end Targets
end Hyperlocal
