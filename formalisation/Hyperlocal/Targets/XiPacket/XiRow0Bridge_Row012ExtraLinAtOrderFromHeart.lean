/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ExtraLinAtOrderFromHeart.lean

  Pure projection (cycle-safe):

  Rebuild `Row012ExtraLin` for the three AtOrder windows from the
  coordinate vanishings (w0=0 and w1=0) delivered by a minimal boundary.

  NOTE:
  The coordinate vanishings are no longer part of the Heart contract; they live in
  `XiRow0Bridge_AtOrderCoords01FromAnalytic.lean` as a minimal admitted boundary
  (intended to be discharged extractor-side later).
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinToCoords
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

/-- Prop bundle: extra linear constraints for the three AtOrder windows. -/
structure XiRow012ExtraLinAtOrderOut (m : ℕ) (s : OffSeed Xi) : Prop where
  hw0At  : Row012ExtraLin s (w0At m s)
  hwp2At : Row012ExtraLin s (wp2At m s)
  hwp3At : Row012ExtraLin s (wp3At m s)

/-- Projection: coordinate vanishings imply the extra-lin bundle. -/
theorem xiRow012ExtraLinAtOrderOut_fromHeart
    (m : ℕ) (s : OffSeed Xi) :
    XiRow012ExtraLinAtOrderOut m s := by
  have HC : XiAtOrderCoords01Out m s :=
    xiAtOrderCoords01Out_fromAnalytic (m := m) (s := s)

  refine ⟨?_, ?_, ?_⟩
  · exact row012ExtraLin_of_coords (s := s) (w := w0At m s) HC.hw0At0 HC.hw0At1
  · exact row012ExtraLin_of_coords (s := s) (w := wp2At m s) HC.hwp2At0 HC.hwp2At1
  · exact row012ExtraLin_of_coords (s := s) (w := wp3At m s) HC.hwp3At0 HC.hwp3At1

end XiPacket
end Targets
end Hyperlocal
