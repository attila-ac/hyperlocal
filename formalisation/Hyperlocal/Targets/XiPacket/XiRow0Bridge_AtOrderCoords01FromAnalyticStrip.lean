/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01FromAnalyticStrip.lean

  Non-cycle-safe *strip* export layer.
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Defs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromAnalyticExtractorStrip

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Strip-specialised discharged coords bundle from the analytic extractor. -/
theorem xiAtOrderCoords01Out_fromAnalytic_strip
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi) :
    XiAtOrderCoords01Out m (s : OffSeed Xi) :=
  xiAtOrderCoords01Out_fromAnalyticExtractor_strip (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
