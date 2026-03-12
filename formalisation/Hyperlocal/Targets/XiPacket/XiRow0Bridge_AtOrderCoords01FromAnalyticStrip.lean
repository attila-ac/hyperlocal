/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01FromAnalyticStrip.lean
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Defs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromAnalyticExtractorStrip

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Complex
open Hyperlocal.Transport

theorem xiAtOrderCoords01Out_fromAnalytic_strip
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiAtOrderCoords01Out m (s : OffSeed Xi) :=
  xiAtOrderCoords01Out_fromAnalyticExtractor_strip (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
