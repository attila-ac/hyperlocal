/-
  Formalisation/Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01FromRec2AtOrderTrueAnalyticStrip.lean

  Strip-specialised theorem wrapper for coords01 from the Rec2-at-order corridor.

  2026-03-12 retarget:
  * no local `A0Nonzero` reinstall
  * delegate to the strengthened true-analytic coords theorem
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderFromRec2AtOrderTrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Transport

theorem xiAtOrderCoords01Out_fromRec2AtOrderTrueAnalytic_strip
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi) :
    XiAtOrderCoords01Out m (s : OffSeed Xi) := by
  letI : XiJetQuotRec2AtOrderProvider := inferInstance
  let s0 : OffSeed Xi := (s : OffSeed Xi)
  simpa [s0] using
    (xiAtOrderCoords01Out_fromRec2AtOrderTrueAnalytic (m := m) (s := s0))

end XiPacket
end Targets
end Hyperlocal
