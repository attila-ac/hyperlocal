/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01ProviderCompatTheorem.lean
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderTheorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromAnalyticStrip

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Transport

theorem xiAtOrderCoords01Out_compat_theorem
    (m : ℕ) (s : OffSeed Xi) [A0Nonzero (s := s)] :
    XiAtOrderCoords01Out m s := by
  exact xiAtOrderCoords01Out_theorem (m := m) (s := s)

theorem xiAtOrderCoords01Out_compat_theorem_strip
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiAtOrderCoords01Out m (s : OffSeed Xi) := by
  exact xiAtOrderCoords01Out_fromAnalytic_strip (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
