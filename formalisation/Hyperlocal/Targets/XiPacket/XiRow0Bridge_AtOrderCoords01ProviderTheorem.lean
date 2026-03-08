import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

/-- Theorem surface exposing the analytic coords01 result.
    We deliberately DO NOT install a typeclass instance here yet,
    because it requires additional boundary structure. -/
theorem xiAtOrderCoords01Out_theorem
    (m : ℕ) (s : OffSeed Xi) [A0Nonzero (s := s)] :
    XiAtOrderCoords01Out m s :=
  xiAtOrderCoords01Out_fromAnalytic (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
