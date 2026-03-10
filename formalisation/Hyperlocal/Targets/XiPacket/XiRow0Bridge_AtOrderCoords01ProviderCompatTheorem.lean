/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01ProviderCompatTheorem.lean

  Theorem-only compatibility surface for coords01-at-order.

  IMPORTANT:
  * this file does NOT replace the historical DAG-clean installer root
  * it provides a theorem-backed sibling for downstream migration
  * use this in theorem corridors; do not import it into installer roots
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderTheorem

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

theorem xiAtOrderCoords01Out_compat_theorem
    (m : ℕ) (s : OffSeed Xi) : XiAtOrderCoords01Out m s := by
  exact xiAtOrderCoords01Out_theorem (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
