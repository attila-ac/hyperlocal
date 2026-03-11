/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01ProviderCompatTheorem.lean

  Theorem-only compatibility surface for coords01-at-order.

  IMPORTANT:
  * this file does NOT replace the historical DAG-clean installer root
  * it provides theorem-backed siblings for downstream migration
  * use this in theorem corridors; do not import it into installer roots

  2026-03-11 repair:
  the general compatibility theorem must expose the same boundary premise
  as the underlying analytic theorem route.
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderTheorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromAnalyticStrip

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

/--
General theorem-only compatibility surface.

This is theorem-backed, but it is intentionally **not** installed as a global
instance because the analytic route requires the explicit boundary premise
`[A0Nonzero (s := s)]`.
-/
theorem xiAtOrderCoords01Out_compat_theorem
    (m : ℕ) (s : OffSeed Xi) [A0Nonzero (s := s)] :
    XiAtOrderCoords01Out m s := by
  exact xiAtOrderCoords01Out_theorem (m := m) (s := s)

/--
Strip-specialised theorem-only compatibility surface.

This gives a theorem-backed downstream migration point on the strip branch
without reinstalling anything at the historical installer root.
-/
theorem xiAtOrderCoords01Out_compat_theorem_strip
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi) :
    XiAtOrderCoords01Out m (s : OffSeed Xi) := by
  exact xiAtOrderCoords01Out_fromAnalytic_strip (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
