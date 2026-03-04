/-
  Historical name `xiAtOrderCoords01Out_axiom`.

  IMPORTANT (new meaning):
  This is no longer an axiom. It is a theorem derived from the
  TRUE-ANALYTIC Rec2-at-order route (plus A0NonzeroBoundary).

  We preserve the old constant name for downstream stability.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderFromRec2AtOrderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-- Historical name (was an axiom): now a theorem from the Rec2-at-order route. -/
theorem xiAtOrderCoords01Out_axiom
    (m : ℕ) (s : OffSeed Xi) : XiAtOrderCoords01Out m s :=
  xiAtOrderCoords01Out_fromRec2AtOrderTrueAnalytic (m := m) (s := s)

/-- Historical provider instance site; now backed by the theorem above. -/
instance (priority := 10) : XiAtOrderCoords01Provider where
  coords01 := xiAtOrderCoords01Out_axiom

end XiPacket
end Targets
end Hyperlocal
