/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderSigmaProviderTheorem.lean

  Historical name `xiAtOrderSigmaOut_axiom`.

  IMPORTANT (new meaning):
  It is a theorem derived from the
  Row0-frontier-at-order route.

  This preserves the old constant name for downstream stability, while
  removing it from the axiom-cone.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderFromRow0FrontierAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-- Historical name: now a theorem from the Row0-frontier route. -/
theorem xiAtOrderSigmaOut_axiom
    (m : ℕ) (s : OffSeed Xi) : XiAtOrderSigmaOut m s :=
  xiAtOrderSigmaOut_fromRow0FrontierAtOrder (m := m) (s := s)

/-- Keep the historical provider instance name/site; now backed by the theorem above. -/
instance (priority := 10) : XiAtOrderSigmaProvider where
  sigma := xiAtOrderSigmaOut_axiom

end XiPacket
end Targets
end Hyperlocal
