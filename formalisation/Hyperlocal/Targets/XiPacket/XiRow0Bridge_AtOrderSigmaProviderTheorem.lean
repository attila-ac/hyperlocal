/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderSigmaProviderTheorem.lean

  Historical name `xiAtOrderSigmaOut_axiom`.

  IMPORTANT (new meaning):
  It is now a theorem derived from the Row0-frontier-at-order route.

  This preserves the old constant name for downstream stability,
  while removing it from the axiom cone.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcSpecFromRouteAStencil
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderFromRow0FrontierAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

/--
Historical name preserved for downstream stability.

Now derived from the Row0-frontier-at-order theorem route.
-/
theorem xiAtOrderSigmaOut_axiom
    (m : ℕ) (s : OffSeed Xi) : XiAtOrderSigmaOut m s :=
  xiAtOrderSigmaOut_fromRow0FrontierAtOrder (m := m) (s := s)

/--
Provider instance (historical site).

Backed by the theorem above instead of an axiom.
-/
instance (priority := 10) : XiAtOrderSigmaProvider where
  sigma := xiAtOrderSigmaOut_axiom

end XiPacket
end Targets
end Hyperlocal
