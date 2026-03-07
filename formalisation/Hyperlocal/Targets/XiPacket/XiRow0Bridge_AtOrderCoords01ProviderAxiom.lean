/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01ProviderAxiom.lean

  DAG-clean fallback installer for the coords01-at-order payload.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-- DAG-clean placeholder axiom for coords01-at-order output. -/
axiom xiAtOrderCoords01Out_axiom_stub
    (m : ℕ) (s : OffSeed Xi) : XiAtOrderCoords01Out m s

instance : XiAtOrderCoords01Provider where
  coords01 := xiAtOrderCoords01Out_axiom_stub

end XiPacket
end Targets
end Hyperlocal
