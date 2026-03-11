/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01ProviderAxiom.lean

  DAG-clean *axiom* instance for coords01-at-order.

  Purpose:
  * extractor/upstream-safe fallback instance
  * MUST NOT import Rec2-at-order / extractor / heart discharge modules

  NOTE:
  We intentionally keep the historical compatibility name
    `xiAtOrderCoords01Out_axiom_stub`
  alive here until the adapter/importer cone is fully evacuated.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

axiom xiAtOrderCoords01Out_axiom_stub
    (m : ℕ) (s : OffSeed Xi) :
    XiAtOrderCoords01Out m s

instance : XiAtOrderCoords01Provider where
  coords01 := xiAtOrderCoords01Out_axiom_stub

end XiPacket
end Targets
end Hyperlocal
