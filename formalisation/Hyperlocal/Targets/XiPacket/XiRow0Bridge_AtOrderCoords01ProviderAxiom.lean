/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01ProviderAxiom.lean

  DAG-clean *axiom* instance for coords01-at-order.

  Purpose:
  * extractor/upstream-safe fallback instance
  * MUST NOT import Rec2-at-order / extractor / heart discharge modules

  NOTE:
  We intentionally DO NOT use the historical name `xiAtOrderCoords01Out_axiom` here,
  because that name is reserved for the theorem-level constant in
  `...ProviderTheorem.lean` (downstream stability / axiom elimination cone).
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

/-- DAG-clean provider instance backed by the axiom stub above. -/
instance (priority := 10) : XiAtOrderCoords01Provider where
  coords01 := xiAtOrderCoords01Out_axiom_stub

end XiPacket
end Targets
end Hyperlocal
