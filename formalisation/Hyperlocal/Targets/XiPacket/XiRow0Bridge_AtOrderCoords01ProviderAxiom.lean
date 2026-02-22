/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01ProviderAxiom.lean

  DAG-clean placeholder instance: provides coords01 by axiom.

  Import this in analytic-only upstream provider modules to keep the project building
  while the true analytic proof is installed.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

/-- Placeholder (DAG-clean) coords01 provider. Replace by a theorem-level instance later. -/
axiom xiAtOrderCoords01Out_axiom
    (m : ℕ) (s : OffSeed Xi) : XiAtOrderCoords01Out m s

instance : XiAtOrderCoords01Provider where
  coords01 := xiAtOrderCoords01Out_axiom

end XiPacket
end Targets
end Hyperlocal
