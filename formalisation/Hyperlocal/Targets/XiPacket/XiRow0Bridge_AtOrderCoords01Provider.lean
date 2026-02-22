/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01Provider.lean

  DAG-clean interface: provide the coords01 bundle for AtOrder windows.

  This isolates the dependency choice:
  * DAG-clean: axiom instance (for now)
  * non-cycle-safe: extractor instance (glue)
  * future: true analytic proof instance
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Defs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

/-- Provider of the AtOrder coords01 bundle (0/1 coordinate vanishings for w0At/wp2At/wp3At). -/
class XiAtOrderCoords01Provider : Type where
  coords01 : ∀ (m : ℕ) (s : OffSeed Xi), XiAtOrderCoords01Out m s

/-- Canonical accessor. -/
theorem xiAtOrderCoords01Out_provided
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderCoords01Provider] :
    XiAtOrderCoords01Out m s :=
  XiAtOrderCoords01Provider.coords01 (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
