/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01ProviderFromAnalyticExtractor.lean

  Non-cycle-safe glue instance:

    coords01 provider := xiAtOrderCoords01Out_fromAnalytic

  This imports the extractor-derived theorem provider, so it must NOT be imported by
  analytic-only upstream modules.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

/-
  NOTE (Lean 4.23 rc2):
  `xiAtOrderCoords01Out_fromAnalytic` requires an implicit instance argument
  `[A0Nonzero (s := s)]`. If we assign it directly, elaboration may fail in some
  contexts because the implicit argument is not made available at the point
  where the record field is filled.

  Eta-expand so typeclass search runs after `s` is in scope.
-/
instance : XiAtOrderCoords01Provider where
  coords01 := by
    intro m s
    classical
    exact xiAtOrderCoords01Out_fromAnalytic (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
