/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01Defs.lean

  Cycle-safe defs-only layer:

  Defines the Prop-bundle `XiAtOrderCoords01Out m s` packaging the coordinate
  vanishings `w 0 = 0` and `w 1 = 0` for each of the three AtOrder windows
  `w0At/wp2At/wp3At`.

  IMPORTANT:
    This file must remain cycle-safe and contain ONLY definitions.
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Bundle: coordinate vanishings `w 0 = 0` and `w 1 = 0` for the three AtOrder windows. -/
structure XiAtOrderCoords01Out (m : ℕ) (s : OffSeed Xi) : Prop where
  hw0At0  : (w0At m s) 0 = 0
  hw0At1  : (w0At m s) 1 = 0

  hwp2At0 : (wp2At m s) 0 = 0
  hwp2At1 : (wp2At m s) 1 = 0

  hwp3At0 : (wp3At m s) 0 = 0
  hwp3At1 : (wp3At m s) 1 = 0

end XiPacket
end Targets
end Hyperlocal
