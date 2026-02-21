/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01FromAnalytic.lean

  Theorem-level discharge of the AtOrder coordinate vanishings bundle.

  This module defines the public name:

    `xiAtOrderCoords01Out_fromAnalytic : ∀ m s, XiAtOrderCoords01Out m s`

  by importing the extractor-side derivation
    `xiAtOrderCoords01Out_fromAnalyticExtractor`.

  NOTE:
  This file is intentionally NOT cycle-safe: it lives on the extractor/analytic side.
  Cycle-safe downstream modules should only depend on `...AtOrderCoords01Defs.lean`.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Defs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromAnalyticExtractor

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Discharged coords bundle from the analytic extractor. -/
theorem xiAtOrderCoords01Out_fromAnalytic
    (m : ℕ) (s : OffSeed Xi) : XiAtOrderCoords01Out m s :=
  xiAtOrderCoords01Out_fromAnalyticExtractor (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
