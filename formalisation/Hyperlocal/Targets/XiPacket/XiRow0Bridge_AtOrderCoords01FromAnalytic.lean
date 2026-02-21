/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01FromAnalytic.lean

  Cycle-safe admitted boundary (minimal):

  Provide the coordinate vanishings
    w 0 = 0 and w 1 = 0
  for each of the three AtOrder windows.

  Rationale:
  * These are exactly what is needed to rebuild Row012ExtraLin via
      row012ExtraLin_of_coords
    (pure algebra, cycle-safe).
  * The “real” derivation is intended to live in the analytic extractor loop
    (see XiRow0Bridge_AtOrderCoords01FromAnalyticExtractor.lean), but this file
    stays cycle-safe for the Row012 discharge DAG.
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Bundle: coordinate vanishings w0=0 and w1=0 for the three AtOrder windows. -/
structure XiAtOrderCoords01Out (m : ℕ) (s : OffSeed Xi) : Prop where
  hw0At0  : (w0At m s) 0 = 0
  hw0At1  : (w0At m s) 1 = 0

  hwp2At0 : (wp2At m s) 0 = 0
  hwp2At1 : (wp2At m s) 1 = 0

  hwp3At0 : (wp3At m s) 0 = 0
  hwp3At1 : (wp3At m s) 1 = 0

/--
Admitted boundary (cycle-safe): the AtOrder coordinate vanishings.

Replace this axiom by a theorem once the extractor-side derivation is plugged in
without introducing cycles.
-/
axiom xiAtOrderCoords01Out_fromAnalytic
    (m : ℕ) (s : OffSeed Xi) : XiAtOrderCoords01Out m s

end XiPacket
end Targets
end Hyperlocal
