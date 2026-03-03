/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceKappaAt0Nonzero.lean

  Minimal semantic seam for the Toeplitz identity route:

      kappaAt0 s ≠ 0

  NOTE:
  There is no global `kappaAt0` identifier in the repo; the order-0 κ used by
  the Toeplitz identity route is:
    Transport.kappa (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (ws s)).
  We package that as a local abbrev here.
-/

import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs  -- brings `w0At`
import Hyperlocal.Targets.XiPacket.Vectorize             -- brings `reVec3`

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport.PrimeTrigPacket
open Hyperlocal.Transport

/-- The “order-0 κ” used by the Toeplitz identity route. -/
abbrev kappaAt0 (s : Hyperlocal.OffSeed Xi) : ℝ :=
  Transport.kappa (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (ws s))

/-- Minimal nonvanishing seam needed by the order-0 Toeplitz identity solver. -/
class XiKappaAt0Nonzero (s : Hyperlocal.OffSeed Xi) : Prop :=
  (kappa_ne0 : kappaAt0 s ≠ 0)

end XiPacket
end Targets
end Hyperlocal
