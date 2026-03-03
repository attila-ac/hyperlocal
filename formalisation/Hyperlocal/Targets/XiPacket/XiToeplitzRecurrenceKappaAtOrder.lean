/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceKappaAtOrder.lean

  Jet-pivot κ definitions (order-m):

    kappaAt m s    := κ built from reVec3(w0At m s) with the fixed real triangular block
    kappaAtIm m s  := κ built from imVec3(w0At m s) with the same fixed real triangular block

  These match the closed-form theorems in `XiWindowKappaClosedFormAtOrder.lean`:
    XiLemmaC_kappa_closedFormAt
    XiLemmaC_kappa_closedFormAt_im
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs  -- w0At
import Hyperlocal.Targets.XiPacket.XiWindowDefs         -- wc, ws
import Hyperlocal.Targets.XiPacket.Vectorize            -- reVec3, imVec3
import Hyperlocal.Transport.PrimeTrigPacket

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- κ at order `m`, using the real-part first column. -/
abbrev kappaAt (m : ℕ) (s : Hyperlocal.OffSeed Xi) : ℝ :=
  Transport.kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s))

/-- κ at order `m`, using the imaginary-part first column but the same real triangular block. -/
abbrev kappaAtIm (m : ℕ) (s : Hyperlocal.OffSeed Xi) : ℝ :=
  Transport.kappa (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s))

end XiPacket
end Targets
end Hyperlocal
