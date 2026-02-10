/-
  Hyperlocal/Targets/OffSeedPhaseLockXiPayloadAtOrder.lean

  Endpoint using the frozen “green” bCoeff interface + JetPivot nonvanishing (AtOrder),
  avoiding the old XiWindowLemmaC semantic cliff.
-/

import Hyperlocal.Transport.OffSeedBridge
import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Targets.XiPacket.WindowPayloadFacts
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotNonvanishingAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceInterface
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace OffSeedPhaseLockXiPayloadAtOrder

open scoped Real

open Hyperlocal.Transport
open Hyperlocal.Targets.XiPacket

/-- Build `WindowPayload` for ξ from hb2/hb3 (green interface) via JetPivot Nonvanishing (AtOrder). -/
def xiWindowPayload_of_window (s : Hyperlocal.OffSeed Xi) :
    WindowPayload (σ s) (t s) :=
  xiWindowPayload_of_hb2hb3 (s := s)
    (xiBcoeff2_eq_zero (s := s))
    (xiBcoeff3_eq_zero (s := s))

/-- Stage-3 bridge: `OffSeedPhaseLock ξ` from `WindowPayloadFacts`. -/
theorem offSeedPhaseLock_Xi : Hyperlocal.Transport.OffSeedPhaseLock Xi := by
  intro s
  simpa [XiPacket.t, XiPacket.σ] using
    (WindowPayload.exists_kappa_sinlog2_sinlog3 (X := xiWindowPayload_of_window (s := s)))

end OffSeedPhaseLockXiPayloadAtOrder
end Targets
end Hyperlocal
