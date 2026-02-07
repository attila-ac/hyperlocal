/-
  Hyperlocal/Targets/OffSeedPhaseLockXiPayload.lean

  New Plan C++ endpoint:

  We obtain the Stage-3 “phase lock” contract for ξ by:
    1) using the single semantic bundle `XiLemmaC s`
    2) building the definitional WindowPayload via `xiWindowPayload`
    3) using the already-green `WindowPayloadFacts` pipeline

  No κ closed-form file is imported here.
-/

import Hyperlocal.Transport.OffSeedBridge
import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Targets.XiPacket.WindowPayloadFacts
import Hyperlocal.Targets.XiPacket.XiWindowLemmaC
import Hyperlocal.Targets.XiPacket.XiWindowLemmaC_FromRecurrence
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace OffSeedPhaseLockXiPayload

open scoped Real

open Hyperlocal.Transport
open Hyperlocal.Targets.XiPacket

/-- Build the full `WindowPayload` for ξ from the single Lemma-C bundle. -/
def xiWindowPayload_of_window (s : Hyperlocal.OffSeed Xi) :
    WindowPayload (σ s) (t s) :=
  xiWindowPayload (s := s)
    (hC := xiWindowLemmaC_fromRecurrence (s := s))

/--
Main deliverable for the Stage-3 bridge:
`OffSeedPhaseLock ξ` obtained purely from `WindowPayloadFacts`.
-/
theorem offSeedPhaseLock_Xi : Hyperlocal.Transport.OffSeedPhaseLock Xi := by
  intro s
  simpa [XiPacket.t, XiPacket.σ] using
    (WindowPayload.exists_kappa_sinlog2_sinlog3 (X := xiWindowPayload_of_window (s := s)))

end OffSeedPhaseLockXiPayload
end Targets
end Hyperlocal
