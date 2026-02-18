/-
  Hyperlocal/Targets/OffSeedPhaseLockXiPayload.lean

  PATCH (Option A compatible):
  `WindowPayloadFacts.exists_kappa_sinlog2_sinlog3` now needs an explicit
  Re-κ witness `hKapRe`.  For the non-jet (Plan C++) payload, this witness
  is exactly `hC.hkappa` from `XiLemmaC`.

  Key point:
  we pass `hC.hkappa` through, after a `simp` rewrite that identifies
  `X.w0/X.wc/X.ws` with the definitional ξ windows.
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
  -- keep the Lemma-C bundle in scope so we can reuse its Re-κ witness
  let hC : XiLemmaC (s := s) := xiWindowLemmaC_fromRecurrence (s := s)
  -- payload constructed from that bundle
  let X : WindowPayload (σ s) (t s) := xiWindowPayload (s := s) (hC := hC)

  -- Re-κ witness in the shape expected by `WindowPayloadFacts`
  have hKapRe :
      kappa (reVec3 X.w0) (reVec3 X.wc) (reVec3 X.ws) ≠ 0 := by
    -- `X` is definitional payload built from `(w0,wc,ws,...)`, so this is just `hC.hkappa`
    simpa [X, xiWindowPayload, xiWindowPayload_of_C, windowPayload_mk_of_BC_offSeed,
      windowPayload_mk_of_BC] using hC.hkappa

  -- now call the smoke-test lemma with the explicit κ witness
  simpa [XiPacket.t, XiPacket.σ, X] using
    (WindowPayload.exists_kappa_sinlog2_sinlog3 (X := X) (hKapRe := hKapRe))

end OffSeedPhaseLockXiPayload
end Targets
end Hyperlocal
