import Hyperlocal.Transport.OffSeedBridge
import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Targets.XiPacket.WindowPayloadFacts
import Hyperlocal.Targets.XiPacket.XiWindowPayloadFromRecurrenceAtOrder
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
  xiWindowPayload_fromRecurrence (s := s)

/--
Main deliverable for the Stage-3 bridge:
`OffSeedPhaseLock ξ` obtained purely from `WindowPayloadFacts`.
-/
theorem offSeedPhaseLock_Xi : Hyperlocal.Transport.OffSeedPhaseLock Xi := by
  intro s
  -- jet-pivot payload
  let X : WindowPayload (σ s) (t s) := xiWindowPayload_fromRecurrence (s := s)

  -- Re-κ witness in the shape expected by `WindowPayloadFacts`
  have hKapRe :
      kappa (reVec3 X.w0) (reVec3 X.wc) (reVec3 X.ws) ≠ 0 := by
    -- Recompute the chosen jet order and use the direct κ-leverage lemma.
    let m : ℕ := xiJetPivotOrder s
    have hmRe : (((cderivIter m Xi) (sc s))).re ≠ 0 := by
      simpa [m, xiJetPivotOrder] using xiJetPivotOrder_spec (s := s)
    have hKap : kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0 :=
      hkappaAt_re_of_cderivRe_ne0 (m := m) (s := s) hmRe
    -- now `X.w0 = w0At m s`, etc., by unfolding the payload definition
    simpa [X, xiWindowPayload_fromRecurrence, xiWindowPayloadAt_of_C, m] using hKap

  -- now call the smoke-test lemma with the explicit κ witness
  simpa [XiPacket.t, XiPacket.σ, X] using
    (WindowPayload.exists_kappa_sinlog2_sinlog3 (X := X) (hKapRe := hKapRe))

end OffSeedPhaseLockXiPayload
end Targets
end Hyperlocal
