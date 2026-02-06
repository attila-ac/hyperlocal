/-
  Hyperlocal/Targets/XiPacket/WindowPayloadFacts.lean

  Phase 1 “smoke tests” (pure algebra, no ξ / transport semantics):

    WindowPayload σ t
      → ∃ κ ≠ 0, sin(t log 2)=0 ∧ sin(t log 3)=0

  Optionally also expose the intermediate facts:
    → bCoeff σ t 2 = 0 and bCoeff σ t 3 = 0

  This file must remain semantic-free: it should compile without importing ξ,
  XiTransportOp, Toeplitz, or any analytic statements.
-/

import Hyperlocal.Targets.XiPacket.ToPrimeTrigPacket
import Hyperlocal.Transport.PrimeTrigPacket
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real

open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- Main smoke-test: payload implies the two-prime sine equalities (and supplies κ ≠ 0). -/
theorem WindowPayload.exists_kappa_sinlog2_sinlog3
    {σ t : ℝ} (X : WindowPayload σ t) :
    ∃ κ : ℝ, κ ≠ 0 ∧
      Real.sin (t * Real.log (2 : ℝ)) = 0 ∧
      Real.sin (t * Real.log (3 : ℝ)) = 0 := by
  -- just compose the already-green pipeline:
  -- WindowPayload → Packet → (κ ≠ 0 ∧ sin(...) = 0 ∧ sin(...) = 0)
  simpa using
    Hyperlocal.Transport.PrimeTrigPacket.offSeedPhaseLock_of_packet
      (X.toPrimeTrigPacket)

/-- Optional: payload forces the sine-coefficient at p=2 to vanish (bCoeff σ t 2 = 0). -/
theorem WindowPayload.bCoeff_two_eq_zero
    {σ t : ℝ} (X : WindowPayload σ t) :
    bCoeff σ t (2 : ℝ) = 0 := by
  classical
  let P : PrimeTrigPacket.Packet σ t := X.toPrimeTrigPacket
  -- determinant rescue gives b=0 from ell(up)=0 and κ≠0
  exact Hyperlocal.Transport.coeff_eq_zero_of_ell_eq_zero
    (u0 := P.u0) (uc := P.uc) (us := P.us) (up := P.up2)
    (a := aCoeff σ t (2 : ℝ)) (b := bCoeff σ t (2 : ℝ))
    (hup := PrimeTrigPacket.hup2_vec P)
    (hEll := P.hell2)
    (hk := P.hkappa)

/-- Optional: payload forces the sine-coefficient at p=3 to vanish (bCoeff σ t 3 = 0). -/
theorem WindowPayload.bCoeff_three_eq_zero
    {σ t : ℝ} (X : WindowPayload σ t) :
    bCoeff σ t (3 : ℝ) = 0 := by
  classical
  let P : PrimeTrigPacket.Packet σ t := X.toPrimeTrigPacket
  exact Hyperlocal.Transport.coeff_eq_zero_of_ell_eq_zero
    (u0 := P.u0) (uc := P.uc) (us := P.us) (up := P.up3)
    (a := aCoeff σ t (3 : ℝ)) (b := bCoeff σ t (3 : ℝ))
    (hup := PrimeTrigPacket.hup3_vec P)
    (hEll := P.hell3)
    (hk := P.hkappa)

end XiPacket
end Targets
end Hyperlocal
