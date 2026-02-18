/-
  Hyperlocal/Targets/XiPacket/WindowPayloadFacts.lean

  Phase 1 “smoke tests” (pure algebra, no ξ / transport semantics):

    WindowPayload σ t
      → (given Re-κ witness) ∃ κ ≠ 0, sin(t log 2)=0 ∧ sin(t log 3)=0

  IMPORTANT (Option A):
    WindowPayload.hkappa is Or-shaped, but PrimeTrigPacket.Packet expects Re-κ only.
    Therefore these smoke tests take an explicit hypothesis
      hKapRe : kappa (reVec3 ...) ≠ 0
    to build the Packet.

  No ξ, Toeplitz, or analytic imports here.
-/

import Hyperlocal.Targets.XiPacket.ToPrimeTrigPacket
import Hyperlocal.Transport.PrimeTrigPacket
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- Main smoke-test: from payload + Re-κ, get the two-prime sine equalities (and κ ≠ 0). -/
theorem WindowPayload.exists_kappa_sinlog2_sinlog3
    {σ t : ℝ} (X : WindowPayload σ t)
    (hKapRe : kappa (reVec3 X.w0) (reVec3 X.wc) (reVec3 X.ws) ≠ 0) :
    ∃ κ : ℝ, κ ≠ 0 ∧
      Real.sin (t * Real.log (2 : ℝ)) = 0 ∧
      Real.sin (t * Real.log (3 : ℝ)) = 0 := by
  -- WindowPayload → Packet → phase-lock output
  -- (now we must supply `hKapRe` explicitly)
  simpa using
    Hyperlocal.Transport.PrimeTrigPacket.offSeedPhaseLock_of_packet
      (X.toPrimeTrigPacket (hKapRe := hKapRe))

/-- Optional: payload + Re-κ forces `bCoeff σ t 2 = 0`. -/
theorem WindowPayload.bCoeff_two_eq_zero
    {σ t : ℝ} (X : WindowPayload σ t)
    (hKapRe : kappa (reVec3 X.w0) (reVec3 X.wc) (reVec3 X.ws) ≠ 0) :
    bCoeff σ t (2 : ℝ) = 0 := by
  classical
  let P : PrimeTrigPacket.Packet σ t := X.toPrimeTrigPacket (hKapRe := hKapRe)
  -- determinant rescue gives b=0 from ell(up)=0 and κ≠0
  exact Hyperlocal.Transport.coeff_eq_zero_of_ell_eq_zero
    (u0 := P.u0) (uc := P.uc) (us := P.us) (up := P.up2)
    (a := aCoeff σ t (2 : ℝ)) (b := bCoeff σ t (2 : ℝ))
    (hup := PrimeTrigPacket.hup2_vec P)
    (hEll := P.hell2)
    (hk := P.hkappa)

/-- Optional: payload + Re-κ forces `bCoeff σ t 3 = 0`. -/
theorem WindowPayload.bCoeff_three_eq_zero
    {σ t : ℝ} (X : WindowPayload σ t)
    (hKapRe : kappa (reVec3 X.w0) (reVec3 X.wc) (reVec3 X.ws) ≠ 0) :
    bCoeff σ t (3 : ℝ) = 0 := by
  classical
  let P : PrimeTrigPacket.Packet σ t := X.toPrimeTrigPacket (hKapRe := hKapRe)
  exact Hyperlocal.Transport.coeff_eq_zero_of_ell_eq_zero
    (u0 := P.u0) (uc := P.uc) (us := P.us) (up := P.up3)
    (a := aCoeff σ t (3 : ℝ)) (b := bCoeff σ t (3 : ℝ))
    (hup := PrimeTrigPacket.hup3_vec P)
    (hEll := P.hell3)
    (hk := P.hkappa)

end XiPacket
end Targets
end Hyperlocal
