/-
  Hyperlocal/Targets/XiPacket/WindowPayload.lean

  FULL REPLACEMENT (Option A: widen κ-witness to accept Re-κ OR Im-κ).

  Change:
    `hkappa` is now an `Or` of the two κ-shapes:

      (kappa (reVec3 w0) (reVec3 wc) (reVec3 ws) ≠ 0)
      ∨
      (kappa (imVec3 w0) (reVec3 wc) (reVec3 ws) ≠ 0)

  No new axioms.
-/

import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.Vectorize
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- Phase-4 payload (Plan C++ / C++J). -/
structure WindowPayload (σ t : ℝ) : Type where
  w0  : Transport.Window 3
  wc  : Transport.Window 3
  ws  : Transport.Window 3
  wp2 : Transport.Window 3
  wp3 : Transport.Window 3

  -- Lemma B (trig split) at p=2,3
  hw2 :
    ∀ i : Fin 3,
      wp2 i = w0 i
        + ((aCoeff σ t (2 : ℝ) : ℂ) * (wc i))
        + ((bCoeff σ t (2 : ℝ) : ℂ) * (ws i))
  hw3 :
    ∀ i : Fin 3,
      wp3 i = w0 i
        + ((aCoeff σ t (3 : ℝ) : ℂ) * (wc i))
        + ((bCoeff σ t (3 : ℝ) : ℂ) * (ws i))

  -- Lemma C consequences
  hell2 : Transport.ell (reVec3 w0) (reVec3 wc) (reVec3 wp2) = 0
  hell3 : Transport.ell (reVec3 w0) (reVec3 wc) (reVec3 wp3) = 0

  /--
  κ-witness (widened): either the real-block κ is nonzero OR the imag-first-column κ is nonzero.
  -/
  hkappa :
    (Transport.kappa (reVec3 w0) (reVec3 wc) (reVec3 ws) ≠ 0)
    ∨ (Transport.kappa (imVec3 w0) (reVec3 wc) (reVec3 ws) ≠ 0)

end XiPacket
end Targets
end Hyperlocal
