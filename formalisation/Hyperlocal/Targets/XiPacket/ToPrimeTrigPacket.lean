/-
  Hyperlocal/Targets/XiPacket/ToPrimeTrigPacket.lean

  Pure packaging:
    WindowPayload (complex windows + window-level prime relations + ell/kappa facts)
      ⟶ PrimeTrigPacket.Packet (the exact Stage-3 trig packet).

  No ξ/Toeplitz semantics are used here: it’s just “take Re componentwise” and simp.

  NOTE:
  We use `reVec3`. If you later decide to vectorize using an imaginary lane
  instead, swap `reVec3` to `imVec3` everywhere (after adding `imVec3` in
  `Vectorize.lean`).
-/

import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.WindowPayload
import Hyperlocal.Targets.XiPacket.Vectorize
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real

open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- Helper simp lemma: for real scalars, real-part commutes with multiplication. -/
@[simp] lemma re_ofReal_mul (r : ℝ) (z : ℂ) :
    (((r : ℂ) * z).re) = r * z.re := by
  -- `Complex.mul_re` expands to `r*z.re - 0*z.im` when `r` is real.
  simp [Complex.mul_re]

/--
Convert the semantic window payload into the exact trig packet
consumed by `PrimeSineRescue`.
-/
def WindowPayload.toPrimeTrigPacket {σ t : ℝ} (X : WindowPayload σ t) :
    PrimeTrigPacket.Packet σ t := by
  classical
  refine
  { u0 := reVec3 X.w0
    uc := reVec3 X.wc
    us := reVec3 X.ws
    up2 := reVec3 X.wp2
    up3 := reVec3 X.wp3
    hup2 := ?_
    hup3 := ?_
    hell2 := by
      simpa using X.hell2
    hell3 := by
      simpa using X.hell3
    hkappa := by
      simpa using X.hkappa }

  · intro i
    have h := congrArg Complex.re (X.hw2 i)
    -- goal is exactly the real-part form of the window identity
    simpa [reVec3, Complex.add_re] using h

  · intro i
    have h := congrArg Complex.re (X.hw3 i)
    simpa [reVec3, Complex.add_re] using h

end XiPacket
end Targets
end Hyperlocal
