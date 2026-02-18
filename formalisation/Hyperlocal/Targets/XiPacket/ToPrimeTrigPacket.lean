/-
  Hyperlocal/Targets/XiPacket/ToPrimeTrigPacket.lean

  FULL REPLACEMENT (Option A compatible, Prop→Type safe).

  WindowPayload.hkappa is Or-shaped, but PrimeTrigPacket.Packet.hkappa is Re-κ only.
  Therefore:
    • the Type-valued conversion takes explicit `hKapRe : Re-κ ≠ 0`.
    • we do NOT attempt any “convenience wrapper” that destructs Prop (Or/Exists)
      to build a Type (Packet), which Lean forbids.

  No new axioms.
-/

import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.WindowPayload
import Hyperlocal.Targets.XiPacket.Vectorize
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
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
  simp [Complex.mul_re]

/--
Convert a semantic window payload into the exact trig packet consumed by `PrimeSineRescue`.

NOTE: `PrimeTrigPacket.Packet` expects the **Re-lane** κ witness, so we take it
as an explicit argument.
-/
def WindowPayload.toPrimeTrigPacket {σ t : ℝ} (X : WindowPayload σ t)
    (hKapRe : kappa (reVec3 X.w0) (reVec3 X.wc) (reVec3 X.ws) ≠ 0) :
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
      simpa using hKapRe }

  · intro i
    have h := congrArg Complex.re (X.hw2 i)
    simpa [reVec3, Complex.add_re] using h

  · intro i
    have h := congrArg Complex.re (X.hw3 i)
    simpa [reVec3, Complex.add_re] using h

end XiPacket
end Targets
end Hyperlocal
