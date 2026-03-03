/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceIdentity.lean

  Option-ELL implementation (cycle-safe, no deleted lemmas).

  Derive bCoeff(p)=0 for p∈{2,3} using:
    • ell-out from recurrence at order m=0
    • κ≠0 at order m=0 provided as a *minimal class seam*:
        [XiKappaAt0Nonzero s]

  NOTE (2026-03-03):
  This file NO LONGER imports the legacy anchor seam directly.
  The temporary provider of `[XiKappaAt0Nonzero s]` (if you still need one)
  should live in a separate injector file.
-/

import Mathlib.Tactic
import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrder
import Hyperlocal.Targets.XiPacket.XiLemmaC_RecurrenceToEllKappaAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceKappaAt0Nonzero

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- The `κ`-nonvanishing hypothesis needed by the identity route, packaged as `kappaAt0`. -/
theorem xi_kappaAt0_ne0 (s : Hyperlocal.OffSeed Xi) [XiKappaAt0Nonzero s] :
    kappaAt0 s ≠ 0 :=
  (XiKappaAt0Nonzero.kappa_ne0 (s := s))

/--
Order-0 Toeplitz identity route:
if `p` is either `2` or `3`, recurrence ell-out at `m=0` forces `bCoeff(p)=0`,
provided `kappaAt0 s ≠ 0`.

(Kept in the older “`p : ℝ` + disjunction” shape to match the rest of the packet.)
-/
theorem xiToeplitzRecurrenceIdentity_p (s : Hyperlocal.OffSeed Xi) [XiKappaAt0Nonzero s]
    (p : ℝ) (hp : p = (2 : ℝ) ∨ p = (3 : ℝ)) :
    bCoeff (σ s) (t s) p = 0 := by
  have hkappaAt : kappaAt0 s ≠ 0 := xi_kappaAt0_ne0 (s := s)

  rcases hp with rfl | rfl
  ·
    have hell2 :
        Transport.ell (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (wp2At 0 s)) = 0 :=
      (xiToeplitzEllOutAt_fromRecurrenceC (m := (0:ℕ)) (s := s)).hell2

    have hmul :
        bCoeff (σ s) (t s) (2 : ℝ) * kappaAt0 s = 0 := by
      calc
        bCoeff (σ s) (t s) (2 : ℝ) * kappaAt0 s
            =
          Transport.ell (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (wp2At 0 s)) := by
            -- unfold only the local abbrev; keep `wc/ws` opaque
            simpa [kappaAt0] using
              (ell_wp2At_eq_b_mul_kappa (m := (0:ℕ)) (s := s)).symm
        _ = 0 := hell2

    have hdisj :
        bCoeff (σ s) (t s) (2 : ℝ) = 0 ∨ kappaAt0 s = 0 :=
      mul_eq_zero.mp hmul

    exact hdisj.resolve_right hkappaAt
  ·
    have hell3 :
        Transport.ell (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (wp3At 0 s)) = 0 :=
      (xiToeplitzEllOutAt_fromRecurrenceC (m := (0:ℕ)) (s := s)).hell3

    have hmul :
        bCoeff (σ s) (t s) (3 : ℝ) * kappaAt0 s = 0 := by
      calc
        bCoeff (σ s) (t s) (3 : ℝ) * kappaAt0 s
            =
          Transport.ell (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (wp3At 0 s)) := by
            simpa [kappaAt0] using
              (ell_wp3At_eq_b_mul_kappa (m := (0:ℕ)) (s := s)).symm
        _ = 0 := hell3

    have hdisj :
        bCoeff (σ s) (t s) (3 : ℝ) = 0 ∨ kappaAt0 s = 0 :=
      mul_eq_zero.mp hmul

    exact hdisj.resolve_right hkappaAt

end XiPacket
end Targets
end Hyperlocal
