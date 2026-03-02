/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceIdentity.lean

  Option-ELL implementation (cycle-safe, no deleted lemmas).

  Derive bCoeff(p)=0 for p∈{2,3} using:
    • ell-out from recurrence at order m=0
    • κ≠0 at order m=0 from κ closed form + legacy anchor axiom
        xi_sc_re_ne_zero : (Xi (sc s)).re ≠ 0

  NOTE (2026-03-02):
  This is the same temporary policy as OffSeedPhaseLockXiPayload:
  the downstream Packet consumer wants Re-κ, so we stay at m=0 until that
  boundary is widened.
-/

import Mathlib.Tactic
import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrder
import Hyperlocal.Targets.XiPacket.XiLemmaC_RecurrenceToEllKappaAtOrder
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedFormAtOrder
import Hyperlocal.Targets.XiPacket.XiWindowScNonvanishing

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- Helper: Re-κ ≠ 0 at order 0 from closed form + `xi_sc_re_ne_zero`. -/
theorem xi_kappaAt0_ne0 (s : Hyperlocal.OffSeed Xi) :
    Transport.kappa (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0 := by
  intro hk0
  -- κ closed form at order 0
  have hk :
      Transport.kappa (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (ws s))
        = (((cderivIter (0:ℕ) Xi) (sc s))).re :=
    XiLemmaC_kappa_closedFormAt (m := (0:ℕ)) (s := s)
  have hRe0 : (((cderivIter (0:ℕ) Xi) (sc s))).re = 0 :=
    hk.symm.trans hk0
  -- unwrap cderivIter 0 to Xi
  have : (Xi (sc s)).re = 0 := by
    simpa [cderivIter] using hRe0
  exact xi_sc_re_ne_zero (s := s) this

theorem xiToeplitzRecurrenceIdentity_p (s : Hyperlocal.OffSeed Xi)
    (p : ℝ) (hp : p = (2 : ℝ) ∨ p = (3 : ℝ)) :
    bCoeff (σ s) (t s) p = 0 := by
  have hkappaAt :
      Transport.kappa (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0 :=
    xi_kappaAt0_ne0 (s := s)

  rcases hp with rfl | rfl
  ·
    have hell2 :
        Transport.ell (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (wp2At 0 s)) = 0 :=
      (xiToeplitzEllOutAt_fromRecurrenceC (m := (0:ℕ)) (s := s)).hell2

    have hmul :
        bCoeff (σ s) (t s) (2 : ℝ)
          * Transport.kappa (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 := by
      calc
        bCoeff (σ s) (t s) (2 : ℝ)
            * Transport.kappa (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (ws s))
            =
          Transport.ell (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (wp2At 0 s)) := by
            simpa using (ell_wp2At_eq_b_mul_kappa (m := (0:ℕ)) (s := s)).symm
        _ = 0 := hell2

    have hdisj :
        bCoeff (σ s) (t s) (2 : ℝ) = 0 ∨
        Transport.kappa (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 :=
      mul_eq_zero.mp hmul

    exact hdisj.resolve_right hkappaAt
  ·
    have hell3 :
        Transport.ell (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (wp3At 0 s)) = 0 :=
      (xiToeplitzEllOutAt_fromRecurrenceC (m := (0:ℕ)) (s := s)).hell3

    have hmul :
        bCoeff (σ s) (t s) (3 : ℝ)
          * Transport.kappa (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 := by
      calc
        bCoeff (σ s) (t s) (3 : ℝ)
            * Transport.kappa (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (ws s))
            =
          Transport.ell (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (wp3At 0 s)) := by
            simpa using (ell_wp3At_eq_b_mul_kappa (m := (0:ℕ)) (s := s)).symm
        _ = 0 := hell3

    have hdisj :
        bCoeff (σ s) (t s) (3 : ℝ) = 0 ∨
        Transport.kappa (reVec3 (w0At 0 s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 :=
      mul_eq_zero.mp hmul

    exact hdisj.resolve_right hkappaAt

end XiPacket
end Targets
end Hyperlocal
