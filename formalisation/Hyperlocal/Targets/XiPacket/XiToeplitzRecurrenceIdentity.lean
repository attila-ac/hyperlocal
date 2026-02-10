/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceIdentity.lean

  Option-ELL implementation (no cyclic imports).

  Derive bCoeff(p)=0 for p∈{2,3} from:
    • ell-out from recurrence (semantic frontier): `xiToeplitzEllOut_fromRecurrence`
    • κ ≠ 0 from the anchor nonvanishing cliff + κ closed form:
        `XiLemmaC_kappa_closedForm` + `xi_sc_re_ne_zero`
    • ell = bCoeff * κ closed forms:
        `ell_wp2_eq_b_mul_kappa`, `ell_wp3_eq_b_mul_kappa`
-/

import Mathlib.Tactic
import Hyperlocal.Transport.PrimeSineRescue
import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceExtract
import Hyperlocal.Targets.XiPacket.XiLemmaC_RecurrenceToEllKappa
import Hyperlocal.Targets.XiPacket.XiWindowKappaClosedForm
import Hyperlocal.Targets.XiPacket.XiWindowAnchorNonvanishing

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

theorem xiToeplitzRecurrenceIdentity_p (s : Hyperlocal.OffSeed Xi)
    (p : ℝ) (hp : p = (2 : ℝ) ∨ p = (3 : ℝ)) :
    bCoeff (σ s) (t s) p = 0 := by
  -- κ ≠ 0, by rewriting the *anchor* nonvanishing `Re(Xi(sc)) ≠ 0`
  -- into κ≠0 using the *symmetric* closed form.
  have hk_eq :
      (Xi (sc s)).re =
        Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) := by
    simpa using (XiLemmaC_kappa_closedForm (s := s)).symm

  have hkappa :
      Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0 := by
    -- key point: rewrite `(Xi (sc s)).re` into κ using `hk_eq`
    simpa [hk_eq] using (xi_sc_re_ne_zero (s := s))

  rcases hp with rfl | rfl
  ·
    have hell2 :
        Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s)) = 0 :=
      (xiToeplitzEllOut_fromRecurrence (s := s)).hell2

    have hmul :
        bCoeff (σ s) (t s) (2 : ℝ)
          * Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 := by
      -- avoid `simp`-matching issues: use `calc` with the *symm* closed form
      calc
        bCoeff (σ s) (t s) (2 : ℝ)
            * Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s))
            =
          Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s)) := by
            simpa using (ell_wp2_eq_b_mul_kappa (s := s)).symm
        _ = 0 := hell2

    have hdisj :
        bCoeff (σ s) (t s) (2 : ℝ) = 0 ∨
        Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 :=
      (mul_eq_zero.mp hmul)

    exact hdisj.resolve_right hkappa
  ·
    have hell3 :
        Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s)) = 0 :=
      (xiToeplitzEllOut_fromRecurrence (s := s)).hell3

    have hmul :
        bCoeff (σ s) (t s) (3 : ℝ)
          * Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 := by
      calc
        bCoeff (σ s) (t s) (3 : ℝ)
            * Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s))
            =
          Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s)) := by
            simpa using (ell_wp3_eq_b_mul_kappa (s := s)).symm
        _ = 0 := hell3

    have hdisj :
        bCoeff (σ s) (t s) (3 : ℝ) = 0 ∨
        Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 :=
      (mul_eq_zero.mp hmul)

    exact hdisj.resolve_right hkappa

end XiPacket
end Targets
end Hyperlocal
