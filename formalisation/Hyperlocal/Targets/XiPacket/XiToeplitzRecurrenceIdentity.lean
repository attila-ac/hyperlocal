/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceIdentity.lean

  Option-ELL implementation (no cyclic imports).

  Derive bCoeff(p)=0 for p∈{2,3} without the legacy value-level anchor axiom.

  New inputs:
    • jet-nonflatness at the anchor provides some order `m` with
        `Re(cderivIter m Xi (sc s)) ≠ 0`.
    • κ≠0 at that order via the jet-pivot κ closed form
        (`hkappaAt_of_cderivRe_ne0`).
    • ell-out from recurrence at that same order (semantic frontier):
        `xiToeplitzEllOutAt_fromRecurrenceC`.
    • ell = bCoeff * κ closed forms at that order:
        `ell_wp2At_eq_b_mul_kappa`, `ell_wp3At_eq_b_mul_kappa`
-/

import Mathlib.Tactic
import Hyperlocal.Transport.PrimeSineRescue
import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrder
import Hyperlocal.Targets.XiPacket.XiLemmaC_RecurrenceToEllKappaAtOrder
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
  rcases (_root_.Hyperlocal.Targets.XiPacket.xiJetNonflat_re (s := s)) with ⟨m, hmRe⟩

  have hkappaAt :
     Transport.kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0 := by
    exact (hkappaAt_re_of_cderivRe_ne0 (m := m) (s := s) hmRe)


  rcases hp with rfl | rfl
  ·
    have hell2 :
        Transport.ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp2At m s)) = 0 :=
      (xiToeplitzEllOutAt_fromRecurrenceC (m := m) (s := s)).hell2

    have hmul :
        bCoeff (σ s) (t s) (2 : ℝ)
          * Transport.kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 := by
      calc
        bCoeff (σ s) (t s) (2 : ℝ)
            * Transport.kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s))
            =
          Transport.ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp2At m s)) := by
            simpa using (ell_wp2At_eq_b_mul_kappa (m := m) (s := s)).symm
        _ = 0 := hell2

    have hdisj :
        bCoeff (σ s) (t s) (2 : ℝ) = 0 ∨
        Transport.kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 :=
      (mul_eq_zero.mp hmul)

    exact hdisj.resolve_right hkappaAt
  ·
    have hell3 :
        Transport.ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp3At m s)) = 0 :=
      (xiToeplitzEllOutAt_fromRecurrenceC (m := m) (s := s)).hell3

    have hmul :
        bCoeff (σ s) (t s) (3 : ℝ)
          * Transport.kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 := by
      calc
        bCoeff (σ s) (t s) (3 : ℝ)
            * Transport.kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s))
            =
          Transport.ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wp3At m s)) := by
            simpa using (ell_wp3At_eq_b_mul_kappa (m := m) (s := s)).symm
        _ = 0 := hell3

    have hdisj :
        bCoeff (σ s) (t s) (3 : ℝ) = 0 ∨
        Transport.kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) = 0 :=
      (mul_eq_zero.mp hmul)

    exact hdisj.resolve_right hkappaAt

end XiPacket
end Targets
end Hyperlocal
