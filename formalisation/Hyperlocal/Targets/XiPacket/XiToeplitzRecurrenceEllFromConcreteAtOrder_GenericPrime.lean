/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceEllFromConcreteAtOrder_GenericPrime.lean

  Honest generic-prime upstream ell-out bridge.

  This file does NOT claim that the current recurrence package already proves
  row-0 zero for every `wpAt m s p`. Instead it isolates the exact remaining
  upstream burden:

      hwpop :
        (toeplitzL 2 (JetQuotOp.aRk1 s) (wpAt m s p)) (0 : Fin 3) = 0

  and proves that this is sufficient to manufacture the generic-prime ell-out
  statements needed by the W1 route.

  So after this file, the remaining obstruction is no longer receiving-side
  linear algebra. It is exactly the upstream production of `hwpop`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceEllFromConcreteAtOrderImProofUpstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_Theorem
import Hyperlocal.Targets.XiPacket.XiWindowJetPivot_wpAtExpand
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open scoped BigOperators Real
open Hyperlocal.Transport
open ToeplitzLToRow3
open ToeplitzEllOutAtOrderProof

/--
Generic-prime real-pivot ell-out from explicit row-0 zeros.
-/
theorem xiToeplitzEllOutAt_p_of_row0zeros
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    (hw0op :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (0 : Fin 3) = 0)
    (hwcop :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0)
    (hwpop :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wpAt m s p)) (0 : Fin 3) = 0) :
    Transport.ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wpAt m s p)) = 0 := by
  classical

  have hreal0 : (JetQuotOp.aRk1 s 0).im = 0 := JetQuotOp.aRk1_im0 (s := s)
  have hreal1 : (JetQuotOp.aRk1 s 1).im = 0 := JetQuotOp.aRk1_im1 (s := s)
  have hreal2 : (JetQuotOp.aRk1 s 2).im = 0 := JetQuotOp.aRk1_im2 (s := s)

  have hc : cOp s ≠ 0 := cOp_ne_zero (s := s)

  have hw0_row0 :
      (toeplitzL 2 (coeffsNat3 (cOp s)) (w0At m s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_op_row0_eq_zero (s := s) (w := w0At m s)
      hreal0 hreal1 hreal2 hw0op

  have hwc_row0 :
      (toeplitzL 2 (coeffsNat3 (cOp s)) (wc s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_op_row0_eq_zero (s := s) (w := wc s)
      hreal0 hreal1 hreal2 hwcop

  have hwp_row0 :
      (toeplitzL 2 (coeffsNat3 (cOp s)) (wpAt m s p)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_op_row0_eq_zero (s := s) (w := wpAt m s p)
      hreal0 hreal1 hreal2 hwpop

  have hU0 : toeplitzRow3 (cOp s) (reVec3 (w0At m s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero (cOp s) (w0At m s) hw0_row0

  have hUc : toeplitzRow3 (cOp s) (reVec3 (wc s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero (cOp s) (wc s) hwc_row0

  have hVp : toeplitzRow3 (cOp s) (reVec3 (wpAt m s p)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero (cOp s) (wpAt m s p) hwp_row0

  exact Hyperlocal.Targets.XiPacket.ell_eq_zero_of_toeplitzRow3
    (u0 := reVec3 (w0At m s))
    (uc := reVec3 (wc s))
    (v := reVec3 (wpAt m s p))
    (c := cOp s)
    hc hU0 hUc hVp

/--
Theorem-side wrapper:
all existing burdens are discharged except the genuine remaining generic-prime
row-0 zero for `wpAt m s p`.
-/
theorem xiToeplitzEllOutAt_p_fromRecurrenceC_of_row0
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0)
    (hwpop :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wpAt m s p)) (0 : Fin 3) = 0) :
    Transport.ell (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wpAt m s p)) = 0 := by
  have Hrec : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_fromRow012Upstream (m := m) (s := s)

  have Hop : XiJetQuotOpZeroAtOrder m s :=
    xiJetQuotOpZeroAtOrder_of_rec2 (m := m) (s := s) Hrec

  have Hw : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s) Hop

  exact xiToeplitzEllOutAt_p_of_row0zeros
    (m := m) (s := s) (p := p)
    (hw0op := Hw.hop_w0At)
    (hwcop := xiJetQuot_row0_wc_fromWcStencil (s := s) (hroute := hroute))
    (hwpop := hwpop)

/--
Generic-prime mixed imag-pivot ell-out from explicit row-0 zeros.
This is the generic version of the local `ImRe` upstream surface.
-/
theorem xiToeplitzEllOutAtImRe_p_of_row0zeros
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    (hw0op :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (0 : Fin 3) = 0)
    (hwcop :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0)
    (hwpop :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wpAt m s p)) (0 : Fin 3) = 0) :
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wpAt m s p)) = 0 := by
  classical

  have hreal0 : (JetQuotOp.aRk1 s 0).im = 0 := JetQuotOp.aRk1_im0 (s := s)
  have hreal1 : (JetQuotOp.aRk1 s 1).im = 0 := JetQuotOp.aRk1_im1 (s := s)
  have hreal2 : (JetQuotOp.aRk1 s 2).im = 0 := JetQuotOp.aRk1_im2 (s := s)

  have hc : cOp s ≠ 0 := cOp_ne_zero (s := s)

  have hw0_row0 :
      (toeplitzL 2 (coeffsNat3 (cOp s)) (w0At m s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_op_row0_eq_zero (s := s) (w := w0At m s)
      hreal0 hreal1 hreal2 hw0op

  have hwc_row0 :
      (toeplitzL 2 (coeffsNat3 (cOp s)) (wc s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_op_row0_eq_zero (s := s) (w := wc s)
      hreal0 hreal1 hreal2 hwcop

  have hwp_row0 :
      (toeplitzL 2 (coeffsNat3 (cOp s)) (wpAt m s p)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_op_row0_eq_zero (s := s) (w := wpAt m s p)
      hreal0 hreal1 hreal2 hwpop

  have hU0 : toeplitzRow3 (cOp s) (imVec3 (w0At m s)) :=
    toeplitzRow3_imVec3_of_toeplitzL_two_fin0_eq_zero (c := cOp s) (w := w0At m s) hw0_row0

  have hUc : toeplitzRow3 (cOp s) (reVec3 (wc s)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero (cOp s) (wc s) hwc_row0

  have hVp : toeplitzRow3 (cOp s) (reVec3 (wpAt m s p)) :=
    toeplitzRow3_reVec3_of_toeplitzL_two_fin0_eq_zero (cOp s) (wpAt m s p) hwp_row0

  exact Hyperlocal.Targets.XiPacket.ell_eq_zero_of_toeplitzRow3
    (u0 := imVec3 (w0At m s))
    (uc := reVec3 (wc s))
    (v := reVec3 (wpAt m s p))
    (c := cOp s)
    hc hU0 hUc hVp

/--
Theorem-side mixed imag-pivot wrapper:
again the only remaining generic-prime burden is the row-0 zero for `wpAt m s p`.
-/
theorem xiToeplitzEllOutAtImRe_p_fromRecurrenceC_of_row0
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0)
    (hwpop :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wpAt m s p)) (0 : Fin 3) = 0) :
    Transport.ell (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (wpAt m s p)) = 0 := by
  have Hrec : XiJetQuotRec2AtOrder m s :=
    xiJetQuotRec2AtOrder_fromRow012Upstream (m := m) (s := s)

  have Hop : XiJetQuotOpZeroAtOrder m s :=
    xiJetQuotOpZeroAtOrder_of_rec2 (m := m) (s := s) Hrec

  have Hw : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s) Hop

  exact xiToeplitzEllOutAtImRe_p_of_row0zeros
    (m := m) (s := s) (p := p)
    (hw0op := Hw.hop_w0At)
    (hwcop := xiJetQuot_row0_wc_fromWcStencil (s := s) (hroute := hroute))
    (hwpop := hwpop)

end XiPacket
end Targets
end Hyperlocal
