/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01FromSigmaAndRow012TrueAnalytic.lean

  Theorem-level coords01-at-order source from:

    * XiAtOrderSigmaProvider
    * XiRow012ConvolutionAtRevAtOrderTrueAnalytic
    * XiSigma3Nonzero

  Updated structure:
  * primary explicit-input theorem
      `xiAtOrderCoords01Out_of_sigmaAndRow012TrueAnalytic`
    consumes a concrete sigma payload `Hσ : XiAtOrderSigmaOut m s`
  * wrapper theorem
      `xiAtOrderCoords01Out_fromSigmaAndRow012TrueAnalytic`
    recovers `Hσ` from `[XiAtOrderSigmaProvider]`

  2026-03-11 downstream retarget:
  * do NOT import the old manuscript installer-level tail file
  * inline only the local coordinate-kill helper needed here
  * keep this file theorem-level only
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Defs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiSigma3Nonzero

import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345Reductions
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345ShiftCoord
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchySemantics

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/-- From `(-σ3) * x = 0` and `σ3 ≠ 0`, deduce `x = 0`. -/
private lemma eq_zero_of_neg_sigma3_mul_eq_zero
    (s : OffSeed Xi) (x : ℂ)
    (hσ3 : (JetQuotOp.σ3 s : ℂ) ≠ 0)
    (h : (-(JetQuotOp.σ3 s : ℂ)) * x = 0) : x = 0 := by
  have hneg : (-(JetQuotOp.σ3 s : ℂ)) ≠ 0 := neg_ne_zero.mpr hσ3
  have hx : (-(JetQuotOp.σ3 s : ℂ)) = 0 ∨ x = 0 := mul_eq_zero.mp h
  cases hx with
  | inl hbad => exact False.elim (hneg hbad)
  | inr hx0  => exact hx0

/--
Core coordinate-kill lemma used by the sigma+row012 theorem route.

Given:
  * `row0Sigma s w = 0`
  * `Row012ConvolutionAtRev s z w`
  * `σ3(s) ≠ 0`

Deduce:
  * `w 0 = 0`
  * `w 1 = 0`
  * `w 2 = 0`
-/
private theorem coords012_eq_zero_of_sigma_and_row012
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (hSigma : row0Sigma s w = 0)
    (H : Row012ConvolutionAtRev s z w)
    (hσ3 : (JetQuotOp.σ3 s : ℂ) ≠ 0) :
    (w 0) = 0 ∧ (w 1) = 0 ∧ (w 2) = 0 := by
  have hsh1 :
      (JetQuotOp.σ2 s) * (w 2) + (-JetQuotOp.σ3 s) * (w 1) = 0 :=
    Tail345ShiftCoord.sigma_shift1_coord_eq_zero_of_row012ConvolutionAtRev
      (s := s) (z := z) (w := w) H

  have hsh2 : (-JetQuotOp.σ3 s) * (w 2) = 0 :=
    Tail345ShiftCoord.sigma_shift2_coord_eq_zero_of_row012ConvolutionAtRev
      (s := s) (z := z) (w := w) H

  have hw2 : (w 2) = 0 :=
    eq_zero_of_neg_sigma3_mul_eq_zero (s := s) (x := (w 2)) hσ3 (by simpa using hsh2)

  have hmul1 : (-(JetQuotOp.σ3 s : ℂ)) * (w 1) = 0 := by
    simpa [hw2, add_zero] using hsh1

  have hw1 : (w 1) = 0 :=
    eq_zero_of_neg_sigma3_mul_eq_zero (s := s) (x := (w 1)) hσ3 hmul1

  have hmul0 : (-(JetQuotOp.σ3 s : ℂ)) * (w 0) = 0 := by
    have : (-(JetQuotOp.σ3 s : ℂ)) * (w 0) = row0Sigma s w := by
      simp [row0Sigma, hw1, hw2, add_assoc, add_left_comm, add_comm]
    calc
      (-(JetQuotOp.σ3 s : ℂ)) * (w 0) = row0Sigma s w := this
      _ = 0 := hSigma

  have hw0 : (w 0) = 0 :=
    eq_zero_of_neg_sigma3_mul_eq_zero (s := s) (x := (w 0)) hσ3 hmul0

  exact ⟨hw0, hw1, hw2⟩

/--
Explicit-input coords01-at-order theorem from:
* a concrete sigma payload `Hσ`
* Row012 true-analytic convolution facts
* σ3 ≠ 0
-/
theorem xiAtOrderCoords01Out_of_sigmaAndRow012TrueAnalytic
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
    [XiSigma3Nonzero]
    (m : ℕ) (s : OffSeed Xi)
    (Hσ : XiAtOrderSigmaOut m s) :
    XiAtOrderCoords01Out m s := by
  classical
  let hσ3 : (JetQuotOp.σ3 s : ℂ) ≠ 0 :=
    XiSigma3Nonzero.sigma3_ne_zero s

  have Hw0 :
      (w0At m s) 0 = 0 ∧ (w0At m s) 1 = 0 ∧ (w0At m s) 2 = 0 :=
    coords012_eq_zero_of_sigma_and_row012
      (s := s) (z := s.ρ) (w := w0At m s)
      (hSigma := Hσ.hw0AtSigma)
      (H := XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hw0At (m := m) (s := s))
      (hσ3 := hσ3)

  have Hwp2 :
      (wp2At m s) 0 = 0 ∧ (wp2At m s) 1 = 0 ∧ (wp2At m s) 2 = 0 :=
    coords012_eq_zero_of_sigma_and_row012
      (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s)
      (hSigma := Hσ.hwp2AtSigma)
      (H := XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hwp2At (m := m) (s := s))
      (hσ3 := hσ3)

  have Hwp3 :
      (wp3At m s) 0 = 0 ∧ (wp3At m s) 1 = 0 ∧ (wp3At m s) 2 = 0 :=
    coords012_eq_zero_of_sigma_and_row012
      (s := s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3At m s)
      (hSigma := Hσ.hwp3AtSigma)
      (H := XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hwp3At (m := m) (s := s))
      (hσ3 := hσ3)

  exact
    { hw0At0 := Hw0.1
      hw0At1 := Hw0.2.1
      hwp2At0 := Hwp2.1
      hwp2At1 := Hwp2.2.1
      hwp3At0 := Hwp3.1
      hwp3At1 := Hwp3.2.1 }

/--
Wrapper theorem recovering the sigma payload from `[XiAtOrderSigmaProvider]`.
-/
theorem xiAtOrderCoords01Out_fromSigmaAndRow012TrueAnalytic
    [XiAtOrderSigmaProvider]
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
    [XiSigma3Nonzero]
    (m : ℕ) (s : OffSeed Xi) :
    XiAtOrderCoords01Out m s := by
  classical
  have Hσ : XiAtOrderSigmaOut m s :=
    xiAtOrderSigmaOut_provided (m := m) (s := s)
  exact xiAtOrderCoords01Out_of_sigmaAndRow012TrueAnalytic
    (m := m) (s := s) Hσ

end XiPacket
end Targets
end Hyperlocal
