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

  IMPORTANT:
  * theorem-level only
  * no provider instance here
  * intended to be installer-free upstream
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Defs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiSigma3Nonzero
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345ManuscriptFromSigmaAndRow012

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

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
    Tail345ManuscriptFromSigmaAndRow012.coords012_eq_zero_of_sigma_and_row012
      (s := s) (z := s.ρ) (w := w0At m s)
      (hSigma := Hσ.hw0AtSigma)
      (H := XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hw0At (m := m) (s := s))
      (hσ3 := hσ3)

  have Hwp2 :
      (wp2At m s) 0 = 0 ∧ (wp2At m s) 1 = 0 ∧ (wp2At m s) 2 = 0 :=
    Tail345ManuscriptFromSigmaAndRow012.coords012_eq_zero_of_sigma_and_row012
      (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s)
      (hSigma := Hσ.hwp2AtSigma)
      (H := XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hwp2At (m := m) (s := s))
      (hσ3 := hσ3)

  have Hwp3 :
      (wp3At m s) 0 = 0 ∧ (wp3At m s) 1 = 0 ∧ (wp3At m s) 2 = 0 :=
    Tail345ManuscriptFromSigmaAndRow012.coords012_eq_zero_of_sigma_and_row012
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
