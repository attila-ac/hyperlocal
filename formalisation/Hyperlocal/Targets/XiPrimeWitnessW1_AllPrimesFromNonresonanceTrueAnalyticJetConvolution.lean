import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_AllPrimesFromNonresonance
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalyticFromJetConvolution
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/--
Real-pivot arbitrary-prime W1 nonresonant consequence, lowered to the theorem-side
reverse jet-convolution gate.
-/
theorem bCoeff_eq_zero_of_tval_ne_zero_of_kappaAt_of_trueanalytic_jetconvolution
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hk : kappaAt m s ≠ 0)
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    bCoeff (σ s) (t s) (p : ℝ) = 0 := by
  exact bCoeff_eq_zero_of_tval_ne_zero_of_kappaAt
    (m := m) (s := s) (p := p) (hk := hk) (htv := htv)

/--
Imag-pivot arbitrary-prime W1 nonresonant consequence, lowered to the theorem-side
reverse jet-convolution gate.
-/
theorem bCoeff_eq_zero_of_tval_ne_zero_of_kappaAtIm_of_trueanalytic_jetconvolution
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hk : kappaAtIm m s ≠ 0)
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    bCoeff (σ s) (t s) (p : ℝ) = 0 := by
  exact bCoeff_eq_zero_of_tval_ne_zero_of_kappaAtIm
    (m := m) (s := s) (p := p) (hk := hk) (htv := htv)

/--
Pivot-gate arbitrary-prime W1 nonresonant consequence, lowered to the theorem-side
reverse jet-convolution gate.
-/
theorem bCoeff_eq_zero_of_tval_ne_zero_of_trueanalytic_jetconvolution
    (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiKappaPivotNonzero s]
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    bCoeff (σ s) (t s) (p : ℝ) = 0 := by
  exact bCoeff_eq_zero_of_tval_ne_zero
    (s := s) (p := p) (htv := htv)

end XiPacket
end Targets
end Hyperlocal
