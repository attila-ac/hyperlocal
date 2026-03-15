/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1_WcScalarOfDetNonzero.lean

  Direct W1 attack on the remaining `wc` scalar seam.

  Main point:
  on the explicit generic/nonresonant branch
      sin(t log(3/2)) ≠ 0
  the existing theorem-side AtOrder operator zeros force the actual
      toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)
  to vanish. Taking row 0 and using the established closed forms then yields
      JetQuotOp.σ2 s = 2 * delta s
  and hence the Route-A scalar zero.

  So this file cleanly localises the remaining burden:
  if `σ2 = 2*delta` is still not closed, then one is forced onto the exact
  resonance branch
      sin(t log(3/2)) = 0.
-/

import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Stage2ConnectorDeterministic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcSigma2EqTwoDelta
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcScalarClosedForm
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Complex
open scoped BigOperators
open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/--
At any chosen order `m`, the W1 generic branch forces the `wc` row-0 convolution
coefficient to vanish.
-/
theorem row0ConvCoeff3_wc_eq_zero_of_tval_ne_zero_atOrder
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0 := by
  have hwc :
      toeplitzL 2 (JetQuotOp.aRk1 s) (wc s) = 0 :=
    W1.toeplitzL_aRk1_wc_eq_zero_of_tval_ne_zero
      (m := m) (s := s) htv

  have hrow0 :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
    have h := congrArg (fun w => w (0 : Fin 3)) hwc
    simpa using h

  have hsigma : row0Sigma s (wc s) = 0 := by
    rw [← toeplitzL_row0_eq_row0Sigma (s := s) (w := wc s)]
    exact hrow0

  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0 := by
    rw [← row0Sigma_eq_convCoeff_rev (s := s) (w := wc s)]
    exact hsigma

  exact h3

/--
Order-free wrapper of the previous theorem, specialized at `m = 0`.
-/
theorem row0ConvCoeff3_wc_eq_zero_of_tval_ne_zero
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0 := by
  exact row0ConvCoeff3_wc_eq_zero_of_tval_ne_zero_atOrder
    (m := 0) (s := s) htv

/--
Direct W1 generic-branch seam kill:
on `sin(t log(3/2)) ≠ 0`, the scalar identity `σ2 = 2*delta` follows.
-/
theorem sigma2_eq_two_delta_of_tval_ne_zero_atOrder
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ) := by
  exact sigma2_eq_two_delta_of_row0ConvCoeff3_wc_zero
    (s := s)
    (h3 := row0ConvCoeff3_wc_eq_zero_of_tval_ne_zero_atOrder
      (m := m) (s := s) htv)

/--
Order-free wrapper of the previous theorem, specialized at `m = 0`.
-/
theorem sigma2_eq_two_delta_of_tval_ne_zero
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ) := by
  exact sigma2_eq_two_delta_of_tval_ne_zero_atOrder
    (m := 0) (s := s) htv

/--
Hence the Route-A scalar zero also closes on the same generic branch.
-/
theorem routeA_stencil_zero_of_tval_ne_zero_atOrder
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
      + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
      - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0 := by
  exact routeA_stencil_zero_of_sigma2_eq_two_delta
    (s := s)
    (hσ2δ := sigma2_eq_two_delta_of_tval_ne_zero_atOrder
      (m := m) (s := s) htv)

/--
Order-free wrapper of the previous theorem, specialized at `m = 0`.
-/
theorem routeA_stencil_zero_of_tval_ne_zero
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
      + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
      - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0 := by
  exact routeA_stencil_zero_of_tval_ne_zero_atOrder
    (m := 0) (s := s) htv

/--
Contrapositive localisation theorem:

if the scalar seam is still open, then the W1 determinant micro-gate must lie
on the exact resonance branch.
-/
theorem tval23_eq_zero_of_sigma2_ne_two_delta
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hσ2δ :
      JetQuotOp.σ2 s ≠ (2 : ℂ) * (XiTransport.delta s : ℂ)) :
    ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) = 0 := by
  by_contra htv
  exact hσ2δ (sigma2_eq_two_delta_of_tval_ne_zero (s := s) htv)

/--
Real-valued version of the previous theorem.
-/
theorem sin_log_three_div_two_eq_zero_of_sigma2_ne_two_delta
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hσ2δ :
      JetQuotOp.σ2 s ≠ (2 : ℂ) * (XiTransport.delta s : ℂ)) :
    Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 := by
  have hC :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) = 0 :=
    tval23_eq_zero_of_sigma2_ne_two_delta (s := s) hσ2δ
  exact Complex.ofReal_eq_zero.mp hC

/--
Clean summary theorem:
either the scalar seam has already closed, or the problem has been pushed all
the way down to the exact resonance branch `sin(t log(3/2)) = 0`.
-/
theorem sigma2_eq_two_delta_or_sin_log_three_div_two_eq_zero
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ)
      ∨ Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 := by
  by_cases hσ2δ : JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ)
  · exact Or.inl hσ2δ
  · exact Or.inr (sin_log_three_div_two_eq_zero_of_sigma2_ne_two_delta
      (s := s) hσ2δ)

end XiPacket
end Targets
end Hyperlocal
