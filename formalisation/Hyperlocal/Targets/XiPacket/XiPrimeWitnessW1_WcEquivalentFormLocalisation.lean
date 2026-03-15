/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1_WcEquivalentFormLocalisation.lean

  Push the current W1 nonresonant seam kill down to the two clean equivalent
  formulations of the remaining `wc` burden:

    (A) row0Sigma s (wc s) = 0
    (D) Route-A recurrence at 1 - ρ

  Main content:
    sin(t log(3/2)) ≠ 0
      -> σ2 = 2*delta                      (already landed)
      -> row0Sigma s (wc s) = 0           (equivalent form A)
      -> Route-A recurrence at 1 - ρ      (equivalent form D)

  Hence, contrapositively:
    if either (A) or (D) still fails,
    the proof has already been forced onto the exact resonance branch
      sin(t log(3/2)) = 0.

  This is the cleanest honest reformulation of the remaining local theorem
  currently supported by the graph.
-/

import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_WcScalarOfDetNonzero
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcSigma2DeltaToToeplitzRow0Core
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_RouteARecurrenceAtOneSubRhoFromWcSigma
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
open Hyperlocal.Cancellation

/--
Equivalent form (A) of the remaining `wc` burden closes on the current
nonresonant W1 branch.
-/
theorem row0Sigma_wc_eq_zero_of_tval_ne_zero_atOrder
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    row0Sigma s (wc s) = 0 := by
  exact
    row0Sigma_wc_eq_zero_of_sigma2_eq_two_delta
      (s := s)
      (hσ2δ := sigma2_eq_two_delta_of_tval_ne_zero_atOrder
        (m := m) (s := s) htv)

/--
Order-free wrapper of the previous theorem, specialized at `m = 0`.
-/
theorem row0Sigma_wc_eq_zero_of_tval_ne_zero
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    row0Sigma s (wc s) = 0 := by
  exact row0Sigma_wc_eq_zero_of_tval_ne_zero_atOrder
    (m := 0) (s := s) htv

/--
Equivalent form (D) of the remaining `wc` burden closes on the current
nonresonant W1 branch.
-/
theorem routeA_recurrence_at_one_sub_rho_of_tval_ne_zero_atOrder
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
      2 * deriv (deriv (routeA_G s)) (1 - s.ρ)
        =
      (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        -
      (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) := by
  exact
    routeA_recurrence_at_one_sub_rho_of_row0Sigma_wc
      (s := s)
      (hsigma := row0Sigma_wc_eq_zero_of_tval_ne_zero_atOrder
        (m := m) (s := s) htv)

/--
Order-free wrapper of the previous theorem, specialized at `m = 0`.
-/
theorem routeA_recurrence_at_one_sub_rho_of_tval_ne_zero
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
      2 * deriv (deriv (routeA_G s)) (1 - s.ρ)
        =
      (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        -
      (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) := by
  exact routeA_recurrence_at_one_sub_rho_of_tval_ne_zero_atOrder
    (m := 0) (s := s) htv

/--
Contrapositive localisation in the clean equivalent form (A):

if `row0Sigma s (wc s)` is still nonzero, then the proof has already been
forced onto the exact resonance branch.
-/
theorem sin_log_three_div_two_eq_zero_of_row0Sigma_wc_ne_zero
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma :
      row0Sigma s (wc s) ≠ 0) :
    Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 := by
  by_contra hsin
  have htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr hsin
  exact hsigma (row0Sigma_wc_eq_zero_of_tval_ne_zero (s := s) htv)

/--
Complex-valued version of the same equivalent-form (A) localisation.
-/
theorem tval23_eq_zero_of_row0Sigma_wc_ne_zero
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma :
      row0Sigma s (wc s) ≠ 0) :
    ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) = 0 := by
  exact Complex.ofReal_eq_zero.mpr
    (sin_log_three_div_two_eq_zero_of_row0Sigma_wc_ne_zero
      (s := s) (hsigma := hsigma))

/--
Dichotomy in the clean equivalent form (A):

either the `wc` row-0 sigma identity is already closed, or one is on the exact
resonance branch.
-/
theorem row0Sigma_wc_eq_zero_or_sin_log_three_div_two_eq_zero
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    row0Sigma s (wc s) = 0
      ∨ Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 := by
  by_cases hsin :
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0
  · exact Or.inr hsin
  · have htv :
        ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr hsin
    exact Or.inl (row0Sigma_wc_eq_zero_of_tval_ne_zero (s := s) htv)

/--
Contrapositive localisation in the clean equivalent form (D):

if the Route-A recurrence at `1 - ρ` still fails, then the proof has already
been forced onto the exact resonance branch.
-/
theorem sin_log_three_div_two_eq_zero_of_routeA_recurrence_failure
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hrec :
      ¬(
        2 * deriv (deriv (routeA_G s)) (1 - s.ρ)
          =
        (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          -
        (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ)
      )) :
    Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 := by
  by_contra hsin
  have htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr hsin
  exact hrec (routeA_recurrence_at_one_sub_rho_of_tval_ne_zero (s := s) htv)

/--
Complex-valued version of the same equivalent-form (D) localisation.
-/
theorem tval23_eq_zero_of_routeA_recurrence_failure
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hrec :
      ¬(
        2 * deriv (deriv (routeA_G s)) (1 - s.ρ)
          =
        (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          -
        (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ)
      )) :
    ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) = 0 := by
  exact Complex.ofReal_eq_zero.mpr
    (sin_log_three_div_two_eq_zero_of_routeA_recurrence_failure
      (s := s) (hrec := hrec))

/--
Dichotomy in the clean equivalent form (D):

either the Route-A recurrence at `1 - ρ` is already closed, or one is on the
exact resonance branch.
-/
theorem routeA_recurrence_at_one_sub_rho_or_sin_log_three_div_two_eq_zero
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
      (2 * deriv (deriv (routeA_G s)) (1 - s.ρ)
        =
      (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        -
      (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ))
      ∨
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 := by
  by_cases hsin :
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0
  · exact Or.inr hsin
  · have htv :
        ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr hsin
    exact Or.inl
      (routeA_recurrence_at_one_sub_rho_of_tval_ne_zero
        (s := s) htv)

end XiPacket
end Targets
end Hyperlocal
