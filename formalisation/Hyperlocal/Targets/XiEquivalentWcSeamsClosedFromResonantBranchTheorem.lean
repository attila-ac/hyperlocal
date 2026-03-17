import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_WcEquivalentFormLocalisation
import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Row0SigmaPair25
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcScalarClosedForm
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Targets.XiPacket
open scoped Real

/--
Close the global wc seam from the resonant-branch local theorem only.

This is the direct mathematics-facing form of the current frontier:
the nonresonant branch is already dead by W1, so a theorem on the exact
`log(3/2)` resonant branch suffices to recover the global seam.
-/
theorem row0Sigma_wc_zero_closed_of_resonant_branch_theorem
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wc s) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      row0Sigma s (wc s) = 0 := by
  intro s
  by_cases hres :
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0
  · exact hsigma_res s hres
  · have htv :
        ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr hres
    exact XiPacket.row0Sigma_wc_eq_zero_of_tval_ne_zero
      (s := s) htv

/--
Equivalent closed-form midpoint of the same frontier:
once the resonant-branch wc seam is known, the global scalar identity
`σ2 = 2*delta` follows.
-/
theorem sigma2_eq_two_delta_closed_of_resonant_branch_theorem
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wc s) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ) := by
  intro s
  have hsigma : row0Sigma s (wc s) = 0 := by
    exact
      row0Sigma_wc_zero_closed_of_resonant_branch_theorem
        (hsigma_res := hsigma_res) s

  have hclosed :
      row0Sigma s (wc s)
        =
      (JetQuotOp.σ2 s : ℂ) - (2 : ℂ) * (XiTransport.delta s : ℂ) := by
    simpa using (XiPacket.W1.row0Sigma_wc_closed (s := s))

  rw [hsigma] at hclosed
  have hz :
      (JetQuotOp.σ2 s : ℂ) - (2 : ℂ) * (XiTransport.delta s : ℂ) = 0 := by
    simpa using hclosed.symm

  exact sub_eq_zero.mp hz

/--
Global Route-A scalar closure from the same resonant-branch wc theorem.

This is the strongest mathematics-facing normalization of the current frontier:
the exact remaining local theorem now feeds directly into the actual manuscript
scalar stencil.
-/
theorem routeA_scalar_zero_closed_of_resonant_branch_theorem
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wc s) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0 := by
  intro s
  exact XiPacket.routeA_stencil_zero_of_sigma2_eq_two_delta
    (s := s)
    (hσ2δ :=
      sigma2_eq_two_delta_closed_of_resonant_branch_theorem
        (hsigma_res := hsigma_res) s)

#print axioms row0Sigma_wc_zero_closed_of_resonant_branch_theorem
#print axioms sigma2_eq_two_delta_closed_of_resonant_branch_theorem
#print axioms routeA_scalar_zero_closed_of_resonant_branch_theorem

end Targets
end Hyperlocal
