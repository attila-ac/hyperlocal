import Hyperlocal.Targets.CriticalZero_Zeta_FinalFromRouteAScalarLocalTheorem
import Hyperlocal.Targets.XiSigma2EqTwoDeltaOnResonantBranchFromWp5Row0
import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_WcScalarOfDetNonzero
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcScalarClosedForm
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Conclusion.OffSeedToTAC
open Hyperlocal.Targets.XiPacket
open scoped Real

/--
Global Route-A scalar closure from the single remaining local theorem
at `wpAt 0 s 5`.

This is the actual endgame collapse:

* off resonance, the existing W1 scalar dichotomy already yields `σ2 = 2*δ`,
  hence the Route-A stencil vanishes;
* on resonance, the local wp5 theorem yields `σ2 = 2*δ`,
  hence the same Route-A stencil vanishes.

So the only remaining burden is exactly the local theorem
`hwp5_res`.
-/
theorem routeA_scalar_zero_closed_of_wp5_row0
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0 := by
  intro s
  rcases sigma2_eq_two_delta_or_sin_log_three_div_two_eq_zero (s := s) with hσ2δ | hres
  · exact routeA_stencil_zero_of_sigma2_eq_two_delta
      (s := s)
      (hσ2δ := hσ2δ)
  · have hσ2δ :
        JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ) := by
      exact sigma2_eq_two_delta_on_resonant_branch_of_wp5_row0
        (s := s)
        (hres := hres)
        (hwp5 := hwp5_res s hres)
    exact routeA_stencil_zero_of_sigma2_eq_two_delta
      (s := s)
      (hσ2δ := hσ2δ)

/--
Final Xi-side closure from the single remaining local wp5 theorem.
-/
theorem noOffSeed_Xi_final_of_wp5_row0_closed
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_final_of_routeA_scalar_closed
    (hroute := routeA_scalar_zero_closed_of_wp5_row0
      (hwp5_res := hwp5_res))

/--
Final ζ-side closure from the same single remaining local wp5 theorem.
-/
theorem noOffSeed_Zeta_final_of_wp5_row0_closed
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_final_of_routeA_scalar_closed
    (hroute := routeA_scalar_zero_closed_of_wp5_row0
      (hwp5_res := hwp5_res))

/--
Final RH-facing closure from the same single remaining local wp5 theorem.
-/
theorem criticalzero_zeta_final_of_wp5_row0_closed
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_final_of_routeA_scalar_closed
    (hroute := routeA_scalar_zero_closed_of_wp5_row0
      (hwp5_res := hwp5_res))
    (hζ := hζ)
    (hIm := hIm)

#print axioms routeA_scalar_zero_closed_of_wp5_row0
#print axioms noOffSeed_Xi_final_of_wp5_row0_closed
#print axioms noOffSeed_Zeta_final_of_wp5_row0_closed
#print axioms criticalzero_zeta_final_of_wp5_row0_closed

end Targets
end Hyperlocal
