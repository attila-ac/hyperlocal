import Hyperlocal.Targets.XiWp5Row0ZeroOnResonantBranchProviderInstalledFromTrueAnalyticPrime
import Hyperlocal.Targets.XiRow0SigmaWcZeroOnResonantBranchFromWp5Theorem
import Hyperlocal.Targets.XiEquivalentWcSeamsClosedFromResonantBranchTheorem
import Hyperlocal.Targets.CriticalZero_Zeta_FinalFromWcResonantBranchViaRouteAScalar
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
Global canonical `wc` seam, discharged from the installed true-analytic-prime packet.
-/
theorem row0Sigma_wc_zero_closed_of_trueanalytic_prime
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    ∀ s : Hyperlocal.OffSeed Xi,
      row0Sigma s (wc s) = 0 := by
  exact row0Sigma_wc_zero_closed_of_resonant_branch_theorem
    (hsigma_res :=
      row0Sigma_wc_zero_on_resonant_branch_of_wp5_theorem
        (hwp5_res := wp5_row0_zero_on_resonant_branch_of_trueanalytic_prime))

/--
Global scalar midpoint identity `σ2 = 2δ`, discharged from true-analytic-prime.
-/
theorem sigma2_eq_two_delta_closed_of_trueanalytic_prime
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    ∀ s : Hyperlocal.OffSeed Xi,
      JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ) := by
  exact sigma2_eq_two_delta_closed_of_resonant_branch_theorem
    (hsigma_res :=
      row0Sigma_wc_zero_on_resonant_branch_of_wp5_theorem
        (hwp5_res := wp5_row0_zero_on_resonant_branch_of_trueanalytic_prime))

/--
Global Route-A scalar stencil, discharged from true-analytic-prime.
-/
theorem routeA_scalar_zero_closed_of_trueanalytic_prime
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    ∀ s : Hyperlocal.OffSeed Xi,
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0 := by
  exact routeA_scalar_zero_closed_of_resonant_branch_theorem
    (hsigma_res :=
      row0Sigma_wc_zero_on_resonant_branch_of_wp5_theorem
        (hwp5_res := wp5_row0_zero_on_resonant_branch_of_trueanalytic_prime))

/--
Xi-side final export under the installed true-analytic-prime packet.
-/
theorem noOffSeed_Xi_final_of_trueanalytic_prime
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_final_of_wcsigma_res_via_routeA_scalar
    (hsigma_res :=
      row0Sigma_wc_zero_on_resonant_branch_of_wp5_theorem
        (hwp5_res := wp5_row0_zero_on_resonant_branch_of_trueanalytic_prime))

/--
ζ-side final export under the installed true-analytic-prime packet.
-/
theorem noOffSeed_Zeta_final_of_trueanalytic_prime
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_final_of_wcsigma_res_via_routeA_scalar
    (hsigma_res :=
      row0Sigma_wc_zero_on_resonant_branch_of_wp5_theorem
        (hwp5_res := wp5_row0_zero_on_resonant_branch_of_trueanalytic_prime))

/--
RH-facing final export under the installed true-analytic-prime packet.
-/
theorem criticalzero_zeta_final_of_trueanalytic_prime
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_final_of_wcsigma_res_via_routeA_scalar
    (hsigma_res :=
      row0Sigma_wc_zero_on_resonant_branch_of_wp5_theorem
        (hwp5_res := wp5_row0_zero_on_resonant_branch_of_trueanalytic_prime))
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
