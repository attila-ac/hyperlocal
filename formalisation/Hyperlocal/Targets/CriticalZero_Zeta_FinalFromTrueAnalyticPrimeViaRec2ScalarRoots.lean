import Hyperlocal.Targets.CriticalZero_Zeta_FinalFromWp5ProviderViaRec2ScalarRoots
import Hyperlocal.Targets.XiWp5Row0ZeroOnResonantBranchProviderInstalledFromTrueAnalyticPrime
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Conclusion
open Hyperlocal.Conclusion.OffSeedToTAC
open Hyperlocal.Targets.XiPacket
open scoped Real

/--
Main-track Xi-side endpoint with the wp5 provider removed.

Public assumptions are now exactly:

* theorem-side jet/window quotient equality
* Route-A scalar normalization
* theorem-side Rec2 true-analytic root
* genuine generic-prime true-analytic root
-/
theorem noOffSeed_Xi_final_of_trueanalytic_prime_via_rec2_scalar_roots
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime] :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_final_of_wp5_provider_via_rec2_scalar_roots

/-- Main-track ζ-side endpoint with the wp5 provider removed. -/
theorem noOffSeed_Zeta_final_of_trueanalytic_prime_via_rec2_scalar_roots
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime] :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_final_of_wp5_provider_via_rec2_scalar_roots

/-- Main-track RH-facing endpoint with the wp5 provider removed. -/
theorem criticalzero_zeta_final_of_trueanalytic_prime_via_rec2_scalar_roots
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_final_of_wp5_provider_via_rec2_scalar_roots
    (hζ := hζ)
    (hIm := hIm)

#print axioms noOffSeed_Zeta_final_of_trueanalytic_prime_via_rec2_scalar_roots
#print axioms criticalzero_zeta_final_of_trueanalytic_prime_via_rec2_scalar_roots

end Targets
end Hyperlocal
