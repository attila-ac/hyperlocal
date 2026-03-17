import Hyperlocal.Targets.CriticalZero_Zeta_FinalFromTrueAnalyticPrimeViaRec2ScalarRoots
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticPrimeFromResonant32Provider
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
Main-track Xi-side endpoint after cutting the global generic-prime root down to
its exact remaining resonant-branch fragment.
-/
theorem noOffSeed_Xi_final_of_resonant32_prime_via_rec2_scalar_roots
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrimeOnResonant32Provider] :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_final_of_trueanalytic_prime_via_rec2_scalar_roots

/-- Main-track ζ-side endpoint on the same reduced surface. -/
theorem noOffSeed_Zeta_final_of_resonant32_prime_via_rec2_scalar_roots
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrimeOnResonant32Provider] :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_final_of_trueanalytic_prime_via_rec2_scalar_roots

/-- Main-track RH-facing endpoint on the same reduced surface. -/
theorem criticalzero_zeta_final_of_resonant32_prime_via_rec2_scalar_roots
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrimeOnResonant32Provider]
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_final_of_trueanalytic_prime_via_rec2_scalar_roots
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
