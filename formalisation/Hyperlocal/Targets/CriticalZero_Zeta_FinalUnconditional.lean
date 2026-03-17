import Hyperlocal.Targets.CriticalZero_Zeta_FinalFromResonant32PrimeViaRec2ScalarRoots
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticPrimeOnResonant32Closed
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
Unconditional Xi-side finish once the resonant32 generic-prime root is closed.
-/
theorem noOffSeed_Xi_final_unconditional
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic] :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_final_of_resonant32_prime_via_rec2_scalar_roots

/-- Unconditional ζ-side finish. -/
theorem noOffSeed_Zeta_final_unconditional
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic] :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_final_of_resonant32_prime_via_rec2_scalar_roots

/-- Unconditional RH-facing finish. -/
theorem criticalzero_zeta_final_unconditional
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic]
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_final_of_resonant32_prime_via_rec2_scalar_roots
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
