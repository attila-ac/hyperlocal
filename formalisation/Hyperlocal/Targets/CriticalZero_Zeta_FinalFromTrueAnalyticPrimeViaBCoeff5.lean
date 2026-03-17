import Hyperlocal.Targets.CriticalZero_Zeta_FinalFromTrueAnalyticPrime
import Hyperlocal.Targets.XiNoOffSeedDirectFromScalarSeam
import Hyperlocal.Targets.CriticalZero_Zeta_FinalFromResonant32AndBCoeff5
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
open Hyperlocal.Transport.PrimeTrigPacket
open scoped Real

/--
On the stronger true-analytic-prime route, the prime-5 coefficient vanishing
theorem is no longer an extra burden: it follows automatically from the global
Route-A scalar stencil.
-/
theorem bCoeff5_zero_on_resonant_branch_of_trueanalytic_prime
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      bCoeff (σ s) (t s) (5 : ℝ) = 0 := by
  intro s _hres
  simpa using
    xiBcoeff_p_eq_zero_of_routeA_scalar
      (s := s) (p := 5)
      (hroute := routeA_scalar_zero_closed_of_trueanalytic_prime s)

/--
Xi-side final export: on the stronger route, no extra local theorem remains.
-/
theorem noOffSeed_Xi_final_of_trueanalytic_prime_via_bCoeff5
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_final_of_resonant32_and_bCoeff5
    (hb5_res := bCoeff5_zero_on_resonant_branch_of_trueanalytic_prime)

/--
ζ-side final export: on the stronger route, no extra local theorem remains.
-/
theorem noOffSeed_Zeta_final_of_trueanalytic_prime_via_bCoeff5
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_final_of_resonant32_and_bCoeff5
    (hb5_res := bCoeff5_zero_on_resonant_branch_of_trueanalytic_prime)

/--
RH-facing final export: on the stronger route, no extra local theorem remains.
-/
theorem criticalzero_zeta_final_of_trueanalytic_prime_via_bCoeff5
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_final_of_resonant32_and_bCoeff5
    (hb5_res := bCoeff5_zero_on_resonant_branch_of_trueanalytic_prime)
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
