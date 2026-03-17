import Hyperlocal.Targets.XiEquivalentWcSeamsClosedFromResonantBranchTheorem
import Hyperlocal.Targets.CriticalZero_Zeta_FinalFromRouteAScalarLocalTheorem
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
Direct final Xi-side export from the sharp resonant wc-seam theorem,
routed through the actual Route-A scalar local theorem rather than the corridor
provider stack.
-/
theorem noOffSeed_Xi_final_of_wcsigma_res_via_routeA_scalar
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wc s) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_final_of_routeA_scalar_closed
    (hroute :=
      routeA_scalar_zero_closed_of_resonant_branch_theorem
        (hsigma_res := hsigma_res))

/-- Direct final ζ-side export from the same route. -/
theorem noOffSeed_Zeta_final_of_wcsigma_res_via_routeA_scalar
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wc s) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_final_of_routeA_scalar_closed
    (hroute :=
      routeA_scalar_zero_closed_of_resonant_branch_theorem
        (hsigma_res := hsigma_res))

/-- Direct RH-facing export from the same route. -/
theorem criticalzero_zeta_final_of_wcsigma_res_via_routeA_scalar
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wc s) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_final_of_routeA_scalar_closed
    (hroute :=
      routeA_scalar_zero_closed_of_resonant_branch_theorem
        (hsigma_res := hsigma_res))
    (hζ := hζ)
    (hIm := hIm)

#print axioms noOffSeed_Zeta_final_of_wcsigma_res_via_routeA_scalar
#print axioms criticalzero_zeta_final_of_wcsigma_res_via_routeA_scalar

end Targets
end Hyperlocal
