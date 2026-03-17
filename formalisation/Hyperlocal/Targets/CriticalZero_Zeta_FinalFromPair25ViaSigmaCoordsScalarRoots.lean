import Hyperlocal.Targets.XiPacket.XiRouteA_WcScalarNormalizationProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01TheoremProvider

import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345FromHeartAndCoords
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionDischarge
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalyticFromJetConvolution

import Hyperlocal.Targets.XiNoOffSeedDirectFromPair25ResonantBranchTrueAnalyticRow012
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
Final Xi-side export from the genuinely reduced theorem roots:

* Route-A scalar normalization packaged as a provider class
* sigma-at-order packaged as a provider class
* coords01-at-order packaged as a provider class
* the remaining local wp5 theorem on the resonant branch

Everything else (Tail345 -> JetConvolution -> Row012 -> pair-{2,5} endgame)
is now pure theorem-side plumbing.
-/
theorem noOffSeed_Xi_final_of_pair25_via_sigma_coords_scalar_roots
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiAtOrderSigmaProvider]
    [XiAtOrderCoords01TheoremProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_via_pair25_resonant_branch_of_trueanalytic_row012
    (hwp5_res := hwp5_res)

/-- Final ζ-side export from the same reduced theorem roots. -/
theorem noOffSeed_Zeta_final_of_pair25_via_sigma_coords_scalar_roots
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiAtOrderSigmaProvider]
    [XiAtOrderCoords01TheoremProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_via_pair25_resonant_branch_of_trueanalytic_row012
    (hwp5_res := hwp5_res)

/-- Final RH-facing export from the same reduced theorem roots. -/
theorem criticalzero_zeta_final_of_pair25_via_sigma_coords_scalar_roots
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiAtOrderSigmaProvider]
    [XiAtOrderCoords01TheoremProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_via_pair25_resonant_branch_of_trueanalytic_row012
    (hwp5_res := hwp5_res)
    (hζ := hζ)
    (hIm := hIm)

#print axioms noOffSeed_Zeta_final_of_pair25_via_sigma_coords_scalar_roots
#print axioms criticalzero_zeta_final_of_pair25_via_sigma_coords_scalar_roots

end Targets
end Hyperlocal
