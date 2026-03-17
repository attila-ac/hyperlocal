import Hyperlocal.Targets.XiPacket.XiRouteA_WcScalarNormalizationProvider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderInstallerFromRec2AtOrderTrueAnalytic

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
Main-track Xi-side endpoint with the sigma root removed.

Compared to the previous reduced surface, this file no longer assumes
`[XiAtOrderSigmaProvider]` or `[XiAtOrderCoords01TheoremProvider]`.
`XiAtOrderCoords01Provider` is synthesized from the honest theorem-side Rec2 root,
while the sigma provider is already supplied by the downstream true-analytic
pair-{2,5} lane imported above.
-/
theorem noOffSeed_Xi_final_of_pair25_via_rec2_scalar_roots
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_via_pair25_resonant_branch_of_trueanalytic_row012
    (hwp5_res := hwp5_res)

/-- Main-track ζ-side endpoint with the sigma root removed. -/
theorem noOffSeed_Zeta_final_of_pair25_via_rec2_scalar_roots
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_via_pair25_resonant_branch_of_trueanalytic_row012
    (hwp5_res := hwp5_res)

/-- Main-track RH-facing endpoint with the sigma root removed. -/
theorem criticalzero_zeta_final_of_pair25_via_rec2_scalar_roots
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarNormalizationProvider]
    [XiJetQuotRec2AtOrderTrueAnalytic]
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

end Targets
end Hyperlocal
