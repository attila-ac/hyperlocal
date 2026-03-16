import Hyperlocal.Targets.XiSigma2EqTwoDeltaOnResonantBranchAttempt
import Hyperlocal.Targets.XiNoOffSeedDirectFromResonantBranchSeamsTrueAnalyticJetConvolution
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

/--
Final Xi-side closure from the resonant-branch scalar midpoint.

At present this is only as unconditional as
`sigma2_eq_two_delta_on_resonant_branch_all`.
So while that theorem still uses `sorry`, this wrapper will also inherit `sorryAx`.
-/
theorem noOffSeed_Xi_final_from_resonant_sigma2_eq_two_delta
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_sigma2_eq_two_delta_on_resonant_branch_of_trueanalytic_jetconvolution
    (hσ2δ_res := sigma2_eq_two_delta_on_resonant_branch_all)

/--
Final ζ-side closure from the resonant-branch scalar midpoint.
-/
theorem noOffSeed_Zeta_final_from_resonant_sigma2_eq_two_delta
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider] :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_sigma2_eq_two_delta_on_resonant_branch_of_trueanalytic_jetconvolution
    (hσ2δ_res := sigma2_eq_two_delta_on_resonant_branch_all)

/--
Final RH-facing closure from the resonant-branch scalar midpoint.
-/
theorem criticalzero_zeta_final_from_resonant_sigma2_eq_two_delta
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_of_sigma2_eq_two_delta_on_resonant_branch_of_trueanalytic_jetconvolution
    (hσ2δ_res := sigma2_eq_two_delta_on_resonant_branch_all)
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
