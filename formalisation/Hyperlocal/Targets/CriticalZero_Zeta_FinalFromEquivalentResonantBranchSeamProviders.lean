import Hyperlocal.Targets.XiFinalRhCorridorProviderInstalledFromEquivalentResonantBranchSeams
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
Final Xi-side export from the resonant-branch equivalent local form (A) provider.
-/
theorem noOffSeed_Xi_final_of_row0Sigma_wc_zero_on_resonant_branch_provider
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiRow0SigmaWcZeroOnResonantBranchProvider] :
    NoOffSeed Hyperlocal.Targets.XiPacket.Xi := by
  letI : XiFinalRhCorridorProvider := inferInstance
  exact noOffSeed_Xi_final_of_corridor_provider

/-- Final ζ-side export from the same form (A) provider. -/
theorem noOffSeed_Zeta_final_of_row0Sigma_wc_zero_on_resonant_branch_provider
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiRow0SigmaWcZeroOnResonantBranchProvider] :
    NoOffSeed Hyperlocal.zeta := by
  letI : XiFinalRhCorridorProvider := inferInstance
  exact noOffSeed_Zeta_final_of_corridor_provider

/-- Final RH-facing export from the same form (A) provider. -/
theorem criticalzero_zeta_final_of_row0Sigma_wc_zero_on_resonant_branch_provider
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiRow0SigmaWcZeroOnResonantBranchProvider]
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  letI : XiFinalRhCorridorProvider := inferInstance
  exact criticalzero_zeta_final_of_corridor_provider
    (hζ := hζ)
    (hIm := hIm)

/--
Final Xi-side export from the resonant-branch equivalent local form (C) provider.
-/
theorem noOffSeed_Xi_final_of_sigma2_eq_two_delta_on_resonant_branch_provider
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiSigma2EqTwoDeltaOnResonantBranchProvider] :
    NoOffSeed Hyperlocal.Targets.XiPacket.Xi := by
  letI : XiFinalRhCorridorProvider := inferInstance
  exact noOffSeed_Xi_final_of_corridor_provider

/-- Final ζ-side export from the same form (C) provider. -/
theorem noOffSeed_Zeta_final_of_sigma2_eq_two_delta_on_resonant_branch_provider
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiSigma2EqTwoDeltaOnResonantBranchProvider] :
    NoOffSeed Hyperlocal.zeta := by
  letI : XiFinalRhCorridorProvider := inferInstance
  exact noOffSeed_Zeta_final_of_corridor_provider

/-- Final RH-facing export from the same form (C) provider. -/
theorem criticalzero_zeta_final_of_sigma2_eq_two_delta_on_resonant_branch_provider
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiSigma2EqTwoDeltaOnResonantBranchProvider]
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  letI : XiFinalRhCorridorProvider := inferInstance
  exact criticalzero_zeta_final_of_corridor_provider
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
