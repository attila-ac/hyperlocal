import Hyperlocal.Targets.CriticalZero_Zeta_FinalFromEquivalentResonantBranchSeamProviders
import Hyperlocal.Targets.XiSin2ProviderFromEquivalentResonantBranchSeams
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
Final Xi-side export from the single local seam (A):
`row0Sigma s (wc s) = 0` on the resonant branch.
-/
theorem noOffSeed_Xi_final_of_row0Sigma_wc_zero_theorem
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wc s) = 0) :
    NoOffSeed Xi := by
  letI : XiRow0SigmaWcZeroOnResonantBranchProvider :=
    instXiRow0SigmaWcZeroOnResonantBranchProviderInstalled
      (hsigma_res := hsigma_res)
  exact noOffSeed_Xi_final_of_row0Sigma_wc_zero_on_resonant_branch_provider

/-- Final ζ-side export from the same seam (A). -/
theorem noOffSeed_Zeta_final_of_row0Sigma_wc_zero_theorem
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wc s) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  letI : XiRow0SigmaWcZeroOnResonantBranchProvider :=
    instXiRow0SigmaWcZeroOnResonantBranchProviderInstalled
      (hsigma_res := hsigma_res)
  exact noOffSeed_Zeta_final_of_row0Sigma_wc_zero_on_resonant_branch_provider

/-- Final RH-facing export from the same seam (A). -/
theorem criticalzero_zeta_final_of_row0Sigma_wc_zero_theorem
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
  letI : XiRow0SigmaWcZeroOnResonantBranchProvider :=
    instXiRow0SigmaWcZeroOnResonantBranchProviderInstalled
      (hsigma_res := hsigma_res)
  exact criticalzero_zeta_final_of_row0Sigma_wc_zero_on_resonant_branch_provider
    (hζ := hζ)
    (hIm := hIm)

#print axioms noOffSeed_Zeta_final_of_row0Sigma_wc_zero_theorem
#print axioms criticalzero_zeta_final_of_row0Sigma_wc_zero_theorem

end Targets
end Hyperlocal
