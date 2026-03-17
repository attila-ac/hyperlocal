import Hyperlocal.Targets.CriticalZero_Zeta_FinalAlmostUnconditional
import Hyperlocal.Targets.XiFinalRhCorridorProviderInstalledFromEquivalentResonantBranchSeams
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
Final Xi-side export from resonant-branch seam (A), routed through the bundled
equivalent-seam corridor installer.
-/
theorem noOffSeed_Xi_final_of_row0Sigma_wc_zero_via_corridor
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
  letI : XiFinalRhCorridorProvider :=
    instXiFinalRhCorridorProviderOfRow0SigmaWcZeroOnResonantBranch
  exact noOffSeed_Xi_final_almost_unconditional

/-- Final ζ-side export from the same resonant-branch seam (A). -/
theorem noOffSeed_Zeta_final_of_row0Sigma_wc_zero_via_corridor
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
  letI : XiFinalRhCorridorProvider :=
    instXiFinalRhCorridorProviderOfRow0SigmaWcZeroOnResonantBranch
  exact noOffSeed_Zeta_final_almost_unconditional

/-- Final RH-facing export from the same resonant-branch seam (A). -/
theorem criticalzero_zeta_final_of_row0Sigma_wc_zero_via_corridor
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
  letI : XiFinalRhCorridorProvider :=
    instXiFinalRhCorridorProviderOfRow0SigmaWcZeroOnResonantBranch
  exact criticalzero_zeta_final_almost_unconditional
    (hζ := hζ)
    (hIm := hIm)

#print axioms noOffSeed_Zeta_final_of_row0Sigma_wc_zero_via_corridor
#print axioms criticalzero_zeta_final_of_row0Sigma_wc_zero_via_corridor

end Targets
end Hyperlocal
