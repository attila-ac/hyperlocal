import Hyperlocal.Targets.XiRow0SigmaWcZeroOnResonantBranchFromWp5Theorem
import Hyperlocal.Targets.CriticalZero_Zeta_FinalFromWcResonantBranchViaCorridor
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

theorem noOffSeed_Xi_final_of_wp5_theorem_via_wc_seam
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_final_of_row0Sigma_wc_zero_via_corridor
    (hsigma_res := row0Sigma_wc_zero_on_resonant_branch_of_wp5_theorem
      (hwp5_res := hwp5_res))

theorem noOffSeed_Zeta_final_of_wp5_theorem_via_wc_seam
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_final_of_row0Sigma_wc_zero_via_corridor
    (hsigma_res := row0Sigma_wc_zero_on_resonant_branch_of_wp5_theorem
      (hwp5_res := hwp5_res))

theorem criticalzero_zeta_final_of_wp5_theorem_via_wc_seam
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_final_of_row0Sigma_wc_zero_via_corridor
    (hsigma_res := row0Sigma_wc_zero_on_resonant_branch_of_wp5_theorem
      (hwp5_res := hwp5_res))
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
