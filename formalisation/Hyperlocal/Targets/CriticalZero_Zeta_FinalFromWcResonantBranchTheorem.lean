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

/--
Direct final Xi-side export from the sharp resonant wc-seam theorem.
-/
theorem noOffSeed_Xi_final_of_wcsigma_res
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wc s) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_final_of_row0Sigma_wc_zero_via_corridor
    (hsigma_res := hsigma_res)

/-- Direct final ζ-side export from the same sharp resonant wc-seam theorem. -/
theorem noOffSeed_Zeta_final_of_wcsigma_res
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wc s) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_final_of_row0Sigma_wc_zero_via_corridor
    (hsigma_res := hsigma_res)

/-- Direct RH-facing export from the same sharp resonant wc-seam theorem. -/
theorem criticalzero_zeta_final_of_wcsigma_res
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
  exact criticalzero_zeta_final_of_row0Sigma_wc_zero_via_corridor
    (hsigma_res := hsigma_res)
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
