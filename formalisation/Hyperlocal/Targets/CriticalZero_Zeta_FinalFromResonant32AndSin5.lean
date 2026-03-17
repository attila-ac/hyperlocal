import Hyperlocal.Targets.XiBCoeff5ZeroOnResonantBranchFromSin5
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
open scoped Real

theorem sin_log2_zero_on_resonant_branch_of_resonant32_and_sin5
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (5 : ℝ)) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (2 : ℝ)) = 0 := by
  exact sin_log2_zero_on_resonant_branch_of_resonant32_and_bCoeff5
    (hb5_res := bCoeff5_zero_on_resonant_branch_of_sin5
      (h5_res := h5_res))

theorem sin_log3_zero_on_resonant_branch_of_resonant32_and_sin5
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (5 : ℝ)) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (3 : ℝ)) = 0 := by
  exact sin_log3_zero_on_resonant_branch_of_resonant32_and_bCoeff5
    (hb5_res := bCoeff5_zero_on_resonant_branch_of_sin5
      (h5_res := h5_res))

theorem noOffSeed_Xi_final_of_resonant32_and_sin5
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (5 : ℝ)) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_final_of_resonant32_and_bCoeff5
    (hb5_res := bCoeff5_zero_on_resonant_branch_of_sin5
      (h5_res := h5_res))

theorem noOffSeed_Zeta_final_of_resonant32_and_sin5
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (5 : ℝ)) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_final_of_resonant32_and_bCoeff5
    (hb5_res := bCoeff5_zero_on_resonant_branch_of_sin5
      (h5_res := h5_res))

theorem criticalzero_zeta_final_of_resonant32_and_sin5
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (5 : ℝ)) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_final_of_resonant32_and_bCoeff5
    (hb5_res := bCoeff5_zero_on_resonant_branch_of_sin5
      (h5_res := h5_res))
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
