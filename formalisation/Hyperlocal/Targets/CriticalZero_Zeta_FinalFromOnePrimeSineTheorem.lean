import Hyperlocal.Targets.XiWp5Row0ZeroOnResonantBranchAttempt
import Hyperlocal.Targets.CriticalZero_Zeta_FinalFromWp5Theorem
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

/-- Final Xi-side closure from the prime-2 resonant sine theorem. -/
theorem noOffSeed_Xi_final_of_sin2_theorem
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h2_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (2 : ℝ)) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_final_of_wp5_row0_closed
    (hwp5_res := wp5_row0_zero_on_resonant_branch_all (h2_res := h2_res))

/-- Final ζ-side closure from the prime-2 resonant sine theorem. -/
theorem noOffSeed_Zeta_final_of_sin2_theorem
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h2_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (2 : ℝ)) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_final_of_wp5_row0_closed
    (hwp5_res := wp5_row0_zero_on_resonant_branch_all (h2_res := h2_res))

/-- Final RH-facing closure from the prime-2 resonant sine theorem. -/
theorem criticalzero_zeta_final_of_sin2_theorem
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h2_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (2 : ℝ)) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_final_of_wp5_row0_closed
    (hwp5_res := wp5_row0_zero_on_resonant_branch_all (h2_res := h2_res))
    (hζ := hζ)
    (hIm := hIm)

/-- Final Xi-side closure from the prime-3 resonant sine theorem. -/
theorem noOffSeed_Xi_final_of_sin3_theorem
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (3 : ℝ)) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_final_of_wp5_row0_closed
    (hwp5_res := wp5_row0_zero_on_resonant_branch_all_of_sin3 (h3_res := h3_res))

/-- Final ζ-side closure from the prime-3 resonant sine theorem. -/
theorem noOffSeed_Zeta_final_of_sin3_theorem
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (3 : ℝ)) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_final_of_wp5_row0_closed
    (hwp5_res := wp5_row0_zero_on_resonant_branch_all_of_sin3 (h3_res := h3_res))

/-- Final RH-facing closure from the prime-3 resonant sine theorem. -/
theorem criticalzero_zeta_final_of_sin3_theorem
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (3 : ℝ)) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_final_of_wp5_row0_closed
    (hwp5_res := wp5_row0_zero_on_resonant_branch_all_of_sin3 (h3_res := h3_res))
    (hζ := hζ)
    (hIm := hIm)

#print axioms noOffSeed_Zeta_final_of_sin2_theorem
#print axioms criticalzero_zeta_final_of_sin2_theorem
#print axioms noOffSeed_Zeta_final_of_sin3_theorem
#print axioms criticalzero_zeta_final_of_sin3_theorem

end Targets
end Hyperlocal
