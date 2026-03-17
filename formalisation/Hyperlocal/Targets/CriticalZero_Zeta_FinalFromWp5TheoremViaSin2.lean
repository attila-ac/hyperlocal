import Hyperlocal.Targets.CriticalZero_Zeta_FinalFromOnePrimeSineTheorem
import Hyperlocal.Targets.CriticalZero_Zeta_FinalLocalScalarTargetInterpolatedFromPair25Wp5Row0
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
Final Xi-side export from the single remaining local wp5 theorem,
routed through the pair-{2,5} interpolation to the prime-2 sine theorem.
-/
theorem noOffSeed_Xi_final_of_wp5_theorem_via_sin2
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_final_of_sin2_theorem
    (h2_res := sin_log2_zero_on_resonant_branch_of_pair25_wp5_row0
      (hwp5_res := hwp5_res))

/-- Final ζ-side export from the same route. -/
theorem noOffSeed_Zeta_final_of_wp5_theorem_via_sin2
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_final_of_sin2_theorem
    (h2_res := sin_log2_zero_on_resonant_branch_of_pair25_wp5_row0
      (hwp5_res := hwp5_res))

/-- Final RH-facing export from the same route. -/
theorem criticalzero_zeta_final_of_wp5_theorem_via_sin2
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
  exact criticalzero_zeta_final_of_sin2_theorem
    (h2_res := sin_log2_zero_on_resonant_branch_of_pair25_wp5_row0
      (hwp5_res := hwp5_res))
    (hζ := hζ)
    (hIm := hIm)

#print axioms noOffSeed_Zeta_final_of_wp5_theorem_via_sin2
#print axioms criticalzero_zeta_final_of_wp5_theorem_via_sin2

end Targets
end Hyperlocal
