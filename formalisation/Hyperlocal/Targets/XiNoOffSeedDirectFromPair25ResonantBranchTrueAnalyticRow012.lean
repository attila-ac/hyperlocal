import Hyperlocal.Targets.XiNoOffSeedDirectFromPair25ResonantBranch
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic
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
Lowered pair-{2,5} Xi-side closure surface.

This removes the explicit `Rec2` class from the consumer boundary and instead
asks directly for the true-analytic Row012 reverse-convolution gate, from which
`XiJetQuotRec2AtOrderTrueAnalytic` is already installed by the existing corridor.
-/
theorem noOffSeed_Xi_via_pair25_resonant_branch_of_trueanalytic_row012
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_via_pair25_resonant_branch_of_wp5_row0
    (hwp5_res := hwp5_res)

/--
Lowered pair-{2,5} ζ-side closure surface.
-/
theorem noOffSeed_Zeta_via_pair25_resonant_branch_of_trueanalytic_row012
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_via_pair25_resonant_branch_of_wp5_row0
    (hwp5_res := hwp5_res)

/--
Lowered pair-{2,5} RH-facing export.

This is the honest theorem surface just above the remaining true-analytic
Row012 gate.
-/
theorem criticalzero_zeta_via_pair25_resonant_branch_of_trueanalytic_row012
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
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
  exact criticalzero_zeta_via_pair25_resonant_branch_of_wp5_row0
    (hwp5_res := hwp5_res)
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
