import Hyperlocal.Targets.XiNoOffSeedDirectFromPair25ResonantBranchJetConvolutionAtRev
import Hyperlocal.Targets.CriticalZero_Zeta_FinalLocalScalarTargetInterpolatedFromPair25Wp5Row0
import Hyperlocal.Targets.XiSigma2EqTwoDeltaOnResonantBranchFromWp5Row0
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
Final Xi-side closure on the honest remaining local theorem node:

  ∀ s, sin(t(s) * log(3/2)) = 0 -> row0Sigma s (wpAt 0 s 5) = 0.
-/
theorem noOffSeed_Xi_final_from_wp5_row0
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_final_local_scalar_target_from_pair25_wp5_row0
    (hwp5_res := hwp5_res)

/--
Final ζ-side closure on the same honest local theorem node.
-/
theorem noOffSeed_Zeta_final_from_wp5_row0
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_final_local_scalar_target_from_pair25_wp5_row0
    (hwp5_res := hwp5_res)

/--
Final RH-facing export on the same honest local theorem node.
-/
theorem criticalzero_zeta_final_from_wp5_row0
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
  exact criticalzero_zeta_of_final_local_scalar_target_from_pair25_wp5_row0
    (hwp5_res := hwp5_res)
    (hζ := hζ)
    (hIm := hIm)

/--
Prime-3 twin from the same honest local theorem node.
-/
theorem noOffSeed_Xi_final_from_wp5_row0_prime3
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_final_local_scalar_target_prime3_from_pair25_wp5_row0
    (hwp5_res := hwp5_res)

theorem noOffSeed_Zeta_final_from_wp5_row0_prime3
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_final_local_scalar_target_prime3_from_pair25_wp5_row0
    (hwp5_res := hwp5_res)

theorem criticalzero_zeta_final_from_wp5_row0_prime3
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
  exact criticalzero_zeta_of_final_local_scalar_target_prime3_from_pair25_wp5_row0
    (hwp5_res := hwp5_res)
    (hζ := hζ)
    (hIm := hIm)

/--
Same final closure, but lowered to the theorem-side jet-convolution surface.
This is the real end-cone surface once the local theorem `hwp5_res` is discharged.
-/
theorem noOffSeed_Xi_final_from_wp5_row0_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_final_local_scalar_target_of_trueanalytic_jetconvolution_from_pair25_wp5_row0
    (hwp5_res := hwp5_res)

theorem noOffSeed_Zeta_final_from_wp5_row0_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_final_local_scalar_target_of_trueanalytic_jetconvolution_from_pair25_wp5_row0
    (hwp5_res := hwp5_res)

theorem criticalzero_zeta_final_from_wp5_row0_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
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
  exact criticalzero_zeta_of_final_local_scalar_target_of_trueanalytic_jetconvolution_from_pair25_wp5_row0
    (hwp5_res := hwp5_res)
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
