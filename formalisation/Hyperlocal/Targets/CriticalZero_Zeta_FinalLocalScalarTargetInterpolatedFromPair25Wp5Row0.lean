import Hyperlocal.Targets.XiNoOffSeedDirectFromPair25ResonantBranchJetConvolutionAtRev
import Hyperlocal.Targets.XiNoOffSeedDirectFromFinalLocalScalarTargetTrueAnalyticJetConvolution
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
Prime-2 interpolation from the sharpened pair-{2,5} wp5-row0 surface.

This removes the generic-prime class completely: the only local burden is
`hwp5_res`.
-/
theorem sin_log2_zero_on_resonant_branch_of_pair25_wp5_row0
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (2 : ℝ)) = 0 := by
  intro s hres
  have hno : NoOffSeed Xi :=
    noOffSeed_Xi_via_pair25_resonant_branch_of_wp5_row0
      (hwp5_res := hwp5_res)
  exact False.elim (hno ⟨s⟩)

/--
Prime-3 interpolation from the sharpened pair-{2,5} wp5-row0 surface.
-/
theorem sin_log3_zero_on_resonant_branch_of_pair25_wp5_row0
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (3 : ℝ)) = 0 := by
  intro s hres
  have hno : NoOffSeed Xi :=
    noOffSeed_Xi_via_pair25_resonant_branch_of_wp5_row0
      (hwp5_res := hwp5_res)
  exact False.elim (hno ⟨s⟩)

/--
Final-local-scalar-target Xi-side closure from the sharpened pair-{2,5}
wp5-row0 surface, with no generic-prime class.
-/
theorem noOffSeed_Xi_of_final_local_scalar_target_from_pair25_wp5_row0
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_final_local_scalar_target
    (h2_res := sin_log2_zero_on_resonant_branch_of_pair25_wp5_row0
      (hwp5_res := hwp5_res))

/--
Final-local-scalar-target ζ-side closure from the sharpened pair-{2,5}
wp5-row0 surface.
-/
theorem noOffSeed_Zeta_of_final_local_scalar_target_from_pair25_wp5_row0
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_final_local_scalar_target
    (h2_res := sin_log2_zero_on_resonant_branch_of_pair25_wp5_row0
      (hwp5_res := hwp5_res))

/--
Final-local-scalar-target RH-facing export from the sharpened pair-{2,5}
wp5-row0 surface.
-/
theorem criticalzero_zeta_of_final_local_scalar_target_from_pair25_wp5_row0
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
  exact criticalzero_zeta_of_final_local_scalar_target
    (h2_res := sin_log2_zero_on_resonant_branch_of_pair25_wp5_row0
      (hwp5_res := hwp5_res))
    (hζ := hζ)
    (hIm := hIm)

/--
Prime-3 twin on the same sharpened pair-{2,5} wp5-row0 surface.
-/
theorem noOffSeed_Xi_of_final_local_scalar_target_prime3_from_pair25_wp5_row0
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_final_local_scalar_target_prime3
    (h3_res := sin_log3_zero_on_resonant_branch_of_pair25_wp5_row0
      (hwp5_res := hwp5_res))

theorem noOffSeed_Zeta_of_final_local_scalar_target_prime3_from_pair25_wp5_row0
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_final_local_scalar_target_prime3
    (h3_res := sin_log3_zero_on_resonant_branch_of_pair25_wp5_row0
      (hwp5_res := hwp5_res))

theorem criticalzero_zeta_of_final_local_scalar_target_prime3_from_pair25_wp5_row0
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
  exact criticalzero_zeta_of_final_local_scalar_target_prime3
    (h3_res := sin_log3_zero_on_resonant_branch_of_pair25_wp5_row0
      (hwp5_res := hwp5_res))
    (hζ := hζ)
    (hIm := hIm)

/--
Lowered prime-2 interpolation on the theorem-side jet-convolution surface.
This is the same refactor, but one corridor layer lower.
-/
theorem sin_log2_zero_on_resonant_branch_of_pair25_wp5_row0_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (2 : ℝ)) = 0 := by
  intro s hres
  have hno : NoOffSeed Xi :=
    noOffSeed_Xi_via_pair25_resonant_branch_of_trueanalytic_jetconvolution
      (hwp5_res := hwp5_res)
  exact False.elim (hno ⟨s⟩)

/--
Lowered prime-3 interpolation on the theorem-side jet-convolution surface.
-/
theorem sin_log3_zero_on_resonant_branch_of_pair25_wp5_row0_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (3 : ℝ)) = 0 := by
  intro s hres
  have hno : NoOffSeed Xi :=
    noOffSeed_Xi_via_pair25_resonant_branch_of_trueanalytic_jetconvolution
      (hwp5_res := hwp5_res)
  exact False.elim (hno ⟨s⟩)

/--
Lowered prime-2 final-local-scalar-target Xi-side closure with no generic-prime
class left anywhere on the consumer surface.
-/
theorem noOffSeed_Xi_of_final_local_scalar_target_of_trueanalytic_jetconvolution_from_pair25_wp5_row0
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_final_local_scalar_target_of_trueanalytic_jetconvolution
    (h2_res := sin_log2_zero_on_resonant_branch_of_pair25_wp5_row0_of_trueanalytic_jetconvolution
      (hwp5_res := hwp5_res))

theorem noOffSeed_Zeta_of_final_local_scalar_target_of_trueanalytic_jetconvolution_from_pair25_wp5_row0
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_final_local_scalar_target_of_trueanalytic_jetconvolution
    (h2_res := sin_log2_zero_on_resonant_branch_of_pair25_wp5_row0_of_trueanalytic_jetconvolution
      (hwp5_res := hwp5_res))

theorem criticalzero_zeta_of_final_local_scalar_target_of_trueanalytic_jetconvolution_from_pair25_wp5_row0
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
  exact criticalzero_zeta_of_final_local_scalar_target_of_trueanalytic_jetconvolution
    (h2_res := sin_log2_zero_on_resonant_branch_of_pair25_wp5_row0_of_trueanalytic_jetconvolution
      (hwp5_res := hwp5_res))
    (hζ := hζ)
    (hIm := hIm)

/--
Lowered prime-3 twin on the theorem-side jet-convolution surface.
-/
theorem noOffSeed_Xi_of_final_local_scalar_target_prime3_of_trueanalytic_jetconvolution_from_pair25_wp5_row0
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Xi := by
  haveI : XiJetQuotRec2AtOrderTrueAnalytic := inferInstance
  exact noOffSeed_Xi_of_final_local_scalar_target_prime3
    (h3_res := sin_log3_zero_on_resonant_branch_of_pair25_wp5_row0_of_trueanalytic_jetconvolution
      (hwp5_res := hwp5_res))

theorem noOffSeed_Zeta_of_final_local_scalar_target_prime3_of_trueanalytic_jetconvolution_from_pair25_wp5_row0
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  haveI : XiJetQuotRec2AtOrderTrueAnalytic := inferInstance
  exact noOffSeed_Zeta_of_final_local_scalar_target_prime3
    (h3_res := sin_log3_zero_on_resonant_branch_of_pair25_wp5_row0_of_trueanalytic_jetconvolution
      (hwp5_res := hwp5_res))

theorem criticalzero_zeta_of_final_local_scalar_target_prime3_of_trueanalytic_jetconvolution_from_pair25_wp5_row0
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
  haveI : XiJetQuotRec2AtOrderTrueAnalytic := inferInstance
  exact criticalzero_zeta_of_final_local_scalar_target_prime3
    (h3_res := sin_log3_zero_on_resonant_branch_of_pair25_wp5_row0_of_trueanalytic_jetconvolution
      (hwp5_res := hwp5_res))
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
