import Hyperlocal.Targets.CriticalZero_Zeta_Pair25TheoremGated
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
Hidden interpolation node, prime-2 version.

Once the sharpened theorem-gated pair-{2,5} closure is available from the local
`wpAt 0 s 5` resonant-branch theorem, the canonical prime-2 final-local-scalar
obligation follows immediately by contradiction.
-/
theorem sin_log2_zero_on_resonant_branch_of_pair25_theorem_gated
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
  have hno : NoOffSeed Hyperlocal.Targets.XiPacket.Xi :=
    noOffSeed_Xi_pair25_theorem_gated (hwp5_res := hwp5_res)
  have hfalse : False := hno ⟨s⟩
  exact False.elim hfalse

/--
Hidden interpolation node, prime-3 version.
-/
theorem sin_log3_zero_on_resonant_branch_of_pair25_theorem_gated
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
  have hno : NoOffSeed Hyperlocal.Targets.XiPacket.Xi :=
    noOffSeed_Xi_pair25_theorem_gated (hwp5_res := hwp5_res)
  have hfalse : False := hno ⟨s⟩
  exact False.elim hfalse

/--
Canonical final-local-scalar-target Xi-side closure, obtained by interpolation
from the sharpened theorem-gated pair-{2,5} closure.
-/
theorem noOffSeed_Xi_of_final_local_scalar_target_from_pair25_theorem_gated
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_final_local_scalar_target
    (h2_res :=
      sin_log2_zero_on_resonant_branch_of_pair25_theorem_gated
        (hwp5_res := hwp5_res))

/--
Canonical final-local-scalar-target ζ-side closure, prime-2 surface.
-/
theorem noOffSeed_Zeta_of_final_local_scalar_target_from_pair25_theorem_gated
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_final_local_scalar_target
    (h2_res :=
      sin_log2_zero_on_resonant_branch_of_pair25_theorem_gated
        (hwp5_res := hwp5_res))

/--
Canonical RH-facing final-local-scalar-target export, prime-2 surface.
-/
theorem criticalzero_zeta_of_final_local_scalar_target_from_pair25_theorem_gated
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
    (h2_res :=
      sin_log2_zero_on_resonant_branch_of_pair25_theorem_gated
        (hwp5_res := hwp5_res))
    (hζ := hζ)
    (hIm := hIm)

/--
Symmetric prime-3 Xi-side final-local-scalar-target closure.
-/
theorem noOffSeed_Xi_of_final_local_scalar_target_prime3_from_pair25_theorem_gated
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_final_local_scalar_target_prime3
    (h3_res :=
      sin_log3_zero_on_resonant_branch_of_pair25_theorem_gated
        (hwp5_res := hwp5_res))

/--
Symmetric prime-3 ζ-side final-local-scalar-target closure.
-/
theorem noOffSeed_Zeta_of_final_local_scalar_target_prime3_from_pair25_theorem_gated
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_final_local_scalar_target_prime3
    (h3_res :=
      sin_log3_zero_on_resonant_branch_of_pair25_theorem_gated
        (hwp5_res := hwp5_res))

/--
Symmetric prime-3 RH-facing final-local-scalar-target export.
-/
theorem criticalzero_zeta_of_final_local_scalar_target_prime3_from_pair25_theorem_gated
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
    (h3_res :=
      sin_log3_zero_on_resonant_branch_of_pair25_theorem_gated
        (hwp5_res := hwp5_res))
    (hζ := hζ)
    (hIm := hIm)

/--
Lowered prime-2 Xi-side final-local-scalar-target closure on the theorem-side
jet-convolution surface, still using the same hidden pair-{2,5}
interpolation.
-/
theorem noOffSeed_Xi_of_final_local_scalar_target_of_trueanalytic_jetconvolution_from_pair25_theorem_gated
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_final_local_scalar_target_of_trueanalytic_jetconvolution
    (h2_res :=
      sin_log2_zero_on_resonant_branch_of_pair25_theorem_gated
        (hwp5_res := hwp5_res))

/--
Lowered prime-2 ζ-side final-local-scalar-target closure on the theorem-side
jet-convolution surface.
-/
theorem noOffSeed_Zeta_of_final_local_scalar_target_of_trueanalytic_jetconvolution_from_pair25_theorem_gated
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_final_local_scalar_target_of_trueanalytic_jetconvolution
    (h2_res :=
      sin_log2_zero_on_resonant_branch_of_pair25_theorem_gated
        (hwp5_res := hwp5_res))

/--
Lowered prime-2 RH-facing final-local-scalar-target export on the theorem-side
jet-convolution surface.
-/
theorem criticalzero_zeta_of_final_local_scalar_target_of_trueanalytic_jetconvolution_from_pair25_theorem_gated
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
    (h2_res :=
      sin_log2_zero_on_resonant_branch_of_pair25_theorem_gated
        (hwp5_res := hwp5_res))
    (hζ := hζ)
    (hIm := hIm)

/--
Lowered symmetric prime-3 Xi-side final-local-scalar-target closure on the
theorem-side jet-convolution surface.
-/
theorem noOffSeed_Xi_of_final_local_scalar_target_prime3_of_trueanalytic_jetconvolution_from_pair25_theorem_gated
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_final_local_scalar_target_prime3
    (h3_res :=
      sin_log3_zero_on_resonant_branch_of_pair25_theorem_gated
        (hwp5_res := hwp5_res))

/--
Lowered symmetric prime-3 ζ-side final-local-scalar-target closure on the
theorem-side jet-convolution surface.
-/
theorem noOffSeed_Zeta_of_final_local_scalar_target_prime3_of_trueanalytic_jetconvolution_from_pair25_theorem_gated
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hwp5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wpAt 0 s 5) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_final_local_scalar_target_prime3
    (h3_res :=
      sin_log3_zero_on_resonant_branch_of_pair25_theorem_gated
        (hwp5_res := hwp5_res))

/--
Lowered symmetric prime-3 RH-facing final-local-scalar-target export on the
theorem-side jet-convolution surface.
-/
theorem criticalzero_zeta_of_final_local_scalar_target_prime3_of_trueanalytic_jetconvolution_from_pair25_theorem_gated
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
  exact criticalzero_zeta_of_final_local_scalar_target_prime3
    (h3_res :=
      sin_log3_zero_on_resonant_branch_of_pair25_theorem_gated
        (hwp5_res := hwp5_res))
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
