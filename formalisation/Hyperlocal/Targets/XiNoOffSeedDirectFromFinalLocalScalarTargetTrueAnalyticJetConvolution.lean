import Hyperlocal.Targets.XiNoOffSeedDirectFromFinalLocalScalarTarget
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalyticFromJetConvolution
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
Lowered final-local-scalar-target Xi-side closure surface.

This removes the explicit Row012 gate from the consumer boundary and asks
instead for the theorem-side reverse jet-convolution gate, from which the
existing corridor already installs the Row012 and Rec2 payloads.
-/
theorem noOffSeed_Xi_of_final_local_scalar_target_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h2_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (2 : ℝ)) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_final_local_scalar_target
    (h2_res := h2_res)

/--
Lowered final-local-scalar-target ζ-side closure surface.
-/
theorem noOffSeed_Zeta_of_final_local_scalar_target_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h2_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Real.sin ((t s) * Real.log (2 : ℝ)) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_final_local_scalar_target
    (h2_res := h2_res)

/--
Lowered final-local-scalar-target RH-facing export.
-/
theorem criticalzero_zeta_of_final_local_scalar_target_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
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
  exact criticalzero_zeta_of_final_local_scalar_target
    (h2_res := h2_res)
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
