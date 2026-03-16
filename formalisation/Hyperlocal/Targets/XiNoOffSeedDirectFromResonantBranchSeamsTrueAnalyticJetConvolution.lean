/-
  NEW FILE PATH
  formalisation/Hyperlocal/Targets/XiNoOffSeedDirectFromResonantBranchSeamsTrueAnalyticJetConvolution.lean
-/

import Hyperlocal.Targets.XiNoOffSeedDirectFromResonantBranchSeams
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalyticFromJetConvolution
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
open Hyperlocal.Transport
open scoped Real

/--
Lowered resonant-branch form (A):

  row0Sigma s (wc s) = 0

This places the exact-resonance Wc-row0 seam directly on the honest theorem-side
reverse jet-convolution gate.
-/
theorem noOffSeed_Xi_of_row0Sigma_wc_zero_on_resonant_branch_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wc s) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_row0Sigma_wc_zero_on_resonant_branch
    (hsigma_res := hsigma_res)

/--
Lowered ζ-side resonant-branch form (A).
-/
theorem noOffSeed_Zeta_of_row0Sigma_wc_zero_on_resonant_branch_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wc s) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_row0Sigma_wc_zero_on_resonant_branch
    (hsigma_res := hsigma_res)

/--
Lowered RH-facing resonant-branch form (A).
-/
theorem criticalzero_zeta_of_row0Sigma_wc_zero_on_resonant_branch_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
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
  exact criticalzero_zeta_of_row0Sigma_wc_zero_on_resonant_branch
    (hsigma_res := hsigma_res)
    (hζ := hζ)
    (hIm := hIm)

/--
Lowered resonant-branch form (C):

  JetQuotOp.σ2 s = 2 * delta(s)

This is the cleanest scalar-side exact-resonance target that avoids the
generic-prime corridor.
-/
theorem noOffSeed_Xi_of_sigma2_eq_two_delta_on_resonant_branch_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hσ2δ_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ)) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_sigma2_eq_two_delta_on_resonant_branch
    (hσ2δ_res := hσ2δ_res)

/--
Lowered ζ-side resonant-branch form (C).
-/
theorem noOffSeed_Zeta_of_sigma2_eq_two_delta_on_resonant_branch_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hσ2δ_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ)) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_sigma2_eq_two_delta_on_resonant_branch
    (hσ2δ_res := hσ2δ_res)

/--
Lowered RH-facing resonant-branch form (C).
-/
theorem criticalzero_zeta_of_sigma2_eq_two_delta_on_resonant_branch_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hσ2δ_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ))
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_of_sigma2_eq_two_delta_on_resonant_branch
    (hσ2δ_res := hσ2δ_res)
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
