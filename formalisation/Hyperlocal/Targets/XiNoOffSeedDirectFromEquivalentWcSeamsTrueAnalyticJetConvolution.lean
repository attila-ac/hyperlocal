import Hyperlocal.Targets.XiNoOffSeedDirectFromEquivalentWcSeams
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
open scoped Real

/--
Lowered Xi-side endgame from equivalent form (A):

    row0Sigma s (wc s) = 0

This removes the explicit Row012 / Rec2 consumer burden and asks only for the
theorem-side reverse jet-convolution gate plus the global Wc-row0 seam.
-/
theorem noOffSeed_Xi_of_row0Sigma_wc_zero_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma :
      ∀ s : Hyperlocal.OffSeed Xi,
        row0Sigma s (wc s) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_row0Sigma_wc_zero
    (hsigma := hsigma)

/--
Lowered ζ-side endgame from equivalent form (A).
-/
theorem noOffSeed_Zeta_of_row0Sigma_wc_zero_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma :
      ∀ s : Hyperlocal.OffSeed Xi,
        row0Sigma s (wc s) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_row0Sigma_wc_zero
    (hsigma := hsigma)

/--
Lowered RH-facing export from equivalent form (A).
-/
theorem criticalzero_zeta_of_row0Sigma_wc_zero_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma :
      ∀ s : Hyperlocal.OffSeed Xi,
        row0Sigma s (wc s) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_of_row0Sigma_wc_zero
    (hsigma := hsigma)
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
