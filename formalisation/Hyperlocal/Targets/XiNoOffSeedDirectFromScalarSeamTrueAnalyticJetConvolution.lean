import Hyperlocal.Targets.XiNoOffSeedDirectFromScalarSeam
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
Lowered scalar-seam Xi-side closure surface.

This removes the explicit Row012 / Rec2 consumer burden and asks only for the
theorem-side reverse jet-convolution gate plus the global Route-A scalar-zero
payload.
-/
theorem noOffSeed_Xi_of_routeA_scalar_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      ∀ s : Hyperlocal.OffSeed Xi,
        (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
          + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_routeA_scalar
    (hroute := hroute)

/--
Lowered scalar-seam ζ-side closure surface.
-/
theorem noOffSeed_Zeta_of_routeA_scalar_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      ∀ s : Hyperlocal.OffSeed Xi,
        (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
          + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_routeA_scalar
    (hroute := hroute)

/--
Lowered scalar-seam RH-facing export.
-/
theorem criticalzero_zeta_of_routeA_scalar_of_trueanalytic_jetconvolution
    [XiJetConvolutionAtRevAtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      ∀ s : Hyperlocal.OffSeed Xi,
        (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
          + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_of_routeA_scalar
    (hroute := hroute)
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
