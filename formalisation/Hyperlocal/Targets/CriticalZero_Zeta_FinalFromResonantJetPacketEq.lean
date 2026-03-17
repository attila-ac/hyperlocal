import Hyperlocal.Targets.XiRow0SigmaWcZeroOnResonantBranchClosed
import Hyperlocal.Targets.XiEquivalentWcSeamsClosedFromResonantBranchTheorem
import Hyperlocal.Targets.CriticalZero_Zeta_FinalFromWcResonantBranchViaRouteAScalar
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
Global canonical `wc` seam from the single sharp resonant packet-equality input

  wpAt 0 s 5 = w0At 0 s.
-/
theorem row0Sigma_wc_zero_closed_of_resonant_jetPacketEq
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hpack_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        wpAt 0 s 5 = w0At 0 s) :
    ∀ s : Hyperlocal.OffSeed Xi,
      row0Sigma s (wc s) = 0 := by
  exact row0Sigma_wc_zero_closed_of_resonant_branch_theorem
    (hsigma_res :=
      row0Sigma_wc_zero_on_resonant_branch_closed
        (hpack_res := hpack_res))

/--
Global scalar midpoint identity `σ2 = 2δ` from the same single sharp packet-equality input.
-/
theorem sigma2_eq_two_delta_closed_of_resonant_jetPacketEq
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hpack_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        wpAt 0 s 5 = w0At 0 s) :
    ∀ s : Hyperlocal.OffSeed Xi,
      JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ) := by
  exact sigma2_eq_two_delta_closed_of_resonant_branch_theorem
    (hsigma_res :=
      row0Sigma_wc_zero_on_resonant_branch_closed
        (hpack_res := hpack_res))

/--
Global Route-A scalar stencil from the same single sharp packet-equality input.
-/
theorem routeA_scalar_zero_closed_of_resonant_jetPacketEq
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hpack_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        wpAt 0 s 5 = w0At 0 s) :
    ∀ s : Hyperlocal.OffSeed Xi,
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0 := by
  exact routeA_scalar_zero_closed_of_resonant_branch_theorem
    (hsigma_res :=
      row0Sigma_wc_zero_on_resonant_branch_closed
        (hpack_res := hpack_res))

/--
Xi-side final export from the single sharp resonant packet-equality input.
-/
theorem noOffSeed_Xi_final_of_resonant_jetPacketEq
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hpack_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        wpAt 0 s 5 = w0At 0 s) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_final_of_wcsigma_res_via_routeA_scalar
    (hsigma_res :=
      row0Sigma_wc_zero_on_resonant_branch_closed
        (hpack_res := hpack_res))

/--
ζ-side final export from the single sharp resonant packet-equality input.
-/
theorem noOffSeed_Zeta_final_of_resonant_jetPacketEq
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hpack_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        wpAt 0 s 5 = w0At 0 s) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_final_of_wcsigma_res_via_routeA_scalar
    (hsigma_res :=
      row0Sigma_wc_zero_on_resonant_branch_closed
        (hpack_res := hpack_res))

/--
RH-facing final export from the single sharp resonant packet-equality input.
-/
theorem criticalzero_zeta_final_of_resonant_jetPacketEq
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hpack_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        wpAt 0 s 5 = w0At 0 s)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_final_of_wcsigma_res_via_routeA_scalar
    (hsigma_res :=
      row0Sigma_wc_zero_on_resonant_branch_closed
        (hpack_res := hpack_res))
    (hζ := hζ)
    (hIm := hIm)

end Targets
end Hyperlocal
