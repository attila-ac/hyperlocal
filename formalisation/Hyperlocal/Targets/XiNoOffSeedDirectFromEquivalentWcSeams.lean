/-
  Hyperlocal/Targets/XiNoOffSeedDirectFromEquivalentWcSeams.lean

  Endgame packaging: once you prove ANY of the equivalent Wc seam forms (A/B/D) globally,
  the RH-facing chain closes immediately.

  Surface fixes:
  * do NOT redeclare `Xi`
  * bring `NoOffSeed` into scope via `Hyperlocal.Conclusion.OffSeedToTAC`
  * bring `convCoeff` into scope via `Hyperlocal.Cancellation`
-/

import Hyperlocal.Targets.XiNoOffSeedDirectFromScalarSeam
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcRouteAStencilZero
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischargeCore
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_RouteAStencilFromRecurrence
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
open Hyperlocal.Cancellation
open scoped Real

/--
Direct Xi-side endgame from equivalent form (A):

    row0Sigma s (wc s) = 0

for every off-seed `s`.
-/
theorem noOffSeed_Xi_of_row0Sigma_wc_zero
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma :
      ∀ s : Hyperlocal.OffSeed Xi,
        row0Sigma s (wc s) = 0) :
    NoOffSeed Xi := by
  have hroute :
      ∀ s : Hyperlocal.OffSeed Xi,
        (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
          + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0 := by
    intro s
    exact routeA_stencil_zero_of_row0Sigma_wc_zero
      (s := s) (hsigma := hsigma s)
  exact noOffSeed_Xi_of_routeA_scalar (hroute := hroute)

/--
Direct ζ-side transfer from equivalent form (A).
-/
theorem noOffSeed_Zeta_of_row0Sigma_wc_zero
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma :
      ∀ s : Hyperlocal.OffSeed Xi,
        row0Sigma s (wc s) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  have hxi : NoOffSeed Xi :=
    noOffSeed_Xi_of_row0Sigma_wc_zero (hsigma := hsigma)

  have hxi' : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi

  simpa [Hyperlocal.Targets.ZetaTransfer.Zeta] using
    (Hyperlocal.Targets.ZetaTransfer.noOffSeed_zeta_of_noOffSeed_xi (hxi := hxi'))

/--
Direct RH-facing export from equivalent form (A).
-/
theorem criticalzero_zeta_of_row0Sigma_wc_zero
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma :
      ∀ s : Hyperlocal.OffSeed Xi,
        row0Sigma s (wc s) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0) (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  have hxi : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    have hxi0 : NoOffSeed Xi :=
      noOffSeed_Xi_of_row0Sigma_wc_zero (hsigma := hsigma)
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi0

  exact Hyperlocal.Targets.ZetaTransfer.criticalzero_zeta_bridge
    (hxi := hxi) (hζ := hζ) (hIm := hIm)

/--
Direct Xi-side endgame from equivalent form (B):

    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0

for every off-seed `s`.
-/
theorem noOffSeed_Xi_of_wc_coeff3_zero
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3 :
      ∀ s : Hyperlocal.OffSeed Xi,
        convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0) :
    NoOffSeed Xi := by
  have hsigma :
      ∀ s : Hyperlocal.OffSeed Xi,
        row0Sigma s (wc s) = 0 := by
    intro s
    exact row0Sigma_wc_eq_zero_of_coeff3 (s := s) (h3 := h3 s)
  exact noOffSeed_Xi_of_row0Sigma_wc_zero (hsigma := hsigma)

/--
Direct ζ-side transfer from equivalent form (B).
-/
theorem noOffSeed_Zeta_of_wc_coeff3_zero
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3 :
      ∀ s : Hyperlocal.OffSeed Xi,
        convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0) :
    NoOffSeed Hyperlocal.zeta := by
  have hxi : NoOffSeed Xi :=
    noOffSeed_Xi_of_wc_coeff3_zero (h3 := h3)

  have hxi' : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi

  simpa [Hyperlocal.Targets.ZetaTransfer.Zeta] using
    (Hyperlocal.Targets.ZetaTransfer.noOffSeed_zeta_of_noOffSeed_xi (hxi := hxi'))

/--
Direct RH-facing export from equivalent form (B).
-/
theorem criticalzero_zeta_of_wc_coeff3_zero
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3 :
      ∀ s : Hyperlocal.OffSeed Xi,
        convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0) (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  have hxi : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    have hxi0 : NoOffSeed Xi :=
      noOffSeed_Xi_of_wc_coeff3_zero (h3 := h3)
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi0

  exact Hyperlocal.Targets.ZetaTransfer.criticalzero_zeta_bridge
    (hxi := hxi) (hζ := hζ) (hIm := hIm)

/--
Direct Xi-side endgame from equivalent form (D):

    2 G''(1-ρ) = σ2 G'(1-ρ) - σ3 G(1-ρ)

for every off-seed `s`.
-/
theorem noOffSeed_Xi_of_routeA_recurrence
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hrec :
      ∀ s : Hyperlocal.OffSeed Xi,
        2 * deriv (deriv (routeA_G s)) (1 - s.ρ)
          =
        (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          -
        (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ)) :
    NoOffSeed Xi := by
  have hroute :
      ∀ s : Hyperlocal.OffSeed Xi,
        (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
          + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0 := by
    intro s
    exact routeA_stencil_zero_fromRecurrence (s := s) (hrec := hrec s)
  exact noOffSeed_Xi_of_routeA_scalar (hroute := hroute)

/--
Direct ζ-side transfer from equivalent form (D).
-/
theorem noOffSeed_Zeta_of_routeA_recurrence
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hrec :
      ∀ s : Hyperlocal.OffSeed Xi,
        2 * deriv (deriv (routeA_G s)) (1 - s.ρ)
          =
        (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          -
        (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ)) :
    NoOffSeed Hyperlocal.zeta := by
  have hxi : NoOffSeed Xi :=
    noOffSeed_Xi_of_routeA_recurrence (hrec := hrec)

  have hxi' : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi

  simpa [Hyperlocal.Targets.ZetaTransfer.Zeta] using
    (Hyperlocal.Targets.ZetaTransfer.noOffSeed_zeta_of_noOffSeed_xi (hxi := hxi'))

/--
Direct RH-facing export from equivalent form (D).
-/
theorem criticalzero_zeta_of_routeA_recurrence
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hrec :
      ∀ s : Hyperlocal.OffSeed Xi,
        2 * deriv (deriv (routeA_G s)) (1 - s.ρ)
          =
        (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          -
        (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ))
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0) (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  have hxi : NoOffSeed Hyperlocal.Targets.ZetaTransfer.Xi := by
    have hxi0 : NoOffSeed Xi :=
      noOffSeed_Xi_of_routeA_recurrence (hrec := hrec)
    simpa [Hyperlocal.Targets.XiPacket.Xi, Hyperlocal.Targets.ZetaTransfer.Xi] using hxi0

  exact Hyperlocal.Targets.ZetaTransfer.criticalzero_zeta_bridge
    (hxi := hxi) (hζ := hζ) (hIm := hIm)

end Targets
end Hyperlocal
